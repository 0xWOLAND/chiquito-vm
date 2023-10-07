use std::{cmp, fs, hash::Hash, usize};

use chiquito::{
    ast::{query::Queriable, Expr},
    frontend::dsl::{circuit, super_circuit, CircuitContext},
    plonkish::{
        backend::halo2::{
            chiquito2Halo2, chiquitoSuperCircuit2Halo2, ChiquitoHalo2Circuit,
            ChiquitoHalo2SuperCircuit,
        },
        compiler::{
            cell_manager::SingleRowCellManager, compile, config,
            step_selector::SimpleStepSelectorBuilder,
        },
        ir::{assignments::AssignmentGenerator, sc::SuperCircuit, Circuit},
    },
};
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
use halo2curves::ff::PrimeField;

pub mod parse;
use parse::*;
#[derive(Clone)]
struct RamParams {
    operations: Vec<Operation>,
    memory_register_count: usize,
    opcode_count: usize,
    ops_count: usize,
}

#[derive(Clone)]
struct CircuitParams {
    memory_register_count: usize,
    opcode_count: usize,
    ops_count: usize,
}

fn build_trace<F: PrimeField>(params: CircuitParams, ops: VMInput<F>) -> Vec<RoundInput<F>> {
    let CircuitParams {
        memory_register_count,
        opcode_count,
        ops_count,
    } = params;

    let VMInput {
        opcodes,
        argument_counts,
        arguments,
    } = ops;
    let mut _memory = vec![F::ZERO; memory_register_count];

    let mut computation_trace: Vec<RoundInput<F>> = Vec::new();

    // possible opcodes as field elements
    let SET: F = Opcode::Set.as_field();
    let MUL: F = Opcode::Mul.as_field();
    let ADD: F = Opcode::Add.as_field();
    let NEG: F = Opcode::Neg.as_field();
    let MOV: F = Opcode::Mov.as_field();
    let EQ: F = Opcode::Eq.as_field();
    let OUT: F = Opcode::Out.as_field();

    let mut start = 0;
    argument_counts
        .iter()
        .zip(opcodes)
        .enumerate()
        .for_each(|(_clock, (len, op))| {
            let mut _current_memory = _memory.clone();
            let mut _read1 = vec![F::ZERO; memory_register_count];
            let mut _read2 = vec![F::ZERO; memory_register_count];
            let mut _output = vec![F::ZERO; memory_register_count];
            let mut _opcode = vec![F::ZERO; opcode_count];
            let mut _free_input = F::ZERO;
            let _clock = F::from(_clock as u64);
            let args = arguments[start..start + len].to_vec();
            if op == SET {
                _read1[0] = F::ONE;
                _read2[0] = F::ONE;
                _output[args[0]] = F::ONE;
                _current_memory[args[0]] = F::from(args[1] as u64);
                _free_input = F::from(args[1] as u64);
                // set opcode register
                _opcode[Opcode::Set.get()] = F::ONE;
            } else if op == MUL {
                _read1[args[1]] = F::ONE;
                _read2[args[2]] = F::ONE;
                _output[args[0]] = F::ONE;
                _current_memory[args[0]] = _memory[args[1]] * _memory[args[2]];
                // set opcode register
                _opcode[Opcode::Mul.get()] = F::ONE;
            } else if op == ADD {
                _read1[args[1]] = F::ONE;
                _read2[args[2]] = F::ONE;
                _output[args[0]] = F::ONE;
                _current_memory[args[0]] = _memory[args[1]] + _memory[args[2]];
                // set opcode register
                _opcode[Opcode::Add.get()] = F::ONE;
            } else if op == NEG {
                _read1[args[1]] = F::ONE;
                _read2[0] = F::ONE;
                _output[args[0]] = F::ONE;
                _current_memory[args[0]] = -F::ONE * _memory[args[1]];
                // set opcode register
                _opcode[Opcode::Neg.get()] = F::ONE;
            } else if op == MOV {
                _read1[0] = F::ONE;
                _read2[args[1]] = F::ONE;
                _output[args[0]] = F::ONE;
                _current_memory[args[0]] = _current_memory[args[1]];
                // set opcode register
                _opcode[Opcode::Mov.get()] = F::ONE;
            } else if op == EQ {
                _read1[args[0]] = F::ONE;
                _read2[args[1]] = F::ONE;
                _output[0] = F::ONE;
                // set opcode register
                _opcode[Opcode::Eq.get()] = F::ONE;
            } else if op == OUT {
                _read1[args[0]] = F::ONE;
                _read2[args[0]] = F::ONE;
                _free_input = F::from(args[1] as u64);
                _output[args[0]] = F::ONE;
                _opcode[Opcode::Out.get()] = F::ONE;
            }

            println!("memory -- {:?}", _memory);
            println!("read1 -- {:?}", _read1);
            println!("read2 -- {:?}", _read2);
            println!("output -- {:?}", _output);
            println!("opcode -- {:?}", _opcode);
            println!("free input -- {:?}", _free_input);

            computation_trace.push(RoundInput {
                _memory: _memory.clone(),
                _read1,
                _read2,
                _output,
                _opcode,
                _free_input,
                _clock,
            });
            _memory = _current_memory;
            start += len;
        });
    let clear_register = vec![F::ZERO; memory_register_count - 1]
        .iter()
        .chain(&[F::ONE])
        .map(|&x| x)
        .collect::<Vec<F>>();
    let _opcode = vec![F::ZERO; opcode_count - 1]
        .iter()
        .chain(&[F::ONE])
        .map(|&x| x)
        .collect::<Vec<F>>();
    let _clock = F::from(arguments.len() as u64);

    computation_trace.push(RoundInput {
        _memory,
        _read1: clear_register.clone(),
        _read2: clear_register.clone(),
        _output: clear_register.clone(),
        _opcode,
        _free_input: F::ZERO,
        _clock,
    });

    computation_trace
}

fn vm_ram<F: PrimeField + Eq + Hash>(ctx: &mut CircuitContext<F, VMInput<F>>, params: RamParams) {
    use chiquito::frontend::dsl::cb::*;

    let RamParams {
        memory_register_count,
        opcode_count,
        ops_count,
        operations,
    } = params;

    let lookup_op = ctx.fixed("op");

    ctx.pragma_num_steps(ops_count);
    ctx.fixed_gen(move |ctx| {});
}

fn vm_circuit<F: PrimeField + Eq + Hash>(
    ctx: &mut CircuitContext<F, VMInput<F>>,
    params: CircuitParams,
) {
    use chiquito::frontend::dsl::cb::*;

    let CircuitParams {
        memory_register_count,
        opcode_count,
        ops_count,
    } = params;

    let memory: Vec<Queriable<F>> = (0..memory_register_count)
        .map(|i| ctx.forward(&format!("memory_register_{}", i)))
        .collect();
    let read1: Vec<Queriable<F>> = (0..memory_register_count)
        .map(|i| ctx.forward(&format!("read1_register_{}", i)))
        .collect();
    let read2: Vec<Queriable<F>> = (0..memory_register_count)
        .map(|i| ctx.forward(&format!("read2_register_{}", i)))
        .collect();
    let output: Vec<Queriable<F>> = (0..memory_register_count)
        .map(|i| ctx.forward(&format!("output_{}", i)))
        .collect();
    let opcode: Vec<Queriable<F>> = (0..opcode_count)
        .map(|i| ctx.forward(&format!("opcode_{}", i)))
        .collect();
    let free_input = ctx.forward("free_input");

    let vm_step = ctx.step_type_def("vm step", |ctx| {
        ctx.setup(|ctx| {
            // memory should stay the same unless being updated
            memory.iter().enumerate().for_each(|(i, &reg)| {
                ctx.transition(eq((reg - reg.next()) * (Expr::from(1) - output[i]), 0));
            });
            // there is only one active selector for each selector range
            let mut constraints = [&read1, &read2, &output, &opcode]
                .iter()
                .map(|selector_range| {
                    selector_range
                        .iter()
                        .fold(Expr::from(0), |acc, &cur| acc + cur)
                        - Expr::from(1)
                })
                .collect::<Vec<Expr<F>>>();

            // Operation constraints
            let _output: Expr<F> = output
                .iter()
                .zip(&memory)
                .map(|(&a, &b)| a * b.next())
                .fold(Expr::from(0), |acc, cur| acc + cur);
            let _output_prev: Expr<F> = output
                .iter()
                .zip(&memory)
                .map(|(&a, &b)| a * b)
                .fold(Expr::from(0), |acc, cur| acc + cur);
            let _read1: Expr<F> = read1
                .iter()
                .zip(&memory)
                .map(|(&a, &b)| a * b)
                .fold(Expr::from(0), |acc, cur| acc + cur);
            let _read2: Expr<F> = read2
                .iter()
                .zip(&memory)
                .map(|(&a, &b)| a * b)
                .fold(Expr::from(0), |acc, cur| acc + cur);

            let _set = (free_input - _output.clone()) * opcode[Opcode::get(Opcode::Set)];
            constraints.push(_set);

            let _add = (_read1.clone() + _read2.clone() - _output.clone())
                * opcode[Opcode::get(Opcode::Add)];
            constraints.push(_add);

            let _neg = (_read1.clone() + _output.clone()) * opcode[Opcode::get(Opcode::Neg)];
            constraints.push(_neg);

            let _mul = (_read1.clone() * _read2.clone() - _output.clone())
                * opcode[Opcode::get(Opcode::Mul)];
            constraints.push(_mul);

            let _mov = (_read2.clone() - _output.clone()) * opcode[Opcode::get(Opcode::Mov)];
            constraints.push(_mov);

            let _eq = (_read1 - _read2) * opcode[Opcode::get(Opcode::Eq)];
            constraints.push(_eq);

            let _eq2 = (_output.clone() - _output_prev) * opcode[Opcode::get(Opcode::Eq)];
            constraints.push(_eq2);

            let _out = (_output - free_input) * opcode[Opcode::get(Opcode::Out)];
            constraints.push(_out);

            ctx.transition(eq(
                constraints
                    .iter()
                    .fold(Expr::from(0), |acc, cur| acc + cur.clone()),
                0,
            ));
        });

        ctx.wg(move |ctx, round_values: RoundInput<F>| {
            let RoundInput {
                _memory,
                _output,
                _read1,
                _read2,
                _opcode,
                _free_input,
                _clock,
            } = round_values;

            // println!("memory_register_count: {:?}", memory_register_count);

            memory
                .iter()
                .zip(_memory)
                .for_each(|(&a, b)| ctx.assign(a, b));

            read1
                .iter()
                .zip(_read1)
                .for_each(|(&a, b)| ctx.assign(a, b));

            read2
                .iter()
                .zip(_read2)
                .for_each(|(&a, b)| ctx.assign(a, b));

            output
                .iter()
                .zip(_output)
                .for_each(|(&a, b)| ctx.assign(a, b));

            opcode
                .iter()
                .zip(_opcode)
                .for_each(|(&a, b)| ctx.assign(a, b));

            ctx.assign(free_input, _free_input)
        })
    });

    ctx.pragma_num_steps(ops_count);

    ctx.trace(move |ctx, ops| {
        let computation_trace = build_trace(params.clone(), ops);

        computation_trace
            .iter()
            .for_each(|values| ctx.add(&vm_step, values.clone()));
    })
}

fn vm_super_circuit<F: PrimeField + Eq + Hash>(params: RamParams) -> SuperCircuit<F, VMInput<F>> {
    super_circuit::<F, VMInput<F>, _>("vm", |ctx| {
        let single_config = config(SingleRowCellManager {}, SimpleStepSelectorBuilder {});
        let RamParams {
            operations: _,
            memory_register_count,
            opcode_count,
            ops_count,
        } = params;

        let vm_params = CircuitParams {
            memory_register_count,
            opcode_count,
            ops_count,
        };
        let (vm, _) = ctx.sub_circuit(single_config, vm_circuit, vm_params);

        ctx.mapping(move |ctx, values| {
            ctx.map(&vm, values);
        })
    })
}

#[derive(Debug, Copy, Clone)]
enum Opcode {
    Set,
    Mul,
    Add,
    Neg,
    Mov,
    Eq,
    Out,
}

impl Opcode {
    pub const COUNT: usize = 7;
    pub fn get(self) -> usize {
        match self {
            Opcode::Set => 0,
            Opcode::Mul => 1,
            Opcode::Add => 2,
            Opcode::Neg => 3,
            Opcode::Mov => 4,
            Opcode::Eq => 5,
            Opcode::Out => 6,
        }
    }
    pub fn as_field<F: PrimeField>(self) -> F {
        F::from(self.get() as u64)
    }
}

#[derive(Debug, Clone)]
struct Operation {
    argument_count: usize,
    args: Vec<usize>,
    opcode: Opcode,
}

#[derive(Debug, Clone)]
struct RoundInput<F: PrimeField> {
    _clock: F,
    _memory: Vec<F>,
    _output: Vec<F>,
    _read1: Vec<F>,
    _read2: Vec<F>,
    _opcode: Vec<F>,
    _free_input: F,
}

#[derive(Debug, Clone)]
struct VMInput<F: PrimeField> {
    opcodes: Vec<F>,
    argument_counts: Vec<usize>,
    arguments: Vec<usize>,
}

pub fn run_vm(file: String) -> Result<(), ()> {
    let mut memory_register_count: usize = 0;
    let contents = fs::read_to_string(file).unwrap();

    let contents = contents
        .lines()
        .map(|line| {
            // doesn't count content after `;`
            line[0..line.find(";").unwrap_or_else(|| line.len())].to_string()
        })
        .filter(|s| !s.is_empty())
        .map(|op| {
            let _op = op
                .split(" ")
                .map(|s| s.to_string())
                .collect::<Vec<String>>();
            let argument_count = _op.len() - 1;
            let args: Vec<usize> = _op[1..].iter().map(|x| parse_number(x)).collect();
            let _op = _op[0].to_owned();

            memory_register_count = match _op.as_ref() {
                "set" | "out" => cmp::max(memory_register_count, args[0]),
                _ => cmp::max(
                    memory_register_count,
                    args.iter().fold(0, |high, &x| cmp::max(high, x)),
                ),
            };
            let op = match _op.as_ref() {
                "set" => Operation {
                    argument_count: 2,
                    opcode: Opcode::Set,
                    args,
                },
                "mul" => Operation {
                    argument_count: 3,
                    opcode: Opcode::Mul,
                    args,
                },
                "add" => Operation {
                    argument_count: 3,
                    opcode: Opcode::Add,
                    args,
                },
                "neg" => Operation {
                    argument_count: 2,
                    opcode: Opcode::Neg,
                    args,
                },
                "mov" => Operation {
                    argument_count: 2,
                    opcode: Opcode::Mov,
                    args,
                },
                "eq" => Operation {
                    argument_count: 2,
                    opcode: Opcode::Eq,
                    args,
                },
                "out" => Operation {
                    argument_count: 2,
                    opcode: Opcode::Out,
                    args,
                },
                _ => panic!("Invalid opcode"),
            };
            assert_eq!(
                op.argument_count, argument_count,
                "Invalid number of arguments. Expected {} received {} for {}",
                op.argument_count, argument_count, _op
            );

            op
        })
        .collect::<Vec<Operation>>();
    memory_register_count += 1;

    // compile to VM input
    let opcodes: Vec<Fr> = contents.iter().map(|call| call.opcode.as_field()).collect();
    let argument_counts: Vec<usize> = contents.iter().map(|call| call.argument_count).collect();
    let arguments: Vec<usize> = contents
        .iter()
        .flat_map(|call| call.args.to_owned())
        .collect();

    let ops_count = contents.len() + 1;
    let opcode_count = Opcode::COUNT;

    let params = RamParams {
        memory_register_count,
        opcode_count,
        ops_count,
        operations: contents,
    };

    let super_circuit = vm_super_circuit(params);
    let compiled = chiquitoSuperCircuit2Halo2(&super_circuit);
    let circuit = ChiquitoHalo2SuperCircuit::new(
        compiled,
        super_circuit.get_mapping().generate(VMInput {
            opcodes,
            argument_counts,
            arguments,
        }),
    );

    let prover = MockProver::<Fr>::run(7, &circuit, circuit.instance()).unwrap();

    let result = prover.verify_par();

    match result {
        Ok(_) => Ok(()),
        Err(failures) => {
            for failure in failures.iter() {
                println!("{}", failure);
            }
            Err(())
        }
    }
}
