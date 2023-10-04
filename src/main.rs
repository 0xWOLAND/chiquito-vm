use std::{cmp, fs, usize};

use std::hash::Hash;

use chiquito::ast::query::Queriable;
use chiquito::ast::Expr;
use chiquito::frontend::dsl::CircuitContext;
use chiquito::{
    ast::ToField,
    frontend::dsl::circuit,
    plonkish::backend::halo2::{chiquito2Halo2, ChiquitoHalo2Circuit},
    plonkish::compiler::{
        cell_manager::SingleRowCellManager, compile, config,
        step_selector::SimpleStepSelectorBuilder,
    },
    plonkish::ir::{assignments::AssignmentGenerator, Circuit},
};
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
use halo2curves::ff::{Field, PrimeField};

fn vm_circuit<F: PrimeField + Eq + Hash>(
    memory_register_count: usize,
    opcode_count: usize,
    ops_count: usize,
) -> (Circuit<F>, Option<AssignmentGenerator<F, VMInput<F>>>) {
    use chiquito::frontend::dsl::cb::*;

    let vm = circuit::<F, VMInput<F>, _>("vm", |ctx| {
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

                let _eq = (_read1 - _read2) * opcode[Opcode::get(Opcode::Eq)];
                constraints.push(_eq);

                let _eq2 = (_output - _output_prev) * opcode[Opcode::get(Opcode::Eq)];
                constraints.push(_eq2);

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
                } = round_values;

                println!("memory_register_count: {:?}", memory_register_count);

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
            let VMInput {
                opcodes,
                argument_counts,
                arguments,
            } = ops;
            let mut _memory = vec![F::ZERO; memory_register_count];

            // possible opcodes as field elements
            let SET: F = Opcode::Set.as_field();
            let MUL: F = Opcode::Mul.as_field();
            let ADD: F = Opcode::Add.as_field();
            let NEG: F = Opcode::Neg.as_field();
            let EQ: F = Opcode::Eq.as_field();
            let OUT: F = Opcode::Out.as_field();

            let mut start = 0;
            argument_counts.iter().zip(opcodes).for_each(|(len, op)| {
                let mut _read1 = vec![F::ZERO; memory_register_count];
                let mut _read2 = vec![F::ZERO; memory_register_count];
                let mut _output = vec![F::ZERO; memory_register_count];
                let mut _opcode = vec![F::ZERO; opcode_count];
                let mut _free_input = F::ZERO;
                let args = arguments[start..start + len].to_vec();
                if op == SET {
                    _read1[0] = F::ONE;
                    _read2[0] = F::ONE;
                    _output[args[0]] = F::ONE;
                    _memory[args[0]] = F::from(args[1] as u64);
                    _free_input = F::from(args[1] as u64);
                } else if op == MUL {
                    _read1[args[1]] = F::ONE;
                    _read2[args[2]] = F::ONE;
                    _output[args[0]] = F::ONE;
                    _memory[args[0]] = _memory[args[1]] * _memory[args[2]];
                } else if op == ADD {
                    _read1[args[1]] = F::ONE;
                    _read2[args[2]] = F::ONE;
                    _output[args[0]] = F::ONE;
                    _memory[args[0]] = _memory[args[1]] + _memory[args[2]];
                } else if op == NEG {
                    _read1[args[1]] = F::ONE;
                    _read2[0] = F::ONE;
                    _output[args[0]] = F::ONE;
                    _memory[args[0]] = -F::ONE * _memory[args[1]];
                } else if op == EQ {
                    _read1[args[0]] = F::ONE;
                    _read2[args[1]] = F::ONE;
                    _output[0] = F::ONE;
                }

                println!("memory -- {:?}", _memory);
                println!("read1 -- {:?}", _read1);
                println!("read2 -- {:?}", _read2);
                println!("output -- {:?}", _output);
                println!("opcode -- {:?}", _opcode);
                println!("free input -- {:?}", _free_input);

                ctx.add(
                    &vm_step,
                    RoundInput {
                        _memory: _memory.clone(),
                        _output: _output.clone(),
                        _read1: _read1.clone(),
                        _read2: _read2.clone(),
                        _opcode: _opcode.clone(),
                        _free_input: _free_input.clone(),
                    },
                );
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

            println!("clear register -- {:?}", clear_register);
            println!("clear opcodes -- {:?}", _opcode);
            ctx.add(
                &vm_step,
                RoundInput {
                    _memory,
                    _output: clear_register.clone(),
                    _read1: clear_register.clone(),
                    _read2: clear_register.clone(),
                    _opcode,
                    _free_input: F::ZERO,
                },
            );
        })
    });
    compile(
        config(SingleRowCellManager {}, SimpleStepSelectorBuilder {}),
        &vm,
    )
}

#[derive(Debug, Copy, Clone)]
enum Opcode {
    Set,
    Mul,
    Add,
    Neg,
    Eq,
    Out,
}

impl Opcode {
    pub const COUNT: usize = 6;
    pub fn get(self) -> usize {
        match self {
            Opcode::Set => 0,
            Opcode::Mul => 1,
            Opcode::Add => 2,
            Opcode::Neg => 3,
            Opcode::Eq => 4,
            Opcode::Out => 0x999999,
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

fn parse_number(s: &str) -> usize {
    if s.contains("0x") {
        return usize::from_str_radix(s.strip_prefix("0x").unwrap(), 16).unwrap();
    }
    usize::from_str_radix(s, 10).unwrap()
}

pub fn main() {
    let mut memory_register_count: usize = 0;

    let contents = fs::read_to_string("asm/test.asm").unwrap();
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
    println!("memory register count: {}", memory_register_count);
    println!("contents -- {:?}", contents);

    // compile to VM input
    let opcodes: Vec<Fr> = contents.iter().map(|call| call.opcode.as_field()).collect();
    let argument_counts: Vec<usize> = contents.iter().map(|call| call.argument_count).collect();
    let arguments: Vec<usize> = contents
        .iter()
        .flat_map(|call| call.args.to_owned())
        .collect();

    let ops_count = contents.len() + 1;
    let opcode_count = Opcode::COUNT;

    let (chiquito, wit_gen) = vm_circuit(memory_register_count, opcode_count, ops_count);
    let compiled = chiquito2Halo2(chiquito);
    let circuit = ChiquitoHalo2Circuit::new(
        compiled,
        wit_gen.map(|x| {
            x.generate(VMInput {
                opcodes,
                argument_counts,
                arguments,
            })
        }),
    );

    let prover = MockProver::<Fr>::run(7, &circuit, circuit.instance()).unwrap();

    let result = prover.verify_par();

    println!("{:#?}", result);

    if let Err(failures) = &result {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::parse_number;

    #[test]
    fn check_hex_parsing() {
        (0..10).into_iter().for_each(|x| {
            let hex = format!("0x{}", x);
            assert_eq!(parse_number(&hex), x);
        })
    }

    #[test]
    fn check() {
        let lengths = vec![3, 5, 6, 7, 3, 6];
        let tot: usize = lengths.iter().sum();
        let arr: Vec<u64> = vec![10; tot]
            .iter()
            .enumerate()
            .map(|(i, &x)| i as u64)
            .collect();

        let mut cur = 0;
        for len in lengths {
            let x = arr[cur..cur + len].to_vec();
            cur += len;
            println!("{:?}", x);
        }
    }
}
