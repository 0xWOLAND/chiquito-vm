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
) {
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
            let memory = memory.clone();
            let read1 = read1.clone();
            let read2 = read2.clone();
            let output = output.clone();
            let opcode = opcode.clone();
            let free_input = free_input.clone();

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
            // ctx.wg(move |ctx, (op, args): (Opcode, Vec<usize>)| {
            ctx.wg(move |ctx, round_values: RoundInput<F>| {
                let mut _memory = vec![F::ZERO; memory_register_count];
                let mut _read1 = vec![F::ZERO; memory_register_count];
                let mut _read2 = vec![F::ZERO; memory_register_count];
                let mut _output = vec![F::ZERO; memory_register_count];
                let mut _opcode = vec![F::ZERO; opcode_count];
                let mut _free_input = F::ZERO;
                let RoundInput { op, args } = round_values;

                // possible opcodes as field elements
                let SET: F = Opcode::Set.as_field();
                let MUL: F = Opcode::Mul.as_field();
                let ADD: F = Opcode::Add.as_field();
                let NEG: F = Opcode::Neg.as_field();
                let EQ: F = Opcode::Eq.as_field();
                let OUT: F = Opcode::Out.as_field();

                let opcodes = match op {
                    SET => {
                        _read1[0] = F::ONE;
                        _read2[0] = F::ONE;
                        _output[args[0]] = F::ONE;
                        _memory[args[0]] = F::from(args[1] as u64);
                        _free_input = F::from(args[1] as u64);
                    }
                    MUL => {
                        _read1[args[1]] = F::ONE;
                        _read2[args[2]] = F::ONE;
                        _output[args[0]] = F::ONE;
                        _memory[args[0]] = _memory[args[1]] * _memory[args[2]]
                    }
                    ADD => {
                        _read1[args[1]] = F::ONE;
                        _read2[args[2]] = F::ONE;
                        _output[args[0]] = F::ONE;
                        _memory[args[0]] = _memory[args[1]] + _memory[args[2]]
                    }
                    NEG => {
                        _read1[args[1]] = F::ONE;
                        _read2[0] = F::ONE;
                        _output[args[0]] = F::ONE;
                        _memory[args[0]] = -F::ONE * _memory[args[1]]
                    }
                    EQ => {
                        _read1[args[0]] = F::ONE;
                        _read2[args[1]] = F::ONE;
                        _output[0] = F::ONE;
                    }
                    OUT => (),
                    _ => (),
                };

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
            })
        });

        ctx.pragma_num_steps(ops_count);

        ctx.trace(move |ctx, ops| {
            let VMInput {
                opcodes,
                argument_counts,
                arguments,
            } = ops;

            let mut start = 0;
            for (len, op) in argument_counts.iter().zip(opcodes) {
                let args = arguments[start..start + len].to_vec();
                ctx.add(&vm_step, RoundInput { op, args });
                start += len;
            }
        })
    });
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

#[derive(Debug, Clone, Copy)]
struct Operation {
    argument_count: usize,
    opcode: Opcode,
}

#[derive(Debug, Clone)]
struct RoundInput<F: PrimeField> {
    op: F,
    args: Vec<usize>,
}

#[derive(Debug, Clone)]
struct VMInput<F: PrimeField> {
    opcodes: Vec<F>,
    argument_counts: Vec<usize>,
    arguments: Vec<usize>,
}

fn parse_hex(s: &str) -> usize {
    usize::from_str_radix(s.strip_prefix("0x").unwrap(), 16).unwrap()
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
            let args: Vec<usize> = _op[1..].iter().map(|x| parse_hex(x)).collect();
            let _op = _op[0].to_owned();
            let op = match _op.as_ref() {
                "set" => Operation {
                    argument_count: 2,
                    opcode: Opcode::Set,
                },
                "mul" => Operation {
                    argument_count: 3,
                    opcode: Opcode::Mul,
                },
                "add" => Operation {
                    argument_count: 3,
                    opcode: Opcode::Add,
                },
                "neg" => Operation {
                    argument_count: 2,
                    opcode: Opcode::Neg,
                },
                "eq" => Operation {
                    argument_count: 2,
                    opcode: Opcode::Eq,
                },
                "out" => Operation {
                    argument_count: 2,
                    opcode: Opcode::Out,
                },
                _ => panic!("Invalid opcode"),
            };
            assert_eq!(
                op.argument_count, argument_count,
                "Invalid number of arguments. Expected {} received {} for {}",
                op.argument_count, argument_count, _op
            );

            memory_register_count = match _op.as_ref() {
                "set" | "out" => cmp::max(memory_register_count, args[0]),
                _ => cmp::max(
                    memory_register_count,
                    args.iter().fold(0, |high, &x| cmp::max(high, x)),
                ),
            };
            op
        })
        .collect::<Vec<Operation>>();
    println!("memory register count: {}", memory_register_count);
    println!("{:?}", contents);
}

#[cfg(test)]
mod tests {
    use crate::parse_hex;

    #[test]
    fn check_hex_parsing() {
        (0..10).into_iter().for_each(|x| {
            let hex = format!("0x{}", x);
            assert_eq!(parse_hex(&hex), x);
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
