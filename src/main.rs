use std::{cmp, fs, usize};

use std::hash::Hash;

use chiquito::ast::query::Queriable;
use chiquito::ast::Expr;
use chiquito::{
    ast::ToField,           // compiled circuit type
    frontend::dsl::circuit, // main function for constructing an AST circuit
    plonkish::backend::halo2::{chiquito2Halo2, ChiquitoHalo2Circuit}, /* compiles to
                             * Chiquito Halo2
                             * backend,
                             * which can be
                             * integrated into
                             * Halo2
                             * circuit */
    plonkish::compiler::{
        cell_manager::SingleRowCellManager, // input for constructing the compiler
        compile,                            // input for constructing the compiler
        config,
        step_selector::SimpleStepSelectorBuilder,
    },
    plonkish::ir::{assignments::AssignmentGenerator, Circuit},
};
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
use halo2curves::ff::Field;

fn vm_circuit<F: Field + From<u64> + Hash>(
    memory_register_count: usize,
    opcode_count: usize,
) -> (Circuit<F>, Option<AssignmentGenerator<F, ()>>) {
    use chiquito::frontend::dsl::cb::*;

    let vm = circuit::<F, (), _>("vm", |ctx| {
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
            ctx.setup(move |ctx| {
                // memory should stay the same unless being updated
                memory.iter().enumerate().for_each(|(i, &reg)| {
                    ctx.transition(eq((reg - reg.next()) * (Expr::from(1) - output[i]), 0));
                });
                // there is only one active selector for each selector range
                let constraints = [&read1, &read2, &output, &opcode]
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

                let _set = (free_input - _output) * opcode[0];
            });
            ctx.wg(move |ctx, x: u32| {})
        });
    });
    todo!()
}

#[derive(Debug, Clone, Copy)]
struct Operation {
    argument_count: usize,
    opcode: i32,
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
            let args: Vec<String> = _op[1..].to_vec();
            let _op = _op[0].to_owned();
            let op = match _op.as_ref() {
                "set" => Operation {
                    argument_count: 2,
                    opcode: 0,
                },
                "mul" => Operation {
                    argument_count: 3,
                    opcode: 1,
                },
                "add" => Operation {
                    argument_count: 3,
                    opcode: 2,
                },
                "neg" => Operation {
                    argument_count: 2,
                    opcode: 3,
                },
                "eq" => Operation {
                    argument_count: 2,
                    opcode: 4,
                },
                "out" => Operation {
                    argument_count: 2,
                    opcode: 0x999999,
                },
                _ => panic!("Invalid opcode"),
            };
            assert_eq!(
                op.argument_count, argument_count,
                "Invalid number of arguments. Expected {} received {} for {}",
                op.argument_count, argument_count, _op
            );

            memory_register_count = match _op.as_ref() {
                "set" | "out" => cmp::max(memory_register_count, parse_hex(&args[0])),
                _ => cmp::max(
                    memory_register_count,
                    args.iter()
                        .map(|x| parse_hex(&x))
                        .fold(0, |high, x| cmp::max(high, x)),
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
}
