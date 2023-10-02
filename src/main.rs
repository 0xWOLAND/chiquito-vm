use std::{cmp, fs};

use std::hash::Hash;

use chiquito::frontend::dsl::circuit;
use chiquito::plonkish::ir::assignments::AssignmentGenerator;
use halo2curves::ff::Field;

// fn vm_circuit<F: Field + From<u64> + Hash>() -> (Circuit<F>, Option<AssignmentGenerator<F, ()>>) {
//     use chiquito::frontend::dsl::cb::*;

//     let vm = circuit::<F, (), _>("vm", |ctx| {});
// }

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
                    opcode: 1,
                },
                "mul" => Operation {
                    argument_count: 3,
                    opcode: 2,
                },
                "add" => Operation {
                    argument_count: 3,
                    opcode: 3,
                },
                "neg" => Operation {
                    argument_count: 2,
                    opcode: 4,
                },
                "eq" => Operation {
                    argument_count: 2,
                    opcode: 5,
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
