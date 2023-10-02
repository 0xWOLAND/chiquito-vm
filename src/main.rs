use std::env;
use std::fs;

#[derive(Debug, Clone, Copy)]
struct Operation {
    argument_count: usize,
    opcode: i32,
}

pub fn main() {
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
            op
        })
        .collect::<Vec<Operation>>();
    println!("{:?}", contents);
}
