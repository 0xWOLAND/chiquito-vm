use std::env;

pub fn parse_number(s: &str) -> usize {
    if s.contains("0x") {
        return usize::from_str_radix(s.strip_prefix("0x").unwrap(), 16).unwrap();
    }
    usize::from_str_radix(s, 10).unwrap()
}

pub fn parse_args() -> String {
    let args: Vec<String> = env::args().collect();
    let asm = match args.len() {
        2 => &args[1],
        _ => "fib",
    };
    let asm = format!("asm/{}.asm", asm);
    println!("reading from {asm}...");
    asm
}
