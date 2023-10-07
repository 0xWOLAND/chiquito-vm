#[cfg(test)]
pub mod tests {
    use chiquito_vm::{parse::parse_number, run_vm};

    #[test]
    fn fib() {
        let result = run_vm("asm/fib.asm".to_string());
        assert!(result.is_ok());
    }

    #[test]
    fn squares() {
        let result = run_vm("asm/squares.asm".to_string());
        assert!(result.is_ok());
    }

    #[test]
    fn check_hex_parsing() {
        (0..10).into_iter().for_each(|x| {
            let hex = format!("0x{}", x);
            assert_eq!(parse_number(&hex), x);
        })
    }
}
