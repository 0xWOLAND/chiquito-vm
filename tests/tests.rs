#[cfg(test)]
pub mod tests {
    use chiquito_vm::*;

    #[test]
    fn fib() {
        let result = run_vm("asm/fib.asm".to_string());
        assert!(result.is_ok());
    }

    #[test]
    fn squares() {
        let contents = parse_args();
        let result = run_vm("asm/squares.asm".to_string());
        assert!(result.is_ok());
    }
}
