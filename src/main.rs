use chiquito_vm::{parse_args, run_vm};
pub fn main() {
    let contents = parse_args();
    let result = run_vm(contents);
    println!(
        "result --- {}",
        match result {
            Ok(_) => "Valid computation trace!",
            Err(_) => "Invalid computatation trace...",
        }
    );
}
