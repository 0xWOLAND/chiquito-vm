# Chiquito Virtual Machine [![Rust](https://github.com/0xWOLAND/chiquito-vm/actions/workflows/rust.yml/badge.svg)](https://github.com/0xWOLAND/chiquito-vm/actions/workflows/rust.yml)
`chiquito-vm` is a zkVM, a zero-knowledge virtual machine implemented using Chiquito, a Halo 2 DSL. zkVM enables secure, private computation with cryptographic guarantees.
## Instructions

The following instructions are supported:

- `set`: Set a variable to a constant.
- `mul`: Multiply values and store the result.
- `add`: Add values and store the result.
- `neg`: Negate a value.
- `mov`: Copy a value from one variable to another.
- `eq`: Check if values are equal.
- `out`: Output a value for zero-knowledge proofs.

## Usage

Write assembly programs using these instructions to define variables, perform computations, and generate proofs of correctness. For example:

```asm
set 0x0 10
set 0x1 5
mul 0x0 0x0 0x1
out 0x0 50
```

Run

```bash
cargo run -- fib # fibonacci sequence
cargo run -- squares # repeated squaring sequence
```

By default, `fib.asm` is used. To run custom assembly files, write to `/asm/yourefile.asm` and run `cargo run -- yourfile`.
