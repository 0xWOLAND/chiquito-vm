`chiquito-vm` is a zkVM, a zero-knowledge virtual machine implemented using Chiquito, a Halo 2 DSL. zkVM enables secure, private computation with cryptographic guarantees. Chiquito offers a high-level interface for zkVM programs.

## Instructions

zkVM in Chiquito supports the following instructions:

- `set`: Set a variable to a constant.
- `mul`: Multiply values and store the result.
- `add`: Add values and store the result.
- `neg`: Negate a value.
- `mov`: Copy a value from one variable to another.
- `eq`: Check if values are equal.
- `out`: Output a value for zero-knowledge proofs.

## Usage

Write Chiquito programs using these instructions to define variables, perform computations, and generate proofs of correctness. For example:

```chiquito
set 0x0 10
set 0x1 5
mul 0x0 0x0 0x1
out 0x0 50
```

zkVM ensures secure computation without revealing values.
