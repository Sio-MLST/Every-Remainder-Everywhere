# Every Remainder Everywhere

For every modulus N ≥ 1, every positive integer w not divisible by 3,
every residue r and every bound B, there is an integer n > B with
n ≡ r (mod N) whose Collatz trajectory reaches w.

In particular, the set of predecessors of w is infinite in every
residue class modulo every N.

The proof is formalized in Lean 4 with no external libraries.

## Files

- `Every Remainder`: Everywhere.pdf": the paper
- `ERE.lean`: the Lean 4 formalization (main theorem: `every_remainder_everywhere`)
