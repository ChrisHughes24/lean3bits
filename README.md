# Tools for proving equalities of operations on bitvectors

This repository contains a program for deciding equalities of operations on bitvectors involving a combination of the group operations, unity and the bitwise operations. For example, it can verify the equality $x + y = (x \oplus y)/ + 2(x\And y)$. 

There is a proof of decidablity in `src/v1/decide.lean`. However this proof is a very slow algorithm. There is also a much faster algorithm demonstrated in `src/vs/tests.lean`. This second algorithm does not yet have a Lean proof of correctness.
