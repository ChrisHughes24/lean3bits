import v3.strucs

open term
def x : term := term.var 0
def y : term := term.var 1
def z : term := term.var 2
def a : term := term.var 3
def b : term := term.var 4
def c : term := term.var 5
def d : term := term.var 6

/- Given two `term`s and a bit length `n`, `check_eq` will check if these two
terms are equal for all inputs, for bitvectors of length `n`. The output will be one
of three things,
* `true for k`, means that it is true for bitvectors of length `k`, but possibly not longer
bitvectors
* `true forall` means that it is true for bitvectors of arbitrary length.
* `false after k` means that the expressions are not equal for bitvectors of length `k`
or longer.   -/

#eval check_eq (x +- x) 0 2
#eval check_eq (x - y) (x + -y) 2
#eval check_eq (x + 1) x.incr 2
#eval check_eq (x - 1) x.decr 2

#eval check_eq (x.xor x) term.zero 1
#eval check_eq (x + y) (y + x) 1
#eval check_eq ((x + y) + z) (x + (y + z)) 2
#eval check_eq (not (xor x y)) (and x y - or x y - 1) 2


-- Checking if the operations satisfy the defining identities
#eval check_eq (x + -x) 0 1
#eval check_eq (incr x) (x + 1) 2
#eval check_eq (decr x) (x - 1) 2
#eval check_eq (x + - y) (x - y) 2
#eval check_eq (neg_one) (-1) 2
#eval check_eq (x + 0) x 1
#eval check_eq (x + y) (y + x) 1

-- Equalities from Zulip
#eval check_eq (-x) (not x).incr 1
#eval check_eq (-x) (not x.decr) 1
#eval check_eq (not x) (-x).decr 1
#eval check_eq (-not x) x.incr 1
#eval check_eq (x + y) (x - not y).decr 1
#eval check_eq (x + y) ((xor x y) + (and x y).ls) 2
#eval check_eq (x + y) (or x y + and x y) 1
#eval check_eq (x + y) ((or x y).ls - (xor x y)) 2
#eval check_eq (x - y) (x + not y).incr 2
#eval check_eq (x - y) (xor x y - (and (not x) y).ls) 2
#eval check_eq (x - y) (and x (not y) - (and (not x) y)) 1
#eval check_eq (x - y) ((and x (not y)).ls - (xor x y)) 2
#eval check_eq (xor x y) ((or x y) - (and x y)) 1
#eval check_eq (and x (not y)) (or x y - y) 1
#eval check_eq (and x (not y)) (x - and x y) 1

#eval check_eq (not (x - y)) (y - x).decr 2
#eval check_eq (not (x - y)) (not x + y) 1
#eval check_eq (not (xor x y)) (and x y - (or x y)).decr 1
#eval check_eq (not (xor x y)) (and x y + not (or x y)) 1
#eval check_eq (or x y) (and x (not y) + y) 1
#eval check_eq (and x y) (or (not x) y - not x) 1

-- Some examples that are not true
#eval check_eq (x+y) (x.not + y) 1
#eval check_eq (x + x + x + x).not (-1) 3
