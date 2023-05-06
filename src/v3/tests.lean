import v3.strucs

open term
def x := var 0
def y := var 1

-- Checking if the operations satisfy the defining identities
#eval check_eq (x + -x) 0 5
#eval check_eq (incr x) (x + 1)
#eval check_eq (decr x) (x - 1)
#eval check_eq (x + - y) (x - y)
#eval check_eq (neg_one) (-1)
#eval check_eq (x + 0) (var 0)
#eval check_eq (x + y) (y + x)

-- Equalities from Zulip
#eval check_eq (-x) (not x).incr
#eval check_eq (-x) (not x.decr)
#eval check_eq (not x) (-x).decr
#eval check_eq (-not x) x.incr
#eval check_eq (x + y) (x - not y).decr
#eval check_eq (x + y) ((xor x y) + (and x y).ls)
#eval check_eq (x + y) (or x y + and x y)
#eval check_eq (x + y) ((or x y).ls - (xor x y))
#eval check_eq (x - y) (x + not y).incr
#eval check_eq (x - y) (xor x y - (and (not x) y).ls)
#eval check_eq (x - y) (and x (not y) - (and (not x) y))
#eval check_eq (x - y) ((and x (not y)).ls - (xor x y))
#eval check_eq (xor x y) ((or x y) - (and x y))
#eval check_eq (and x (not y)) (or x y - y)
#eval check_eq (and x (not y)) (x - and x y)

#eval check_eq (not (x - y)) (y - x).decr
#eval check_eq (not (x - y)) (not x + y)
#eval check_eq (not (xor x y)) (and x y - (or x y)).decr
#eval check_eq (not (xor x y)) (and x y + not (or x y))
#eval check_eq (or x y) (and x (not y) + y)
#eval check_eq (and x y) (or (not x) y - not x)
