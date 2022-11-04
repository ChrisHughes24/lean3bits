import decide

open term
def x := var 0
def y := var 1

-- Checking if the operations satisfy the defining identities
#eval decide (x + -x) 0
#eval decide (incr x) (x + 1)
#eval decide (decr x) (x - 1)
#eval decide (x + - y) (x - y)
#eval decide (neg_one) (-1)
#eval decide (x + 0) (var 0)
#eval decide (x + y) (y + x)

-- Equalities from Zulip
#eval decide (-x) (not x).incr
#eval decide (-x) (not x.decr)
#eval decide (not x) (-x).decr
#eval decide (-not x) x.incr
#eval decide (x + y) (x - not y).decr
#eval decide (x + y) ((xor x y) + (and x y).ls)
#eval decide (x + y) (or x y + and x y)
#eval decide (x + y) ((or x y).ls - (xor x y))
#eval decide (x - y) (x + not y).incr
#eval decide (x - y) (xor x y - (and (not x) y).ls)
#eval decide (x - y) (and x (not y) - (and (not x) y))
#eval decide (x - y) ((and x (not y)).ls - (xor x y))
#eval decide (xor x y) ((or x y) - (and x y))
#eval decide (and x (not y)) (or x y - y)
#eval decide (and x (not y)) (x - and x y)

#eval decide (not (x - y)) (y - x).decr
#eval decide (not (x - y)) (not x + y)
#eval decide (not (xor x y)) (and x y - (or x y)).decr
#eval decide (not (xor x y)) (and x y + not (or x y))
#eval decide (or x y) (and x (not y) + y)
#eval decide (and x y) (or (not x) y - not x)
