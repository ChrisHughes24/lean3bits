import decide

open term
def x := var 0
def y := var 1
-- Checking I sub and neg and neg_one satisfy the defining identities
#eval decide (x + -x) 0
#eval decide (x + - y) (x - y)
#eval decide (neg_one) (-1)
#eval decide (x + 0) (var 0)
#eval decide (x + y) (y + x)

-- Equalities from Zulip
#eval decide (-var 0) (not x + 1)
#eval decide (-var 0) (not (x - 1))
#eval decide (not x) (-x - 1)
#eval decide (-not x) (x + 1)
#eval decide (x + y) (x - not y + neg_one)
#eval decide (x + y) ((xor x y) + (and x y).ls)
#eval decide (x + y) (or x y + and x y)
#eval decide (x + y) ((or x y).ls - (xor x y))
--#eval decide (x - y) (x + not y + 1)
#eval decide (x - y) (xor x y - (and (not x) y).ls)
#eval decide (x - y) (and x (not y) - (and (not x) y))
#eval decide (x - y) ((and x (not y)).ls - (xor x y))
#eval decide (xor x y) ((or x y) - (and x y))
#eval decide (and x (not y)) (or x y - y)
#eval decide (and x (not y)) (x - and x y)

#eval decide (not (x - y)) (y - x + neg_one)
#eval decide (not (x - y)) (not x + y)
#eval decide (not (xor x y)) (and x y - or x y + neg_one)
#eval decide (not (xor x y)) (and x y + not (or x y))
#eval decide (or x y) (and x (not y) + y)
#eval decide (and x y) (or (not x) y - not x)
