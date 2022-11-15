inductive term : Type
| var : ℕ → term
| zero : term
| neg_one : term
| one : term
| and : term → term → term
| or : term → term → term
| xor : term → term → term
| not : term → term
| ls : term → term
| add : term → term → term
| sub : term → term → term
| neg : term → term
| incr : term → term
| decr : term → term
| mul : term → term → term

open term

def zero_seq : ℕ → bool := λ n, ff

def one_seq : ℕ → bool := λ n, n = 0

def neg_one_seq : ℕ → bool := λ n, tt

def and_seq : Π (x y : ℕ → bool), ℕ → bool := λ x y n, x n && y n

def or_seq : Π (x y : ℕ → bool), ℕ → bool := λ x y n, x n || y n

def xor_seq : Π (x y : ℕ → bool), ℕ → bool := λ x y n, bxor (x n) (y n)

def not_seq : Π (x : ℕ → bool), ℕ → bool := λ x n, bnot (x n)

def ls_seq (s : ℕ → bool) : ℕ → bool
| 0 := ff
| (n+1) := s n

def add_seq_aux (x y : ℕ → bool) : ℕ → bool × bool
| 0 := (bxor (x 0) (y 0), x 0 && y 0)
| (n+1) := let carry := (add_seq_aux n).2 in
  let a := x (n + 1), b := y (n + 1) in
  (bxor a (bxor b carry), (a && b) || (b && carry) || (a && carry))

def add_seq (x y : ℕ → bool) : ℕ → bool :=
λ n, (add_seq_aux x y n).1

def sub_seq_aux (x y : ℕ → bool) : ℕ → bool × bool
| 0 := (bxor (x 0) (y 0), bnot (x 0) && y 0)
| (n+1) := let borrow := (sub_seq_aux n).2 in
  let a := x (n + 1), b := y (n + 1) in
  (bxor a (bxor b borrow), (bnot a && b) || ((bnot (bxor a b)) && borrow))

def sub_seq (x y : ℕ → bool) : ℕ → bool :=
λ n, (sub_seq_aux x y n).1

def neg_seq_aux (x : ℕ → bool) : ℕ → bool × bool
| 0 := (x 0, bnot (x 0))
| (n+1) := let borrow := (neg_seq_aux n).2 in
  let a := x (n + 1) in
  (bxor (bnot a) borrow, bnot a && borrow)

def neg_seq (x : ℕ → bool) : ℕ → bool :=
λ n, (neg_seq_aux x n).1

def incr_seq_aux (x : ℕ → bool) : ℕ → bool × bool
| 0 := (bnot (x 0), x 0)
| (n+1) := let carry := (incr_seq_aux n).2 in
  let a := x (n + 1) in
  (bxor a carry, a && carry)

def incr_seq (x : ℕ → bool) : ℕ → bool :=
λ n, (incr_seq_aux x n).1

def decr_seq_aux (x : ℕ → bool) : ℕ → bool × bool
| 0 := (bnot (x 0), bnot (x 0))
| (n+1) := let borrow := (decr_seq_aux n).2 in
  let a := x (n + 1) in
  (bxor a borrow, bnot a && borrow)

def decr_seq (x : ℕ → bool) : ℕ → bool :=
λ n, (decr_seq_aux x n).1

def mul_seq_aux (x y : ℕ → bool) : ℕ → bool × (ℕ → bool)
| 0 := (x 0 && y 0, ff)
| (n+1) := let carry := (mul_seq_aux n).2 in
  let a := x (n + 1), b := y (n + 1) in
  (bxor (a && b) carry, (a && b) || (b && carry) || (a && carry))

def term.eval : Π (t : term) (vars : ℕ → ℕ → bool), ℕ → bool
| (var n) vars := vars n
| zero vars := zero_seq
| one vars := one_seq
| neg_one vars := neg_one_seq
| (and t₁ t₂) vars := and_seq (term.eval t₁ vars) (term.eval t₂ vars)
| (or t₁ t₂) vars := or_seq (term.eval t₁ vars) (term.eval t₂ vars)
| (xor t₁ t₂) vars := xor_seq (term.eval t₁ vars) (term.eval t₂ vars)
| (not t) vars := not_seq (term.eval t vars)
| (ls t) vars := ls_seq (term.eval t vars)
| (add t₁ t₂) vars := add_seq (term.eval t₁ vars) (term.eval t₂ vars)
| (sub t₁ t₂) vars := sub_seq (term.eval t₁ vars) (term.eval t₂ vars)
| (neg t) vars := neg_seq (term.eval t vars)
| (incr t) vars := incr_seq (term.eval t vars)
| (decr t) vars := decr_seq (term.eval t vars)

instance : has_add term := ⟨add⟩
instance : has_sub term := ⟨sub⟩
instance : has_one term := ⟨one⟩
instance : has_zero term := ⟨zero⟩
instance : has_neg term := ⟨neg⟩