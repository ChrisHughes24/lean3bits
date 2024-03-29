import data.fintype.card
import tactic.zify
import tactic.ring
import tactic.linarith
import .defs

open sum

variables {α β α' β' : Type} {γ : β → Type}

def propagate_aux (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (x : β → ℕ → bool) : ℕ → (α → bool) × bool
| 0 := next_bit init_carry (λ i, x i 0)
| (n+1) :=
next_bit (propagate_aux n).1 (λ i, x i (n+1))

def propagate (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (x : β → ℕ → bool) (i : ℕ) : bool :=
(propagate_aux init_carry next_bit x i).2

@[simp] def propagate_carry (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool))
  (x : β → ℕ → bool) : ℕ → (α → bool)
| 0 := next_bit init_carry (λ i, x i 0)
| (n+1) := next_bit (propagate_carry n) (λ i, x i (n+1))

@[simp] def propagate_carry2 (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool))
  (x : β → ℕ → bool) : ℕ → (α → bool)
| 0 := init_carry
| (n+1) := next_bit (propagate_carry2 n) (λ i, x i n)

lemma propagate_carry2_succ (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool))
  (x : β → ℕ → bool) (n : ℕ) :
  propagate_carry2 init_carry next_bit x (n+1) =
  propagate_carry init_carry next_bit x n :=
by induction n; simp *

@[simp] lemma propagate_aux_fst_eq_carry (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (x : β → ℕ → bool) : ∀ n : ℕ,
  (propagate_aux init_carry next_bit x n).1 =
  propagate_carry init_carry (λ c b, (next_bit c b).1) x n
| 0 := rfl
| (n+1) := by rw [propagate_aux, propagate_carry, propagate_aux_fst_eq_carry]

@[simp] lemma propagate_zero (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
  (α → bool) × bool)
  (x : β → ℕ → bool) :
  propagate init_carry next_bit x 0 = (next_bit init_carry (λ i, x i 0)).2 :=
rfl

lemma propagate_succ (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (x : β → ℕ → bool) (i : ℕ) :
  propagate init_carry next_bit x (i+1) = (next_bit
    (propagate_carry init_carry (λ c b, (next_bit c b).1) x i)
    (λ j, x j (i+1))).2 :=
by rw [← propagate_aux_fst_eq_carry]; refl

lemma propagate_succ2 (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (x : β → ℕ → bool) (i : ℕ) :
  propagate init_carry next_bit x (i+1) = (next_bit
    (propagate_carry2 init_carry (λ c b, (next_bit c b).1) x (i+1))
    (λ j, x j (i+1))).2 :=
by rw [propagate_carry2_succ, ← propagate_aux_fst_eq_carry]; refl

lemma propagate_carry_propagate {δ : β → Type*} {β' : Type}
    (f : Π a, δ a → β') : Π (n : ℕ) (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool))
  (init_carry_x : Π a, γ a → bool)
  (next_bit_x : Π a (carry : γ a → bool) (bits : δ a → bool),
    (γ a → bool) × bool)
  (x : β' → ℕ → bool),
  propagate_carry init_carry next_bit (λ a, propagate (init_carry_x a)
    (next_bit_x a) (λ d, x (f a d))) n =
  propagate_carry
    (λ a : α ⊕ (Σ a, γ a), sum.elim init_carry (λ b : Σ a, γ a,
      init_carry_x b.1 b.2) a)
    (λ (carry : (α ⊕ (Σ a, γ a)) → bool) (bits : β' → bool),
  -- first compute (propagate (init_carry_x a) (next_bit_x a) (x a) n)
      let f : Π (a : β), (γ a → bool) × bool := λ a, next_bit_x a (λ d,
        carry (inr ⟨a, d⟩)) (λ d, bits (f a d)) in
      let g : (α → bool) := (next_bit (carry ∘ inl) (λ a, (f a).2)) in
      sum.elim g (λ x, (f x.1).1 x.2)
    )
    x n ∘ inl
| 0 init_carry next_bit init_carry_x next_bit_x x := rfl
| (n+1) init_carry next_bit init_carry_x next_bit_x x := begin
  have := propagate_carry_propagate n,
  clear_aux_decl,
  simp only [propagate_carry, propagate_succ, elim_inl] at *,
  conv_lhs { simp only [this] },
  clear this,
  ext,
  congr,
  ext,
  congr,
  induction n with n ih,
  { simp },
  { simp [ih] }
end

lemma propagate_propagate {δ : β → Type*} {β' : Type}
    (f : Π a, δ a → β') : Π (n : ℕ) (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (init_carry_x : Π a, γ a → bool)
  (next_bit_x : Π a (carry : γ a → bool) (bits : δ a → bool),
    (γ a → bool) × bool)
  (x : β' → ℕ → bool),
  propagate init_carry next_bit (λ a, propagate (init_carry_x a)
    (next_bit_x a) (λ d, x (f a d))) n =
  propagate
    (λ a : α ⊕ (Σ a, γ a), sum.elim init_carry (λ b : Σ a, γ a,
      init_carry_x b.1 b.2) a)
    (λ (carry : (α ⊕ (Σ a, γ a)) → bool) (bits : β' → bool),
      -- first compute (propagate (init_carry_x a) (next_bit_x a) (x a) n)
      let f : Π (a : β), (γ a → bool) × bool := λ a, next_bit_x a (λ d,
        carry (inr ⟨a, d⟩)) (λ d, bits (f a d)) in
      let g : (α → bool) × bool := (next_bit (carry ∘ inl) (λ a, (f a).2)) in
      (sum.elim g.1 (λ x, (f x.1).1 x.2), g.2)
    )
  x n
| 0 init_carry next_bit init_carry_x next_bit_x x := rfl
| (n+1) init_carry next_bit init_carry_x next_bit_x x := begin
  simp only [propagate_succ],
  clear_aux_decl,
  rw [propagate_carry_propagate],
  congr,
  ext,
  congr,
  induction n with n ih,
  { simp },
  { simp [ih] }
end

lemma propagate_carry_change_vars {β' : Type}
  (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool))
  (x : β' → ℕ → bool) (i : ℕ)
  (change_vars : β → β') :
  propagate_carry init_carry next_bit (λ b, x (change_vars b)) i =
  propagate_carry init_carry (λ (carry : α → bool) (bits : β' → bool),
    next_bit carry (λ b, bits (change_vars b))) x i :=
begin
  induction i,
  { simp },
  { simp * }
end

lemma propagate_change_vars {β' : Type}
  (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (x : β' → ℕ → bool) (i : ℕ)
  (change_vars : β → β') :
  propagate init_carry next_bit (λ b, x (change_vars b)) i =
  propagate init_carry (λ (carry : α → bool) (bits : β' → bool),
    next_bit carry (λ b, bits (change_vars b))) x i :=
begin
  induction i with i ih,
  { refl },
  { simp only [propagate_succ, propagate_carry_change_vars, ih] }
end

open term

@[simp] def arity : term → ℕ
| (var n) := n+1
| zero := 0
| one := 0
| neg_one := 0
| (and t₁ t₂) := max (arity t₁) (arity t₂)
| (or t₁ t₂) := max (arity t₁) (arity t₂)
| (xor t₁ t₂) := max (arity t₁) (arity t₂)
| (not t) := arity t
| (ls t) := arity t
| (add t₁ t₂) := max (arity t₁) (arity t₂)
| (sub t₁ t₂) := max (arity t₁) (arity t₂)
| (neg t) := arity t
| (incr t) := arity t
| (decr t) := arity t

@[simp] def term.eval_fin : Π (t : term) (vars : fin (arity t) → ℕ → bool), ℕ → bool
| (var n) vars := vars (fin.last n)
| zero vars := zero_seq
| one vars := one_seq
| neg_one vars := neg_one_seq
| (and t₁ t₂) vars :=
  and_seq (term.eval_fin t₁
    (λ i, vars (fin.cast_le (by simp [arity]) i)))
  (term.eval_fin t₂
    (λ i, vars (fin.cast_le (by simp [arity]) i)))
| (or t₁ t₂) vars :=
  or_seq (term.eval_fin t₁
    (λ i, vars (fin.cast_le (by simp [arity]) i)))
  (term.eval_fin t₂
    (λ i, vars (fin.cast_le (by simp [arity]) i)))
| (xor t₁ t₂) vars :=
  xor_seq (term.eval_fin t₁
    (λ i, vars (fin.cast_le (by simp [arity]) i)))
  (term.eval_fin t₂
    (λ i, vars (fin.cast_le (by simp [arity]) i)))
| (not t) vars := not_seq (term.eval_fin t vars)
| (ls t) vars := ls_seq (term.eval_fin t vars)
| (add t₁ t₂) vars :=
  add_seq (term.eval_fin t₁
    (λ i, vars (fin.cast_le (by simp [arity]) i)))
  (term.eval_fin t₂
    (λ i, vars (fin.cast_le (by simp [arity]) i)))
| (sub t₁ t₂) vars :=
  sub_seq (term.eval_fin t₁
    (λ i, vars (fin.cast_le (by simp [arity]) i)))
  (term.eval_fin t₂
    (λ i, vars (fin.cast_le (by simp [arity]) i)))
| (neg t) vars := neg_seq (term.eval_fin t vars)
| (incr t) vars := incr_seq (term.eval_fin t vars)
| (decr t) vars := decr_seq (term.eval_fin t vars)

lemma eval_fin_eq_eval (t : term) (vars : ℕ → ℕ → bool) :
  term.eval_fin t (λ i, vars i) = term.eval t vars :=
begin
  induction t;
  dsimp [term.eval_fin, term.eval, arity] at *; simp *
end

lemma id_eq_propagate (x : ℕ → bool) :
  x = propagate empty.elim (λ _ (y : unit → bool), (empty.elim, y ())) (λ _, x) :=
by ext n; cases n; refl

lemma zero_eq_propagate :
  zero_seq = propagate empty.elim (λ (_ _ : empty → bool), (empty.elim, ff)) empty.elim :=
by ext n; cases n; refl

lemma one_eq_propagate :
  one_seq = propagate (λ _ : unit, tt) (λ f (_ : empty → bool), (λ _, ff, f ())) empty.elim :=
begin
  ext n,
  cases n with n,
  { refl },
  { cases n,
    { simp [one_seq, propagate_succ] },
    { simp [one_seq, propagate_succ] } }
end

lemma and_eq_propagate (x y : ℕ → bool) :
  and_seq x y = propagate empty.elim
    (λ _ (y : bool → bool), (empty.elim, y tt && y ff)) (λ b, cond b x y) :=
by ext n; cases n; simp [propagate, propagate_aux, and_seq]

lemma or_eq_propagate (x y : ℕ → bool) :
  or_seq x y = propagate empty.elim
    (λ _ (y : bool → bool), (empty.elim, y tt || y ff)) (λ b, cond b x y) :=
by ext n; cases n; simp [propagate, propagate_aux, or_seq]

lemma xor_eq_propagate (x y : ℕ → bool) :
  xor_seq x y = propagate empty.elim
    (λ _ (y : bool → bool), (empty.elim, bxor (y tt) (y ff))) (λ b, cond b x y) :=
by ext n; cases n; simp [propagate, propagate_aux, xor_seq]

lemma not_eq_propagate (x : ℕ → bool) :
  not_seq x = propagate empty.elim (λ _ (y : unit → bool), (empty.elim, bnot (y ()))) (λ _, x) :=
by ext n; cases n; simp [propagate, propagate_aux, not_seq]

lemma ls_eq_propagate (x : ℕ → bool) :
  ls_seq x = propagate (λ _ : unit, ff) (λ (carry x : unit → bool), (x, carry ())) (λ _, x) :=
begin
  ext n,
  cases n with n,
  { refl },
  { cases n,
    { simp [ls_seq, propagate_succ] },
    { simp [ls_seq, propagate_succ] } }
end

lemma add_seq_aux_eq_propagate_carry (x y : ℕ → bool) (n : ℕ) :
  (add_seq_aux x y n).2 = propagate_carry (λ _, ff)
    (λ (carry : unit → bool) (bits : bool → bool),
      λ _, (bits tt && bits ff) || (bits ff && carry ()) || (bits tt && carry ()))
  (λ b, cond b x y) n () :=
begin
  induction n,
  { simp [add_seq_aux] },
  { simp [add_seq_aux, *] }
end

lemma add_eq_propagate (x y : ℕ → bool) :
  add_seq x y = propagate (λ _, ff)
    (λ (carry : unit → bool) (bits : bool → bool),
      (λ _, (bits tt && bits ff) || (bits ff && carry ()) || (bits tt && carry ()),
        bxor (bits tt) (bxor (bits ff) (carry ()))))
  (λ b, cond b x y) :=
begin
  ext n,
  cases n with n,
  { simp [add_seq, add_seq_aux] },
  { cases n,
    { simp [add_seq, add_seq_aux, propagate_succ] },
    { simp [add_seq, add_seq_aux, add_seq_aux_eq_propagate_carry,
        propagate_succ] } }
end

lemma sub_seq_aux_eq_propagate_carry (x y : ℕ → bool) (n : ℕ) :
  (sub_seq_aux x y n).2 = propagate_carry (λ _, ff)
    (λ (carry : unit → bool) (bits : bool → bool),
      λ _, (bnot (bits tt) && (bits ff)) ||
        (bnot (bxor (bits tt) (bits ff))) && carry ())
  (λ b, cond b x y) n () :=
begin
  induction n,
  { simp [sub_seq_aux] },
  { simp [sub_seq_aux, *] }
end

lemma sub_eq_propagate (x y : ℕ → bool) :
  sub_seq x y = propagate (λ _, ff)
    (λ (carry : unit → bool) (bits : bool → bool),
      (λ _, (bnot (bits tt) && (bits ff)) ||
        ((bnot (bxor (bits tt) (bits ff))) && carry ()),
        bxor (bits tt) (bxor (bits ff) (carry ()))))
  (λ b, cond b x y) :=
begin
  ext n,
  cases n with n,
  { simp [sub_seq, sub_seq_aux] },
  { cases n,
    { simp [sub_seq, sub_seq_aux, propagate_succ] },
    { simp [sub_seq, sub_seq_aux, sub_seq_aux_eq_propagate_carry,
        propagate_succ] } }
end

lemma neg_seq_aux_eq_propagate_carry (x : ℕ → bool) (n : ℕ) :
  (neg_seq_aux x n).2 = propagate_carry (λ _, tt)
    (λ (carry : unit → bool) (bits : unit → bool),
      λ _, (bnot (bits ())) && (carry ()))
  (λ _, x) n () :=
begin
  induction n,
  { simp [neg_seq_aux] },
  { simp [neg_seq_aux, *] }
end

lemma neg_eq_propagate (x : ℕ → bool) :
  neg_seq x = propagate (λ _, tt)
    (λ (carry : unit → bool) (bits : unit → bool),
      (λ _, (bnot (bits ())) && (carry ()), bxor (bnot (bits ())) (carry ())))
  (λ _, x) :=
begin
  ext n,
  cases n with n,
  { simp [neg_seq, neg_seq_aux] },
  { cases n,
    { simp [neg_seq, neg_seq_aux, propagate_succ] },
    { simp [neg_seq, neg_seq_aux, neg_seq_aux_eq_propagate_carry,
        propagate_succ] } }
end

lemma incr_seq_aux_eq_propagate_carry (x : ℕ → bool) (n : ℕ) :
  (incr_seq_aux x n).2 = propagate_carry (λ _, tt)
    (λ (carry : unit → bool) (bits : unit → bool),
      λ _, (bits ()) && carry ())
  (λ _, x) n () :=
begin
  induction n,
  { simp [incr_seq_aux] },
  { simp [incr_seq_aux, *] }
end

lemma incr_eq_propagate (x : ℕ → bool) :
  incr_seq x = propagate (λ _, tt)
    (λ (carry : unit → bool) (bits : unit → bool),
      (λ _, (bits ()) && carry (), bxor (bits ()) (carry ())))
  (λ _, x) :=
begin
  ext n,
  cases n with n,
  { simp [incr_seq, incr_seq_aux] },
  { cases n,
    { simp [incr_seq, incr_seq_aux, propagate_succ] },
    { simp [incr_seq, incr_seq_aux, incr_seq_aux_eq_propagate_carry,
        propagate_succ] } }
end

lemma decr_seq_aux_eq_propagate_carry (x : ℕ → bool) (n : ℕ) :
  (decr_seq_aux x n).2 = propagate_carry (λ _, tt)
    (λ (carry : unit → bool) (bits : unit → bool),
      λ _, (bnot (bits ())) && carry ())
  (λ _, x) n () :=
begin
  induction n,
  { simp [decr_seq_aux] },
  { simp [decr_seq_aux, *] }
end

lemma decr_eq_propagate (x : ℕ → bool) :
  decr_seq x = propagate (λ _, tt)
    (λ (carry : unit → bool) (bits : unit → bool),
      (λ _, (bnot (bits ())) && carry (), bxor (bits ()) (carry ())))
  (λ _, x) :=
begin
  ext n,
  cases n with n,
  { simp [decr_seq, decr_seq_aux] },
  { cases n,
    { simp [decr_seq, decr_seq_aux, propagate_succ] },
    { simp [decr_seq, decr_seq_aux, decr_seq_aux_eq_propagate_carry,
        propagate_succ] } }
end

structure propagate_struc (arity : Type) : Type 1 :=
( α  : Type )
[ i : fintype α ]
( init_carry : α → bool )
( next_bit : Π (carry : α → bool) (bits : arity → bool),
    (α → bool) × bool )

attribute [instance] propagate_struc.i

namespace propagate_struc

variables {arity : Type} (p : propagate_struc arity)

def eval : (arity → ℕ → bool) → ℕ → bool :=
propagate p.init_carry p.next_bit

def change_vars {arity2 : Type} (change_vars : arity → arity2) :
  propagate_struc arity2 :=
{ α := p.α,
  i := p.i,
  init_carry := p.init_carry,
  next_bit := λ carry bits, p.next_bit carry (λ i, bits (change_vars i)) }

def compose [fintype arity]
  (new_arity : Type)
  (q_arity : arity → Type)
  (vars : Π (a : arity), q_arity a → new_arity)
  (q : Π (a : arity), propagate_struc (q_arity a)) :
  propagate_struc (new_arity) :=
{ α := p.α ⊕ (Σ a, (q a).α),
  i := by letI := p.i; apply_instance,
  init_carry := sum.elim p.init_carry (λ x, (q x.1).init_carry x.2),
  next_bit := λ carry bits,
    let f : Π (a : arity), ((q a).α → bool) × bool := λ a, (q a).next_bit (λ d,
        carry (inr ⟨a, d⟩)) (λ d, bits (vars a d)) in
    let g : (p.α → bool) × bool := (p.next_bit (carry ∘ inl) (λ a, (f a).2)) in
    (sum.elim g.1 (λ x, (f x.1).1 x.2), g.2) }

lemma eval_compose [fintype arity]
  (new_arity : Type)
  (q_arity : arity → Type)
  (vars : Π (a : arity), q_arity a → new_arity)
  (q : Π (a : arity), propagate_struc (q_arity a))
  (x : new_arity → ℕ → bool):
  (p.compose new_arity q_arity vars q).eval x =
  p.eval (λ a, (q a).eval (λ i, x (vars _ i))) :=
begin
  ext n,
  simp only [eval, compose, propagate_propagate]
end

def and : propagate_struc bool :=
{ α := empty,
  i := by apply_instance,
  init_carry := empty.elim,
  next_bit := λ carry bits, (empty.elim, bits tt && bits ff) }

@[simp] lemma eval_and (x : bool → ℕ → bool) : and.eval x = and_seq (x tt) (x ff) :=
by ext n; cases n; simp [and, and_seq, eval, propagate_succ]

def or : propagate_struc bool :=
{ α := empty,
  i := by apply_instance,
  init_carry := empty.elim,
  next_bit := λ carry bits, (empty.elim, bits tt || bits ff) }

@[simp] lemma eval_or (x : bool → ℕ → bool) : or.eval x = or_seq (x tt) (x ff) :=
by ext n; cases n; simp [or, or_seq, eval, propagate_succ]

def xor : propagate_struc bool :=
{ α := empty,
  i := by apply_instance,
  init_carry := empty.elim,
  next_bit := λ carry bits, (empty.elim, bxor (bits tt) (bits ff)) }

@[simp] lemma eval_xor (x : bool → ℕ → bool) : xor.eval x = xor_seq (x tt) (x ff) :=
by ext n; cases n; simp [xor, xor_seq, eval, propagate_succ]

def add : propagate_struc bool :=
{ α := unit,
  i := by apply_instance,
  init_carry := λ _, ff,
  next_bit := λ (carry : unit → bool) (bits : bool → bool),
      (λ _, (bits tt && bits ff) || (bits ff && carry ()) || (bits tt && carry ()),
        bxor (bits tt) (bxor (bits ff) (carry ()))) }

@[simp] lemma eval_add (x : bool → ℕ → bool) : add.eval x = add_seq (x tt) (x ff) :=
begin
  dsimp [add, eval],
  rw [add_eq_propagate],
  congr,
  funext b,
  cases b; refl
end

def sub : propagate_struc bool :=
{ α := unit,
  i := by apply_instance,
  init_carry := λ _, ff,
  next_bit := λ (carry : unit → bool) (bits : bool → bool),
      (λ _, (bnot (bits tt) && (bits ff)) ||
        ((bnot (bxor (bits tt) (bits ff))) && carry ()),
        bxor (bits tt) (bxor (bits ff) (carry ()))) }

@[simp] lemma eval_sub (x : bool → ℕ → bool) : sub.eval x = sub_seq (x tt) (x ff) :=
begin
  dsimp [sub, eval],
  rw [sub_eq_propagate],
  congr,
  funext b,
  cases b; refl
end

def neg : propagate_struc unit :=
{ α := unit,
  i := by apply_instance,
  init_carry := λ _, tt,
  next_bit := λ (carry : unit → bool) (bits : unit → bool),
    (λ _, (bnot (bits ())) && (carry ()), bxor (bnot (bits ())) (carry ())) }

@[simp] lemma eval_neg (x : unit → ℕ → bool) : neg.eval x = neg_seq (x ()) :=
begin
  dsimp [neg, eval],
  rw [neg_eq_propagate],
  congr,
  funext b,
  cases b; refl
end

def not : propagate_struc unit :=
{ α := empty,
  i := by apply_instance,
  init_carry := empty.elim,
  next_bit := λ carry bits, (empty.elim, bnot (bits ())) }

@[simp] lemma eval_not (x : unit → ℕ → bool) : not.eval x = not_seq (x ()) :=
by ext n; cases n; simp [not, not_seq, eval, propagate_succ]

def zero : propagate_struc (fin 0) :=
{ α := empty,
  i := by apply_instance,
  init_carry := empty.elim,
  next_bit := λ carry bits, (empty.elim, ff) }

@[simp] lemma eval_zero (x : fin 0 → ℕ → bool) : zero.eval x = zero_seq :=
by ext n; cases n; simp [zero, zero_seq, eval, propagate_succ]

def one : propagate_struc (fin 0) :=
{ α := unit,
  i := by apply_instance,
  init_carry := λ _, tt,
  next_bit := λ carry bits, (λ _, ff, carry ()) }

@[simp] lemma eval_one (x : fin 0 → ℕ → bool) : one.eval x = one_seq :=
by ext n; cases n; simp [one, one_seq, eval, propagate_succ2]

def neg_one : propagate_struc (fin 0) :=
{ α := empty,
  i := by apply_instance,
  init_carry := empty.elim,
  next_bit := λ carry bits, (empty.elim, tt) }

@[simp] lemma eval_neg_one (x : fin 0 → ℕ → bool) : neg_one.eval x = neg_one_seq :=
by ext n; cases n; simp [neg_one, neg_one_seq, eval, propagate_succ2]

def ls : propagate_struc unit :=
{ α := unit,
  i := by apply_instance,
  init_carry := λ _, ff,
  next_bit := λ carry bits, (bits, carry ()) }

@[simp] lemma eval_ls (x : unit → ℕ → bool) : ls.eval x = ls_seq (x ()) :=
by ext n; cases n; simp [ls, ls_seq, eval, propagate_succ2]

def var (n : ℕ) : propagate_struc (fin (n+1)) :=
{ α := empty,
  i := by apply_instance,
  init_carry := empty.elim,
  next_bit := λ carry bits, (empty.elim, bits (fin.last n)) }

@[simp] lemma eval_var (n : ℕ) (x : fin (n+1) → ℕ → bool) : (var n).eval x = x (fin.last n) :=
by ext m; cases m; simp [var, eval, propagate_succ]

def incr : propagate_struc unit :=
{ α := unit,
  i := by apply_instance,
  init_carry := λ _, tt,
  next_bit := λ carry bits, (λ _, bits () && carry (), bxor (bits ()) (carry ())) }

@[simp] lemma eval_incr (x : unit → ℕ → bool) : incr.eval x = incr_seq (x ()) :=
begin
  dsimp [incr, eval],
  rw [incr_eq_propagate],
  congr,
  funext b,
  cases b; refl
end

def decr : propagate_struc unit :=
{ α := unit,
  i := by apply_instance,
  init_carry := λ _, tt,
  next_bit := λ carry bits, (λ _, bnot (bits ()) && carry (), bxor (bits ()) (carry ())) }

@[simp] lemma eval_decr (x : unit → ℕ → bool) : decr.eval x = decr_seq (x ()) :=
begin
  dsimp [decr, eval],
  rw [decr_eq_propagate],
  congr,
  funext b,
  cases b; refl
end

end propagate_struc

structure propagate_solution (t : term) extends propagate_struc (fin (arity t)) :=
( good : t.eval_fin = to_propagate_struc.eval )

def compose_unary
  (p : propagate_struc unit)
  {t : term}
  (q : propagate_solution t) :
  propagate_struc (fin (arity t)) :=
p.compose
  (fin (arity t))
  _
  (λ _ , id)
  (λ _, q.to_propagate_struc)

def compose_binary
  (p : propagate_struc bool)
  {t₁ t₂ : term}
  (q₁ : propagate_solution t₁)
  (q₂ : propagate_solution t₂) :
  propagate_struc (fin (max (arity t₁) (arity t₂))) :=
p.compose (fin (max (arity t₁) (arity t₂)))
  (λ b, fin (cond b (arity t₁) (arity t₂)))
  (λ b i, fin.cast_le (by cases b; simp) i)
  (λ b, bool.rec q₂.to_propagate_struc q₁.to_propagate_struc b)

@[simp] lemma compose_unary_eval
  (p : propagate_struc unit)
  {t : term}
  (q : propagate_solution t)
  (x : fin (arity t) → ℕ → bool) :
  (compose_unary p q).eval x = p.eval (λ _, t.eval_fin x) :=
begin
  rw [compose_unary, propagate_struc.eval_compose, q.good],
  refl
end

@[simp] lemma compose_binary_eval
  (p : propagate_struc bool)
  {t₁ t₂ : term}
  (q₁ : propagate_solution t₁)
  (q₂ : propagate_solution t₂)
  (x : fin (max (arity t₁) (arity t₂)) → ℕ → bool) :
  (compose_binary p q₁ q₂).eval x = p.eval
    (λ b, cond b (t₁.eval_fin (λ i, x (fin.cast_le (by simp) i)))
                 (t₂.eval_fin (λ i, x (fin.cast_le (by simp) i)))) :=
begin
  rw [compose_binary, propagate_struc.eval_compose, q₁.good, q₂.good],
  congr,
  ext b,
  cases b; refl
end

instance {α β : Type*} [fintype α] [fintype β] (b : bool) :
  fintype (cond b α β) :=
by cases b; dsimp; apply_instance

lemma cond_propagate {α α' β β' : Type}
  (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (init_carry' : α' → bool)
  (next_bit' : Π (carry : α' → bool) (bits : β' → bool),
    (α' → bool) × bool)
  {γ : Type} (fβ : β → γ) (fβ' : β' → γ)
  (x : γ → ℕ → bool) (b : bool) :
  cond b (propagate init_carry next_bit (λ b, (x (fβ b))))
    (propagate init_carry' next_bit' (λ b, (x (fβ' b)))) =
  propagate (show cond b α α' → bool, from bool.rec init_carry' init_carry b)
    (show Π (carry : cond b α α' → bool) (bits : cond b β β' → bool),
        (cond b α α' → bool) × bool,
      from bool.rec next_bit' next_bit b)
    (show cond b β β' → ℕ → bool, from bool.rec (λ b, (x (fβ' b))) (λ b, (x (fβ b))) b) :=
by cases b; refl

def term_eval_eq_propagate : Π (t : term),
  propagate_solution t
| (var n) :=
  { to_propagate_struc := propagate_struc.var n,
    good := by ext; simp [term.eval_fin] }
| zero :=
  { to_propagate_struc := propagate_struc.zero,
    good := by ext; simp [term.eval_fin] }
| one :=
  { to_propagate_struc := propagate_struc.one,
    good := by ext; simp [term.eval_fin] }
| neg_one :=
  { to_propagate_struc := propagate_struc.neg_one,
    good := by ext; simp [term.eval_fin] }
| (and t₁ t₂) :=
  let q₁ := term_eval_eq_propagate t₁ in
  let q₂ := term_eval_eq_propagate t₂ in
  { to_propagate_struc := compose_binary propagate_struc.and q₁ q₂,
    good := by ext; simp; refl }
| (or t₁ t₂) :=
  let q₁ := term_eval_eq_propagate t₁ in
  let q₂ := term_eval_eq_propagate t₂ in
  { to_propagate_struc := compose_binary propagate_struc.or q₁ q₂,
    good := by ext; simp; refl }
| (xor t₁ t₂) :=
  let q₁ := term_eval_eq_propagate t₁ in
  let q₂ := term_eval_eq_propagate t₂ in
  { to_propagate_struc := compose_binary propagate_struc.xor q₁ q₂,
    good := by ext; simp; refl }
| (ls t) :=
  let q := term_eval_eq_propagate t in
  { to_propagate_struc := by dsimp [arity]; exact compose_unary propagate_struc.ls q,
    good := by ext; simp; refl }
| (not t) :=
  let q := term_eval_eq_propagate t in
  { to_propagate_struc := by dsimp [arity]; exact compose_unary propagate_struc.not q,
    good := by ext; simp; refl }
| (add t₁ t₂) :=
  let q₁ := term_eval_eq_propagate t₁ in
  let q₂ := term_eval_eq_propagate t₂ in
  { to_propagate_struc := compose_binary propagate_struc.add q₁ q₂,
    good := by ext; simp; refl }
| (sub t₁ t₂) :=
  let q₁ := term_eval_eq_propagate t₁ in
  let q₂ := term_eval_eq_propagate t₂ in
  { to_propagate_struc := compose_binary propagate_struc.sub q₁ q₂,
    good := by ext; simp; refl }
| (neg t) :=
  let q := term_eval_eq_propagate t in
  { to_propagate_struc := by dsimp [arity]; exact compose_unary propagate_struc.neg q,
    good := by ext; simp; refl }
| (incr t) :=
  let q := term_eval_eq_propagate t in
  { to_propagate_struc := by dsimp [arity]; exact compose_unary propagate_struc.incr q,
    good := by ext; simp; refl }
| (decr t) :=
  let q := term_eval_eq_propagate t in
  { to_propagate_struc := by dsimp [arity]; exact compose_unary propagate_struc.decr q,
    good := by ext; simp; refl }

variables
  (init_carry : α → bool)
  (next_carry : Π (carry : α → bool) (bits : β → bool), (α → bool))
  (next_bit : Π (carry : α → bool) (bits : β → bool), (α → bool) × bool)

variables [fintype α] [fintype α']

open fintype

lemma exists_repeat_carry (seq : β → ℕ → bool) :
  ∃ n m : fin (2 ^ (card α) + 1),
    propagate_carry2 init_carry next_carry seq n =
    propagate_carry2 init_carry next_carry seq m ∧
    n < m :=
begin
  by_contra h,
  letI : decidable_eq α := classical.dec_eq α,
  push_neg at h,
  have := λ a b hab, (le_antisymm (h a b hab) (h b a hab.symm)).symm,
  simpa using fintype.card_le_of_injective _ this
end

lemma propagate_carry2_eq_of_seq_eq_lt (seq₁ seq₂ : β → ℕ → bool)
  (init_carry : α → bool)
  (next_carry : Π (carry : α → bool) (bits : β → bool), (α → bool))
  (i : ℕ) (h : ∀ (b) j < i, seq₁ b j = seq₂ b j) :
  propagate_carry2 init_carry next_carry seq₁ i =
    propagate_carry2 init_carry next_carry seq₂ i :=
begin
  induction i with i ih,
  { simp [propagate_carry2] },
  { simp [propagate_carry2, h _ i (nat.lt_succ_self i)],
    rw ih,
    exact λ b j hj, h b j (nat.lt_succ_of_lt hj) }
end

lemma propagate_eq_of_seq_eq_le (seq₁ seq₂ : β → ℕ → bool)
  (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool), (α → bool) × bool)
  (i : ℕ) (h : ∀ (b) j ≤ i, seq₁ b j = seq₂ b j) :
  propagate init_carry next_bit seq₁ i =
    propagate init_carry next_bit seq₂ i :=
begin
  cases i,
  { simp [propagate_zero, h _ 0 (le_refl _)] },
  { simp only [propagate_succ2, propagate_succ2, h _ _ (le_refl _)],
    congr' 2,
    apply propagate_carry2_eq_of_seq_eq_lt,
    exact λ b j hj, h b j (le_of_lt hj) }
end

lemma propagate_carry2_eq_of_carry_eq (seq₁ seq₂ : β → ℕ → bool)
  (m n : ℕ)
  (h₁ : propagate_carry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₁ m =
       propagate_carry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₂ n) (x : ℕ)
  (h₃ : ∀ y b, y ≤ x → seq₁ b (m + y) = seq₂ b (n + y))  :
  propagate_carry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₁ (m + x) =
  propagate_carry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₂ (n + x) :=
begin
  induction x with x ih generalizing seq₁ seq₂,
  { simp * at * },
  { simp only [h₃ x _ (nat.le_succ _),
      nat.add_succ, propagate_carry2, add_zero] at *,
    rw [ih],
    assumption,
    exact λ y b h, h₃ y b (nat.le_succ_of_le h) }
end

lemma propagate_eq_of_carry_eq (seq₁ seq₂ : β → ℕ → bool)
  (m n : ℕ)
  (h₁ : propagate_carry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₁ m =
       propagate_carry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₂ n) (x : ℕ)
  (h₃ : ∀ y b, y ≤ x → seq₁ b (m + y) = seq₂ b (n + y))  :
  propagate init_carry next_bit seq₁ (m + x) =
  propagate init_carry next_bit seq₂ (n + x) :=
begin
  cases x,
  { cases m,
    { cases n,
      { simp [h₃ 0 _ (le_refl _), propagate_carry2, *] at * },
      { simp [*, h₃ 0 _ (le_refl _), propagate_succ2] at *,
        rw [← h₁] } },
    { cases n,
      { simp [*, propagate_succ2] at *,
        simp [← h₃ 0 _ rfl] },
      { rw [propagate_succ2, h₁, propagate_succ2],
        have := h₃ 0,
        simp * at * } } },
  { simp only [nat.add_succ, propagate_succ2, add_zero],
    simp [← nat.add_succ, h₃ _ _ (le_refl _)],
    congr' 2,
    apply propagate_carry2_eq_of_carry_eq,
    assumption,
    assumption }
end

lemma propagate_carry_propagate_carry_add (x : β → ℕ → bool) :
  ∀ (init_carry : α → bool)
    (next_carry : Π (carry : α → bool) (bits : β → bool), (α → bool)),
  ∀ n i : ℕ,
  propagate_carry2 (propagate_carry2 init_carry next_carry x n)
    next_carry (λ b k, x b (k + n)) i =
  propagate_carry2 init_carry next_carry x (i + n)
| init_carry next_carry 0 0 := by simp [propagate_carry2]
| init_carry next_carry (n+1) 0 :=
  by simp [propagate_carry, propagate_carry2_succ]
| init_carry next_carry n (i+1) := begin
  rw [propagate_carry2, add_assoc,
    propagate_carry_propagate_carry_add],
  simp only [nat.one_add, nat.add_one, nat.succ_add, nat.add_succ,
    add_zero, propagate_carry2, zero_add]
end

lemma exists_repeat : ∀ (seq : β → ℕ → bool)
  (n : ℕ),
  ∃ (m < 2 ^ (card α)) (seq2 : β → ℕ → bool),
    propagate init_carry next_bit seq2 m = propagate init_carry next_bit seq n
| seq n :=
begin
  by_cases hn2 : n < 2 ^ card α,
  { exact ⟨n, hn2, seq, rfl⟩ },
  { rcases exists_repeat_carry (propagate_carry2 init_carry (λ c b, (next_bit c b).1) seq
        (n - 2 ^ card α))
      (λ carry bits, (next_bit  carry bits).1)
      (λ b i, seq b (i + (n - 2^ (card α)))) with ⟨a, b, h₁, h₂⟩,
    simp only [propagate_carry_propagate_carry_add] at h₁,
    rcases have wf : n - (b - a) < n,
        from nat.sub_lt (lt_of_lt_of_le (pow_pos two_pos _) (le_of_not_gt hn2))
          (nat.sub_pos_of_lt h₂),
      exists_repeat (λ c i, if i < a + (n - 2 ^ card α) then seq c i else
        seq c (i + (b - a))) (n - (b - a)) with ⟨m, hmle, seq2, hm⟩,
    use [m, hmle, seq2],
    rw [hm], clear hm,
    have h1 : n - (b - a) = (a + (n - 2 ^ (card α))) + (2 ^ card α - b),
    { zify,
      rw [nat.cast_sub, nat.cast_sub, nat.cast_sub, nat.cast_sub],
      ring,
      exact nat.le_of_lt_succ b.2,
      simp * at *,
      exact le_of_lt h₂,
      exact le_trans (nat.sub_le _ _) (le_trans (nat.le_of_lt_succ b.2)
        (by simp * at *)) },
    rw h1,
    have h2 : n = (b + (n - 2 ^ card α)) + (2 ^ card α - b),
    { zify,
      rw [nat.cast_sub, nat.cast_sub],
      ring,
      exact nat.le_of_lt_succ b.2,
      simp * at *, },
    conv_rhs { rw h2 },
    refine propagate_eq_of_carry_eq _ _ _ _ _ _ _ _ _,
    { have h : ↑b + (n - 2 ^ card α) = (a + (n - 2 ^ card α)) + (b - a),
      { zify,
        rw [nat.cast_sub, nat.cast_sub],
        ring,
        exact le_of_lt h₂,
        simp * at * },
      rw [← h₁],
      apply propagate_carry2_eq_of_seq_eq_lt,
      simp { contextual := tt } },
    { intros y c hc,
      simp only [add_lt_iff_neg_left, not_lt_zero', if_false],
      congr' 1,
      zify,
      rw [nat.cast_sub, nat.cast_sub],
      ring,
      exact le_of_lt h₂,
      simp * at * } },
end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.snd⟩] }

lemma propagate_eq_zero_iff (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool), (α → bool) × bool) :
  (∀ seq, propagate init_carry next_bit seq = zero_seq) ↔
  (∀ seq, ∀ i < 2 ^ (card α), propagate init_carry next_bit seq i = ff) :=
begin
  split,
  { intros h i _,
    simp [h, zero_seq] },
  { intros h seq,
    funext i,
    rcases exists_repeat init_carry next_bit seq i with ⟨j, hj, seq2, hseq2⟩,
    rw [← hseq2, h seq2 j hj, zero_seq] }
end

lemma eq_iff_xor_seq_eq_zero (seq₁ seq₂ : ℕ → bool) :
  (∀ i, seq₁ i = seq₂ i) ↔ (∀ i, xor_seq seq₁ seq₂ i = zero_seq i) :=
begin
  simp [function.funext_iff, xor_seq, zero_seq],
  split,
  { intros, simp * },
  { intros h a,
    specialize h a,
    cases (seq₁ a); cases (seq₂ a); simp * at *, }
end

lemma eval_eq_iff_xor_seq_eq_zero (t₁ t₂ : term) :
  t₁.eval = t₂.eval ↔ (t₁.xor t₂).eval_fin = λ _, zero_seq :=
begin
  simp only [function.funext_iff, term.eval, term.eval_fin,
    ← eq_iff_xor_seq_eq_zero, ← eval_fin_eq_eval],
  split,
  { intros h seq n,
    have := h (λ j, if hj : j < (arity (t₁.xor t₂)) then seq ⟨j, hj⟩ else λ _, ff) n,
    simp at this,
    convert this },
  { intros h seq m,
    exact h (λ j, seq j) _ }
end


