import data.fintype.card
import tactic.zify
import tactic.ring
import tactic.linarith

open sum

variables {α β α' β' : Type} {γ : β → Type}

def propogate_aux (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (x : β → ℕ → bool) : ℕ → (α → bool) × bool
| 0 := next_bit init_carry (λ i, x i 0)
| (n+1) :=
next_bit (propogate_aux n).1 (λ i, x i (n+1))

def propogate (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (x : β → ℕ → bool) (i : ℕ) : bool :=
(propogate_aux init_carry next_bit x i).2

@[simp] def propogate_carry (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool))
  (x : β → ℕ → bool) : ℕ → (α → bool)
| 0 := next_bit init_carry (λ i, x i 0)
| (n+1) := next_bit (propogate_carry n) (λ i, x i (n+1))

@[simp] def propogate_carry2 (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool))
  (x : β → ℕ → bool) : ℕ → (α → bool)
| 0 := init_carry
| (n+1) := next_bit (propogate_carry2 n) (λ i, x i n)

lemma propogate_carry2_succ (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool))
  (x : β → ℕ → bool) (n : ℕ) :
  propogate_carry2 init_carry next_bit x (n+1) =
  propogate_carry init_carry next_bit x n :=
by induction n; simp *

@[simp] lemma propogate_aux_fst_eq_carry (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (x : β → ℕ → bool) : ∀ n : ℕ,
  (propogate_aux init_carry next_bit x n).1 =
  propogate_carry init_carry (λ c b, (next_bit c b).1) x n
| 0 := rfl
| (n+1) := by rw [propogate_aux, propogate_carry, propogate_aux_fst_eq_carry]

@[simp] lemma propogate_zero (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
  (α → bool) × bool)
  (x : β → ℕ → bool) :
  propogate init_carry next_bit x 0 = (next_bit init_carry (λ i, x i 0)).2 :=
rfl

lemma propogate_succ (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (x : β → ℕ → bool) (i : ℕ) :
  propogate init_carry next_bit x (i+1) = (next_bit
    (propogate_carry init_carry (λ c b, (next_bit c b).1) x i)
    (λ j, x j (i+1))).2 :=
by rw [← propogate_aux_fst_eq_carry]; refl

lemma propogate_succ2 (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (x : β → ℕ → bool) (i : ℕ) :
  propogate init_carry next_bit x (i+1) = (next_bit
    (propogate_carry2 init_carry (λ c b, (next_bit c b).1) x (i+1))
    (λ j, x j (i+1))).2 :=
by rw [propogate_carry2_succ, ← propogate_aux_fst_eq_carry]; refl

lemma propogate_carry_propogate {δ : β → Type*} {β' : Type}
    (f : Π a, δ a → β') : Π (n : ℕ) (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool))
  (init_carry_x : Π a, γ a → bool)
  (next_bit_x : Π a (carry : γ a → bool) (bits : δ a → bool),
    (γ a → bool) × bool)
  (x : β' → ℕ → bool),
  propogate_carry init_carry next_bit (λ a, propogate (init_carry_x a)
    (next_bit_x a) (λ d, x (f a d))) n =
  propogate_carry
    (λ a : α ⊕ (Σ a, γ a), sum.elim init_carry (λ b : Σ a, γ a,
      init_carry_x b.1 b.2) a)
    (λ (carry : (α ⊕ (Σ a, γ a)) → bool) (bits : β' → bool),
  -- first compute (propogate (init_carry_x a) (next_bit_x a) (x a) n)
      let f : Π (a : β), (γ a → bool) × bool := λ a, next_bit_x a (λ d,
        carry (inr ⟨a, d⟩)) (λ d, bits (f a d)) in
      let g : (α → bool) := (next_bit (carry ∘ inl) (λ a, (f a).2)) in
      sum.elim g (λ x, (f x.1).1 x.2)
    )
    x n ∘ inl
| 0 init_carry next_bit init_carry_x next_bit_x x := rfl
| (n+1) init_carry next_bit init_carry_x next_bit_x x := begin
  have := propogate_carry_propogate n,
  clear_aux_decl,
  simp only [propogate_carry, propogate_succ, elim_inl] at *,
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

lemma propogate_propogate {δ : β → Type*} {β' : Type}
    (f : Π a, δ a → β') : Π (n : ℕ) (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (init_carry_x : Π a, γ a → bool)
  (next_bit_x : Π a (carry : γ a → bool) (bits : δ a → bool),
    (γ a → bool) × bool)
  (x : β' → ℕ → bool),
  propogate init_carry next_bit (λ a, propogate (init_carry_x a)
    (next_bit_x a) (λ d, x (f a d))) n =
  propogate
    (λ a : α ⊕ (Σ a, γ a), sum.elim init_carry (λ b : Σ a, γ a,
      init_carry_x b.1 b.2) a)
    (λ (carry : (α ⊕ (Σ a, γ a)) → bool) (bits : β' → bool),
      -- first compute (propogate (init_carry_x a) (next_bit_x a) (x a) n)
      let f : Π (a : β), (γ a → bool) × bool := λ a, next_bit_x a (λ d,
        carry (inr ⟨a, d⟩)) (λ d, bits (f a d)) in
      let g : (α → bool) × bool := (next_bit (carry ∘ inl) (λ a, (f a).2)) in
      (sum.elim g.1 (λ x, (f x.1).1 x.2), g.2)
    )
  x n
| 0 init_carry next_bit init_carry_x next_bit_x x := rfl
| (n+1) init_carry next_bit init_carry_x next_bit_x x := begin
  simp only [propogate_succ],
  clear_aux_decl,
  rw [propogate_carry_propogate],
  congr,
  ext,
  congr,
  induction n with n ih,
  { simp },
  { simp [ih] }
end

lemma propogate_carry_change_vars {β' : Type}
  (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool))
  (x : β' → ℕ → bool) (i : ℕ)
  (change_vars : β → β') :
  propogate_carry init_carry next_bit (λ b, x (change_vars b)) i =
  propogate_carry init_carry (λ (carry : α → bool) (bits : β' → bool),
    next_bit carry (λ b, bits (change_vars b))) x i :=
begin
  induction i,
  { simp },
  { simp * }
end

lemma propogate_change_vars {β' : Type}
  (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (x : β' → ℕ → bool) (i : ℕ)
  (change_vars : β → β') :
  propogate init_carry next_bit (λ b, x (change_vars b)) i =
  propogate init_carry (λ (carry : α → bool) (bits : β' → bool),
    next_bit carry (λ b, bits (change_vars b))) x i :=
begin
  induction i with i ih,
  { refl },
  { simp only [propogate_succ, propogate_carry_change_vars, ih] }
end

inductive term : Type
| var : ℕ → term
| zero : term
| one : term
| and : term → term → term
| or : term → term → term
| xor : term → term → term
| not : term → term
| ls : term → term
| add : term → term → term

open term


def zero_seq : ℕ → bool := λ n, ff

def one_seq : ℕ → bool := λ n, n = 0

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

def term.eval : Π (t : term) (vars : ℕ → ℕ → bool), ℕ → bool
| (var n) vars := vars n
| zero vars := zero_seq
| one vars := one_seq
| (and t₁ t₂) vars := and_seq (term.eval t₁ vars) (term.eval t₂ vars)
| (or t₁ t₂) vars := or_seq (term.eval t₁ vars) (term.eval t₂ vars)
| (xor t₁ t₂) vars := xor_seq (term.eval t₁ vars) (term.eval t₂ vars)
| (not t) vars := not_seq (term.eval t vars)
| (ls t) vars := ls_seq (term.eval t vars)
| (add t₁ t₂) vars := add_seq (term.eval t₁ vars) (term.eval t₂ vars)

@[simp] def arity : term → ℕ
| (var n) := n+1
| zero := 0
| one := 0
| (and t₁ t₂) := max (arity t₁) (arity t₂)
| (or t₁ t₂) := max (arity t₁) (arity t₂)
| (xor t₁ t₂) := max (arity t₁) (arity t₂)
| (not t) := arity t
| (ls t) := arity t
| (add t₁ t₂) := max (arity t₁) (arity t₂)

@[simp] def term.eval_fin : Π (t : term) (vars : fin (arity t) → ℕ → bool), ℕ → bool
| (var n) vars := vars (fin.last n)
| zero vars := zero_seq
| one vars := one_seq
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

lemma eval_fin_eq_eval (t : term) (vars : ℕ → ℕ → bool) :
  term.eval_fin t (λ i, vars i) = term.eval t vars :=
begin
  induction t;
  dsimp [term.eval_fin, term.eval, arity] at *; simp *
end

lemma id_eq_propogate (x : ℕ → bool) :
  x = propogate empty.elim (λ _ (y : unit → bool), (empty.elim, y ())) (λ _, x) :=
by ext n; cases n; refl

lemma zero_eq_propogate :
  zero_seq = propogate empty.elim (λ (_ _ : empty → bool), (empty.elim, ff)) empty.elim :=
by ext n; cases n; refl

lemma one_eq_propogate :
  one_seq = propogate (λ _ : unit, tt) (λ f (_ : empty → bool), (λ _, ff, f ())) empty.elim :=
begin
  ext n,
  cases n with n,
  { refl },
  { cases n,
    { simp [one_seq, propogate_succ] },
    { simp [one_seq, propogate_succ] } }
end

lemma and_eq_propogate (x y : ℕ → bool) :
  and_seq x y = propogate empty.elim
    (λ _ (y : bool → bool), (empty.elim, y tt && y ff)) (λ b, cond b x y) :=
by ext n; cases n; simp [propogate, propogate_aux, and_seq]

lemma or_eq_propogate (x y : ℕ → bool) :
  or_seq x y = propogate empty.elim
    (λ _ (y : bool → bool), (empty.elim, y tt || y ff)) (λ b, cond b x y) :=
by ext n; cases n; simp [propogate, propogate_aux, or_seq]

lemma xor_eq_propogate (x y : ℕ → bool) :
  xor_seq x y = propogate empty.elim
    (λ _ (y : bool → bool), (empty.elim, bxor (y tt) (y ff))) (λ b, cond b x y) :=
by ext n; cases n; simp [propogate, propogate_aux, xor_seq]

lemma not_eq_propogate (x : ℕ → bool) :
  not_seq x = propogate empty.elim (λ _ (y : unit → bool), (empty.elim, bnot (y ()))) (λ _, x) :=
by ext n; cases n; simp [propogate, propogate_aux, not_seq]

lemma ls_eq_propogate (x : ℕ → bool) :
  ls_seq x = propogate (λ _ : unit, ff) (λ (carry x : unit → bool), (x, carry ())) (λ _, x) :=
begin
  ext n,
  cases n with n,
  { refl },
  { cases n,
    { simp [ls_seq, propogate_succ] },
    { simp [ls_seq, propogate_succ] } }
end

lemma add_seq_aux_eq_propogate_carry (x y : ℕ → bool) (n : ℕ) :
  (add_seq_aux x y n).2 = propogate_carry (λ _, ff)
    (λ (carry : unit → bool) (bits : bool → bool),
      λ _, (bits tt && bits ff) || (bits ff && carry ()) || (bits tt && carry ()))
  (λ b, cond b x y) n () :=
begin
  induction n,
  { simp [add_seq_aux] },
  { simp [add_seq_aux, *] }
end

lemma add_eq_propogate (x y : ℕ → bool) :
  add_seq x y = propogate (λ _, ff)
    (λ (carry : unit → bool) (bits : bool → bool),
      (λ _, (bits tt && bits ff) || (bits ff && carry ()) || (bits tt && carry ()),
        bxor (bits tt) (bxor (bits ff) (carry ()))))
  (λ b, cond b x y) :=
begin
  ext n,
  cases n with n,
  { simp [add_seq, add_seq_aux] },
  { cases n,
    { simp [add_seq, add_seq_aux, propogate_succ] },
    { simp [add_seq, add_seq_aux, add_seq_aux_eq_propogate_carry,
        propogate_succ] } }
end

structure propogate_solution (t : term) : Type 1 :=
( α  : Type )
[ i : fintype α ]
( init_carry : α → bool )
( next_bit : Π (carry : α → bool) (bits : fin (arity t) → bool),
    (α → bool) × bool )
( good : t.eval_fin = propogate init_carry next_bit )

instance {α β : Type*} [fintype α] [fintype β] (b : bool) :
  fintype (cond b α β) :=
by cases b; dsimp; apply_instance

lemma cond_propogate {α α' β β' : Type}
  (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (init_carry' : α' → bool)
  (next_bit' : Π (carry : α' → bool) (bits : β' → bool),
    (α' → bool) × bool)
  {γ : Type} (fβ : β → γ) (fβ' : β' → γ)
  (x : γ → ℕ → bool) (b : bool) :
  cond b (propogate init_carry next_bit (λ b, (x (fβ b))))
    (propogate init_carry' next_bit' (λ b, (x (fβ' b)))) =
  propogate (show cond b α α' → bool, from bool.rec init_carry' init_carry b)
    (show Π (carry : cond b α α' → bool) (bits : cond b β β' → bool),
        (cond b α α' → bool) × bool,
      from bool.rec next_bit' next_bit b)
    (show cond b β β' → ℕ → bool, from bool.rec (λ b, (x (fβ' b))) (λ b, (x (fβ b))) b) :=
by cases b; refl

def term_eval_eq_propogate : Π (t : term),
  propogate_solution t
| (var n) :=
  { α := empty,
    i := by apply_instance,
    init_carry := empty.elim,
    next_bit := (λ _ (y : fin (n+1) → bool), (empty.elim, y (fin.last n))),
    good := begin
      ext x i,
      cases i with i,
      { refl },
      { cases i,
        { simp [term.eval_fin, propogate_succ] },
        { simp [term.eval_fin, propogate_succ] } }
    end }
| zero :=
  { α := empty,
    i := by apply_instance,
    init_carry := empty.elim,
    next_bit := (λ _ (y : fin 0 → bool), (empty.elim, ff)),
    good := by ext x i; cases i; simp [term.eval_fin, zero_seq, propogate_succ] }
| one :=
  { α := unit,
    i := by apply_instance,
    init_carry := λ _, tt,
    next_bit := (λ carry (y : fin 0 → bool), (λ _, ff, carry ())),
    good := begin
      ext x i,
      cases i with i,
      { simp [one_seq] },
      { cases i with i,
        { simp [one_seq, propogate_succ] },
        { simp [one_seq, propogate_succ] } }
    end }
| (and t₁ t₂) :=
  let p₁ := term_eval_eq_propogate t₁ in
  let p₂ := term_eval_eq_propogate t₂ in
  { α := empty ⊕ Σ (b : bool), cond b p₁.α p₂.α,
    i := by letI := p₁.i; letI := p₂.i; apply_instance,
    init_carry := sum.elim (λ _, ff)
      (λ x, match x with
        | ⟨tt, a⟩ := p₁.init_carry a
        | ⟨ff, a⟩ := p₂.init_carry a
        end),
    next_bit := _,
    good := begin
      ext x i,
      rw [term.eval_fin, p₁.good, p₂.good, and_eq_propogate],
      simp only [cond_propogate],
      dsimp,
      have := propogate_propogate
        (λ (a : bool),
          show cond a (fin (arity t₁)) (fin (arity t₂)) → fin (arity (t₁.and t₂)),
            from bool.rec (fin.cast_le (by simp)) (fin.cast_le (by simp)) a) i
        empty.elim
        (λ f y, (empty.elim, y tt && y ff))
        (λ b, show cond b p₁.α p₂.α → bool, from bool.rec p₂.init_carry p₁.init_carry b)
        (λ b, bool.rec p₂.next_bit p₁.next_bit b) x,
      dsimp at this,
      convert this.trans _; clear this,
      ext b, cases b; refl,
      congr,
      ext b, rcases b with ⟨ff, _⟩| ⟨tt, _⟩; refl
    end }
| (or t₁ t₂) :=
  let p₁ := term_eval_eq_propogate t₁ in
  let p₂ := term_eval_eq_propogate t₂ in
  { α := empty ⊕ Σ (b : bool), cond b p₁.α p₂.α,
    i := by letI := p₁.i; letI := p₂.i; apply_instance,
    init_carry := sum.elim (λ _, ff)
      (λ x, match x with
        | ⟨tt, a⟩ := p₁.init_carry a
        | ⟨ff, a⟩ := p₂.init_carry a
        end),
    next_bit := _,
    good := begin
      ext x i,
      rw [term.eval_fin, p₁.good, p₂.good, or_eq_propogate],
      simp only [cond_propogate],
      dsimp,
      have := propogate_propogate
        (λ (a : bool),
          show cond a (fin (arity t₁)) (fin (arity t₂)) → fin (arity (t₁.and t₂)),
            from bool.rec (fin.cast_le (by simp)) (fin.cast_le (by simp)) a) i
        empty.elim
        (λ f y, (empty.elim, y tt || y ff))
        (λ b, show cond b p₁.α p₂.α → bool, from bool.rec p₂.init_carry p₁.init_carry b)
        (λ b, bool.rec p₂.next_bit p₁.next_bit b) x,
      dsimp at this,
      convert this.trans _; clear this,
      ext b, cases b; refl,
      congr,
      ext b, rcases b with ⟨ff, _⟩| ⟨tt, _⟩; refl
    end }
| (xor t₁ t₂) :=
  let p₁ := term_eval_eq_propogate t₁ in
  let p₂ := term_eval_eq_propogate t₂ in
  { α := empty ⊕ Σ (b : bool), cond b p₁.α p₂.α,
    i := by letI := p₁.i; letI := p₂.i; apply_instance,
    init_carry := sum.elim (λ _, ff)
      (λ x, match x with
        | ⟨tt, a⟩ := p₁.init_carry a
        | ⟨ff, a⟩ := p₂.init_carry a
        end),
    next_bit := _,
    good := begin
      ext x i,
      rw [term.eval_fin, p₁.good, p₂.good, xor_eq_propogate],
      simp only [cond_propogate],
      dsimp,
      have := propogate_propogate
        (λ (a : bool),
          show cond a (fin (arity t₁)) (fin (arity t₂)) → fin (arity (t₁.and t₂)),
            from bool.rec (fin.cast_le (by simp)) (fin.cast_le (by simp)) a) i
        empty.elim
        (λ f y, (empty.elim, bxor (y tt) (y ff)))
        (λ b, show cond b p₁.α p₂.α → bool, from bool.rec p₂.init_carry p₁.init_carry b)
        (λ b, bool.rec p₂.next_bit p₁.next_bit b) x,
      dsimp at this,
      convert this.trans _; clear this,
      ext b, cases b; refl,
      congr,
      ext b, rcases b with ⟨ff, _⟩| ⟨tt, _⟩; refl
    end }
| (ls t) :=
  let p := term_eval_eq_propogate t in
  { α := unit ⊕ Σ s : unit, p.α,
    i := by letI := p.i; apply_instance,
    init_carry := sum.elim (λ _, ff) (λ x, p.init_carry x.2),
    next_bit := _,
    good := begin
      ext x i,
      rw [term.eval_fin, p.good, ls_eq_propogate],
      dsimp,
      exact propogate_propogate
        (λ (a : unit),
          show fin (arity t) → fin (arity t), from id) i
        (λ _ : unit, ff)
        (λ carry bits, (bits, carry ()))
        (λ _, p.init_carry)
        (λ _, p.next_bit) x
    end }
| (not t) :=
  let p := term_eval_eq_propogate t in
  { α := empty ⊕ Σ s : unit, p.α,
    i := by letI := p.i; apply_instance,
    init_carry := sum.elim empty.elim (λ x, p.init_carry x.2),
    next_bit := _,
    good := begin
      ext x i,
      rw [term.eval_fin, p.good, not_eq_propogate],
      dsimp,
      have := propogate_propogate
        (λ (a : unit),
          show fin (arity t) → fin (arity t), from id) i
        empty.elim
        (λ carry bits, (empty.elim, !(bits ())))
        (λ _, p.init_carry)
        (λ _, p.next_bit) x,
      convert this.trans _; clear this,
      dsimp,
      refl
    end }
| (add t₁ t₂) :=
  let p₁ := term_eval_eq_propogate t₁ in
  let p₂ := term_eval_eq_propogate t₂ in
  { α := unit ⊕ Σ (b : bool), cond b p₁.α p₂.α,
    i := by letI := p₁.i; letI := p₂.i; apply_instance,
    init_carry := sum.elim (λ _, ff)
      (λ x, match x with
        | ⟨tt, a⟩ := p₁.init_carry a
        | ⟨ff, a⟩ := p₂.init_carry a
        end),
    next_bit := _,
    good := begin
      ext x i,
      rw [term.eval_fin, p₁.good, p₂.good, add_eq_propogate],
      simp only [cond_propogate],
      dsimp,
      have := propogate_propogate
        (λ (a : bool),
          show cond a (fin (arity t₁)) (fin (arity t₂)) → fin (arity (t₁.and t₂)),
            from bool.rec (fin.cast_le (by simp)) (fin.cast_le (by simp)) a) i
        (λ _, ff)
        (λ (carry : unit → bool) (bits : bool → bool),
          (λ _, (bits tt && bits ff) || (bits ff && carry ()) || (bits tt && carry ()),
            bxor (bits tt) (bxor (bits ff) (carry ()))))
        (λ b, show cond b p₁.α p₂.α → bool, from bool.rec p₂.init_carry p₁.init_carry b)
        (λ b, bool.rec p₂.next_bit p₁.next_bit b) x,
      dsimp at this,
      convert this.trans _; clear this,
      ext b, cases b; refl,
      congr,
      ext b, rcases b with ⟨ff, _⟩| ⟨tt, _⟩; refl
    end }

variables
  (init_carry : α → bool)
  (next_carry : Π (carry : α → bool) (bits : β → bool), (α → bool))
  (next_bit : Π (carry : α → bool) (bits : β → bool), (α → bool) × bool)

variables [fintype α] [fintype α']

open fintype

lemma exists_repeat_carry (seq : β → ℕ → bool) :
  ∃ n m : fin (2 ^ (card α) + 1),
    propogate_carry2 init_carry next_carry seq n =
    propogate_carry2 init_carry next_carry seq m ∧
    n < m :=
begin
  by_contra h,
  letI : decidable_eq α := classical.dec_eq α,
  push_neg at h,
  have := λ a b hab, (le_antisymm (h a b hab) (h b a hab.symm)).symm,
  simpa using fintype.card_le_of_injective _ this
end

lemma propogate_carry2_eq_of_seq_eq_lt (seq₁ seq₂ : β → ℕ → bool)
  (init_carry : α → bool)
  (next_carry : Π (carry : α → bool) (bits : β → bool), (α → bool))
  (i : ℕ) (h : ∀ (b) j < i, seq₁ b j = seq₂ b j) :
  propogate_carry2 init_carry next_carry seq₁ i =
    propogate_carry2 init_carry next_carry seq₂ i :=
begin
  induction i with i ih,
  { simp [propogate_carry2] },
  { simp [propogate_carry2, h _ i (nat.lt_succ_self i)],
    rw ih,
    exact λ b j hj, h b j (nat.lt_succ_of_lt hj) }
end

lemma propogate_eq_of_seq_eq_le (seq₁ seq₂ : β → ℕ → bool)
  (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool), (α → bool) × bool)
  (i : ℕ) (h : ∀ (b) j ≤ i, seq₁ b j = seq₂ b j) :
  propogate init_carry next_bit seq₁ i =
    propogate init_carry next_bit seq₂ i :=
begin
  cases i,
  { simp [propogate_zero, h _ 0 (le_refl _)] },
  { simp only [propogate_succ2, propogate_succ2, h _ _ (le_refl _)],
    congr' 2,
    apply propogate_carry2_eq_of_seq_eq_lt,
    exact λ b j hj, h b j (le_of_lt hj) }
end

lemma propogate_carry2_eq_of_carry_eq (seq₁ seq₂ : β → ℕ → bool)
  (m n : ℕ)
  (h₁ : propogate_carry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₁ m =
       propogate_carry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₂ n) (x : ℕ)
  (h₃ : ∀ y b, y ≤ x → seq₁ b (m + y) = seq₂ b (n + y))  :
  propogate_carry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₁ (m + x) =
  propogate_carry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₂ (n + x) :=
begin
  induction x with x ih generalizing seq₁ seq₂,
  { simp * at * },
  { simp only [h₃ x _ (nat.le_succ _),
      nat.add_succ, propogate_carry2, add_zero] at *,
    rw [ih],
    assumption,
    exact λ y b h, h₃ y b (nat.le_succ_of_le h) }
end

lemma propogate_eq_of_carry_eq (seq₁ seq₂ : β → ℕ → bool)
  (m n : ℕ)
  (h₁ : propogate_carry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₁ m =
       propogate_carry2 init_carry
    (λ carry bits, (next_bit carry bits).1) seq₂ n) (x : ℕ)
  (h₃ : ∀ y b, y ≤ x → seq₁ b (m + y) = seq₂ b (n + y))  :
  propogate init_carry next_bit seq₁ (m + x) =
  propogate init_carry next_bit seq₂ (n + x) :=
begin
  cases x,
  { cases m,
    { cases n,
      { simp [h₃ 0 _ (le_refl _), propogate_carry2, *] at * },
      { simp [*, h₃ 0 _ (le_refl _), propogate_succ2] at *,
        rw [← h₁] } },
    { cases n,
      { simp [*, propogate_succ2] at *,
        simp [← h₃ 0 _ rfl] },
      { rw [propogate_succ2, h₁, propogate_succ2],
        have := h₃ 0,
        simp * at * } } },
  { simp only [nat.add_succ, propogate_succ2, add_zero],
    simp [← nat.add_succ, h₃ _ _ (le_refl _)],
    congr' 2,
    apply propogate_carry2_eq_of_carry_eq,
    assumption,
    assumption }
end

lemma propogate_carry_propogate_carry_add (x : β → ℕ → bool) :
  ∀ (init_carry : α → bool)
    (next_carry : Π (carry : α → bool) (bits : β → bool), (α → bool)),
  ∀ n i : ℕ,
  propogate_carry2 (propogate_carry2 init_carry next_carry x n)
    next_carry (λ b k, x b (k + n)) i =
  propogate_carry2 init_carry next_carry x (i + n)
| init_carry next_carry 0 0 := by simp [propogate_carry2]
| init_carry next_carry (n+1) 0 :=
  by simp [propogate_carry, propogate_carry2_succ]
| init_carry next_carry n (i+1) := begin
  rw [propogate_carry2, add_assoc,
    propogate_carry_propogate_carry_add],
  simp only [nat.one_add, nat.add_one, nat.succ_add, nat.add_succ,
    add_zero, propogate_carry2, zero_add]
end

lemma exists_repeat : ∀ (seq : β → ℕ → bool)
  (n : ℕ),
  ∃ (m < 2 ^ (card α)) (seq2 : β → ℕ → bool),
    propogate init_carry next_bit seq2 m = propogate init_carry next_bit seq n
| seq n :=
begin
  by_cases hn2 : n < 2 ^ card α,
  { exact ⟨n, hn2, seq, rfl⟩ },
  { rcases exists_repeat_carry (propogate_carry2 init_carry (λ c b, (next_bit c b).1) seq
        (n - 2 ^ card α))
      (λ carry bits, (next_bit  carry bits).1)
      (λ b i, seq b (i + (n - 2^ (card α)))) with ⟨a, b, h₁, h₂⟩,
    simp only [propogate_carry_propogate_carry_add] at h₁,
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
    refine propogate_eq_of_carry_eq _ _ _ _ _ _ _ _ _,
    { have h : ↑b + (n - 2 ^ card α) = (a + (n - 2 ^ card α)) + (b - a),
      { zify,
        rw [nat.cast_sub, nat.cast_sub],
        ring,
        exact le_of_lt h₂,
        simp * at * },
      rw [← h₁],
      apply propogate_carry2_eq_of_seq_eq_lt,
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

lemma propogate_eq_zero_iff (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool), (α → bool) × bool) :
  (∀ seq, propogate init_carry next_bit seq = zero_seq) ↔
  (∀ seq, ∀ i < 2 ^ (card α), propogate init_carry next_bit seq i = ff) :=
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

instance decidable_eval_eq (t₁ t₂ : term) :
  decidable (t₁.eval = t₂.eval) :=
begin
  let p := term_eval_eq_propogate (t₁.xor t₂),
  letI := p.i,
  refine decidable_of_iff
    (∀ (seq : fin (arity (t₁.xor t₂)) →
      fin (2 ^ (card p.α)) → bool)
      (i : fin (2 ^ card p.α)),
      (t₁.xor t₂).eval
      (λ i j, if hij : i < arity (t₁.xor t₂) ∧ j < 2 ^ (card p.α)
        then seq ⟨i, hij.1⟩ ⟨j, hij.2⟩ else ff) i = ff) _,
  rw [eval_eq_iff_xor_seq_eq_zero, p.good],
  rw [function.funext_iff, propogate_eq_zero_iff],
  simp only [← eval_fin_eq_eval, p.good],
  split,
  { intros h seq i hi,
    rw ← h (λ i j, seq i j) ⟨i, hi⟩,
    apply propogate_eq_of_seq_eq_le,
    intros b j hj,
    simp [lt_of_le_of_lt hj hi] },
  { intros h seq i,
    rw h,
    exact i.2 }
end
