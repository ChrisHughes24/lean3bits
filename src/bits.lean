import data.fintype.card_embedding

open sum

variables {α β α' β' : Type*} {γ : β → Type*}

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
| (n+1) :=
next_bit (propogate_carry n) (λ i, x i (n+1))

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

@[simp] lemma propogate_succ (init_carry : α → bool)
  (next_bit : Π (carry : α → bool) (bits : β → bool),
    (α → bool) × bool)
  (x : β → ℕ → bool) (i : ℕ) :
  propogate init_carry next_bit x (i+1) = (next_bit
    (propogate_carry init_carry (λ c b, (next_bit c b).1) x i)
    (λ j, x j (i+1))).2 :=
by rw [← propogate_aux_fst_eq_carry]; refl

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
    { simp [one_seq] },
    { simp [one_seq] } }
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
    { simp [ls_seq] },
    { simp [ls_seq] } }
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
    { simp [add_seq, add_seq_aux] },
    { simp [add_seq, add_seq_aux, add_seq_aux_eq_propogate_carry] } }
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
        { simp [term.eval_fin] },
        { simp [term.eval_fin] } }
    end }
| zero :=
  { α := empty,
    i := by apply_instance,
    init_carry := empty.elim,
    next_bit := (λ _ (y : fin 0 → bool), (empty.elim, ff)),
    good := by ext x i; cases i; simp [term.eval_fin, zero_seq] }
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
        { simp [one_seq] },
        { simp [one_seq] } }
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
