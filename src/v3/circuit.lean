import data.finset
import .list_pi

universes u v

inductive circuit (α : Type u) : Type u
| true : circuit
| false : circuit
| var : α → circuit
| and : circuit → circuit → circuit
| or : circuit → circuit → circuit
| not : circuit → circuit
| xor : circuit → circuit → circuit
| imp : circuit → circuit → circuit

namespace circuit
variables {α : Type u} {β : Type v}

def reppr [has_repr α] : (circuit α) → string
| true := "⊤"
| false := "⊥"
| (var x) := repr x
| (and x y) := "(" ++ reppr x ++ " ∧ " ++ reppr y ++ ")"
| (or x y) := "(" ++ reppr x ++ " ∨ " ++ reppr y ++ ")"
| (not x) := "¬" ++ reppr x
| (xor x y) := "(" ++ reppr x ++ " ⊕ " ++ reppr y ++ ")"
| (imp x y) := "(" ++ reppr x ++ " → " ++ reppr y ++ ")"

instance [has_repr α] : has_repr (circuit α) := ⟨reppr⟩

def vars [decidable_eq α] : circuit α → list α
| true := []
| false := []
| (var x) := [x]
| (and c₁ c₂) := (vars c₁ ++ vars c₂).dedup
| (or c₁ c₂) := (vars c₁ ++ vars c₂).dedup
| (not c) := vars c
| (xor c₁ c₂) := (vars c₁ ++ vars c₂).dedup
| (imp c₁ c₂) := (vars c₁ ++ vars c₂).dedup

@[simp] def eval : circuit α → (α → bool) → bool
| true _ := tt
| false _ := ff
| (var x) f := f x
| (and c₁ c₂) f := (eval c₁ f) && (eval c₂ f)
| (or c₁ c₂) f := (eval c₁ f) || (eval c₂ f)
| (not c) f := bnot (eval c f)
| (xor c₁ c₂) f := bxor (eval c₁ f) (eval c₂ f)
| (imp c₁ c₂) f := bnot (eval c₁ f) || (eval c₂ f)

@[simp] def evalv [decidable_eq α] : Π (c : circuit α), (Π a ∈ vars c, bool) → bool
| true _ := tt
| false _ := ff
| (var x) f := f x (by simp [vars])
| (and c₁ c₂) f := (evalv c₁ (λ i hi, f i (by simp [hi, vars]))) &&
  (evalv c₂ (λ i hi, f i (by simp [hi, vars])))
| (or c₁ c₂) f := (evalv c₁ (λ i hi, f i (by simp [hi, vars]))) ||
  (evalv c₂ (λ i hi, f i (by simp [hi, vars])))
| (not c) f := bnot (evalv c (λ i hi, f i (by simp [hi, vars])))
| (xor c₁ c₂) f := bxor (evalv c₁ (λ i hi, f i (by simp [hi, vars])))
  (evalv c₂ (λ i hi, f i (by simp [hi, vars])))
| (imp c₁ c₂) f := bnot (evalv c₁ (λ i hi, f i (by simp [hi, vars]))) ||
  (evalv c₂ (λ i hi, f i (by simp [hi, vars])))

lemma eval_eq_evalv [decidable_eq α] : ∀ (c : circuit α) (f : α → bool),
  eval c f = evalv c (λ x _, f x)
| true _ := rfl
| false _ := rfl
| (var x) f := rfl
| (and c₁ c₂) f := by rw [eval, evalv, eval_eq_evalv, eval_eq_evalv]
| (or c₁ c₂) f := by rw [eval, evalv, eval_eq_evalv, eval_eq_evalv]
| (not c) f := by rw [eval, evalv, eval_eq_evalv]
| (xor c₁ c₂) f := by rw [eval, evalv, eval_eq_evalv, eval_eq_evalv]
| (imp c₁ c₂) f := by rw [eval, evalv, eval_eq_evalv, eval_eq_evalv]

@[simp] def of_bool : bool → circuit α
| tt := true
| ff := false

instance : has_le (circuit α) :=
⟨λ c₁ c₂, ∀ f, eval c₁ f → eval c₂ f⟩

instance : preorder (circuit α) :=
{ le := (≤),
  le_refl := λ c f h, h,
  le_trans := λ c₁ c₂ c₃ h₁₂ h₂₃ f h₁, h₂₃ f (h₁₂ f h₁) }

instance [decidable_eq α] :
  decidable_rel ((≤) : circuit α → circuit α → Prop) :=
λ c₁ c₂, decidable_of_iff (∀ (x : Π (i : α), (i ∈ (c₁.vars ++ c₂.vars).dedup) → bool),
  x ∈ (c₁.vars ++ c₂.vars).dedup.pi (λ _, [tt, ff]) →
  c₁.evalv (λ i hi, x i (by simp [hi])) → c₂.evalv (λ i hi, x i (by simp [hi])))
   sorry

def simplify_and : circuit α → circuit α → circuit α
| true c := c
| c true := c
| false _ := false
| _ false := false
| c₁ c₂ := and c₁ c₂

@[simp] lemma eval_simplify_and : ∀ (c₁ c₂ : circuit α) (f : α → bool),
  eval (simplify_and c₁ c₂) f = (eval c₁ f) && (eval c₂ f) :=
begin
  intros c₁ c₂ f,
  cases c₁; cases c₂; simp [*, circuit.simplify_and, eval] at *
end

def simplify_or : circuit α → circuit α → circuit α
| true _ := true
| _ true := true
| false c := c
| c false := c
| c₁ c₂ := or c₁ c₂

@[simp] lemma eval_simplify_or : ∀ (c₁ c₂ : circuit α) (f : α → bool),
  eval (simplify_or c₁ c₂) f = (eval c₁ f) || (eval c₂ f) :=
begin
  intros c₁ c₂ f,
  cases c₁; cases c₂; simp [*, circuit.simplify_or, eval] at *
end

def simplify_not : circuit α → circuit α
| true := false
| false := true
| (not c) := c
| c := not c

@[simp] lemma eval_simplify_not : ∀ (c : circuit α) (f : α → bool),
  eval (simplify_not c) f = bnot (eval c f) :=
begin
  intros c f,
  cases c; simp [*, circuit.simplify_not, eval] at *
end

def simplify_xor : circuit α → circuit α → circuit α
| false c := c
| c false := c
| true c := not c
| c true := not c
| c₁ c₂ := xor c₁ c₂

lemma bnot_bxor : ∀ (b₁ b₂ : bool), bnot (bxor b₁ b₂) = bxor b₁ (bnot b₂) :=
dec_trivial

@[simp] lemma eval_simplify_xor : ∀ (c₁ c₂ : circuit α) (f : α → bool),
  eval (simplify_xor c₁ c₂) f = bxor (eval c₁ f) (eval c₂ f) :=
begin
  intros c₁ c₂ f,
  cases c₁; cases c₂; simp [*, circuit.simplify_xor, eval, bnot_bxor] at *,
end

def simplify_imp : circuit α → circuit α → circuit α
| false _ := true
| _ true := true
| true c := c
| c false := not c
| c₁ c₂ := imp c₁ c₂

@[simp] lemma eval_simplify_imp : ∀ (c₁ c₂ : circuit α) (f : α → bool),
  eval (simplify_imp c₁ c₂) f = bnot (eval c₁ f) || (eval c₂ f) :=
begin
  intros c₁ c₂ f,
  cases c₁; cases c₂; simp [*, circuit.simplify_imp, eval] at *
end

def map : Π (c : circuit α) (f : α → β), circuit β
| true _ := true
| false _ := false
| (var x) f := var (f x)
| (and c₁ c₂) f := simplify_and (map c₁ f) (map c₂ f)
| (or c₁ c₂) f := simplify_or (map c₁ f) (map c₂ f)
| (not c) f := simplify_not (map c f)
| (xor c₁ c₂) f := simplify_xor (map c₁ f) (map c₂ f)
| (imp c₁ c₂) f := simplify_imp (map c₁ f) (map c₂ f)

lemma eval_map {c : circuit α} {f : α → β} {g : β → bool} :
  eval (map c f) g = eval c (λ x, g (f x)) :=
begin
  induction c; simp [*, circuit.map, eval] at *
end

def simplify : Π (c : circuit α), circuit α
| true := true
| false := false
| (var x) := var x
| (and c₁ c₂) := simplify_and (simplify c₁) (simplify c₂)
| (or c₁ c₂) := simplify_or (simplify c₁) (simplify c₂)
| (not c) := simplify_not (simplify c)
| (xor c₁ c₂) := simplify_xor (simplify c₁) (simplify c₂)
| (imp c₁ c₂) := simplify_imp (simplify c₁) (simplify c₂)

@[simp] lemma eval_simplify : Π {c : circuit α} {f : α → bool},
  eval (simplify c) f = eval c f
| true _ := rfl
| false _ := rfl
| (var x) f := rfl
| (and c₁ c₂) f := by rw [simplify]; simp *
| (or c₁ c₂) f := by rw [simplify]; simp *
| (not c) f := by rw [simplify]; simp *
| (xor c₁ c₂) f := by rw [simplify]; simp *
| (imp c₁ c₂) f := by rw [simplify]; simp *

def sum_vars_left [decidable_eq α] [decidable_eq β] : circuit (α ⊕ β) → list α
| true := []
| false := []
| (var (sum.inl x)) := [x]
| (var (sum.inr _)) := []
| (and c₁ c₂) := (sum_vars_left c₁ ++ sum_vars_left c₂).dedup
| (or c₁ c₂) := (sum_vars_left c₁ ++ sum_vars_left c₂).dedup
| (not c) := sum_vars_left c
| (xor c₁ c₂) := (sum_vars_left c₁ ++ sum_vars_left c₂).dedup
| (imp c₁ c₂) := (sum_vars_left c₁ ++ sum_vars_left c₂).dedup

def sum_vars_right [decidable_eq α] [decidable_eq β] : circuit (α ⊕ β) → list β
| true := []
| false := []
| (var (sum.inl _)) := []
| (var (sum.inr x)) := [x]
| (and c₁ c₂) := (sum_vars_right c₁ ++ sum_vars_right c₂).dedup
| (or c₁ c₂) := (sum_vars_right c₁ ++ sum_vars_right c₂).dedup
| (not c) := sum_vars_right c
| (xor c₁ c₂) := (sum_vars_right c₁ ++ sum_vars_right c₂).dedup
| (imp c₁ c₂) := (sum_vars_right c₁ ++ sum_vars_right c₂).dedup

lemma eval_eq_of_eq_on_vars [decidable_eq α] : Π {c : circuit α} {f g : α → bool}
  (h : ∀ x ∈ c.vars, f x = g x), eval c f = eval c g
| true _ _ _ := rfl
| false _ _ _ := rfl
| (var x) f g h := h x (by simp [vars])
| (and c₁ c₂) f g h :=
begin
  simp only [vars, list.mem_append, list.mem_dedup] at h,
  rw [eval, eval,
    eval_eq_of_eq_on_vars (λ x hx, h x (or.inl hx)),
    eval_eq_of_eq_on_vars (λ x hx, h x (or.inr hx))]
end
| (or c₁ c₂) f g h :=
begin
  simp only [vars, list.mem_append, list.mem_dedup] at h,
  rw [eval, eval,
    eval_eq_of_eq_on_vars (λ x hx, h x (or.inl hx)),
    eval_eq_of_eq_on_vars (λ x hx, h x (or.inr hx))]
end
| (not c) f g h :=
begin
  simp only [vars] at h,
  rw [eval, eval, eval_eq_of_eq_on_vars h]
end
| (xor c₁ c₂) f g h :=
begin
  simp only [vars, list.mem_append, list.mem_dedup] at h,
  rw [eval, eval,
    eval_eq_of_eq_on_vars (λ x hx, h x (or.inl hx)),
    eval_eq_of_eq_on_vars (λ x hx, h x (or.inr hx))]
end
| (imp c₁ c₂) f g h :=
begin
  simp only [vars, list.mem_append, list.mem_dedup] at h,
  rw [eval, eval,
    eval_eq_of_eq_on_vars (λ x hx, h x (or.inl hx)),
    eval_eq_of_eq_on_vars (λ x hx, h x (or.inr hx))]
end

@[simp] lemma mem_vars_iff_mem_sum_vars_left [decidable_eq α] [decidable_eq β] :
  Π {c : circuit (α ⊕ β)} {x : α},
  (x ∈ c.sum_vars_left) ↔ sum.inl x ∈ c.vars
| true _  := by simp [vars, sum_vars_left]
| false _  := by simp [vars, sum_vars_left]
| (var (sum.inl x)) _ := by simp [vars, sum_vars_left]
| (var (sum.inr _)) _ := by simp [vars, sum_vars_left]
| (and c₁ c₂) _ :=
  begin
    simp [vars, sum_vars_left],
    simp [mem_vars_iff_mem_sum_vars_left]
  end
| (or c₁ c₂) _ :=
  begin
    simp [vars, sum_vars_left],
    simp [mem_vars_iff_mem_sum_vars_left]
  end
| (not c) _ :=
  begin
    simp [vars, sum_vars_left],
    simp [mem_vars_iff_mem_sum_vars_left]
  end
| (xor c₁ c₂) _ :=
  begin
    simp [vars, sum_vars_left],
    simp [mem_vars_iff_mem_sum_vars_left]
  end
| (imp c₁ c₂) _ :=
  begin
    simp [vars, sum_vars_left],
    simp [mem_vars_iff_mem_sum_vars_left]
  end

@[simp] lemma mem_vars_iff_mem_sum_vars_right [decidable_eq α] [decidable_eq β] :
  Π {c : circuit (α ⊕ β)} {x : β},
  (x ∈ c.sum_vars_right) ↔ sum.inr x ∈ c.vars
| true _  := by simp [vars, sum_vars_right]
| false _  := by simp [vars, sum_vars_right]
| (var (sum.inl _)) _ := by simp [vars, sum_vars_right]
| (var (sum.inr x)) _ := by simp [vars, sum_vars_right]
| (and c₁ c₂) _ :=
  begin
    simp [vars, sum_vars_right],
    simp [mem_vars_iff_mem_sum_vars_right]
  end
| (or c₁ c₂) _ :=
  begin
    simp [vars, sum_vars_right],
    simp [mem_vars_iff_mem_sum_vars_right]
  end
| (not c) _ :=
  begin
    simp [vars, sum_vars_right],
    simp [mem_vars_iff_mem_sum_vars_right]
  end
| (xor c₁ c₂) _ :=
  begin
    simp [vars, sum_vars_right],
    simp [mem_vars_iff_mem_sum_vars_right]
  end
| (imp c₁ c₂) _ :=
  begin
    simp [vars, sum_vars_right],
    simp [mem_vars_iff_mem_sum_vars_right]
  end

lemma eval_eq_of_eq_on_sum_vars_left_right
  [decidable_eq α] [decidable_eq β] :
  Π {c : circuit (α ⊕ β)} {f g : α ⊕ β → bool}
  (h₁ : ∀ x ∈ c.sum_vars_left, f (sum.inl x) = g (sum.inl x))
  (h₂ : ∀ x ∈ c.sum_vars_right, f (sum.inr x) = g (sum.inr x)),
  eval c f = eval c g
| true _ _ _ _ := rfl
| false _ _ _ _ := rfl
| (var (sum.inl x)) f g h₁ h₂ := h₁ x (by simp [sum_vars_left])
| (var (sum.inr x)) f g h₁ h₂ := h₂ x (by simp [sum_vars_right])
| (and c₁ c₂) f g h₁ h₂ :=
begin
  simp only [sum_vars_left, sum_vars_right, list.mem_append, list.mem_dedup] at h₁ h₂,
  rw [eval, eval,
    eval_eq_of_eq_on_sum_vars_left_right
      (λ x hx, h₁ x (or.inl hx)) (λ x hx, h₂ x (or.inl hx)),
    eval_eq_of_eq_on_sum_vars_left_right
      (λ x hx, h₁ x (or.inr hx)) (λ x hx, h₂ x (or.inr hx))]
end
| (or c₁ c₂) f g h₁ h₂ :=
begin
  simp only [sum_vars_left, sum_vars_right, list.mem_append, list.mem_dedup] at h₁ h₂,
  rw [eval, eval,
    eval_eq_of_eq_on_sum_vars_left_right
      (λ x hx, h₁ x (or.inl hx)) (λ x hx, h₂ x (or.inl hx)),
    eval_eq_of_eq_on_sum_vars_left_right
      (λ x hx, h₁ x (or.inr hx)) (λ x hx, h₂ x (or.inr hx))]
end
| (not c) f g h₁ h₂ :=
begin
  simp only [sum_vars_left, sum_vars_right] at h₁ h₂,
  rw [eval, eval, eval_eq_of_eq_on_sum_vars_left_right h₁ h₂]
end
| (xor c₁ c₂) f g h₁ h₂ :=
begin
  simp only [sum_vars_left, sum_vars_right, list.mem_append, list.mem_dedup] at h₁ h₂,
  rw [eval, eval,
    eval_eq_of_eq_on_sum_vars_left_right
      (λ x hx, h₁ x (or.inl hx)) (λ x hx, h₂ x (or.inl hx)),
    eval_eq_of_eq_on_sum_vars_left_right
      (λ x hx, h₁ x (or.inr hx)) (λ x hx, h₂ x (or.inr hx))]
end
| (imp c₁ c₂) f g h₁ h₂ :=
begin
  simp only [sum_vars_left, sum_vars_right, list.mem_append, list.mem_dedup] at h₁ h₂,
  rw [eval, eval,
    eval_eq_of_eq_on_sum_vars_left_right
      (λ x hx, h₁ x (or.inl hx)) (λ x hx, h₂ x (or.inl hx)),
    eval_eq_of_eq_on_sum_vars_left_right
      (λ x hx, h₁ x (or.inr hx)) (λ x hx, h₂ x (or.inr hx))]
end

def bOr : Π (s : list α) (f : α → circuit β), circuit β
| [] _ := false
| (a::l) f := l.foldl (λ c x, simplify_or c (f x)) (f a)

@[simp] lemma eval_foldl_or :
  ∀ (s : list α) (f : α → circuit β) (c : circuit β) (g : β → bool),
    (eval (s.foldl (λ c x, simplify_or c (f x)) c) g : Prop) ↔
      eval c g ∨ (∃ a ∈ s, eval (f a) g)
| [] f c g := by simp [eval]; cases c.eval g; simp
| (a::l) f c g := begin
  rw [list.foldl_cons, eval_foldl_or],
  simp only [eval_simplify_or, bor_coe_iff, exists_prop, list.mem_cons_iff],
  split,
  { intro h,
    rcases h with (h₁ | h₂) | ⟨a, ha⟩,
    { simp * },
    { exact or.inr ⟨_, or.inl rfl, h₂⟩ },
    { exact or.inr ⟨_, or.inr ha.1, ha.2⟩ } },
  { intro h,
    rcases h with h | ⟨a, rfl| ha, h⟩,
    { simp * },
    { simp * },
    { exact or.inr ⟨_, ha, h⟩ } }
end

@[simp] lemma eval_bOr :
  ∀ {s : list α} {f : α → circuit β} {g : β → bool},
    eval (bOr s f) g ↔ ∃ a ∈ s, eval (f a) g
| [] _ _ := by simp [bOr, eval]
| [a] f g := by simp [bOr, eval]
| (a::l) f g :=
by rw [bOr, eval_foldl_or, list.exists_mem_cons_iff]

def bAnd : Π (s : list α) (f : α → circuit β), circuit β
| [] _ := true
| (a::l) f := l.foldl (λ c x, simplify_and c (f x)) (f a)

@[simp] lemma eval_foldl_and :
  ∀ (s : list α) (f : α → circuit β) (c : circuit β) (g : β → bool),
    (eval (s.foldl (λ c x, simplify_and c (f x)) c) g : Prop) ↔
      eval c g ∧ (∀ a ∈ s, eval (f a) g)
| [] f c g := by simp [eval]; cases c.eval g; simp
| (a::l) f c g := begin
  rw [list.foldl_cons, eval_foldl_and],
  simp only [eval_simplify_and, band_coe_iff, list.mem_cons_iff, forall_eq_or_imp],
  simp [and.assoc]
end

@[simp] lemma eval_bAnd :
  ∀ {s : list α} {f : α → circuit β} {g : β → bool},
    eval (bAnd s f) g ↔ ∀ a ∈ s, eval (f a) g
| [] _ _ := by simp [bAnd, eval]
| [a] f g := by simp [bAnd, eval]
| (a::l) f g :=
by rw [bAnd, eval_foldl_and]; simp

def assign_vars [decidable_eq α] :
  Π (c : circuit α) (f : Π (a : α) (ha : a ∈ c.vars), β ⊕ bool), circuit β
| true _ := true
| false _ := false
| (var x) f := sum.elim var (λ b : bool, if b then true else false) (f x (by simp [vars]))
| (and c₁ c₂) f := simplify_and (assign_vars c₁ (λ x hx, f x (by simp [hx, vars])))
                       (assign_vars c₂ (λ x hx, f x (by simp [hx, vars])))
| (or c₁ c₂) f := simplify_or (assign_vars c₁ (λ x hx, f x (by simp [hx, vars])))
                      (assign_vars c₂ (λ x hx, f x (by simp [hx, vars])))
| (not c) f := simplify_not (assign_vars c (λ x hx, f x (by simp [hx, vars])))
| (xor c₁ c₂) f := simplify_xor (assign_vars c₁ (λ x hx, f x (by simp [hx, vars])))
                        (assign_vars c₂ (λ x hx, f x (by simp [hx, vars])))
| (imp c₁ c₂) f := simplify_imp (assign_vars c₁ (λ x hx, f x (by simp [hx, vars])))
                        (assign_vars c₂ (λ x hx, f x (by simp [hx, vars])))

lemma eval_assign_vars [decidable_eq α] : ∀ {c : circuit α}
  {f : Π (a : α) (ha : a ∈ c.vars), β ⊕ bool} {g : β → bool},
  eval (assign_vars c f) g = evalv c (λ a ha,sum.elim g id (f a ha))
| true _ _ := rfl
| false _ _ := rfl
| (var x) f g := begin
  simp [assign_vars, eval, vars],
  cases f x (by simp [vars]),
  simp [eval],
  simp [eval],
  cases val; simp [eval]
end
| (and c₁ c₂) f g := begin
  simp [assign_vars, eval, vars],
  rw [eval_assign_vars, eval_assign_vars]
end
| (or c₁ c₂) f g := begin
  simp [assign_vars, eval, vars],
  rw [eval_assign_vars, eval_assign_vars]
end
| (not c) f g := begin
  simp [assign_vars, eval, vars],
  rw [eval_assign_vars]
end
| (xor c₁ c₂) f g := begin
  simp [assign_vars, eval, vars],
  rw [eval_assign_vars, eval_assign_vars]
end
| (imp c₁ c₂) f g := begin
  simp [assign_vars, eval, vars],
  rw [eval_assign_vars, eval_assign_vars]
end

def bind : Π (c : circuit α) (f : α → circuit β), circuit β
| true _ := true
| false _ := false
| (var x) f := f x
| (and c₁ c₂) f := simplify_and (bind c₁ f) (bind c₂ f)
| (or c₁ c₂) f := simplify_or (bind c₁ f) (bind c₂ f)
| (not c) f := simplify_not (bind c f)
| (xor c₁ c₂) f := simplify_xor (bind c₁ f) (bind c₂ f)
| (imp c₁ c₂) f := simplify_imp (bind c₁ f) (bind c₂ f)

lemma eval_bind : ∀ (c : circuit α) (f : α → circuit β) (g : β → bool),
  eval (bind c f) g = eval c (λ a, eval (f a) g)
| true _ _ := rfl
| false _ _ := rfl
| (var x) f g := rfl
| (and c₁ c₂) f g := begin
  simp [bind, eval],
  rw [eval_bind, eval_bind]
end
| (or c₁ c₂) f g := begin
  simp [bind, eval],
  rw [eval_bind, eval_bind]
end
| (not c) f g := begin
  simp [bind, eval],
  rw [eval_bind]
end
| (xor c₁ c₂) f g := begin
  simp [bind, eval],
  rw [eval_bind, eval_bind]
end
| (imp c₁ c₂) f g := begin
  simp [bind, eval],
  rw [eval_bind, eval_bind]
end

def single [decidable_eq α] {s : list α} (x : Π a ∈ s, bool) : circuit α :=
bAnd s (λ i, if hi : i ∈ s then cond (x i hi) (var i) (not (var i)) else true)

@[simp] lemma eval_single [decidable_eq α] {s : list α} (x : Π a ∈ s, bool) (g : α → bool):
  eval (single x) g ↔ (∀ a ∈ s, g a = x a (by simpa)) :=
begin
  rw [single],
  simp,
  split,
  { intros h a ha,
    specialize h a ha,
    rw [dif_pos ha] at h,
    cases x a ha; simpa using h },
  { intros h a ha,
    rw [dif_pos ha],
    specialize h a ha,
    cases x a ha; simp [h] }
end


end circuit
