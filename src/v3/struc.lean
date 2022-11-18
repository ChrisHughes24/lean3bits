import data.fintype.basic
import data.int.interval
import topology.bases
import topology.compact_open
import .circuit
import .list_pi

open set topological_space

@[protect_proj] structure profinite : Type 1 :=
( ι : Type )
[ dec_eq : decidable_eq ι ]
( X : Type )
[ top_inst : topological_space X ]
( proj : ι → X → bool)
( continuous_swap_proj : continuous (function.swap proj) )
( inv : (ι → bool) → X )
( continuous_inv : continuous inv )
( is_inv : ∀ x y, function.swap proj x = y ↔ x = inv y )

attribute [instance] profinite.top_inst profinite.dec_eq

namespace profinite

variables {X : profinite} {i : X.ι}

instance : has_coe_to_sort profinite Type := ⟨profinite.X⟩

@[simp] lemma proj_inv (x : X.ι → bool) : X.proj i (X.inv x) = x i :=
begin
  have := X.is_inv (X.inv x) x,
  simp [function.swap, function.funext_iff, *] at *
end

@[simp] lemma inv_proj (x : X) : X.inv (λ i, X.proj i x) = x :=
begin
  have := (X.is_inv x (λ i, X.proj i x)).symm,
  simp [function.swap, function.funext_iff, eq_comm, *] at *
end

lemma closed_embedding (X : profinite) : closed_embedding (function.swap X.proj) :=
closed_embedding_of_continuous_injective_closed
  X.continuous_swap_proj
  (λ x y hxy, begin
    rw [X.is_inv] at hxy,
    rw [hxy, eq_comm, ← X.is_inv]
  end)
  begin
    intros s hs,
    have : is_closed (X.inv ⁻¹' s) := continuous_iff_is_closed.1 X.continuous_inv _ hs,
    convert this,
    simp [set.ext_iff],
    intro x,
    split,
    { rintro ⟨y, hy, rfl⟩,
      convert hy,
      rw [eq_comm, ← X.is_inv] },
    { intro hx,
      use X.inv x,
      use hx,
      rw [X.is_inv] }
  end

attribute [continuity] profinite.continuous_inv

instance : compact_space X := X.closed_embedding.compact_space
instance : t2_space X := X.closed_embedding.t2_space
instance : totally_disconnected_space X :=
⟨is_totally_disconnected_of_image
  X.closed_embedding.continuous.continuous_on
  X.closed_embedding.inj $
  is_totally_disconnected_of_totally_disconnected_space _⟩

@[continuity] lemma continuous_proj (i : X.ι) : continuous (X.proj i) :=
show continuous ((λ x : Π i : X.ι, bool, x i) ∘ (λ (x : X) (j : X.ι), X.proj j x)),
from (continuous_apply i).comp X.closed_embedding.continuous

lemma continuous_iff_proj {Y : Type*} [topological_space Y] (f : Y → X) :
  continuous f ↔ ∀ i, continuous (λ y, X.proj i (f y)) :=
by simp only [X.closed_embedding.continuous_iff, continuous_pi_iff]

lemma is_open_iff_pi (U : set X) : is_open U ↔ ∃ (V : set (X.ι → bool)),
  is_open V ∧ (function.swap X.proj ⁻¹' V) = U :=
X.closed_embedding.is_open_iff

lemma is_closed_iff_pi (F : set X) : is_closed F ↔ ∃ (V : set (X.ι → bool)),
  is_closed V ∧ (function.swap X.proj ⁻¹' V) = F :=
X.closed_embedding.is_closed_iff

def prod (X Y : profinite) : profinite :=
{ ι := X.ι ⊕ Y.ι,
  X := X × Y,
  proj := sum.elim (λ i xy, X.proj i xy.1) (λ i xy, Y.proj i xy.2),
  continuous_swap_proj := begin
      dsimp [function.swap],
      continuity,
      cases i,
      { dsimp,
        continuity },
      { dsimp,
        continuity }
    end,
  inv := λ x, (X.inv (x ∘ sum.inl), Y.inv (x ∘ sum.inr)),
  continuous_inv := begin
      continuity,

     end,
  is_inv := begin
    rintros ⟨x, y⟩ z,
    simp [← X.is_inv, ← Y.is_inv, function.swap, prod.ext_iff, function.funext_iff]
  end }

instance {X Y : profinite} [fintype X.ι] [fintype Y.ι] : fintype (X.prod Y).ι :=
by dsimp [profinite.prod]; apply_instance

instance {X Y : profinite} [fintype X.X] [fintype Y.X] : fintype (X.prod Y).X :=
by dsimp [profinite.prod]; apply_instance

instance {X Y : profinite} [has_repr X.ι] [has_repr Y.ι] : has_repr (X.prod Y).ι :=
by dsimp [profinite.prod]; apply_instance

instance {X Y : profinite} [has_repr X.X] [has_repr Y.X] : has_repr (X.prod Y).X :=
by dsimp [profinite.prod]; apply_instance

def boolp : profinite :=
{ ι := unit,
  X := bool,
  proj := λ _, id,
  continuous_swap_proj := by continuity,
  inv := λ i, i (),
  continuous_inv := by continuity,
  is_inv := dec_trivial}

instance Safsasg: fintype (boolp.ι) := by dsimp [boolp]; apply_instance
instance aagsga : fintype (boolp.X) := by dsimp [boolp]; apply_instance

instance agdgs : has_repr (boolp.ι) := by dsimp [boolp]; apply_instance
instance agdgsa : has_repr (boolp.X) := by dsimp [boolp]; apply_instance

def twoadic : profinite :=
{ ι := ℕ,
  X := ℕ → bool,
  proj := function.swap id,
  continuous_swap_proj := continuous_id,
  continuous_inv := by continuity,
  inv := id,
  is_inv := by simp [function.swap] }

open circuit

def circuit.to_set (c : circuit X.ι) : set X :=
{ x | c.eval (λ i, X.proj i x) }

structure map (X Y : profinite) : Type :=
( to_fun : X → Y )
( preimage : circuit Y.ι → circuit X.ι )
( continuous' : ∀ (x : X) (C : circuit Y.ι),
  to_fun x ∈ C.to_set ↔ x ∈ (preimage C).to_set )

instance (X Y : profinite) : has_coe_to_fun (map X Y) (λ _, X → Y) :=
⟨map.to_fun⟩

theorem map.continuous {Y : profinite}: ∀ (f : map X Y) (x : X) (C : circuit Y.ι),
  f x ∈ C.to_set ↔ x ∈ (f.preimage C).to_set :=
map.continuous'

def map.id (X : profinite) : map X X :=
{ to_fun := id,
  preimage := λ C, C,
  continuous' := λ x C, by simp }

def map.comp {X Y Z : profinite} (f : map X Y) (g : map Y Z) : map X Z :=
{ to_fun := g ∘ f,
  preimage := λ C, f.preimage (g.preimage C),
  continuous' := λ x C, by simp [f.continuous, g.continuous] }

def projm (X : profinite) (i : X.ι) : map X boolp :=
{ to_fun := X.proj i,
  preimage := λ C, C.map (λ _, i),
  continuous' := λ x C, by simp [circuit.to_set, eval_map]; refl }

def fstm {X Y : profinite} : (X.prod Y).map X :=
{ to_fun := prod.fst,
  preimage := λ C, C.map sum.inl,
  continuous' := λ x C, begin
    delta profinite.prod circuit.to_set,
    simp [eval_map],
  end }

def sndm {X Y : profinite} : (X.prod Y).map Y :=
{ to_fun := prod.snd,
  preimage := λ C, C.map sum.inr,
  continuous' := λ x C, begin
    delta profinite.prod circuit.to_set,
    simp [eval_map],
  end }

def reindex {X Y : profinite} (e : Y.ι → X.ι) : map X Y :=
{ to_fun := λ x, Y.inv (λ i, X.proj (e i) x),
  preimage := λ C, C.map e,
  continuous' := λ x C, by simp [eval_map, circuit.to_set] }

def prod_mk_reindex {X Y Z : profinite} (e₁ : Y.ι → X.ι)
  (e₂ : Z.ι → X.ι) : map X (Y.prod Z) :=
{ to_fun := λ x, (Y.inv (λ i, X.proj (e₁ i) x), Z.inv (λ i, X.proj (e₂ i) x)),
  preimage := λ C, C.map (sum.elim e₁ e₂),
  continuous' := λ x C, begin
    delta profinite.prod circuit.to_set,
    simp [eval_map, circuit.to_set],
    rw [iff_iff_eq],
    congr' 2,
    ext i,
    cases i with i i;
    simp,
  end }

def diag {X : profinite} : X.map (X.prod X) :=
prod_mk_reindex id id

def fst {Y : profinite} (C : circuit (X.prod Y).ι) : circuit X.ι :=
circuit.bOr (C.sum_vars_right.pi (λ _, [tt, ff]))
  (λ x, circuit.assign_vars C
    (λ i, sum.rec (λ i _, sum.inl i) (λ i hi, sum.inr (x i (by simp [hi]))) i))

lemma mem_fst {Y : profinite} (C : circuit (X.prod Y).ι) (x : X) :
  x ∈ (fst C).to_set ↔ ∃ y, (x, y) ∈ C.to_set :=
begin
  dsimp [fst, circuit.to_set],
  simp only [eval_assign_vars, list.mem_pi, or_iff_not_imp_left, eval_bOr,
    list.mem_cons_iff, list.mem_singleton,
    eq_ff_eq_not_eq_tt, imp_self, implies_true_iff, exists_true_left],
  dsimp [set_of, set.mem_def, profinite.prod],
  split,
  { rintros ⟨a, ha⟩,
    refine ⟨Y.inv (λ i, if hi : i ∈ C.sum_vars_right then a i hi else tt), _⟩,
    simp [eval_eq_evalv],
    convert ha,
    ext i hi,
    cases i with i i; simp * },
  { rintro ⟨y, hy⟩,
    use λ i hi, Y.proj i y,
    convert hy,
    simp [eval_eq_evalv],
    congr' 1,
    ext i hi,
    cases i with i i; simp * }
end

def snd {Y : profinite} (C : circuit (X.prod Y).ι) : circuit Y.ι :=
circuit.bOr (C.sum_vars_left.pi (λ _, [tt, ff]))
  (λ x, circuit.assign_vars C
    (λ i, sum.rec (λ i hi, sum.inr (x i (by simp [hi]))) (λ i _, sum.inl i) i))

lemma mem_snd {Y : profinite} (C : circuit (X.prod Y).ι) (y : Y) :
  y ∈ (snd C).to_set ↔ ∃ x, (x, y) ∈ C.to_set :=
begin
  dsimp [snd, circuit.to_set],
  simp only [eval_assign_vars, list.mem_pi, or_iff_not_imp_left, eval_bOr,
    list.mem_cons_iff, list.mem_singleton,
    eq_ff_eq_not_eq_tt, imp_self, implies_true_iff, exists_true_left],
  dsimp [set_of, set.mem_def, profinite.prod],
  split,
  { rintros ⟨a, ha⟩,
    refine ⟨X.inv (λ i, if hi : i ∈ C.sum_vars_left then a i hi else tt), _⟩,
    simp [eval_eq_evalv],
    convert ha,
    ext i hi,
    cases i with i i; simp * },
  { rintro ⟨x, hx⟩,
    use λ i hi, X.proj i x,
    convert hx,
    simp [eval_eq_evalv],
    congr' 1,
    ext i hi,
    cases i with i i; simp * }
end

def prod_mk {X Y Z : profinite} (f : X.map Y) (g : X.map Z) : X.map (Y.prod Z) :=
{ to_fun := λ x, (f x, g x),
  preimage := λ C, circuit.bOr C.vars (λ i, sum.elim _ _ i),
  continuous' := _ }

def prod_map {W X Y Z : profinite} (f : W.map Y) (g : X.map Z) : (W.prod X).map (Y.prod Z) :=
prod_mk (fstm.comp f) (sndm.comp g)

def unitp : profinite :=
{ ι := empty,
  X := unit,
  proj := empty.elim,
  continuous_swap_proj := by continuity,
  continuous_inv := by continuity,
  inv := λ _, (),
  is_inv := dec_trivial }

instance : has_repr empty := ⟨empty.elim⟩
instance unitp.finι : fintype unitp.ι := by dsimp [unitp]; apply_instance
instance unitp.finX : fintype unitp.X := by dsimp [unitp]; apply_instance
instance afas : has_repr unitp.ι := by dsimp [unitp]; apply_instance
instance ads : has_repr unitp.X := by dsimp [unitp]; apply_instance

end profinite

open profinite

structure propagate_struc (input : profinite) (state : profinite) : Type 1 :=
( init : state )
( transition : (state.prod input).map state )
( output : (state.prod input).map boolp )

variables {input state : profinite}
  (p : propagate_struc input state)
  {p₁ p₂ : propagate_struc input state}

namespace propagate_struc

@[simp] def nth_state (x : ℕ → input) : ℕ → state
| 0     := p.init
| (n+1) := p.transition (nth_state n, x n)

@[simp] def nth_output (x : ℕ → input) (n : ℕ) : bool :=
p.output (nth_state p x n, x n)

lemma nth_state_eq_of_nth_state_eq
  {m n : ℕ}
  {x₁ x₂ : ℕ → input} : ∀ (i : ℕ)
  (hs : p₁.nth_state x₁ m = p₂.nth_state x₂ n)
  (hc : ∀ s, p₁.transition s = p₂.transition s)
  (hx : ∀ (j), j ≤ i → x₁ (m + j) = x₂ (n + j)),
  p₁.nth_state x₁ (m + i) = p₂.nth_state x₂ (n + i)
| 0 hs ht hx := hs
| (i+1) hs hc hx := begin
  rw [← add_assoc, ← add_assoc, nth_state, nth_state,
    nth_state_eq_of_nth_state_eq i hs hc (λ j hj, hx j (nat.le_succ_of_le hj)), hc,
    hx _ (nat.le_succ _)],
end

lemma nth_output_eq_of_nth_state_eq
  {m n : ℕ}
  {x₁ x₂ : ℕ → input} (i : ℕ)
  (hs : p₁.nth_state x₁ m = p₂.nth_state x₂ n)
  (hc : ∀ s, p₁.transition s = p₂.transition s)
  (ho : ∀ s, p₁.output s = p₂.output s)
  (hx : ∀ (j), j ≤ i → x₁ (m + j) = x₂ (n + j)) :
  p₁.nth_output x₁ (m + i) = p₂.nth_output x₂ (n + i) :=
begin
  have := nth_state_eq_of_nth_state_eq i (by simpa using hs) hc hx,
  rw [nth_output, nth_output, ho, this, hx _ (le_refl _)]
end

def iterate_preimage (o : bool) : Π (n : ℕ), circuit state.ι
| 0     := (p.output.preimage (circuit.of_bool o)).fst
| (n+1) := (p.transition.preimage (iterate_preimage n)).fst

inductive result : Type
| false_after (n : ℕ) : result
| true_for_n (n : ℕ) : result
| true_forall : result

instance : has_repr result :=
⟨λ r, match r with
| result.false_after n := "false after " ++ repr n
| result.true_for_n n := "true for " ++ repr n
| result.true_forall := "true forall"
end⟩

def decide_if_zeros_aux : Π (n : ℕ), result × clopen state
| 0 := (result.true_for_n 0, (p.output.preimage ⟨{()}, {λ _, tt}⟩).fst)
| (n+1) :=
  match decide_if_zeros_aux n with
  | (result.true_for_n m, s) :=
    let s' := (p.transition.preimage s).fst in
    if p.init ∈ s.to_set then (result.false_after (n+1), s')
    else if s'.subset s then (result.true_forall, s)
    else (result.true_for_n (n+1), s')
  | x := x
  end

def decide_if_zeros (n : ℕ) : result :=
(decide_if_zeros_aux p n).1

end propagate_struc