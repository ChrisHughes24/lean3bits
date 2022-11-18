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
  continuous_inv := by continuity,
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

abbreviation clopen (X : profinite) := circuit X.ι

def clopen.to_set (C : clopen X) : set X :=
{x | C.eval (λ i, X.proj i x) }

instance clopen.decidable_mem (C : clopen X) : decidable_pred (∈ C.to_set) :=
begin
  simp [clopen.to_set],
  apply_instance
end

structure map (X Y : profinite) : Type :=
( to_fun : X → Y )
( preimage : clopen Y → clopen X )
( continuous' : ∀ (x : X) (C : clopen Y),
    to_fun x ∈ C.to_set ↔ x ∈ (preimage C).to_set )

instance (X Y : profinite) : has_coe_to_fun (map X Y) (λ _, X → Y) :=
⟨map.to_fun⟩

theorem map.continuous {Y : profinite}: ∀ (f : map X Y) (x : X) (C : clopen Y),
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
  preimage := λ (C : circuit unit), show circuit X.ι, from C.map (λ _, i),
  continuous' := begin
    intros x i,
    simp [circuit.eval_map, clopen.to_set, function.const],
    dsimp [boolp],
    refl
  end }

def fstm {X Y : profinite} : (X.prod Y).map X :=
{ to_fun := prod.fst,
  preimage := λ C, C.map sum.inl,
  continuous' := λ x C, begin
    delta profinite.prod clopen.to_set boolp,
    simp [circuit.eval_map],
    dsimp [function.comp],
    refl
  end }

def sndm {X Y : profinite} : (X.prod Y).map Y :=
{ to_fun := prod.snd,
  preimage := λ C, C.map sum.inr,
  continuous' := λ x C, begin
    delta profinite.prod clopen.to_set boolp,
    simp [circuit.eval_map],
    dsimp [function.comp],
    refl
  end }

def clopen.fst {Y : profinite} (C : clopen (X.prod Y)) : clopen X :=
let l : list Y.ι := circuit.sum_vars_right C in
circuit.bOr (list.pi l (λ _, [ff, tt]))
  (λ x, circuit.assign_vars C (λ i, sum.rec (λ x _, sum.inl x)
    (λ i hi, sum.inr (x i (by simp [hi,l]))) i))

lemma clopen.mem_fst {Y : profinite} (C : clopen (X.prod Y)) (x : X) :
  x ∈ C.fst.to_set ↔ ∃ y, (x, y) ∈ C.to_set :=
begin
  rw [clopen.fst, clopen.to_set],
  simp [circuit.eval_bOr, list.mem_pi, circuit.eval_assign_vars],
  split,
  { intro h,
    rcases h with ⟨y, hy₁, hy⟩, clear hy₁,
    use Y.inv (λ i, if hi : i ∈ circuit.sum_vars_right C then y i hi else tt),
    dsimp [clopen.to_set, set.mem_def, set_of],
    rw [circuit.eval_eq_evalv],
    convert hy,
    funext i hi,
    dsimp [profinite.prod] at *,
    cases i with i i,
    { refl },
    { simp, rw dif_pos, simpa } },
  { rintros ⟨y, hy⟩,
    use [λ i _, Y.proj i y],
    split,
    { intros a ha, cases Y.proj a y; simp },
    { dsimp [clopen.to_set, set.mem_def, set_of] at hy,
      rw [circuit.eval_eq_evalv] at hy,
      convert hy,
      funext i hi,
      cases i with i i,
      { refl },
      { refl } } }
end

def clopen.snd {Y : profinite} (C : clopen (X.prod Y)) : clopen Y :=
let l : list X.ι := circuit.sum_vars_left C in
circuit.bOr (list.pi l (λ _, [ff, tt]))
  (λ x, circuit.assign_vars C (λ i, sum.rec (λ i hi, sum.inr (x i (by simp [hi]))) (λ i _, sum.inl i) i))

lemma clopen.mem_snd {Y : profinite} (C : clopen (X.prod Y)) (y : Y) :
  y ∈ C.snd.to_set ↔ ∃ x, (x, y) ∈ C.to_set :=
begin
  rw [clopen.snd, clopen.to_set],
  simp [circuit.eval_bOr, list.mem_pi, circuit.eval_assign_vars],
  split,
  { intro h,
    rcases h with ⟨x, hx₁, hx⟩, clear hx₁,
    use X.inv (λ i, if hi : i ∈ circuit.sum_vars_left C then x i hi else tt),
    dsimp [clopen.to_set, set.mem_def, set_of],
    rw [circuit.eval_eq_evalv],
    convert hx,
    funext i hi,
    dsimp [profinite.prod] at *,
    cases i with i i,
    { simp, rw dif_pos, simpa },
    { refl } },
  { rintros ⟨x, hx⟩,
    use [λ i _, X.proj i x],
    split,
    { intros a ha, cases X.proj a x; simp },
    { dsimp [clopen.to_set, set.mem_def, set_of] at hx,
      rw [circuit.eval_eq_evalv] at hx,
      convert hx,
      funext i hi,
      cases i with i i,
      { refl },
      { refl } } }
end

def diag {X : profinite} : X.map (X.prod X) :=
{ to_fun := λ x, (x, x),
  preimage := λ C, C.map (sum.elim id id),
  continuous' := begin
    intros x C,
    simp [clopen.to_set, circuit.eval_map, function.comp],
    dsimp [profinite.prod],
    rw [iff_iff_eq],
    congr,
    ext i,
    cases i with i i; refl
  end }

def prodmk {X Y Z : profinite} (f : X.map Y) (g : X.map Z) : X.map (Y.prod Z) :=
{ to_fun := λ x, (f x, g x),
  preimage := λ C, _,
  continuous' := begin
    intros x C,
    simp [to_set_inter, ← f.continuous, ← g.continuous, clopen.mem_fst,
      clopen.mem_snd],
    simp [clopen.to_set],
    dsimp,
    split,
    { intro h,
      exact ⟨_, h, ⟨_, rfl⟩, ⟨_, rfl⟩⟩ },
    { rintro ⟨y, hy, ⟨z, rfl⟩, ⟨b, hb⟩⟩,
      simp only [function.funext_iff] at hb,
      convert hy,
      funext i,
      specialize hb i,
      cases i with i hi,
      cases i with i i,
      { dsimp [profinite.prod],
        refl },
      { dsimp [profinite.prod] at *,
        exact hb  } }
  end }

def prodmapm {W X Y Z : profinite} (f : W.map Y) (g : X.map Z) : (W.prod X).map (Y.prod Z) :=
prodmk (fstm.comp f) (sndm.comp g)

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

def iterate_preimage (o : bool) : Π (n : ℕ), clopen state
| 0     := (p.output.preimage ⟨{()}, {λ _, o}⟩).fst
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
    else (result.true_for_n (n+1), s.union s')
  | x := x
  end

def decide_if_zeros (n : ℕ) : result :=
(decide_if_zeros_aux p n).1

end propagate_struc