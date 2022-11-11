import data.fintype.basic
import data.int.interval
import topology.bases
import topology.compact_open

open set topological_space

structure profinite : Type 1 :=
( ι : Type )
( X : Type )
[ top_inst : topological_space X ]
( proj : ι → X → bool)
( closed_embedding : closed_embedding (function.swap proj) )

attribute [instance] profinite.top_inst

namespace profinite

variables {X : profinite} {i : X.ι}

instance : has_coe_to_sort profinite Type := ⟨profinite.X⟩

instance : compact_space X := X.closed_embedding.compact_space
instance : t2_space X := X.closed_embedding.t2_space
instance : totally_disconnected_space X :=
⟨is_totally_disconnected_of_image
  X.closed_embedding.continuous.continuous_on
  X.closed_embedding.inj $
  is_totally_disconnected_of_totally_disconnected_space _⟩

lemma continuous_proj (i : X.ι) : continuous (proj X i) :=
show continuous ((λ x : Π i : X.ι, bool, x i) ∘ (λ (x : X) (j : X.ι), X.proj j x)),
from (continuous_apply i).comp X.closed_embedding.continuous

lemma continuous_iff_proj {Y : Type*} [topological_space Y] (f : Y → X) :
  continuous f ↔ ∀ i, continuous (λ y, proj X i (f y)) :=
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
  closed_embedding := closed_embedding_of_continuous_injective_closed
    begin
      dsimp [function.swap],
      continuity,
      cases i,
      { dsimp,
        continuity,
        exact continuous_proj _ },
      { dsimp,
        continuity,
        exact continuous_proj _ }
    end
    begin
      intros x y h,
      simp only [function.funext_iff, sum.forall, function.swap] at *,
      dsimp at h,
      ext,
      { apply X.closed_embedding.inj,
        funext,
        exact h.1 _ },
      { apply Y.closed_embedding.inj,
        funext,
        exact h.2 _ }
    end
    sorry }

def boolp : profinite :=
{ ι := unit,
  X := bool,
  proj := λ _, id,
  closed_embedding := closed_embedding_of_continuous_injective_closed
    (continuous_def.2 (λ _ _, by simp))
    dec_trivial
    (λ _ _, by simp) }

structure clopen (X : profinite) : Type :=
( s : finset X.ι )
( S : finset (Π i, i ∈ s → bool) )

def clopen.to_set (C : clopen X) : set X :=
{ x | (λ i (hi : i ∈ C.s), X.proj i x) ∈ C.S  }

lemma clopen.is_open_to_set (C : clopen X) : is_open C.to_set := sorry

lemma clopen.is_closed_to_set (C : clopen X) : is_closed C.to_set := sorry

lemma clopen.is_clopen_to_set (C : clopen X) : is_clopen C.to_set :=
⟨C.is_open_to_set, C.is_closed_to_set⟩

lemma exists_clopen_of_clopen (U : set X) (h : is_clopen U) :
  ∃ c : clopen X, c.to_set = U := sorry

structure map (X Y : profinite) : Type :=
( to_fun : X → Y )
( clopen : Π i : Y.ι, clopen X )
( continuous : ∀ (i : Y.ι) (x : X), Y.proj i (to_fun x) = tt ↔ x ∈ (clopen i).to_set )

instance (X Y : profinite) : has_coe_to_fun (map X Y) (λ _, X → Y) :=
⟨map.to_fun⟩

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

def iterate_preimage (b : bool) : Π (n : ℕ), clopen state
-- | 0     := (mod_two ∘ coe) ⁻¹' {b}
-- | (n+1) := ⋃ (x : arity → bool), (p.next_carry x ∘ coe) ⁻¹' (coe '' reachable_from n)

#print set.image_union

end propagate_struc