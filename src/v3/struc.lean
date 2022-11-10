import data.fintype.basic
import data.int.interval
import topology.bases
import topology.compact_open

open set topological_space

structure profinite : Type 1 :=
( ι : Type )
( X : Type )
[ top_inst : topological_space X ]
( proj_type : ι → Type )
[ top_inst2 : Π i, topological_space (proj_type i) ]
[ disc_inst : Π i, discrete_topology (proj_type i) ]
[ fintype_inst : Πi, fintype (proj_type i) ]
( proj : Πi, X → proj_type i )
( closed_embedding : closed_embedding (function.swap proj) )

attribute [instance] profinite.top_inst profinite.fintype_inst profinite.top_inst2
attribute [instance] profinite.disc_inst

namespace profinite

variables {X : profinite} {i : X.ι}

instance : has_coe_to_sort profinite Type := ⟨profinite.X⟩

instance : compact_space X := X.closed_embedding.compact_space

lemma continuous_proj (i : X.ι) : continuous (proj X i) :=
show continuous ((λ x : Π i : X.ι, X.proj_type i, x i) ∘ (λ (x : X) (j : X.ι), X.proj j x)),
from (continuous_apply i).comp X.closed_embedding.continuous

lemma continuous_iff_proj {Y : Type*} [topological_space Y] (f : Y → X) :
  continuous f ↔ ∀ i, continuous (λ y, proj X i (f y)) :=
by simp only [X.closed_embedding.continuous_iff, continuous_pi_iff]

lemma continuous_iff_exists_finset {Y : Type*} [topological_space Y]
  [discrete_topology Y] (f : X → Y) :
  continuous f ↔ ∃ (s : finset X.ι), ∀ x y : X,
    (∀ i ∈ s, proj X i x = proj X i y) → f x = f y := sorry

end profinite

structure propagate_struc (input : profinite) (state : profinite) : Type 1 :=
( i : state )
( t : state → input → state )
( t_continuous_finset : Π (i : state.ι)
   (a : state.proj_type i), finset (state.ι × input.ι) )
(  )
( o : state → input → output )

variables {arity : Type}
  (p : propagate_struc arity)
  {p₁ p₂ : propagate_struc arity}

namespace propagate_struc

def next_carry (x : arity → bool) (c : ℤ) : ℤ :=
(c + p.carry x (mod_two c)) / 2

@[simp] def nth_carry (x : ℕ → arity → bool) : ℕ → ℤ
| 0     := p.init_carry
| (n+1) := next_carry p (x n) (nth_carry n)

lemma nth_carry_le (x : ℕ → arity → bool) (n : ℕ) :
  p.nth_carry x n ≤ p.max_carry :=
begin
  induction n with n ih,
  { exact p.init_carry_le },
  { have h₁ : p.nth_carry x n ≤ p.max_carry,
    { exact ih },
    have h₂ : p.carry (x n) (mod_two (p.nth_carry x n)) ≤ p.max_carry,
    { exact p.carry_le (x n) (mod_two (p.nth_carry x n)) },
    have h₃ : p.nth_carry x n + p.carry (x n) (mod_two (p.nth_carry x n)) ≤ p.max_carry + p.max_carry,
    { exact add_le_add h₁ h₂ },
    rw nth_carry,
    exact int.div_le_of_le_mul (by norm_num) (by rwa mul_two) }
end

lemma le_nth_carry (x : ℕ → arity → bool) (n : ℕ) :
  p.min_carry ≤ p.nth_carry x n :=
begin
  induction n with n ih,
  { exact p.le_init_carry },
  { have h₁ : p.min_carry ≤ p.nth_carry x n,
    { exact ih },
    have h₂ : p.min_carry ≤ p.carry (x n) (mod_two (p.nth_carry x n)),
    { exact p.le_carry (x n) (mod_two (p.nth_carry x n)) },
    have h₃ : p.min_carry + p.min_carry ≤ p.nth_carry x n + p.carry (x n) (mod_two (p.nth_carry x n)),
    { exact add_le_add h₁ h₂ },
    rw nth_carry,
    exact int.le_div_of_mul_le (by norm_num) (by rwa [mul_two]) }
end

@[simp] def nth_output (x : ℕ → arity → bool) (n : ℕ) : bool :=
p.output (x n) (mod_two (p.nth_carry x n))

lemma nth_carry_eq_of_nth_carry_eq
  {m n : ℕ}
  {x₁ x₂ : ℕ → arity → bool} : ∀ (i : ℕ)
  (hs : p₁.nth_carry x₁ m = p₂.nth_carry x₂ n)
  (hc : p₁.carry = p₂.carry)
  (hx : ∀ (j), j ≤ i → x₁ (m + j) = x₂ (n + j)),
  p₁.nth_carry x₁ (m + i) = p₂.nth_carry x₂ (n + i)
| 0 hs ht hx := hs
| (i+1) hs hc hx := begin
  rw [← add_assoc, ← add_assoc, nth_carry, nth_carry, next_carry, next_carry,
    hc, hx _ (nat.le_succ _),
    nth_carry_eq_of_nth_carry_eq _ _ hc (λ j hj, hx j (nat.le_succ_of_le hj))],
  { simpa [add_comm, add_assoc, add_left_comm] using hs }
end

lemma nth_output_eq_of_nth_carry_eq
  {m n : ℕ}
  {x₁ x₂ : ℕ → arity → bool} (i : ℕ)
  (hs : p₁.nth_carry x₁ m = p₂.nth_carry x₂ n)
  (hc : p₁.carry = p₂.carry)
  (ho : p₁.output = p₂.output)
  (hx : ∀ (j), j ≤ i → x₁ (m + j) = x₂ (n + j)) :
  p₁.nth_output x₁ (m + i) = p₂.nth_output x₂ (n + i) :=
begin
  have := nth_carry_eq_of_nth_carry_eq i (by simpa using hs) hc hx,
  rw [nth_output, nth_output, ho, this, hx _ (le_refl _)]
end

inductive reachable_in : ℕ → ℤ → ℤ → Prop
| init (i : ℤ) : reachable_in 0 i i
| succ {n i j} (x : arity → bool) (h : reachable_in n i j) :
  reachable_in (n + 1) i ((j + p.carry x (mod_two j)) / 2)

def reachable_from (b : bool) : ∀ (n : ℕ), set (finset.Icc p.min_carry p.max_carry)
| 0     := (mod_two ∘ coe) ⁻¹' {b}
| (n+1) := ⋃ (x : arity → bool), (p.next_carry x ∘ coe) ⁻¹' (coe '' reachable_from n)

#print set.image_union

end propagate_struc