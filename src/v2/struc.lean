import data.fintype.basic
import data.int.interval

def mod_two (a : ℤ) : bool :=
a % 2 = 1

structure propagate_struc (arity : Type) : Type 1 :=
( init_carry : ℤ )
( max_carry : ℤ )
( min_carry : ℤ )
( carry : (arity → bool) → bool → ℤ )
( carry_le : ∀ x b, carry x b ≤ max_carry )
( le_carry : ∀ x b, min_carry ≤ carry x b )
( init_carry_le : init_carry ≤ max_carry )
( le_init_carry : min_carry ≤ init_carry )
( output : (arity → bool) → bool → bool )

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



end propagate_struc