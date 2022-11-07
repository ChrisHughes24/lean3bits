import data.fintype.basic
import data.zmod.basic

def mod_two (a : ℤ) : bool :=
a % 2 = 1

structure state_struc : Type 1 :=
( state : Type )
( rels : ℕ → Type )
[ fin_rels : ∀ n, fintype (rels n) ]
[ dec_eq_rels : ∀ n, decidable_eq (rels n) ]
( to_rels : Π (n), state → rels n )
( rels_to_rels : Π {n m} (h : n ≤ m), rels m → rels n )
( rels_to_rels_id {n : ℕ} (h : n ≤ n) (x): rels_to_rels h x = x )
( rels_to_rels_trans {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) (x) :
    rels_to_rels h₁ (rels_to_rels h₂ x) = rels_to_rels (le_trans h₁ h₂) x )
( rels_commute : ∀ {n m} (h : n ≤ m) (s : state),
    rels_to_rels h (to_rels m s) = to_rels n s )
( rels_to_state : Π {n}, rels n → state )
( to_rels_to_state : ∀ {n x}, to_rels n (rels_to_state x) = x )

attribute [instance] state_struc.fin_rels state_struc.dec_eq_rels

variable (S : state_struc)

def state_struc.rel (n : ℕ) (s t : S.state) : Prop :=
S.to_rels n s = S.to_rels n t

structure propagate_struc (arity : Type) (S : state_struc) : Type 1 :=
( init_state : S.state )
( transition : (arity → bool) → S.state → S.state )
( transition_rel {x : arity → bool} {n : ℕ} {s t : S.state} :
    S.rel (n + 1) s t → S.rel n (transition x s) (transition x t) )
( output : (arity → bool) → S.rels 0 → bool )

variables {arity : Type} {S}
  (p : propagate_struc arity S)
  {p₁ p₂ : propagate_struc arity S}

lemma state_struc.rel.eq {n : ℕ} {s t : S.state} (h : S.rel n s t) :
  S.to_rels n s = S.to_rels n t := h

namespace propagate_struc

@[simp] def nth_state (x : ℕ → arity → bool) : ℕ → S.state
| 0     := p.init_state
| (n+1) := p.transition (x n) (nth_state n)

@[simp] def nth_output (x : ℕ → arity → bool) (n : ℕ) : bool :=
p.output (x n) (S.to_rels 0 (p.nth_state x n))

lemma nth_state_rel_of_nth_state_rel
  {m n : ℕ}
  {x₁ x₂ : ℕ → arity → bool} : ∀ (d : ℕ) (i : ℕ)
  (hs : S.rel (d + i) (p₁.nth_state x₁ m) (p₂.nth_state x₂ n))
  (ht : p₁.transition = p₂.transition)
  (hx : ∀ (j), j ≤ i → x₁ (m + j) = x₂ (n + j)),
  S.rel d (p₁.nth_state x₁ (m + i)) (p₂.nth_state x₂ (n + i))
| d 0 hs ht hx := hs
| d (i+1) hs ht hx := begin
  rw [← add_assoc, ← add_assoc, nth_state, nth_state, ht, hx _ (nat.le_succ _)],
  apply p₂.transition_rel,
  apply nth_state_rel_of_nth_state_rel _ i,
  { simpa [add_comm, add_assoc, add_left_comm] using hs },
  { exact ht },
  { exact λ j hj, hx j (nat.le_succ_of_le hj) }
end

lemma nth_output_eq_of_nth_state_rel
  {m n : ℕ}
  {x₁ x₂ : ℕ → arity → bool} (i : ℕ)
  (hs : S.rel i (p₁.nth_state x₁ m) (p₂.nth_state x₂ n))
  (ht : p₁.transition = p₂.transition)
  (ho : p₁.output = p₂.output)
  (hx : ∀ (j), j ≤ i → x₁ (m + j) = x₂ (n + j)) :
  p₁.nth_output x₁ (m + i) = p₂.nth_output x₂ (n + i) :=
begin
  have := nth_state_rel_of_nth_state_rel 0 i (by simpa using hs) ht hx,
  rw [nth_output, nth_output, ho, this.eq, hx _ (le_refl _)]
end

inductive reachable_in (p : propagate_struc arity S) (m : ℕ) (s : S.rels m) :
  Π (n : ℕ), S.rels (m + n) → Prop
| refl : reachable_in 0 s
| succ {n t} (x : arity → bool) (h : reachable_in n (S.to_rels _ t)) :
  reachable_in (n + 1) (S.to_rels _ (p.transition x t))

def find_reachables [fintype arity] [decidable_eq arity] : Π (m : ℕ) (s : finset (S.rels m)),
  Π (n : ℕ), finset (S.rels (m + n))
| m s  0    := s
| m s (n+1) := let t := find_reachables m s n in
finset.univ.filter (λ s, ∃ x : arity → bool, S.to_rels _ (p.transition x (S.rels_to_state s)) ∈ t)

end propagate_struc