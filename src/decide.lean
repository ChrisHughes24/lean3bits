import lemmas

open fintype

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