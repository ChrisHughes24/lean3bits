import .struc

open profinite

structure carry_struc (input : profinite) : Type :=
( init : twoadic )
( carry_add : (twoadic.prod input).map twoadic )
( output : input.map boolp )

def add_seq_aux (x y : ℕ → bool) : ℕ → bool × bool
| 0 := (bxor (x 0) (y 0), x 0 && y 0)
| (n+1) := let carry := (add_seq_aux n).2 in
  let a := x (n + 1), b := y (n + 1) in
  (bxor a (bxor b carry), (a && b) || (b && carry) || (a && carry))

def add_seq (x y : ℕ → bool) : ℕ → bool :=
λ n, (add_seq_aux x y n).1

def fin_add_seq_aux {n : ℕ} (x y : fin n → bool) : fin n → bool × bool
| ⟨0, h⟩ := (bxor (x ⟨0, h⟩) (y ⟨0, h⟩), x ⟨0, h⟩ && y ⟨0, h⟩)
| ⟨k+1, h⟩ := let carry :=
    (fin_add_seq_aux ⟨k, lt_trans (nat.lt_succ_self _) h⟩).2 in
  let a := x ⟨k+1, h⟩, b := y ⟨k+1, h⟩ in
  (bxor a (bxor b carry), (a && b) || (b && carry) || (a && carry))

def fin_add_seq {n : ℕ} (x y : fin n → bool) : fin n → bool :=
λ i, (fin_add_seq_aux x y i).1

lemma fin_add_seq_eq_add_seq_aux {n : ℕ} (x y : ℕ → bool) : ∀ (i : fin n),
  fin_add_seq (λ i, x i) (λ i, y i) i = add_seq x y i ∧
    (fin_add_seq_aux (λ i, x i) (λ i, y i) i).2 =
      (add_seq_aux x y i).2
| ⟨0, h⟩ :=
 by simp [fin_add_seq, fin_add_seq_aux, add_seq, add_seq_aux]
| ⟨(n+1), h⟩ :=
begin
  cases fin_add_seq_eq_add_seq_aux ⟨n, lt_trans (nat.lt_succ_self _) h⟩ with H1 H2,
  clear_aux_decl,
  simp [fin_add_seq, fin_add_seq_aux, add_seq, add_seq_aux] at *,
  simp [H1, H2]
end

lemma fin_add_seq_eq_add_seq {n : ℕ} (x y : ℕ → bool) : ∀ (i : fin n),
  fin_add_seq (λ i, x i) (λ i, y i) i = add_seq x y i :=
λ i, (fin_add_seq_eq_add_seq_aux x y i).1

lemma finset.sup_id_mem (s : finset ℕ) : ∀ (hs : s.nonempty), s.sup id ∈ s :=
finset.induction_on s (by simp) $
(λ a s has ih, begin
  clear ih has,
  apply finset.induction_on s,
  { simp },
  { intros b s hbs ih _,
    simp at *,
    cases ih with ih ih,
    { cases le_total b a with hba hba,
      { tauto },
      { have : s.sup id ≤ a,
        { rw [finset.sup_le_iff],
          simpa },
        rw [← sup_assoc, sup_eq_right.2 hba, sup_eq_left.2 (le_trans this hba)],
        simp * } },
    { cases le_total b a with hba hba,
      { rw [← sup_assoc, sup_eq_left.2 hba],
        simp * },
      { cases le_total b (s.sup id) with hbs hbs,
        { rw [sup_eq_right.2 hbs], simp * },
        { rw [sup_eq_left.2 hbs, sup_eq_right.2 hba],
          simp * } } } }
end)

def divtwo : twoadic.map twoadic :=
{ to_fun := λ f i, f (i + 1),
  preimage := λ C,
  { s := C.s.image nat.succ,
    S := C.S.map ⟨λ f i, f ⟨nat.pred i.1, begin have := i.2,
      simp at this,
      cases this with a ha,
      simp [← ha.2, ha.1],
       end⟩, begin
         intros x y hxy,
         simp [function.funext_iff] at *,
         intros x h,
         exact hxy _ _ ⟨h, rfl⟩,
       end⟩  },
  continuous' := begin
   intros x hx,
    dsimp [twoadic, clopen.to_set] at *,
    simp [function.swap, function.funext_iff],
    split,
    { intro h,
      refine ⟨_, h, _⟩,
      simp },
    { rintros ⟨a, ha, ha₂⟩,
      convert ha,
      funext,
      have := ha₂ _ _ ⟨i.2, rfl⟩,
      cases i, exact this.symm }
  end }

def twoadic_add : (twoadic.prod twoadic).map twoadic :=
{ to_fun := λ x, add_seq x.1 x.2,
  preimage := λ x, show clopen (twoadic.prod twoadic), from
  { s := let t := finset.range (x.s.sup id + 1) in
    ⟨(t.map ⟨sum.inl, by intros _ _ h; injection h⟩).1 +
     (t.map ⟨sum.inr, by intros _ _ h; injection h⟩).1,
    (multiset.nodup.add_iff (finset.nodup _) (finset.nodup _)).2 (λ x h₁ h₂, begin
      simp only [finset.map_val, finset.range_coe, function.embedding.coe_fn_mk, multiset.mem_map, multiset.mem_range,
        finset.lt_sup_iff, id.def, exists_prop] at *,
      rcases h₁ with ⟨a, _, rfl⟩,
      rcases h₂ with ⟨s, _, _, h⟩, end)⟩,
    S := finset.univ.filter (λ f,
      let n : ℕ := x.s.sup id in
      let a : fin (n+1) → bool := λ i, f ⟨sum.inl (i : ℕ), begin
        cases i with i hi,
        simp [sum.inl.inj_eq, n] at *,
        rw [nat.lt_succ_iff] at hi,
        cases lt_or_eq_of_le hi with hi hi,
        { right,
          use n,
          simp only [hi, and_true],
          apply finset.sup_id_mem _ _,
          apply finset.nonempty_of_ne_empty,
          intro h; simp * at * },
        { simp * at * }
        end⟩ in
      let b : fin (n+1) → bool := λ i, f ⟨sum.inr (i : ℕ), begin
        cases i with i hi,
        simp [sum.inr.inj_eq, n] at *,
        rw [nat.lt_succ_iff] at hi,
        cases lt_or_eq_of_le hi with hi hi,
        { right,
          use n,
          simp only [hi, and_true],
          apply finset.sup_id_mem _ _,
          apply finset.nonempty_of_ne_empty,
          intro h; simp * at * },
        { simp * at * }
        end⟩ in
      let a_add_b : (x.s : set twoadic.ι) → bool :=
        λ i, fin_add_seq a b ⟨i.1, nat.lt_succ_of_le (begin
          dsimp [n],
          refine @finset.le_sup _ _ _ _ _ id _ _,
          exact i.2
        end)⟩ in
      a_add_b ∈ x.S) },
  continuous' := begin
    dsimp [clopen.to_set],
    intros x c,
    simp,
    rw [iff_iff_eq],
    congr' 1,
    funext i,
    dsimp [twoadic, function.swap, profinite.prod],
    rw [fin_add_seq_eq_add_seq],
    simp,
  end }

@[simps] def xor_map : (boolp.prod boolp).map boolp :=
{ to_fun := λ x, bxor x.1 x.2,
  preimage := λ C, let C' : finset bool := finset.univ.filter (λ x, x ∈ C.to_set) in
  { s :=
    if tt ∈ C'
      then if ff ∈ C' then ∅
      else {sum.inl (), sum.inr ()}
    else if ff ∈ C' then {sum.inl (), sum.inr ()}
    else {sum.inl ()},
    S := if h₁ : tt ∈ C'
      then if h₂ : ff ∈ C' then finset.univ
      else begin
        rw [if_pos h₁, if_neg h₂],
        exact {λ x, sum.elim (λ _, tt) (λ _, ff) x.1,
               λ x, sum.elim (λ _, ff) (λ _, tt) x.1}
      end
    else if h₂ : ff ∈ C' then begin
      rw [if_neg h₁, if_pos h₂],
      exact {λ x, sum.elim (λ _, ff) (λ _, ff) x.1,
             λ x, sum.elim (λ _, tt) (λ _, tt) x.1}
      end
      else ∅ },
  continuous' := begin
    dsimp [boolp, profinite.prod, coe_sort, has_coe_to_sort.coe, clopen.to_set],
    intros x c, cases c with s S,
    dsimp at *,
    revert x s S,
    exact dec_trivial
  end }

@[simps] def carry_struc.to_propagate_struc {input : profinite} (struc : carry_struc input) :
  propagate_struc input twoadic :=
{ init := struc.init,
  transition := diag.comp ((prodmapm struc.carry_add fstm).comp twoadic_add),
  output := begin
    have f := struc.output,
    have g := prodmapm (twoadic.projm (show ℕ, from 0)) f,
    exact g.comp xor_map,
  end }


@[simps] def add_struc {X : profinite} (p q : carry_struc X) :
  carry_struc X :=
{ init := twoadic_add (p.init, q.init),
  carry_add := diag.comp ((prodmapm p.carry_add q.carry_add).comp twoadic_add),
  output := diag.comp ((prodmapm p.output q.output).comp xor_map) }
--FALSE
def nth_state_add_struc {X : profinite} (p q : carry_struc X) (x : ℕ → X)
  (i : ℕ) : (add_struc p q).to_propagate_struc.nth_state x i =
  twoadic_add (p.to_propagate_struc.nth_state x i, q.to_propagate_struc.nth_state x i) :=
begin
  induction i with i ih,
  { dsimp [propagate_struc.nth_state, add_struc, carry_struc.to_propagate_struc],
    refl },
  { rw [propagate_struc.nth_state, ih, propagate_struc.nth_state,
      propagate_struc.nth_state],
    dsimp [diag, profinite.map.comp, coe_fn, has_coe_to_fun.coe, prodmapm, fstm,
      twoadic_add],

     }

end