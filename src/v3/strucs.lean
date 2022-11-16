import .struc
import logic.equiv.defs
import .defs

open propagate_struc profinite

set_option class.instance_max_depth 100

def bitwise_map (op : bool → bool → bool) : (boolp.prod boolp).map boolp :=
{ to_fun := λ x, op x.1 x.2,
    preimage := λ C, shrink
      { s := by simp [unitp, boolp, profinite.prod]; exact finset.univ,
        S := finset.univ.filter (λ x, op (x ⟨sum.inl (), by simp⟩)
                                          (x ⟨sum.inr (), by simp⟩) ∈ C.to_set) },
    continuous' := begin
      intros x C,
      rw [to_set_shrink],
      simp [clopen.to_set, boolp],
      refl
    end }

def bitwise_map3 (op : bool → bool → bool → bool) : (boolp.prod (boolp.prod boolp)).map boolp :=
{ to_fun := λ x, op x.1 x.2.1 x.2.2,
  preimage := λ C, shrink
      { s := by simp [unitp, boolp, profinite.prod]; exact finset.univ,
        S := finset.univ.filter (λ x, op (x ⟨sum.inl (), by simp⟩)
                                          (x ⟨sum.inr (sum.inl ()), by simp⟩)
                                          (x ⟨sum.inr (sum.inr ()), by simp⟩) ∈ C.to_set) },
  continuous' := begin
      intros x C,
      rw [to_set_shrink],
      simp [clopen.to_set, boolp],
      refl
    end }

def const {X Y : profinite} (y : Y) : map X Y :=
{ to_fun := λ _, y,
    preimage := λ C,
      if y ∈ C.to_set then clopen.univ else clopen.empty,
    continuous' := λ x C, begin
     split_ifs,
     simp [clopen.univ, clopen.to_set, clopen.empty, unitp, *] at *,
     simp [clopen.univ, clopen.to_set, clopen.empty, unitp, *] at *,
    end }

def bitwise_struc (op : bool → bool → bool) : propagate_struc (boolp.prod boolp) unitp :=
{ init := (),
  transition := const (),
  output := sndm.comp (bitwise_map op) }

def not_struc : propagate_struc boolp unitp :=
{ init := (),
  transition := const (),
  output :=
  { to_fun := λ x, bnot x.2,
    preimage := λ C, shrink
      { s := by simp [unitp, boolp, profinite.prod]; exact finset.univ,
        S := finset.univ.filter (λ x, bnot (x ⟨sum.inr (), by simp⟩) ∈ C.to_set) },
    continuous' := begin
      dsimp [boolp, profinite.prod, coe_sort, has_coe_to_sort.coe, unitp],
      intros x C, cases C with C₁ C₂,
      dsimp [clopen.to_set] at *,
      revert x C₁ C₂,
      exact dec_trivial
    end } }

def ls_struc (b : bool) : propagate_struc boolp boolp :=
{ init := b,
  transition := sndm,
  output := fstm }

def add_struc : propagate_struc (boolp.prod boolp) boolp :=
{ init := ff,
  transition := bitwise_map3 (λ x y z, bxor (bxor x y) z),
  output := bitwise_map3 (λ x y z, band (bxor x y) z) }

def sub_struc : propagate_struc (boolp.prod boolp) boolp :=
{ init := ff,
  transition := bitwise_map3 (λ x y z, bxor (bxor x y) z),
  output := bitwise_map3 (λ x y z, band (bxor x y) (bnot z)) }

def neg_struc : propagate_struc boolp boolp :=
{ init := ff,
  transition := sndm,
  output := bitwise_map (λ x y, band x (bnot y)) }

def incr_struc : propagate_struc boolp boolp :=
{ init := tt,
  transition := sndm,
  output := bitwise_map (λ x y, band x y) }

def decr_struc : propagate_struc boolp boolp :=
{ init := tt,
  transition := sndm,
  output := bitwise_map (λ x y, band (bnot x) y) }

def reindex {X Y : profinite} (f : X.ι ≃ Y.ι) : X.map Y :=
{ to_fun := λ x, Y.inv (λ i, X.proj (f.symm i) x),
  preimage := λ C,
  { s := C.s.map f.symm.to_embedding,
    S := C.S.map ⟨λ x i, x ⟨f i, by simpa using i.prop⟩,
      begin
        intros x y hxy,
        simp [function.funext_iff] at *,
        intros i hi,
        simpa using hxy (f.symm i) (by simpa using hi),
      end⟩ },
  continuous' := begin
    dsimp [clopen.to_set],
    simp [function.funext_iff],
    intros x C,
    split,
    { intro h,
      refine ⟨_, h, _⟩,
      simp },
    { rintro ⟨y, hy, h⟩,
      convert hy,
      ext i,
      cases i with i hi,
      rw [← h],
      simp,
      simpa }
  end }

def rearrange_prod₁ {W X Y Z : profinite} :
  ((W.prod X).prod (Y.prod Z)).map ((W.prod Y).prod (X.prod Z)) :=
reindex begin
  dsimp [profinite.prod],
  refine (equiv.sum_assoc _ _ _).symm.trans _,
  refine equiv.trans _ (equiv.sum_assoc _ _ _),
  refine equiv.sum_congr _ (equiv.refl _),
  refine equiv.trans (equiv.sum_assoc _ _ _) _,
  refine equiv.trans _ (equiv.sum_assoc _ _ _).symm,
  refine equiv.sum_congr (equiv.refl _) _,
  refine equiv.sum_comm _ _
end

def prod_assoc {X Y Z : profinite} :
  ((X.prod Y).prod Z).map (X.prod (Y.prod Z)) :=
reindex (equiv.sum_assoc _ _ _)

def bin_comp {input state₁ state₂ state₃ : profinite} (p : propagate_struc (boolp.prod boolp) state₁)
  (q : propagate_struc input state₂) (r : propagate_struc input state₃) :
  propagate_struc input (state₁.prod (state₂.prod state₃)) :=
{ init := (p.init, q.init, r.init),
  transition := begin
    have f₁ := prod_assoc.comp ((prodmapm (map.id _) ((prodmapm (map.id _) (diag)).comp
      (rearrange_prod₁.comp (prodmapm q.output r.output)))).comp p.transition),
    have f₂ := (prodmapm (sndm.comp fstm) (map.id _)).comp q.transition,
    have f₃ := (prodmapm (sndm.comp sndm) (map.id _)).comp r.transition,
    exact prodmk f₁ (prodmk f₂ f₃)
  end,
  output := begin
    refine map.comp _ p.output,
    refine prod_assoc.comp _,
    refine prodmapm (map.id _) _,
    have := rearrange_prod₁.comp (prodmapm q.output r.output),
    refine map.comp _ this,
    refine prodmapm (map.id _) diag,
  end }

def una_comp {input state₁ state₂ : profinite} (p : propagate_struc boolp state₁)
  (q : propagate_struc input state₂) : propagate_struc input (state₁.prod state₂) :=
{ init := (p.init, q.init),
  transition := begin
    have := p.transition,
    have := q.output,
    have := q.transition,
    refine prodmk (prod_assoc.comp _) _,
    { refine (prodmapm (map.id _) q.output).comp p.transition },
    { refine (prodmapm sndm (map.id _)).comp q.transition }
  end,
  output := begin
    have := p.output,
    have := q.output,
    have := prod_assoc.comp ((prodmapm _ q.output).comp p.output),
    exact this,
    exact map.id _
  end }

def propagate_struc.proj (n : ℕ) : propagate_struc twoadic unitp :=
{ init := (),
  transition := const (),
  output := sndm.comp (projm _ n) }

def propagate_struc.zero : propagate_struc twoadic unitp :=
{ init := (),
  transition := const (),
  output := const ff }

def propagate_struc.neg_one : propagate_struc twoadic unitp :=
{ init := (),
  transition := const (),
  output := const tt }

def propagate_struc.one : propagate_struc twoadic boolp :=
{ init := tt,
  transition :=
  { to_fun := λ _, ff,
    preimage := λ C,
    if h : ff ∈ C.to_set
    then clopen.univ
    else ⟨{sum.inr nat.zero}, ∅⟩,
    continuous' := begin
      intros,split_ifs;
      simp [*, clopen.univ, clopen.to_set] at *,
    end },
  output := fstm }

def of_term : term → Σ (state : profinite), propagate_struc twoadic state
| (term.var n) := ⟨unitp, propagate_struc.proj n⟩
| (term.zero) := ⟨unitp, propagate_struc.zero⟩
| (term.one) := ⟨_, propagate_struc.one⟩
| (term.add t₁ t₂) :=
  let ⟨state₁, p₁⟩ := of_term t₁,
      ⟨state₂, p₂⟩ := of_term t₂ in
  ⟨_, bin_comp add_struc p₂ p₂⟩
| (term.sub t₁ t₂) :=
  let ⟨state₁, p₁⟩ := of_term t₁,
      ⟨state₂, p₂⟩ := of_term t₂ in
  ⟨_, bin_comp sub_struc p₂ p₂⟩
| (term.neg t) :=
  let ⟨state, p⟩ := of_term t in
  ⟨_, una_comp neg_struc p⟩
| (term.and t₁ t₂) :=
  let ⟨state₁, p₁⟩ := of_term t₁,
      ⟨state₂, p₂⟩ := of_term t₂ in
  ⟨_, bin_comp (bitwise_struc band) p₂ p₂⟩
| (term.or t₁ t₂) :=
  let ⟨state₁, p₁⟩ := of_term t₁,
      ⟨state₂, p₂⟩ := of_term t₂ in
  ⟨_, bin_comp (bitwise_struc bor) p₂ p₂⟩
| (term.xor t₁ t₂) :=
  let ⟨state₁, p₁⟩ := of_term t₁,
      ⟨state₂, p₂⟩ := of_term t₂ in
  ⟨_, bin_comp (bitwise_struc bxor) p₂ p₂⟩
| (term.not t) :=
  let ⟨state, p⟩ := of_term t in
  ⟨_, una_comp not_struc p⟩
| (term.incr t) :=
  let ⟨state, p⟩ := of_term t in
  ⟨_, una_comp incr_struc p⟩
| (term.decr t) :=
  let ⟨state, p⟩ := of_term t in
  ⟨_, una_comp decr_struc p⟩
| (term.ls t) :=
  let ⟨state, p⟩ := of_term t in
  ⟨_, una_comp (ls_struc ff) p⟩
| (term.neg_one) :=
  ⟨_, propagate_struc.neg_one⟩

def check_eq (t₁ t₂ : term) (n : ℕ) : result :=
decide_if_zeros (of_term (t₁.xor t₂)).2 n
open term
#eval check_eq (var 0) (var 1) 1

#eval let t := (var 0).xor (var 1) in
  let p := (of_term t).2 in
  (p.output.preimage ⟨{()}, {λ _, tt}⟩).fst.S.card

open term
