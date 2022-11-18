import .struc
import logic.equiv.defs
import .defs

open propagate_struc profinite

set_option class.instance_max_depth 100

section

open circuit

def xor_map : (boolp.prod boolp).map boolp :=
{ to_fun := λ x, bxor x.1 x.2,
  preimage := λ C, C.bind (λ _, (var (sum.inl ())).xor (var (sum.inr ()))),
  continuous' := begin
     simp [circuit.to_set, eval_bind],
     intros x C,
     refl
  end }

def and_map : (boolp.prod boolp).map boolp :=
{ to_fun := λ x, band x.1 x.2,
  preimage := λ C, C.bind (λ _, (var (sum.inl ())).and (var (sum.inr ()))),
  continuous' := begin
     simp [circuit.to_set, eval_bind],
     intros x C,
     refl
  end }

def or_map : (boolp.prod boolp).map boolp :=
{ to_fun := λ x, bor x.1 x.2,
  preimage := λ C, C.bind (λ _, (var (sum.inl ())).or (var (sum.inr ()))),
  continuous' := begin
    simp [circuit.to_set, eval_bind],
    intros x C,
    refl
  end }

def not_map : boolp.map boolp :=
{ to_fun := bnot,
  preimage := λ C, C.bind (λ _, (var ()).not),
  continuous' := begin
    simp [circuit.to_set, eval_bind],
    intros x C,
    refl
  end }

def bitwise_map2 (op : circuit (fin 2)) :
  (boolp.prod boolp).map boolp :=
{ to_fun := λ x, op.eval (λ i, list.nth_le [x.1, x.2] i i.prop),
  preimage := λ C, C.bind (λ _, op.map (λ i, list.nth_le [sum.inl (), sum.inr ()] i i.prop)),
  continuous' := begin
      simp [circuit.to_set, eval_bind, eval_map],
      intros x C,
      rw [iff_iff_eq],
      congr' 2,
      ext i,
      cases i,
      dsimp [boolp, profinite.prod, coe_sort, has_coe_to_sort.coe],
      congr' 1,
      ext i,
      cases i with i hi,
      cases i,
      simp,
      cases i,
      simp,
      simp [nat.succ_lt_succ_iff] at hi,
      contradiction
  end }

def bitwise_map3 (op : circuit (fin 3)) :
  (boolp.prod (boolp.prod boolp)).map boolp :=
{ to_fun := λ x, op.eval (λ i, list.nth_le [x.1, x.2.1, x.2.2] i i.prop),
  preimage := λ C, C.bind (λ x, op.map (λ i, list.nth_le [sum.inl (), sum.inr (sum.inl ()), sum.inr (sum.inr ())] i i.prop)),
  continuous' := begin
      simp [circuit.to_set, eval_bind, eval_map],
      intros x C,
      rw [iff_iff_eq],
      congr' 2,
      ext i,
      cases i,
      dsimp [boolp, profinite.prod, coe_sort, has_coe_to_sort.coe],
      congr' 1,
      ext i,
      cases i with i hi,
      cases i,
      simp,
      cases i,
      simp,
      cases i,
      simp,
      simp [nat.succ_lt_succ_iff] at hi,
      contradiction
    end }

def const {X Y : profinite} (y : Y) : map X Y :=
{ to_fun := λ _, y,
  preimage := λ C, if y ∈ C.to_set then true else false,
  continuous' := λ x C, begin
    split_ifs;
    simp [circuit.to_set, *] at *,
  end }

def xor_struc : propagate_struc (boolp.prod boolp) unitp :=
{ init := (),
  transition := const (),
  output := sndm.comp xor_map }

def and_struc : propagate_struc (boolp.prod boolp) unitp :=
{ init := (),
  transition := const (),
  output := sndm.comp and_map }

def or_struc : propagate_struc (boolp.prod boolp) unitp :=
{ init := (),
  transition := const (),
  output := sndm.comp or_map }

def not_struc : propagate_struc boolp unitp :=
{ init := (),
  transition := const (),
  output := sndm.comp not_map }

def ls_struc (b : bool) : propagate_struc boolp boolp :=
{ init := b,
  transition := sndm,
  output := fstm }

def add_struc : propagate_struc (boolp.prod boolp) boolp :=
{ init := ff,
  transition := bitwise_map3 (xor (xor (var 0) (var 1)) (var 2)),
  output := bitwise_map3 (and (xor (var 0) (var 1)) (var 2)) }

def sub_struc : propagate_struc (boolp.prod boolp) boolp :=
{ init := ff,
  transition := bitwise_map3 (xor (xor (var 0) (var 1)) (var 2)),
  output := bitwise_map3 (and (xor (var 0) (var 1)) (var 2)) }

def band_bnot_map : (boolp.prod boolp).map boolp :=
bitwise_map2 (and (var 0) (var 1).not)

def bnot_band_map : (boolp.prod boolp).map boolp :=
bitwise_map2 (and (var 0).not (var 1))

def neg_struc : propagate_struc boolp boolp :=
{ init := ff,
  transition := sndm,
  output := band_bnot_map }

def incr_struc : propagate_struc boolp boolp :=
{ init := tt,
  transition := sndm,
  output := and_map }

def decr_struc : propagate_struc boolp boolp :=
{ init := tt,
  transition := sndm,
  output := bnot_band_map }

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
reindex (equiv.sum_assoc _ _ _).symm

def bin_comp {input state₁ state₂ state₃ : profinite} (p : propagate_struc (boolp.prod boolp) state₁)
  (q : propagate_struc input state₂) (r : propagate_struc input state₃) :
  propagate_struc input (state₁.prod (state₂.prod state₃)) :=
{ init := (p.init, q.init, r.init),
  transition := begin
    have f₁ := prod_assoc.comp ((prod_mapm (map.id _) ((prod_mapm (map.id _) (diag)).comp
      (rearrange_prod₁.comp (prod_mapm q.output r.output)))).comp p.transition),
    have f₂ := (prod_mapm (sndm.comp fstm) (map.id _)).comp q.transition,
    have f₃ := (prod_mapm (sndm.comp sndm) (map.id _)).comp r.transition,
    exact prod_mk f₁ (prod_mk f₂ f₃)
  end,
  output := begin
    refine map.comp _ p.output,
    refine prod_assoc.comp _,
    refine prod_mapm (map.id _) _,
    have := rearrange_prod₁.comp (prod_mapm q.output r.output),
    refine map.comp _ this,
    refine prod_mapm (map.id _) diag,
  end }

@[simp] lemma bin_comp_init {input state₁ state₂ state₃ : profinite}
  (p : propagate_struc (boolp.prod boolp) state₁) (q : propagate_struc input state₂)
  (r : propagate_struc input state₃) :
  (bin_comp p q r).init = (p.init, q.init, r.init) := rfl

@[simp] lemma bin_comp_transition {input state₁ state₂ state₃ : profinite}
  (p : propagate_struc (boolp.prod boolp) state₁) (q : propagate_struc input state₂)
  (r : propagate_struc input state₃) :
  coe_fn (bin_comp p q r).transition = (λ x : (state₁.prod (state₂.prod state₃)).prod input,
    (p.transition (x.1.1, q.output (x.1.2.1, x.2), r.output (x.1.2.2, x.2)),
      q.transition (x.1.2.1, x.2),
      r.transition (x.1.2.2, x.2))) :=
begin
  funext i,
  rcases i with ⟨⟨i, j, k⟩, x⟩,
  dsimp [nth_output, bin_comp, prod_assoc, map.comp, prod_mapm, boolp, function.comp,
    map.id, coe_fn, has_coe_to_fun.coe, prod_mk, fstm, sndm, diag, rearrange_prod₁, reindex,
    equiv.sum_assoc, equiv.trans, equiv.refl, equiv.sum_congr, equiv.symm, equiv.sum_comm,
    profinite.prod, prod_mk_reindex],
  simp [inv_proj]
end

@[simp] lemma bin_comp_output {input state₁ state₂ state₃ : profinite}
  (p : propagate_struc (boolp.prod boolp) state₁) (q : propagate_struc input state₂)
  (r : propagate_struc input state₃) :
  coe_fn (bin_comp p q r).output = (λ x : (state₁.prod (state₂.prod state₃)).prod input,
    p.output (x.1.1, q.output (x.1.2.1, x.2), r.output (x.1.2.2, x.2))) :=
begin
  funext i,
  rcases i with ⟨⟨i, j, k⟩, x⟩,
  dsimp [nth_output, bin_comp, prod_assoc, map.comp, prod_mapm, boolp, function.comp,
    map.id, coe_fn, has_coe_to_fun.coe, prod_mk, fstm, sndm, diag, rearrange_prod₁, reindex,
    equiv.sum_assoc, equiv.trans, equiv.refl, equiv.sum_congr, equiv.symm, equiv.sum_comm,
    profinite.prod, prod_mk_reindex],
  simp [inv_proj]
end

lemma nth_state_bin_comp {input state₁ state₂ state₃ : profinite} (p : propagate_struc (boolp.prod boolp) state₁)
  (q : propagate_struc input state₂) (r : propagate_struc input state₃) (x : ℕ → input) (n : ℕ) :
  (bin_comp p q r).nth_state x n = (p.nth_state (λ i, (q.nth_output x i, r.nth_output x i)) n,
    q.nth_state x n, r.nth_state x n) ∧
  (bin_comp p q r).nth_output x n = p.nth_output (λ i, (q.nth_output x i, r.nth_output x i)) n :=
begin
  induction n with n ih,
  { simp [nth_state] },
  { simp * }
end

def una_comp {input state₁ state₂ : profinite} (p : propagate_struc boolp state₁)
  (q : propagate_struc input state₂) : propagate_struc input (state₁.prod state₂) :=
{ init := (p.init, q.init),
  transition := begin
    have := p.transition,
    have := q.output,
    have := q.transition,
    refine prod_mk (prod_assoc.comp _) _,
    { refine (prod_mapm (map.id _) q.output).comp p.transition },
    { refine (prod_mapm sndm (map.id _)).comp q.transition }
  end,
  output := begin
    have := p.output,
    have := q.output,
    have := prod_assoc.comp ((prod_mapm _ q.output).comp p.output),
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
    then true
    else false,
    continuous' := begin
      intros,split_ifs;
      dsimp [circuit.to_set, set.mem_def, set_of] at *;
      simp * at *
    end },
  output := fstm }

def of_term : term → Σ (state : profinite), propagate_struc twoadic state
| (term.var n) := ⟨unitp, propagate_struc.proj n⟩
| (term.zero) := ⟨unitp, propagate_struc.zero⟩
| (term.one) := ⟨_, propagate_struc.one⟩
| (term.and t₁ t₂) :=
  let p₁ := of_term t₁,
      p₂ := of_term t₂ in
  ⟨_, bin_comp and_struc p₁.2 p₂.2⟩
| (term.or t₁ t₂) :=
  let p₁ := of_term t₁,
      p₂ := of_term t₂ in
  ⟨_, bin_comp or_struc p₁.2 p₂.2⟩
| (term.neg t) :=
  let p := of_term t in
  ⟨_, una_comp neg_struc p.2⟩
| (term.neg_one) := ⟨_, propagate_struc.neg_one⟩
| (term.add t₁ t₂) :=
  let p₁ := of_term t₁,
      p₂ := of_term t₂ in
  ⟨_, bin_comp add_struc p₁.2 p₂.2⟩
| (term.xor t₁ t₂) :=
  let p₁ := of_term t₁,
      p₂ := of_term t₂ in
  ⟨_, bin_comp xor_struc p₁.2 p₂.2⟩
| (term.not t) :=
  let p := of_term t in
  ⟨_, una_comp not_struc p.2⟩
| (term.ls t) :=
  let p := of_term t in
  ⟨_, una_comp (ls_struc ff) p.2⟩
| (term.sub t₁ t₂) :=
  let p₁ := of_term t₁,
      p₂ := of_term t₂ in
  ⟨_, bin_comp sub_struc p₁.2 p₂.2⟩
| (term.incr t) :=
  let p := of_term t in
  ⟨_, una_comp incr_struc p.2⟩
| (term.decr t) :=
  let p := of_term t in
  ⟨_, una_comp decr_struc p.2⟩

instance : Π (t : term), has_repr (of_term t).1.ι
| (term.var n) := by dsimp [of_term]; apply_instance
| (term.zero) := by dsimp [of_term]; apply_instance
| (term.one) := by dsimp [of_term]; apply_instance
| (term.add t₁ t₂) := by letI := ι.has_repr t₁; letI := ι.has_repr t₂;
  dsimp [of_term]; apply_instance
| (term.and t₁ t₂) := by letI := ι.has_repr t₁; letI := ι.has_repr t₂;
  dsimp [of_term]; apply_instance
| (term.or t₁ t₂) := by letI := ι.has_repr t₁; letI := ι.has_repr t₂;
  dsimp [of_term]; apply_instance
| (term.neg t) := by letI := ι.has_repr t; dsimp [of_term]; apply_instance
| (term.neg_one) := by dsimp [of_term]; apply_instance
| (term.xor t₁ t₂) := by letI := ι.has_repr t₁; letI := ι.has_repr t₂;
  dsimp [of_term]; apply_instance
| (term.not t) := by letI := ι.has_repr t; dsimp [of_term]; apply_instance
| (term.ls t) := by letI := ι.has_repr t; dsimp [of_term]; apply_instance
| (term.sub t₁ t₂) := by letI := ι.has_repr t₁; letI := ι.has_repr t₂;
  dsimp [of_term]; apply_instance
| (term.incr t) := by letI := ι.has_repr t; dsimp [of_term]; apply_instance
| (term.decr t) := by letI := ι.has_repr t; dsimp [of_term]; apply_instance

def check_eq (t₁ t₂ : term) (n : ℕ) : result :=
decide_if_zeros (of_term (t₁.xor t₂)).2 n

end

open term

#eval check_eq ((var 0).xor (var 0)) term.zero 1
#eval check_eq (var 0 + var 1 + var 2) (var 1 + var 0) 2


-- #eval (bitwise_struc bxor).nth_output (λ _, (tt, tt)) 0

open term
