import data.fintype.basic
import data.int.interval
import topology.bases
import topology.compact_open

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

structure clopen (X : profinite) : Type :=
( s : finset X.ι )
( S : finset (s → bool) )

def clopen.univ : clopen X :=
{ s := ∅,
  S := finset.univ }

def clopen.empty : clopen X :=
{ s := ∅,
  S := ∅ }

def clopen.union (C D : clopen X) : clopen X :=
{ s := C.s ∪ D.s,
  S := finset.univ.filter
    (λ x, x ∘ inclusion (finset.subset_union_left _ _) ∈ C.S ∨
          x ∘ inclusion (finset.subset_union_right _ _) ∈ D.S) }

def clopen.to_set (C : clopen X) : set X :=
(λ (x : X) (i : C.s), X.proj i x) ⁻¹' C.S

@[simp] lemma to_set_univ : (clopen.univ.to_set : set X) = set.univ :=
by simp [set.ext_iff, clopen.univ, clopen.to_set]

@[simp] lemma to_set_empty : (clopen.empty.to_set : set X) = ∅ :=
by simp [set.ext_iff, clopen.empty, clopen.to_set]

instance clopen.decidable_mem (C : clopen X) : decidable_pred (∈ C.to_set) :=
begin
  simp [clopen.to_set],
  apply_instance
end

def clopen.subset (C D : clopen X) : Prop := C.to_set ⊆ D.to_set

instance : decidable_rel (@clopen.subset X) :=
λ C D, decidable_of_iff
  (∀ x : (C.s ∪ D.s → bool), show Prop,
    from x ∘ inclusion (finset.subset_union_left _ _) ∈ C.S →
         x ∘ inclusion (finset.subset_union_right _ _) ∈ D.S)
begin
  simp [clopen.subset, clopen.to_set, set.subset_def, function.comp],
  split,
  { intros h x hx,
    have := h (λ i, X.proj i x) hx,
    exact this },
  { intros h x hx,
    convert  h (X.inv (λ i, if h : i ∈ C.s ∪ D.s then x ⟨i, h⟩ else tt)) _,
    { ext i,
      cases i with i hi,
      dsimp [set.mem_def, ← finset.mem_def] at hi,
      simp [inclusion, hi],
      refl },
    { convert hx,
      ext i,
      cases i with i hi,
      simp [inclusion, hi],
      refl } }
end

lemma to_set_union (C D : clopen X) : (C.union D).to_set = C.to_set ∪ D.to_set :=
begin
  ext x,
  dsimp [clopen.to_set, clopen.union],
  simp,
  refl
end

def clopen.inter (C D : clopen X) : clopen X :=
{ s := C.s ∪ D.s,
  S := finset.univ.filter
    (λ x, x ∘ inclusion (finset.subset_union_left _ _) ∈ C.S ∧
          x ∘ inclusion (finset.subset_union_right _ _) ∈ D.S) }

lemma to_set_inter (C D : clopen X) : (C.inter D).to_set = C.to_set ∩ D.to_set :=
begin
  ext x,
  dsimp [clopen.to_set, clopen.inter],
  simp,
  refl
end

lemma clopen.is_clopen_to_set (C : clopen X) : is_clopen C.to_set :=
have hc : continuous (λ (x : X) (i : C.s), X.proj i x),
  by continuity; exact continuous_proj _,
⟨continuous_def.1 hc _ (by simp), continuous_iff_is_closed.1 hc _ (by simp)⟩

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
  preimage := λ C, { s := {i},
                      S := finset.univ.filter (λ f, f ⟨i, by simp⟩ ∈ C.to_set) },
  continuous' := λ x C, by simp [clopen.to_set] }

def clopen.bUnion {ι : Type*} [fintype ι] (f : ι → clopen X) : clopen X :=
{ s := finset.univ.bUnion (λ i : ι, (f i).s),
  S := finset.univ.filter (λ x, ∃ i, x ∘ inclusion (finset.subset_bUnion_of_mem _ (by simp)) ∈ (f i).S) }

@[simp] lemma to_set_bUnion {ι : Type*} [fintype ι] (f : ι → clopen X) :
  (clopen.bUnion f).to_set = ⋃ i, (f i).to_set :=
begin
  ext x,
  dsimp [clopen.bUnion, clopen.to_set],
  simp,
  refl
end

def clopen.bInter {ι : Type*} [fintype ι] (f : ι → clopen X) : clopen X :=
{ s := finset.univ.bUnion (λ i : ι, (f i).s),
  S := finset.univ.filter (λ x, ∀ i, x ∘ inclusion (finset.subset_bUnion_of_mem _ (by simp)) ∈ (f i).S) }

@[simp] lemma to_set_bInter {ι : Type*} [fintype ι] (f : ι → clopen X) :
  (clopen.bInter f).to_set = ⋂ i, (f i).to_set :=
begin
  ext x,
  dsimp [clopen.bInter, clopen.to_set],
  simp,
  refl
end

def finset.inl {X Y : Type*} (s : finset (X ⊕ Y)) : finset X :=
(@finset.filter _ (sum.elim (λ _, true) (λ _, false))
  (id (λ x : X ⊕ Y, by cases x; dsimp; apply_instance)) s).attach.map
  ⟨λ x, begin
    cases x with x hx,
    cases x,
    { exact x },
    { simp * at * }
  end, begin
    intros x y hxy,
    cases x with x hx,
    cases y with y hy,
    cases x; cases y,
    { simp at *, assumption },
    { simp at *,
      rw [finset.mem_filter] at hy,
      simp * at * },
    { simp at *,
      rw [finset.mem_filter] at hx,
      simp * at * },
    { simp at *,
      rw [finset.mem_filter] at hx hy,
      simp * at * }
  end⟩

@[simp] lemma finset.mem_inl {X Y : Type*} (s : finset (X ⊕ Y)) (x : X) :
  x ∈ finset.inl s ↔ sum.inl x ∈ s :=
by simp [finset.inl]

def finset.inr {X Y : Type*} (s : finset (X ⊕ Y)) : finset Y :=
(@finset.filter _ (sum.elim (λ _, false) (λ _, true))
  (id (λ x : X ⊕ Y, by cases x; dsimp; apply_instance)) s).attach.map
  ⟨λ x, begin
    cases x with x hx,
    cases x,
    { simp * at * },
    { exact x }
  end, begin
    intros x y hxy,
    cases x with x hx,
    cases y with y hy,
    cases x; cases y,
    { simp at *,
      rw [finset.mem_filter] at hx hy,
      simp * at * },
    { simp at *,
      rw [finset.mem_filter] at hx,
      simp * at * },
    { simp at *,
      rw [finset.mem_filter] at hy,
      simp * at * },
    { simp at *, assumption }
  end⟩

@[simp] lemma finset.mem_inr {X Y : Type*} (s : finset (X ⊕ Y)) (y : Y) :
  y ∈ finset.inr s ↔ sum.inr y ∈ s :=
by simp [finset.inr]

def fstm {X Y : profinite} : (X.prod Y).map X :=
{ to_fun := prod.fst,
  preimage := λ C,
  { s := C.s.map ⟨sum.inl, λ _, by simp [sum.inl.inj_eq]⟩,
    S := finset.univ.filter (λ f, begin
      let f' : C.s → bool := λ i, f ⟨sum.inl i, by cases i with i hi; simp [hi, sum.inl.inj_eq]⟩,
      exact f' ∈ C.S
    end) },
  continuous' := λ x C, begin
    delta profinite.prod clopen.to_set,
    dsimp,
    simp
  end }

def sndm {X Y : profinite} : (X.prod Y).map Y :=
{ to_fun := prod.snd,
  preimage := λ C,
  { s := C.s.map ⟨sum.inr, λ _, by simp [sum.inr.inj_eq]⟩,
    S := finset.univ.filter (λ f, begin
      let f' : C.s → bool := λ i, f ⟨sum.inr i, by cases i with i hi; simp [hi, sum.inr.inj_eq]⟩,
      exact f' ∈ C.S
    end) },
  continuous' := λ x C, begin
    delta profinite.prod clopen.to_set,
    dsimp,
    simp
  end }

def clopen.prod {X Y : profinite} (C : clopen X) (D : clopen Y) : clopen (X.prod Y) :=
{ s := ⟨(C.s.map ⟨sum.inl, sum.inl_injective⟩).1 +
        (D.s.map ⟨sum.inr, sum.inr_injective⟩).1,
        multiset.nodup_add.2 ⟨finset.nodup _, finset.nodup _,
           begin
            simp [multiset.disjoint] at *,

          end⟩⟩,
  S := (finset.product C.S D.S).map
    ⟨λ f i, begin
      cases i with i hi,
      simp at hi,
      cases i,
      { refine f.1 ⟨i, _⟩,
        simp [sum.inl.inj_eq, *, finset.mem_def] at * },
      { refine f.2 ⟨i, _⟩,
        simp [sum.inr.inj_eq, *, finset.mem_def] at * }

    end, begin
      intros x y hxy,
      dsimp at *,
      simp [function.funext_iff] at *,
      dsimp [profinite.prod] at *,
      ext i,
      { cases i with i hi,
        exact hxy (sum.inl i) (by simp [*, finset.mem_def] at *) },
      { ext j,
        cases j with j hj,
        exact hxy (sum.inr j) (by simp [*, finset.mem_def] at *) }
    end⟩ }

def clopen.fst {Y : profinite} (C : clopen (X.prod Y)) : clopen X :=
{ s := finset.inl C.s,
  S := C.S.image (λ f x, f ⟨sum.inl x, by simpa [finset.mem_inl] using x.2⟩) }

def clopen.mem_fst {Y : profinite} (C : clopen (X.prod Y)) (x : X) :
  x ∈ C.fst.to_set ↔ ∃ y, (x, y) ∈ C.to_set :=
begin
  simp [clopen.fst, clopen.to_set, function.funext_iff],
  split,
  { rintro ⟨y, hy⟩,
    use ((X.prod Y).inv (λ i : (X.prod Y).ι, if h : i ∈ C.s then y ⟨i, h⟩ else tt)).snd,
    convert hy.1,
    ext i,
    cases i with i hi,
    cases i with i i,
    { dsimp [profinite.prod, function.comp],
      rw hy.2 _ hi },
    { dsimp [profinite.prod, function.comp],
      rw proj_inv,
      simp [hi] } },
  { rintro ⟨y, hy⟩,
    refine ⟨_, hy, _⟩,
    dsimp [profinite.prod],
    simp }
end

def clopen.snd {Y : profinite} (C : clopen (X.prod Y)) : clopen Y :=
{ s := finset.inr C.s,
  S := C.S.image (λ f x, f ⟨sum.inr x, by simpa [finset.mem_inl] using x.2⟩) }

def clopen.mem_snd {Y : profinite} (C : clopen (X.prod Y)) (y : Y) :
  y ∈ C.snd.to_set ↔ ∃ x, (x, y) ∈ C.to_set :=
begin
  simp [clopen.snd, clopen.to_set, function.funext_iff],
  split,
  { rintro ⟨x, hx⟩,
    use ((X.prod Y).inv (λ i : (X.prod Y).ι, if h : i ∈ C.s then x ⟨i, h⟩ else ff)).fst,
    convert hx.1,
    ext i,
    cases i with i hi,
    cases i with i i,
    { dsimp [profinite.prod, function.comp],
      rw proj_inv,
      simp [hi] },
    { dsimp [profinite.prod, function.comp],
      rw hx.2 _ hi } },
  { rintro ⟨x, hx⟩,
    refine ⟨_, hx, _⟩,
    dsimp [profinite.prod],
    simp }
end

def diag {X : profinite} : X.map (X.prod X) :=
{ to_fun := λ x, (x, x),
  preimage := λ C,
  { s := C.s.image (sum.elim id id),
    S := finset.univ.filter (λ f, (show C.s → bool, from λ i, f ⟨sum.elim id id i.1,
      by simp; use i; simp [i.2]⟩) ∈ C.S) },
  continuous' := λ x C, begin
    simp [to_set_inter, clopen.to_set],
    dsimp [profinite.prod],
    rw [iff_iff_eq],
    congr' 1,
    simp [function.funext_iff],
  end }

def prodmk {X Y Z : profinite} (f : X.map Y) (g : X.map Z) : X.map (Y.prod Z) :=
{ to_fun := λ x, (f x, g x),
  preimage := λ C, clopen.bUnion (λ x : C.S,
    let D : clopen (Y.prod Z) := ⟨C.s, {x}⟩ in
    (f.preimage D.fst).inter (g.preimage D.snd)),
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