import data.list.basic

universes u v w

variables {α : Type u} {β : Type v} {δ : α → Type w}
variables [decidable_eq α]

namespace list

open function

def pi.cons (m : list α) (a : α) (b : δ a) (f : Πa∈m, δ a) : Πa'∈a :: m, δ a' :=
λa' ha', if h : a' = a then eq.rec b h.symm else f a' $ ((mem_cons_iff _ _ _).1 ha').resolve_left h

lemma pi.cons_same {m : list α} {a : α} {b : δ a} {f : Πa∈m, δ a} (h : a ∈ a :: m) :
  pi.cons m a b f a h = b :=
dif_pos rfl

lemma pi.cons_ne {m : list α} {a a' : α} {b : δ a} {f : Πa∈m, δ a}
  (h' : a' ∈ a :: m) (h : a' ≠ a) :
  pi.cons m a b f a' h' = f a' (((mem_cons_iff _ _ _).1 h').resolve_left h) :=
dif_neg h

lemma pi.cons_swap {a a' : α} {b : δ a} {b' : δ a'} {m : list α} {f : Πa∈m, δ a} (h : a ≠ a') :
  pi.cons (a' :: m) a b (pi.cons m a' b' f) == pi.cons (a :: m) a' b' (pi.cons m a b f) :=
begin
  apply hfunext rfl,
  rintro a'' _ rfl,
  refine hfunext (by simp [or_comm, or_assoc, or.left_comm]) (λ ha₁ ha₂ _, _),
  rcases ne_or_eq a'' a with h₁ | rfl,
  rcases eq_or_ne a'' a' with rfl | h₂,
  all_goals { simp [*, pi.cons_same, pi.cons_ne] },
end

def pi : Π (s : list α) (t : Πa, list (δ a)), list (Πa∈s, δ a)
| [] t := [λa ha, false.elim (list.not_mem_nil _ ha)]
| (a::m) t := (t a).bind $ λb, (pi m t).map $ list.pi.cons m a b

@[simp] lemma pi_nil (t : Πa, list (δ a)) :
  pi [] t = [λa ha, false.elim (list.not_mem_nil _ ha)] := rfl

@[simp] lemma pi_cons (a : α) (m : list α) (t : Πa, list (δ a)) :
  pi (a :: m) t = (t a).bind (λb, (pi m t).map $ list.pi.cons m a b) := rfl

@[simp]
lemma pi.cons_ext {m : list α} {a : α} (f : Π a' ∈ a :: m, δ a') :
  pi.cons m a (f _ (mem_cons_self _ _)) (λ a' ha', f a' (mem_cons_of_mem _ ha')) = f :=
begin
  ext a' h',
  by_cases a' = a,
  { subst h, rw [pi.cons_same] },
  { rw [pi.cons_ne _ h] }
end

lemma mem_pi (m : list α) (t : Πa, list (δ a)) :
  ∀f:Πa∈m, δ a, (f ∈ pi m t) ↔ (∀a (h : a ∈ m), f a h ∈ t a) :=
begin
  intro f,
  induction m with a m ih,
  { simp [function.funext_iff] },
  { simp_rw [pi_cons, mem_bind, mem_map, ih],
    split,
    { rintro ⟨b, hb, f', hf', rfl⟩ a' ha',
      by_cases a' = a,
      { subst h, rwa [pi.cons_same] },
      { rw [pi.cons_ne _ h], apply hf' } },
    { intro hf,
      refine ⟨_, hf a (mem_cons_self _ _), _, λ a ha, hf a (mem_cons_of_mem _ ha), _⟩,
      rw pi.cons_ext } }
end

end list