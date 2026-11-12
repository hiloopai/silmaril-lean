module

public import Silmaril.Semantics.ElgotMonads.Defs
import Batteries.Tactic.Alias

/-!
# Nondeterministic complete Elgot iteration: proofs

Proofs for `Silmaril.Semantics.ElgotMonads.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

universe u

namespace Silmaril.Elgot.Nondet

private theorem mem_pure_iff {A : Type u} {a b : A} :
    a ∈ₘ (pure b : _root_.SetM A) ↔ a = b := Iff.rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.mem_pure_iff := Silmaril.Elgot.Nondet.mem_pure_iff

private theorem mem_pure {A : Type u} (a : A) : a ∈ₘ (pure a : _root_.SetM A) := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.mem_pure := Silmaril.Elgot.Nondet.mem_pure

private theorem mem_bind_iff {A B : Type u} {s : _root_.SetM A} {f : A → _root_.SetM B} {b : B} :
    b ∈ₘ (s >>= f) ↔ ∃ a, a ∈ₘ s ∧ b ∈ₘ f a := by
  change b ∈ ⋃ a ∈ s.run, (f a).run ↔ _
  simp only [Set.mem_iUnion, exists_prop]
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.mem_bind_iff := Silmaril.Elgot.Nondet.mem_bind_iff

private theorem ext {A : Type u} {s t : _root_.SetM A}
    (h : ∀ a, a ∈ₘ s ↔ a ∈ₘ t) : s = t := Set.ext h
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.ext := Silmaril.Elgot.Nondet.ext

variable {A B C : Type u}

private theorem mem_iter_iff {A B : Type u} (f : A → _root_.SetM (B ⊕ A)) (a : A) (b : B) :
    b ∈ₘ iter f a ↔ Runs f a b := Iff.rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.mem_iter_iff := Silmaril.Elgot.Nondet.mem_iter_iff

private theorem mem_kleisliRight_iff (f : A → _root_.SetM B) (g : B → _root_.SetM C) (a : A) (c : C) :
    c ∈ₘ (f >=> g) a ↔ ∃ b, b ∈ₘ f a ∧ c ∈ₘ g b := by
  exact mem_bind_iff
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.mem_kleisliRight_iff := Silmaril.Elgot.Nondet.mem_kleisliRight_iff

private theorem mem_mapReturn_iff (f : A → _root_.SetM (B ⊕ A)) (g : B → _root_.SetM C)
    (a : A) (s : C ⊕ A) :
    s ∈ₘ mapReturn f g a ↔
      (∃ b c, Sum.inl b ∈ₘ f a ∧ c ∈ₘ g b ∧ s = Sum.inl c) ∨
      (∃ a', Sum.inr a' ∈ₘ f a ∧ s = Sum.inr a') := by
  change s ∈ₘ (f >=> Sum.elim (g >=> pure ∘ Sum.inl) (pure ∘ Sum.inr)) a ↔ _
  rw [mem_kleisliRight_iff]
  constructor
  · rintro ⟨x, hx, hs⟩
    cases x with
    | inl b =>
        change s ∈ₘ (g >=> pure ∘ Sum.inl) b at hs
        rw [mem_kleisliRight_iff] at hs
        rcases hs with ⟨c, hc, hs⟩
        exact Or.inl ⟨b, c, hx, hc, mem_pure_iff.mp hs⟩
    | inr a' => exact Or.inr ⟨a', hx, mem_pure_iff.mp hs⟩
  · rintro (⟨b, c, hb, hc, rfl⟩ | ⟨a', ha, rfl⟩)
    · refine ⟨Sum.inl b, hb, ?_⟩
      change Sum.inl c ∈ₘ (g >=> pure ∘ Sum.inl) b
      rw [mem_kleisliRight_iff]
      exact ⟨c, hc, mem_pure _⟩
    · exact ⟨Sum.inr a', ha, mem_pure _⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.mem_mapReturn_iff := Silmaril.Elgot.Nondet.mem_mapReturn_iff

private theorem fixpoint (f : A → _root_.SetM (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  funext a
  apply ext
  intro b
  show b ∈ₘ iter f a ↔ b ∈ₘ (f >=> Sum.elim pure (iter f)) a
  rw [mem_iter_iff, mem_kleisliRight_iff]
  constructor
  · intro h
    cases h with
    | done hs => exact ⟨Sum.inl b, hs, mem_pure b⟩
    | more hs hr => exact ⟨Sum.inr _, hs, (mem_iter_iff _ _ _).2 hr⟩
  · rintro ⟨s, hs, hb⟩
    cases s with
    | inl b' =>
        have hb' : b = b' := mem_pure_iff.mp hb
        rw [hb']
        exact .done hs
    | inr a' => exact .more hs ((mem_iter_iff _ _ _).1 hb)
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.fixpoint := Silmaril.Elgot.Nondet.fixpoint

private theorem runs_mapReturn_iff (f : A → _root_.SetM (B ⊕ A)) (g : B → _root_.SetM C) (a : A) (c : C) :
    Runs (mapReturn f g) a c ↔ ∃ b, Runs f a b ∧ c ∈ₘ g b := by
  constructor
  · intro h
    induction h with
    | done hdone =>
        obtain ⟨b, c', hs, hc', heq⟩ | ⟨a', _, heq⟩ := (mem_mapReturn_iff f g _ _).1 hdone
        · have hc : _ = c' := Sum.inl.inj heq
          exact ⟨b, .done hs, hc ▸ hc'⟩
        · cases heq
    | more hmore hr ih =>
        obtain ⟨b, c', _, _, heq⟩ | ⟨a', hs, heq⟩ := (mem_mapReturn_iff f g _ _).1 hmore
        · cases heq
        · have ha : _ = a' := Sum.inr.inj heq
          obtain ⟨b, hb, hc⟩ := ih
          exact ⟨b, .more (ha ▸ hs) hb, hc⟩
  · rintro ⟨b, hr, hc⟩
    induction hr with
    | done hs => exact .done ((mem_mapReturn_iff f g _ _).2 (Or.inl ⟨_, c, hs, hc, rfl⟩))
    | more hs _ ih => exact .more ((mem_mapReturn_iff f g _ _).2 (Or.inr ⟨_, hs, rfl⟩)) (ih hc)
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.runs_mapReturn_iff := Silmaril.Elgot.Nondet.runs_mapReturn_iff

private theorem naturality (f : A → _root_.SetM (B ⊕ A)) (g : B → _root_.SetM C) :
    (iter f >=> g) = iter (mapReturn f g) := by
  funext a
  apply ext
  intro c
  rw [mem_iter_iff, runs_mapReturn_iff, mem_kleisliRight_iff]
  constructor <;> rintro ⟨b, hb, hc⟩
  · exact ⟨b, (mem_iter_iff _ _ _).1 hb, hc⟩
  · exact ⟨b, (mem_iter_iff _ _ _).2 hb, hc⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.naturality := Silmaril.Elgot.Nondet.naturality

private theorem mem_flattenBody_iff (f : A → _root_.SetM ((B ⊕ A) ⊕ A)) (a : A) (s : B ⊕ A) :
    s ∈ₘ flattenBody f a ↔ ∃ x, x ∈ₘ f a ∧ flatten x = s := by
  rw [show flattenBody f = (f >=> liftPure flatten) by rfl, mem_kleisliRight_iff]
  constructor <;> rintro ⟨x, hx, hs⟩
  · exact ⟨x, hx, (mem_pure_iff.mp hs).symm⟩
  · exact ⟨x, hx, mem_pure_iff.mpr hs.symm⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.mem_flattenBody_iff := Silmaril.Elgot.Nondet.mem_flattenBody_iff

private theorem runs_flatten_cases (f : A → _root_.SetM ((B ⊕ A) ⊕ A))
    {a : A} {s : B ⊕ A} (h : Runs f a s) :
    (∀ b, s = Sum.inl b → Runs (flattenBody f) a b) ∧
    (∀ a' b, s = Sum.inr a' → Runs (flattenBody f) a' b →
      Runs (flattenBody f) a b) := by
  induction h with
  | @done a s hs =>
      have step : ∀ x, flatten (Sum.inl s) = x → x ∈ₘ flattenBody f a := fun x hx =>
        (mem_flattenBody_iff f a x).2 ⟨Sum.inl s, hs, hx⟩
      constructor
      · rintro b rfl
        exact .done (step _ rfl)
      · rintro a' b rfl tail
        exact .more (step _ rfl) tail
  | @more a a' s hs _ ih =>
      have step : Sum.inr a' ∈ₘ flattenBody f a :=
        (mem_flattenBody_iff f a _).2 ⟨Sum.inr a', hs, rfl⟩
      exact ⟨fun b heq => .more step (ih.1 b heq),
        fun a'' b heq tail => .more step (ih.2 a'' b heq tail)⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.runs_flatten_cases := Silmaril.Elgot.Nondet.runs_flatten_cases

private theorem runs_flatten_of_left (f : A → _root_.SetM ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs f a (Sum.inl b)) : Runs (flattenBody f) a b :=
  (runs_flatten_cases f h).1 b rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.runs_flatten_of_left := Silmaril.Elgot.Nondet.runs_flatten_of_left

private theorem runs_flatten_append (f : A → _root_.SetM ((B ⊕ A) ⊕ A))
    {a a' : A} {b : B} (h : Runs f a (Sum.inr a'))
    (tail : Runs (flattenBody f) a' b) : Runs (flattenBody f) a b :=
  (runs_flatten_cases f h).2 a' b rfl tail
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.runs_flatten_append := Silmaril.Elgot.Nondet.runs_flatten_append

private theorem runs_flatten_of_nested (f : A → _root_.SetM ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs (iter f) a b) : Runs (flattenBody f) a b := by
  induction h with
  | done hs => exact runs_flatten_of_left f ((mem_iter_iff _ _ _).1 hs)
  | more hs hr ih => exact runs_flatten_append f ((mem_iter_iff _ _ _).1 hs) ih
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.runs_flatten_of_nested := Silmaril.Elgot.Nondet.runs_flatten_of_nested

private theorem runs_nested_of_flatten (f : A → _root_.SetM ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs (flattenBody f) a b) : Runs (iter f) a b := by
  induction h with
  | @done a b hs =>
      obtain ⟨x, hx, heq⟩ : ∃ x, x ∈ₘ f a ∧ flatten x = Sum.inl b :=
        (mem_flattenBody_iff f a _).1 hs
      match x, heq with
      | Sum.inl (Sum.inl _), rfl => exact .done ((mem_iter_iff _ _ _).2 (.done hx))
  | @more a a' b hs _ ih =>
      obtain ⟨x, hx, heq⟩ : ∃ x, x ∈ₘ f a ∧ flatten x = Sum.inr a' :=
        (mem_flattenBody_iff f a _).1 hs
      match x, heq with
      | Sum.inl (Sum.inr _), rfl => exact .more ((mem_iter_iff _ _ _).2 (.done hx)) ih
      | Sum.inr _, rfl =>
          show Runs (iter f) a b
          cases ih with
          | done hi => exact .done ((mem_iter_iff _ _ _).2 (.more hx ((mem_iter_iff _ _ _).1 hi)))
          | more hi ht =>
              exact .more ((mem_iter_iff _ _ _).2 (.more hx ((mem_iter_iff _ _ _).1 hi))) ht
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.runs_nested_of_flatten := Silmaril.Elgot.Nondet.runs_nested_of_flatten

private theorem codiagonal (f : A → _root_.SetM ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  apply ext
  intro b
  rw [mem_iter_iff, mem_iter_iff]
  exact ⟨runs_flatten_of_nested f, runs_nested_of_flatten f⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.codiagonal := Silmaril.Elgot.Nondet.codiagonal

private theorem uniform_step (f : A → _root_.SetM (B ⊕ A)) (g : C → _root_.SetM (B ⊕ C))
    (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g))
    (a : A) (t : B ⊕ C) :
    t ∈ₘ g (h a) ↔ ∃ s, s ∈ₘ f a ∧ Sum.map id h s = t := by
  have square := congrFun comm a
  constructor
  · intro ht
    have hr : t ∈ₘ (liftPure h >=> g) a := by
      rw [mem_kleisliRight_iff]
      exact ⟨h a, mem_pure _, ht⟩
    rw [← square, mem_kleisliRight_iff] at hr
    rcases hr with ⟨s, hs, ht⟩
    exact ⟨s, hs, (mem_pure_iff.mp ht).symm⟩
  · rintro ⟨s, hs, rfl⟩
    have hl : Sum.map id h s ∈ₘ (f >=> liftPure (Sum.map id h)) a := by
      rw [mem_kleisliRight_iff]
      exact ⟨s, hs, mem_pure _⟩
    rw [square, mem_kleisliRight_iff] at hl
    rcases hl with ⟨c, hc, ht⟩
    have hcEq : c = h a := mem_pure_iff.mp hc
    subst c
    exact ht
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.uniform_step := Silmaril.Elgot.Nondet.uniform_step

private theorem runs_uniform_forward (f : A → _root_.SetM (B ⊕ A))
    (g : C → _root_.SetM (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g))
    {a : A} {b : B} (hr : Runs f a b) : Runs g (h a) b := by
  induction hr with
  | done hs =>
      apply Runs.done
      rw [uniform_step f g h comm]
      exact ⟨Sum.inl _, hs, rfl⟩
  | more hs hr ih =>
      apply Runs.more
      · rw [uniform_step f g h comm]
        exact ⟨Sum.inr _, hs, rfl⟩
      · exact ih
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.runs_uniform_forward := Silmaril.Elgot.Nondet.runs_uniform_forward

private theorem runs_uniform_reverse (f : A → _root_.SetM (B ⊕ A))
    (g : C → _root_.SetM (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g))
    {c : C} {b : B} (hr : Runs g c b) : ∀ a, c = h a → Runs f a b := by
  induction hr with
  | @done c b ht =>
      intro a ha
      obtain ⟨s, hs, heq⟩ : ∃ s, s ∈ₘ f a ∧ Sum.map id h s = Sum.inl b :=
        (uniform_step f g h comm a _).1 (ha ▸ ht)
      match s, heq with
      | Sum.inl _, rfl => exact .done hs
  | @more c c' b ht _ ih =>
      intro a ha
      obtain ⟨s, hs, heq⟩ : ∃ s, s ∈ₘ f a ∧ Sum.map id h s = Sum.inr c' :=
        (uniform_step f g h comm a _).1 (ha ▸ ht)
      match s, heq with
      | Sum.inr a', heq =>
          have hc : h a' = c' := Sum.inr.inj heq
          exact .more hs (ih a' hc.symm)
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.runs_uniform_reverse := Silmaril.Elgot.Nondet.runs_uniform_reverse

private theorem uniformity (f : A → _root_.SetM (B ⊕ A)) (g : C → _root_.SetM (B ⊕ C))
    (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g)) :
    iter f = (liftPure h >=> iter g) := by
  funext a
  apply ext
  intro b
  rw [mem_iter_iff, mem_kleisliRight_iff]
  constructor
  · intro hr
    exact ⟨h a, mem_pure _, (mem_iter_iff _ _ _).2 (runs_uniform_forward f g h comm hr)⟩
  · rintro ⟨c, hc, hb⟩
    have hcEq : c = h a := mem_pure_iff.mp hc
    exact runs_uniform_reverse f g h comm ((mem_iter_iff _ _ _).1 hb) a hcEq
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.uniformity := Silmaril.Elgot.Nondet.uniformity

instance _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.instLawfulElgotMonadSetM : LawfulElgotMonad _root_.SetM where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

private theorem iter_no_return (f : A → _root_.SetM (B ⊕ A))
    (h : ∀ a b, ¬ Sum.inl b ∈ₘ f a) (a : A) : iter f a = (∅ : Set B) := by
  apply ext
  intro b
  constructor
  · intro hr
    induction hr with
    | done hs => exact (h _ _ hs).elim
    | more _ _ ih => exact ih
  · exact False.elim
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.iter_no_return := Silmaril.Elgot.Nondet.iter_no_return

private theorem iter_two_returns (a : A) (left right : B) :
    iter (m := _root_.SetM) (fun _ : A => ({Sum.inl left, Sum.inl right} : Set (B ⊕ A))) a =
      ({left, right} : Set B) := by
  apply ext
  intro b
  change Runs _ a b ↔ b = left ∨ b = right
  constructor
  · intro h
    cases h with
    | done hs => simpa only [SetM.run, Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inl.injEq] using hs
    | more hs _ => simp only [SetM.run, Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inr_ne_inl, or_self] at hs
  · rintro (rfl | rfl)
    · exact .done (Or.inl rfl)
    · exact .done (Or.inr rfl)
alias _root_.Silmaril.Proofs.Semantics.Elgot.Nondet.iter_two_returns := Silmaril.Elgot.Nondet.iter_two_returns

end Silmaril.Elgot.Nondet
