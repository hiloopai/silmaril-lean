module

public import Silmaril.Semantics.Elgot.Defs
import Batteries.Tactic.Alias

/-!
# Complete Elgot monads on types: proofs

Proofs for `Silmaril.Semantics.Elgot.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot

universe u v

namespace Part

variable {A B C : Type u}

private theorem Runs.unique {A B : Type u} {f : A → _root_.Part (B ⊕ A)}
    {a : A} {b c : B} (hb : Runs f a b) (hc : Runs f a c) : b = c := by
  induction hb generalizing c with
  | done h =>
      cases hc with
      | done h' => exact Sum.inl.inj (_root_.Part.mem_unique h h')
      | more h' _ => cases _root_.Part.mem_unique h h'
  | more h hr ih =>
      cases hc with
      | done h' => cases _root_.Part.mem_unique h h'
      | more h' hc =>
          have := Sum.inr.inj (_root_.Part.mem_unique h h')
          subst this
          exact ih hc
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.Runs.unique := Silmaril.Elgot.Part.Runs.unique

private theorem mem_run_iff {A B : Type u} (f : A → _root_.Part (B ⊕ A)) (a : A) (b : B) :
    b ∈ run f a ↔ Runs f a b := by
  constructor
  · rintro ⟨h, rfl⟩
    exact Classical.choose_spec h
  · intro hb
    refine ⟨⟨b, hb⟩, ?_⟩
    exact Runs.unique (Classical.choose_spec ⟨b, hb⟩) hb
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.mem_run_iff := Silmaril.Elgot.Part.mem_run_iff

private theorem mem_iter_iff {A B : Type u} (f : A → _root_.Part (B ⊕ A)) (a : A) (b : B) :
    b ∈ iter f a ↔ Runs f a b := mem_run_iff f a b
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.mem_iter_iff := Silmaril.Elgot.Part.mem_iter_iff

private theorem mem_kleisliRight_iff (f : A → _root_.Part B) (g : B → _root_.Part C) (a : A) (c : C) :
    c ∈ (f >=> g) a ↔ ∃ b, b ∈ f a ∧ c ∈ g b := by
  simpa only [Bind.kleisliRight, _root_.Part.bind_eq_bind] using
    (_root_.Part.mem_bind_iff (f := f a) (g := g) (b := c))
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.mem_kleisliRight_iff := Silmaril.Elgot.Part.mem_kleisliRight_iff

private theorem mem_mapReturn_iff (f : A → _root_.Part (B ⊕ A)) (g : B → _root_.Part C)
    (a : A) (s : C ⊕ A) :
    s ∈ mapReturn f g a ↔
      (∃ b c, Sum.inl b ∈ f a ∧ c ∈ g b ∧ s = Sum.inl c) ∨
      (∃ a', Sum.inr a' ∈ f a ∧ s = Sum.inr a') := by
  change s ∈ (f >=> Sum.elim (fun b ↦ (g >=> pure ∘ Sum.inl) b)
    (pure ∘ Sum.inr)) a ↔ _
  rw [mem_kleisliRight_iff]
  constructor
  · rintro ⟨x, hx, hs⟩
    cases x with
    | inl b =>
        change s ∈ (g >=> pure ∘ Sum.inl) b at hs
        rw [mem_kleisliRight_iff] at hs
        rcases hs with ⟨c, hc, hs⟩
        exact Or.inl ⟨b, c, hx, hc, _root_.Part.mem_some_iff.mp hs⟩
    | inr a' => exact Or.inr ⟨a', hx, _root_.Part.mem_some_iff.mp hs⟩
  · rintro (⟨b, c, hb, hc, rfl⟩ | ⟨a', ha, rfl⟩)
    · refine ⟨Sum.inl b, hb, ?_⟩
      change Sum.inl c ∈ (g >=> pure ∘ Sum.inl) b
      rw [mem_kleisliRight_iff]
      exact ⟨c, hc, _root_.Part.mem_some _⟩
    · exact ⟨Sum.inr a', ha, _root_.Part.mem_some _⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.mem_mapReturn_iff := Silmaril.Elgot.Part.mem_mapReturn_iff

private theorem fixpoint (f : A → _root_.Part (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  funext a
  apply _root_.Part.ext
  intro b
  show b ∈ iter f a ↔ b ∈ (f >=> Sum.elim pure (iter f)) a
  rw [mem_iter_iff, mem_kleisliRight_iff]
  constructor
  · intro h
    cases h with
    | done hs => exact ⟨Sum.inl b, hs, _root_.Part.mem_some b⟩
    | more hs hr => exact ⟨Sum.inr _, hs, (mem_iter_iff _ _ _).2 hr⟩
  · rintro ⟨s, hs, hb⟩
    cases s with
    | inl b' =>
        have hb' : b = b' := _root_.Part.mem_some_iff.mp hb
        rw [hb']
        exact .done hs
    | inr a' => exact .more hs ((mem_iter_iff _ _ _).1 hb)
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.fixpoint := Silmaril.Elgot.Part.fixpoint

private theorem runs_mapReturn_iff (f : A → _root_.Part (B ⊕ A)) (g : B → _root_.Part C) (a : A) (c : C) :
    Runs (mapReturn f g) a c ↔ ∃ b, Runs f a b ∧ c ∈ g b := by
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
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.runs_mapReturn_iff := Silmaril.Elgot.Part.runs_mapReturn_iff

private theorem naturality (f : A → _root_.Part (B ⊕ A)) (g : B → _root_.Part C) :
    (iter f >=> g) = iter (mapReturn f g) := by
  funext a
  apply _root_.Part.ext
  intro c
  rw [mem_iter_iff, runs_mapReturn_iff, mem_kleisliRight_iff]
  constructor <;> rintro ⟨b, hb, hc⟩
  · exact ⟨b, (mem_iter_iff _ _ _).1 hb, hc⟩
  · exact ⟨b, (mem_iter_iff _ _ _).2 hb, hc⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.naturality := Silmaril.Elgot.Part.naturality

private theorem mem_flattenBody_iff (f : A → _root_.Part ((B ⊕ A) ⊕ A)) (a : A) (s : B ⊕ A) :
    s ∈ flattenBody f a ↔ ∃ x, x ∈ f a ∧ flatten x = s := by
  rw [show flattenBody f = (f >=> liftPure flatten) by rfl, mem_kleisliRight_iff]
  constructor <;> rintro ⟨x, hx, hs⟩
  · exact ⟨x, hx, (_root_.Part.mem_some_iff.mp hs).symm⟩
  · exact ⟨x, hx, _root_.Part.mem_some_iff.mpr hs.symm⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.mem_flattenBody_iff := Silmaril.Elgot.Part.mem_flattenBody_iff

private theorem runs_flatten_cases (f : A → _root_.Part ((B ⊕ A) ⊕ A))
    {a : A} {s : B ⊕ A} (h : Runs f a s) :
    (∀ b, s = Sum.inl b → Runs (flattenBody f) a b) ∧
    (∀ a' b, s = Sum.inr a' → Runs (flattenBody f) a' b →
      Runs (flattenBody f) a b) := by
  induction h with
  | @done a s hs =>
      have step : ∀ x, flatten (Sum.inl s) = x → x ∈ flattenBody f a := fun x hx =>
        (mem_flattenBody_iff f a x).2 ⟨Sum.inl s, hs, hx⟩
      constructor
      · rintro b rfl
        exact .done (step _ rfl)
      · rintro a' b rfl tail
        exact .more (step _ rfl) tail
  | @more a a' s hs _ ih =>
      have step : Sum.inr a' ∈ flattenBody f a :=
        (mem_flattenBody_iff f a _).2 ⟨Sum.inr a', hs, rfl⟩
      exact ⟨fun b heq => .more step (ih.1 b heq),
        fun a'' b heq tail => .more step (ih.2 a'' b heq tail)⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.runs_flatten_cases := Silmaril.Elgot.Part.runs_flatten_cases

private theorem runs_flatten_of_left (f : A → _root_.Part ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs f a (Sum.inl b)) : Runs (flattenBody f) a b :=
  (runs_flatten_cases f h).1 b rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.runs_flatten_of_left := Silmaril.Elgot.Part.runs_flatten_of_left

private theorem runs_flatten_append (f : A → _root_.Part ((B ⊕ A) ⊕ A))
    {a a' : A} {b : B} (h : Runs f a (Sum.inr a'))
    (tail : Runs (flattenBody f) a' b) : Runs (flattenBody f) a b :=
  (runs_flatten_cases f h).2 a' b rfl tail
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.runs_flatten_append := Silmaril.Elgot.Part.runs_flatten_append

private theorem runs_flatten_of_nested (f : A → _root_.Part ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs (iter f) a b) : Runs (flattenBody f) a b := by
  induction h with
  | done hs => exact runs_flatten_of_left f ((mem_iter_iff _ _ _).1 hs)
  | more hs hr ih => exact runs_flatten_append f ((mem_iter_iff _ _ _).1 hs) ih
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.runs_flatten_of_nested := Silmaril.Elgot.Part.runs_flatten_of_nested

private theorem runs_nested_of_flatten (f : A → _root_.Part ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs (flattenBody f) a b) : Runs (iter f) a b := by
  induction h with
  | @done a b hs =>
      obtain ⟨x, hx, heq⟩ : ∃ x, x ∈ f a ∧ flatten x = Sum.inl b :=
        (mem_flattenBody_iff f a _).1 hs
      match x, heq with
      | Sum.inl (Sum.inl _), rfl => exact .done ((mem_iter_iff _ _ _).2 (.done hx))
  | @more a a' b hs _ ih =>
      obtain ⟨x, hx, heq⟩ : ∃ x, x ∈ f a ∧ flatten x = Sum.inr a' :=
        (mem_flattenBody_iff f a _).1 hs
      match x, heq with
      | Sum.inl (Sum.inr _), rfl => exact .more ((mem_iter_iff _ _ _).2 (.done hx)) ih
      | Sum.inr _, rfl =>
          show Runs (iter f) a b
          cases ih with
          | done hi => exact .done ((mem_iter_iff _ _ _).2 (.more hx ((mem_iter_iff _ _ _).1 hi)))
          | more hi ht =>
              exact .more ((mem_iter_iff _ _ _).2 (.more hx ((mem_iter_iff _ _ _).1 hi))) ht
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.runs_nested_of_flatten := Silmaril.Elgot.Part.runs_nested_of_flatten

private theorem codiagonal (f : A → _root_.Part ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  apply _root_.Part.ext
  intro b
  rw [mem_iter_iff, mem_iter_iff]
  exact ⟨runs_flatten_of_nested f, runs_nested_of_flatten f⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.codiagonal := Silmaril.Elgot.Part.codiagonal

private theorem uniform_step (f : A → _root_.Part (B ⊕ A)) (g : C → _root_.Part (B ⊕ C))
    (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g))
    (a : A) (t : B ⊕ C) :
    t ∈ g (h a) ↔ ∃ s, s ∈ f a ∧ Sum.map id h s = t := by
  have square := congrFun comm a
  constructor
  · intro ht
    have hr : t ∈ (liftPure h >=> g) a := by
      rw [mem_kleisliRight_iff]
      exact ⟨h a, _root_.Part.mem_some _, ht⟩
    rw [← square, mem_kleisliRight_iff] at hr
    rcases hr with ⟨s, hs, ht⟩
    exact ⟨s, hs, (_root_.Part.mem_some_iff.mp ht).symm⟩
  · rintro ⟨s, hs, rfl⟩
    have hl : Sum.map id h s ∈ (f >=> liftPure (Sum.map id h)) a := by
      rw [mem_kleisliRight_iff]
      exact ⟨s, hs, _root_.Part.mem_some _⟩
    rw [square, mem_kleisliRight_iff] at hl
    rcases hl with ⟨c, hc, ht⟩
    have hcEq : c = h a := _root_.Part.mem_some_iff.mp hc
    subst c
    exact ht
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.uniform_step := Silmaril.Elgot.Part.uniform_step

private theorem runs_uniform_forward (f : A → _root_.Part (B ⊕ A))
    (g : C → _root_.Part (B ⊕ C)) (h : A → C)
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
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.runs_uniform_forward := Silmaril.Elgot.Part.runs_uniform_forward

private theorem runs_uniform_reverse (f : A → _root_.Part (B ⊕ A))
    (g : C → _root_.Part (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g))
    {c : C} {b : B} (hr : Runs g c b) : ∀ a, c = h a → Runs f a b := by
  induction hr with
  | @done c b ht =>
      intro a ha
      obtain ⟨s, hs, heq⟩ : ∃ s, s ∈ f a ∧ Sum.map id h s = Sum.inl b :=
        (uniform_step f g h comm a _).1 (ha ▸ ht)
      match s, heq with
      | Sum.inl _, rfl => exact .done hs
  | @more c c' b ht _ ih =>
      intro a ha
      obtain ⟨s, hs, heq⟩ : ∃ s, s ∈ f a ∧ Sum.map id h s = Sum.inr c' :=
        (uniform_step f g h comm a _).1 (ha ▸ ht)
      match s, heq with
      | Sum.inr a', heq =>
          have hc : h a' = c' := Sum.inr.inj heq
          exact .more hs (ih a' hc.symm)
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.runs_uniform_reverse := Silmaril.Elgot.Part.runs_uniform_reverse

private theorem uniformity (f : A → _root_.Part (B ⊕ A)) (g : C → _root_.Part (B ⊕ C))
    (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g)) :
    iter f = (liftPure h >=> iter g) := by
  funext a
  apply _root_.Part.ext
  intro b
  rw [mem_iter_iff, mem_kleisliRight_iff]
  constructor
  · intro hr
    exact ⟨h a, _root_.Part.mem_some _, (mem_iter_iff _ _ _).2 (runs_uniform_forward f g h comm hr)⟩
  · rintro ⟨c, hc, hb⟩
    have hcEq : c = h a := _root_.Part.mem_some_iff.mp hc
    exact runs_uniform_reverse f g h comm ((mem_iter_iff _ _ _).1 hb) a hcEq
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.uniformity := Silmaril.Elgot.Part.uniformity

noncomputable instance _root_.Silmaril.Proofs.Semantics.Elgot.Part.instLawfulElgotMonadPart : LawfulElgotMonad _root_.Part where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

section Examples

@[simp] private theorem iter_immediate (a : A) (b : B) :
    iter (fun _ : A ↦ _root_.Part.some (Sum.inl b)) a = _root_.Part.some b := by
  apply _root_.Part.ext
  intro b'
  rw [mem_iter_iff, _root_.Part.mem_some_iff]
  constructor
  · intro hr
    cases hr with
    | done hs => exact Sum.inl.inj (_root_.Part.mem_some_iff.mp hs)
    | more hs _ => cases _root_.Part.mem_some_iff.mp hs
  · intro hb
    subst b'
    exact .done (_root_.Part.mem_some _)
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.iter_immediate := Silmaril.Elgot.Part.iter_immediate

@[simp] private theorem iter_forever (a : A) :
    iter (B := B) (fun a : A ↦ _root_.Part.some (Sum.inr a)) a =
      (_root_.Part.none : _root_.Part B) := by
  apply _root_.Part.ext
  intro b
  rw [mem_iter_iff]
  constructor
  · intro hr
    induction hr with
    | done hs => cases _root_.Part.mem_some_iff.mp hs
    | more _ _ ih => exact ih
  · exact (_root_.Part.notMem_none b).elim
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.iter_forever := Silmaril.Elgot.Part.iter_forever

end Examples

end Part

end Silmaril.Elgot
