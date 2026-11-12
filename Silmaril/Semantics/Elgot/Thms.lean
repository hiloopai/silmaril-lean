module

public import Silmaril.Semantics.Elgot.Defs
import Silmaril.Proofs.Semantics.Elgot.Basic
import Silmaril.Proofs.Semantics.Elgot.Iteration.Bind
import Silmaril.Proofs.Semantics.Elgot.Iteration.MonadMap
import Silmaril.Proofs.Semantics.Elgot.Identity
import Silmaril.Proofs.Semantics.Elgot.Transport

/-!
# Elgot

Source: the thesis [imbrem/thesis](https://github.com/imbrem/thesis) at `69a8126`, Denotational Semantics,
§Freyd–Elgot Categories: Conway iteration, uniformity and strong Elgot structure.
The mapping to the thesis is by content; the source modules do not cite it.

Theorems about `Silmaril.Semantics.Elgot.Defs`. Proofs longer than a few lines live
under `Silmaril.Proofs.Semantics.Elgot` and are only pointed at from here.
-/

public section

section

/-! ## Complete Elgot monads on types -/

namespace Silmaril.Elgot

universe u v

namespace Part

variable {A B C : Type u}

theorem Runs.unique {A B : Type u} {f : A → _root_.Part (B ⊕ A)}
    {a : A} {b c : B} (hb : Runs f a b) (hc : Runs f a c) : b = c :=
  Silmaril.Proofs.Semantics.Elgot.Part.Runs.unique hb hc

theorem mem_run_iff {A B : Type u} (f : A → _root_.Part (B ⊕ A)) (a : A) (b : B) :
    b ∈ run f a ↔ Runs f a b :=
  Silmaril.Proofs.Semantics.Elgot.Part.mem_run_iff f a b

theorem mem_iter_iff {A B : Type u} (f : A → _root_.Part (B ⊕ A)) (a : A) (b : B) :
    b ∈ iter f a ↔ Runs f a b :=
  Silmaril.Proofs.Semantics.Elgot.Part.mem_iter_iff f a b

theorem mem_kleisliRight_iff (f : A → _root_.Part B) (g : B → _root_.Part C) (a : A) (c : C) :
    c ∈ (f >=> g) a ↔ ∃ b, b ∈ f a ∧ c ∈ g b :=
  Silmaril.Proofs.Semantics.Elgot.Part.mem_kleisliRight_iff f g a c

theorem mem_mapReturn_iff (f : A → _root_.Part (B ⊕ A)) (g : B → _root_.Part C)
    (a : A) (s : C ⊕ A) :
    s ∈ mapReturn f g a ↔
      (∃ b c, Sum.inl b ∈ f a ∧ c ∈ g b ∧ s = Sum.inl c) ∨
      (∃ a', Sum.inr a' ∈ f a ∧ s = Sum.inr a') :=
  Silmaril.Proofs.Semantics.Elgot.Part.mem_mapReturn_iff f g a s

theorem fixpoint (f : A → _root_.Part (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) :=
  Silmaril.Proofs.Semantics.Elgot.Part.fixpoint f

theorem runs_mapReturn_iff (f : A → _root_.Part (B ⊕ A)) (g : B → _root_.Part C) (a : A) (c : C) :
    Runs (mapReturn f g) a c ↔ ∃ b, Runs f a b ∧ c ∈ g b :=
  Silmaril.Proofs.Semantics.Elgot.Part.runs_mapReturn_iff f g a c

theorem naturality (f : A → _root_.Part (B ⊕ A)) (g : B → _root_.Part C) :
    (iter f >=> g) = iter (mapReturn f g) :=
  Silmaril.Proofs.Semantics.Elgot.Part.naturality f g

theorem mem_flattenBody_iff (f : A → _root_.Part ((B ⊕ A) ⊕ A)) (a : A) (s : B ⊕ A) :
    s ∈ flattenBody f a ↔ ∃ x, x ∈ f a ∧ flatten x = s :=
  Silmaril.Proofs.Semantics.Elgot.Part.mem_flattenBody_iff f a s

theorem runs_flatten_cases (f : A → _root_.Part ((B ⊕ A) ⊕ A))
    {a : A} {s : B ⊕ A} (h : Runs f a s) :
    (∀ b, s = Sum.inl b → Runs (flattenBody f) a b) ∧
    (∀ a' b, s = Sum.inr a' → Runs (flattenBody f) a' b →
      Runs (flattenBody f) a b) :=
  Silmaril.Proofs.Semantics.Elgot.Part.runs_flatten_cases f h

theorem runs_flatten_of_left (f : A → _root_.Part ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs f a (Sum.inl b)) : Runs (flattenBody f) a b :=
  Silmaril.Proofs.Semantics.Elgot.Part.runs_flatten_of_left f h

theorem runs_flatten_append (f : A → _root_.Part ((B ⊕ A) ⊕ A))
    {a a' : A} {b : B} (h : Runs f a (Sum.inr a'))
    (tail : Runs (flattenBody f) a' b) : Runs (flattenBody f) a b :=
  Silmaril.Proofs.Semantics.Elgot.Part.runs_flatten_append f h tail

theorem runs_flatten_of_nested (f : A → _root_.Part ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs (iter f) a b) : Runs (flattenBody f) a b :=
  Silmaril.Proofs.Semantics.Elgot.Part.runs_flatten_of_nested f h

theorem runs_nested_of_flatten (f : A → _root_.Part ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs (flattenBody f) a b) : Runs (iter f) a b :=
  Silmaril.Proofs.Semantics.Elgot.Part.runs_nested_of_flatten f h

theorem codiagonal (f : A → _root_.Part ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) :=
  Silmaril.Proofs.Semantics.Elgot.Part.codiagonal f

theorem uniform_step (f : A → _root_.Part (B ⊕ A)) (g : C → _root_.Part (B ⊕ C))
    (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g))
    (a : A) (t : B ⊕ C) :
    t ∈ g (h a) ↔ ∃ s, s ∈ f a ∧ Sum.map id h s = t :=
  Silmaril.Proofs.Semantics.Elgot.Part.uniform_step f g h comm a t

theorem runs_uniform_forward (f : A → _root_.Part (B ⊕ A))
    (g : C → _root_.Part (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g))
    {a : A} {b : B} (hr : Runs f a b) : Runs g (h a) b :=
  Silmaril.Proofs.Semantics.Elgot.Part.runs_uniform_forward f g h comm hr

theorem runs_uniform_reverse (f : A → _root_.Part (B ⊕ A))
    (g : C → _root_.Part (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g))
    {c : C} {b : B} (hr : Runs g c b) : ∀ a, c = h a → Runs f a b :=
  Silmaril.Proofs.Semantics.Elgot.Part.runs_uniform_reverse f g h comm hr

theorem uniformity (f : A → _root_.Part (B ⊕ A)) (g : C → _root_.Part (B ⊕ C))
    (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g)) :
    iter f = (liftPure h >=> iter g) :=
  Silmaril.Proofs.Semantics.Elgot.Part.uniformity f g h comm

noncomputable instance : LawfulElgotMonad _root_.Part :=
  Silmaril.Proofs.Semantics.Elgot.Part.instLawfulElgotMonadPart

section Examples

@[simp] theorem iter_immediate (a : A) (b : B) :
    iter (fun _ : A ↦ _root_.Part.some (Sum.inl b)) a = _root_.Part.some b :=
  Silmaril.Proofs.Semantics.Elgot.Part.iter_immediate a b

@[simp] theorem iter_forever (a : A) :
    iter (B := B) (fun a : A ↦ _root_.Part.some (Sum.inr a)) a =
      (_root_.Part.none : _root_.Part B) :=
  Silmaril.Proofs.Semantics.Elgot.Part.iter_forever a

end Examples

end Part

end Silmaril.Elgot

end

section

/-! ## Iteration.Bind -/

namespace Silmaril.Elgot

universe u v

variable {m : Type u → Type v} [Monad m]

variable {A B : Type u}

variable [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

/-- The second phase immediately returns the continuation's result. -/
@[simp] theorem iter_bindBody_inr (x : m A) (f : A → m B) (a : A) :
    iter (bindBody x f) (.inr a) = f a :=
  Silmaril.Proofs.Semantics.Elgot.iter_bindBody_inr x f a

/-- Bind is determined by pure mapping and iteration. -/
theorem bind_eq_iter (x : m A) (f : A → m B) :
    (x >>= f) = iter (bindBody x f) (.inl PUnit.unit) :=
  Silmaril.Proofs.Semantics.Elgot.bind_eq_iter x f

end Silmaril.Elgot

end

section

/-! ## Iteration.MonadMap -/

namespace Silmaril.Elgot

universe u v w

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

variable {n : Type u → Type w} [Monad n] [LawfulMonad n] [Iterate n] [LawfulElgotMonad n]

/-- A natural transformation that preserves iteration also preserves bind. -/
theorem map_bind_of_map_iter (map : {A : Type u} → m A → n A)
    (map_map : ∀ {A B : Type u} (x : m A) (f : A → B),
      map (x >>= pure ∘ f) = (map x >>= pure ∘ f))
    (map_iter : ∀ {A B : Type u} (f : A → m (B ⊕ A)) (a : A),
      map (iter f a) = iter (fun a => map (f a)) a)
    {A B : Type u} (x : m A) (f : A → m B) :
    map (x >>= f) = (map x >>= fun a => map (f a)) :=
  Silmaril.Proofs.Semantics.Elgot.map_bind_of_map_iter map map_map map_iter x f

end Silmaril.Elgot

end

section

/-! ## Identity -/

namespace Silmaril.Elgot

universe u

/-- Even an iteration operator without laws cannot exist on total functions. -/
theorem not_nonempty_iterate_id : ¬ Nonempty (Iterate (Id : Type u → Type u)) :=
  Silmaril.Proofs.Semantics.Elgot.not_nonempty_iterate_id

end Silmaril.Elgot

end

section

/-! ## Transport of Elgot laws -/

namespace Silmaril.Elgot

universe u

variable {m n : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m]
  [Monad n] [LawfulMonad n] [Iterate n]

namespace Embedding

variable (e : Embedding m n)

@[simp] theorem map_map {A B : Type u} (f : A → B) (x : m A) :
    e.map (f <$> x) = f <$> e.map x :=
  Silmaril.Proofs.Semantics.Elgot.Embedding.map_map e f x

@[simp] theorem map_mapReturn {A B C : Type u}
    (f : A → m (B ⊕ A)) (g : B → m C) (a : A) :
    e.map (mapReturn f g a) = mapReturn (fun a => e.map (f a)) (fun b => e.map (g b)) a :=
  Silmaril.Proofs.Semantics.Elgot.Embedding.map_mapReturn e f g a

@[simp] theorem map_flattenBody {A B : Type u} (f : A → m ((B ⊕ A) ⊕ A)) (a : A) :
    e.map (flattenBody f a) = flattenBody (fun a => e.map (f a)) a :=
  Silmaril.Proofs.Semantics.Elgot.Embedding.map_flattenBody e f a

include e in
/-- All four Elgot equations descend along a faithful iteration-preserving monad map. -/
theorem lawful [LawfulElgotMonad n] : LawfulElgotMonad m :=
  Silmaril.Proofs.Semantics.Elgot.Embedding.lawful e

end Embedding

end Silmaril.Elgot

end
