module

public import Silmaril.Semantics.ElgotMonads.Defs
import Silmaril.Proofs.Semantics.ElgotMonads.Partiality
import Silmaril.Proofs.Semantics.ElgotMonads.ExceptT
import Silmaril.Proofs.Semantics.ElgotMonads.ReaderT
import Silmaril.Proofs.Semantics.ElgotMonads.Set
import Silmaril.Proofs.Semantics.ElgotMonads.StateT
import Silmaril.Proofs.Semantics.ElgotMonads.WriterT

/-!
# ElgotMonads

Source: the thesis [imbrem/thesis](https://github.com/imbrem/thesis) at `69a8126`, Concrete Models,
§Monads and Monad Transformers (mapped by content).

Theorems about `Silmaril.Semantics.ElgotMonads.Defs`. Proofs longer than a few lines live
under `Silmaril.Proofs.Semantics.ElgotMonads` and are only pointed at from here.
-/

public section

section

/-! ## Partiality and finite approximations -/

universe u

namespace Silmaril.Elgot.Part

variable {A B : Type u}

theorem runs_of_mem_runFor {f : A → _root_.Part (B ⊕ A)} {fuel : Nat} {a : A} {b : B}
    (h : b ∈ runFor f fuel a) : Runs f a b :=
  Silmaril.Proofs.Semantics.Elgot.Part.runs_of_mem_runFor h

theorem Runs.exists_fuel {f : A → _root_.Part (B ⊕ A)} {a : A} {b : B}
    (h : Runs f a b) : ∃ fuel, b ∈ runFor f fuel a :=
  Silmaril.Proofs.Semantics.Elgot.Part.Runs.exists_fuel h

/-- Unbounded partial iteration is exactly the union of its finite approximations. -/
theorem mem_iter_iff_exists_fuel (f : A → _root_.Part (B ⊕ A)) (a : A) (b : B) :
    b ∈ iter f a ↔ ∃ fuel, b ∈ runFor f fuel a := by
  rw [mem_iter_iff]
  exact ⟨Runs.exists_fuel, fun ⟨_, h⟩ => runs_of_mem_runFor h⟩

theorem runFor_mono_succ (f : A → _root_.Part (B ⊕ A)) (fuel : Nat) (a : A) (b : B)
    (h : b ∈ runFor f fuel a) : b ∈ runFor f (fuel + 1) a :=
  Silmaril.Proofs.Semantics.Elgot.Part.runFor_mono_succ f fuel a b h

theorem runFor_mono (f : A → _root_.Part (B ⊕ A)) {n k : Nat} (h : n ≤ k)
    (a : A) (b : B) : b ∈ runFor f n a → b ∈ runFor f k a :=
  Silmaril.Proofs.Semantics.Elgot.Part.runFor_mono f h a b

/-- The Elgot solution is least among predicates closed under return and looping. -/
theorem iter_induction (f : A → _root_.Part (B ⊕ A)) (P : A → B → Prop)
    (done : ∀ a b, Sum.inl b ∈ f a → P a b)
    (more : ∀ a a' b, Sum.inr a' ∈ f a → P a' b → P a b)
    {a : A} {b : B} (h : b ∈ iter f a) : P a b :=
  Silmaril.Proofs.Semantics.Elgot.Part.iter_induction f P done more h

end Silmaril.Elgot.Part

end

section

/-! ## Complete Elgot iteration with errors -/

namespace Silmaril.Elgot.ExceptT

universe u

variable {m : Type u → Type u} [Monad m] {ε A B C : Type u}

@[simp] theorem run_iter [Iterate m] (f : A → _root_.ExceptT ε m (B ⊕ A)) (a : A) :
    (iter f a).run = iter (body f) a :=
  Silmaril.Proofs.Semantics.Elgot.ExceptT.run_iter f a

variable [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

theorem fixpoint (f : A → _root_.ExceptT ε m (B ⊕ A)) :
    iter f = fun a => f a >>= Sum.elim pure (iter f) :=
  Silmaril.Proofs.Semantics.Elgot.ExceptT.fixpoint f

omit [Iterate m] [LawfulElgotMonad m] in
theorem body_mapReturn (f : A → _root_.ExceptT ε m (B ⊕ A))
    (g : B → _root_.ExceptT ε m C) :
    body (mapReturn f g) = mapReturn (body f) (extend g) :=
  Silmaril.Proofs.Semantics.Elgot.ExceptT.body_mapReturn f g

theorem naturality (f : A → _root_.ExceptT ε m (B ⊕ A))
    (g : B → _root_.ExceptT ε m C) :
    (iter f >=> g) = iter (mapReturn f g) :=
  Silmaril.Proofs.Semantics.Elgot.ExceptT.naturality f g

theorem body_iter (f : A → _root_.ExceptT ε m ((B ⊕ A) ⊕ A)) :
    body (iter f) = iter (mapReturn (body f) (pure ∘ distribute)) :=
  Silmaril.Proofs.Semantics.Elgot.ExceptT.body_iter f

omit [Iterate m] [LawfulElgotMonad m] in
theorem body_flatten (f : A → _root_.ExceptT ε m ((B ⊕ A) ⊕ A)) :
    flattenBody (mapReturn (body f) (pure ∘ distribute)) = body (flattenBody f) :=
  Silmaril.Proofs.Semantics.Elgot.ExceptT.body_flatten f

theorem codiagonal (f : A → _root_.ExceptT ε m ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) :=
  Silmaril.Proofs.Semantics.Elgot.ExceptT.codiagonal f

theorem uniformity (f : A → _root_.ExceptT ε m (B ⊕ A))
    (g : C → _root_.ExceptT ε m (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g)) :
    iter f = (liftPure h >=> iter g) :=
  Silmaril.Proofs.Semantics.Elgot.ExceptT.uniformity f g h comm

instance : LawfulElgotMonad (_root_.ExceptT ε m) :=
  Silmaril.Proofs.Semantics.Elgot.ExceptT.instLawfulElgotMonadExceptT

end Silmaril.Elgot.ExceptT

end

section

/-! ## Complete Elgot iteration with optional failure -/

namespace Silmaril.Elgot.OptionT

universe u

variable {m : Type u → Type u} [Monad m] {A B : Type u}

variable [LawfulMonad m]

variable [Iterate m] [LawfulElgotMonad m]

instance : LawfulElgotMonad (_root_.OptionT m) := embedding.lawful

end Silmaril.Elgot.OptionT

end

section

/-! ## ReaderT -/

namespace Silmaril.Elgot.ReaderT

universe u

variable {m : Type u → Type u} [Monad m] {ρ A B C : Type u}

omit [Monad m] in
@[simp] theorem run_iter [Iterate m] (f : A → _root_.ReaderT ρ m (B ⊕ A)) (a : A) (r : ρ) :
    (iter f a).run r = iter (fun a => (f a).run r) a :=
  Silmaril.Proofs.Semantics.Elgot.ReaderT.run_iter f a r

variable [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

theorem fixpoint (f : A → _root_.ReaderT ρ m (B ⊕ A)) :
    iter f = fun a => f a >>= Sum.elim pure (iter f) :=
  Silmaril.Proofs.Semantics.Elgot.ReaderT.fixpoint f

omit [LawfulMonad m] [Iterate m] [LawfulElgotMonad m] in
theorem run_mapReturn (f : A → _root_.ReaderT ρ m (B ⊕ A))
    (g : B → _root_.ReaderT ρ m C) (r : ρ) :
    (fun a => (mapReturn f g a).run r) =
      mapReturn (fun a => (f a).run r) (fun b => (g b).run r) :=
  Silmaril.Proofs.Semantics.Elgot.ReaderT.run_mapReturn f g r

theorem naturality (f : A → _root_.ReaderT ρ m (B ⊕ A))
    (g : B → _root_.ReaderT ρ m C) :
    (iter f >=> g) = iter (mapReturn f g) :=
  Silmaril.Proofs.Semantics.Elgot.ReaderT.naturality f g

theorem codiagonal (f : A → _root_.ReaderT ρ m ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) :=
  Silmaril.Proofs.Semantics.Elgot.ReaderT.codiagonal f

theorem uniformity (f : A → _root_.ReaderT ρ m (B ⊕ A))
    (g : C → _root_.ReaderT ρ m (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g)) :
    iter f = (liftPure h >=> iter g) :=
  Silmaril.Proofs.Semantics.Elgot.ReaderT.uniformity f g h comm

instance : LawfulElgotMonad (_root_.ReaderT ρ m) :=
  Silmaril.Proofs.Semantics.Elgot.ReaderT.instLawfulElgotMonadReaderT

end Silmaril.Elgot.ReaderT

end

section

/-! ## Nondeterministic complete Elgot iteration -/

universe u

namespace Silmaril.Elgot.Nondet

theorem mem_pure_iff {A : Type u} {a b : A} :
    a ∈ₘ (pure b : _root_.SetM A) ↔ a = b :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.mem_pure_iff

theorem mem_pure {A : Type u} (a : A) : a ∈ₘ (pure a : _root_.SetM A) :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.mem_pure a

theorem mem_bind_iff {A B : Type u} {s : _root_.SetM A} {f : A → _root_.SetM B} {b : B} :
    b ∈ₘ (s >>= f) ↔ ∃ a, a ∈ₘ s ∧ b ∈ₘ f a :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.mem_bind_iff

theorem ext {A : Type u} {s t : _root_.SetM A}
    (h : ∀ a, a ∈ₘ s ↔ a ∈ₘ t) : s = t :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.ext h

variable {A B C : Type u}

theorem mem_iter_iff {A B : Type u} (f : A → _root_.SetM (B ⊕ A)) (a : A) (b : B) :
    b ∈ₘ iter f a ↔ Runs f a b :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.mem_iter_iff f a b

theorem mem_kleisliRight_iff (f : A → _root_.SetM B) (g : B → _root_.SetM C) (a : A) (c : C) :
    c ∈ₘ (f >=> g) a ↔ ∃ b, b ∈ₘ f a ∧ c ∈ₘ g b :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.mem_kleisliRight_iff f g a c

theorem mem_mapReturn_iff (f : A → _root_.SetM (B ⊕ A)) (g : B → _root_.SetM C)
    (a : A) (s : C ⊕ A) :
    s ∈ₘ mapReturn f g a ↔
      (∃ b c, Sum.inl b ∈ₘ f a ∧ c ∈ₘ g b ∧ s = Sum.inl c) ∨
      (∃ a', Sum.inr a' ∈ₘ f a ∧ s = Sum.inr a') :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.mem_mapReturn_iff f g a s

theorem fixpoint (f : A → _root_.SetM (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.fixpoint f

theorem runs_mapReturn_iff (f : A → _root_.SetM (B ⊕ A)) (g : B → _root_.SetM C) (a : A) (c : C) :
    Runs (mapReturn f g) a c ↔ ∃ b, Runs f a b ∧ c ∈ₘ g b :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.runs_mapReturn_iff f g a c

theorem naturality (f : A → _root_.SetM (B ⊕ A)) (g : B → _root_.SetM C) :
    (iter f >=> g) = iter (mapReturn f g) :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.naturality f g

theorem mem_flattenBody_iff (f : A → _root_.SetM ((B ⊕ A) ⊕ A)) (a : A) (s : B ⊕ A) :
    s ∈ₘ flattenBody f a ↔ ∃ x, x ∈ₘ f a ∧ flatten x = s :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.mem_flattenBody_iff f a s

theorem runs_flatten_cases (f : A → _root_.SetM ((B ⊕ A) ⊕ A))
    {a : A} {s : B ⊕ A} (h : Runs f a s) :
    (∀ b, s = Sum.inl b → Runs (flattenBody f) a b) ∧
    (∀ a' b, s = Sum.inr a' → Runs (flattenBody f) a' b →
      Runs (flattenBody f) a b) :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.runs_flatten_cases f h

theorem runs_flatten_of_left (f : A → _root_.SetM ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs f a (Sum.inl b)) : Runs (flattenBody f) a b :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.runs_flatten_of_left f h

theorem runs_flatten_append (f : A → _root_.SetM ((B ⊕ A) ⊕ A))
    {a a' : A} {b : B} (h : Runs f a (Sum.inr a'))
    (tail : Runs (flattenBody f) a' b) : Runs (flattenBody f) a b :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.runs_flatten_append f h tail

theorem runs_flatten_of_nested (f : A → _root_.SetM ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs (iter f) a b) : Runs (flattenBody f) a b :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.runs_flatten_of_nested f h

theorem runs_nested_of_flatten (f : A → _root_.SetM ((B ⊕ A) ⊕ A))
    {a : A} {b : B} (h : Runs (flattenBody f) a b) : Runs (iter f) a b :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.runs_nested_of_flatten f h

theorem codiagonal (f : A → _root_.SetM ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.codiagonal f

theorem uniform_step (f : A → _root_.SetM (B ⊕ A)) (g : C → _root_.SetM (B ⊕ C))
    (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g))
    (a : A) (t : B ⊕ C) :
    t ∈ₘ g (h a) ↔ ∃ s, s ∈ₘ f a ∧ Sum.map id h s = t :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.uniform_step f g h comm a t

theorem runs_uniform_forward (f : A → _root_.SetM (B ⊕ A))
    (g : C → _root_.SetM (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g))
    {a : A} {b : B} (hr : Runs f a b) : Runs g (h a) b :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.runs_uniform_forward f g h comm hr

theorem runs_uniform_reverse (f : A → _root_.SetM (B ⊕ A))
    (g : C → _root_.SetM (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g))
    {c : C} {b : B} (hr : Runs g c b) : ∀ a, c = h a → Runs f a b :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.runs_uniform_reverse f g h comm hr

theorem uniformity (f : A → _root_.SetM (B ⊕ A)) (g : C → _root_.SetM (B ⊕ C))
    (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g)) :
    iter f = (liftPure h >=> iter g) :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.uniformity f g h comm

instance : LawfulElgotMonad _root_.SetM :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.instLawfulElgotMonadSetM

/-- An iteration with no return edge has no finite successful outcome. -/
theorem iter_no_return (f : A → _root_.SetM (B ⊕ A))
    (h : ∀ a b, ¬ Sum.inl b ∈ₘ f a) (a : A) : iter f a = (∅ : Set B) :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.iter_no_return f h a

/-- Nondeterministic alternatives are retained, rather than choosing one run. -/
theorem iter_two_returns (a : A) (left right : B) :
    iter (m := _root_.SetM) (fun _ : A => ({Sum.inl left, Sum.inl right} : Set (B ⊕ A))) a =
      ({left, right} : Set B) :=
  Silmaril.Proofs.Semantics.Elgot.Nondet.iter_two_returns a left right

end Silmaril.Elgot.Nondet

end

section

/-! ## Complete Elgot iteration through mutable state -/

namespace Silmaril.Elgot.StateT

universe u v

variable {m : Type u → Type v} [Monad m] {σ A B C : Type u}

@[simp] theorem run_iter [Iterate m] (f : A → _root_.StateT σ m (B ⊕ A)) (a : A) (s : σ) :
    (iter f a).run s = iter (body f) (a, s) :=
  Silmaril.Proofs.Semantics.Elgot.StateT.run_iter f a s

variable [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

theorem fixpoint (f : A → _root_.StateT σ m (B ⊕ A)) :
    iter f = fun a => f a >>= Sum.elim pure (iter f) :=
  Silmaril.Proofs.Semantics.Elgot.StateT.fixpoint f

omit [Iterate m] [LawfulElgotMonad m] in
theorem body_mapReturn (f : A → _root_.StateT σ m (B ⊕ A))
    (g : B → _root_.StateT σ m C) :
    body (mapReturn f g) = mapReturn (body f) (fun p => (g p.1).run p.2) :=
  Silmaril.Proofs.Semantics.Elgot.StateT.body_mapReturn f g

theorem naturality (f : A → _root_.StateT σ m (B ⊕ A))
    (g : B → _root_.StateT σ m C) :
    (iter f >=> g) = iter (mapReturn f g) :=
  Silmaril.Proofs.Semantics.Elgot.StateT.naturality f g

theorem body_iter (f : A → _root_.StateT σ m ((B ⊕ A) ⊕ A)) :
    body (iter f) = iter (mapReturn (body f) (pure ∘ distribute)) :=
  Silmaril.Proofs.Semantics.Elgot.StateT.body_iter f

omit [Iterate m] [LawfulElgotMonad m] in
theorem body_flatten (f : A → _root_.StateT σ m ((B ⊕ A) ⊕ A)) :
    flattenBody (mapReturn (body f) (pure ∘ distribute)) = body (flattenBody f) :=
  Silmaril.Proofs.Semantics.Elgot.StateT.body_flatten f

theorem codiagonal (f : A → _root_.StateT σ m ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) :=
  Silmaril.Proofs.Semantics.Elgot.StateT.codiagonal f

theorem distribute_map (h : A → C) (p : (B ⊕ A) × σ) :
    Sum.map id (Prod.map h id) (distribute p) = distribute (Sum.map id h p.1, p.2) :=
  Silmaril.Proofs.Semantics.Elgot.StateT.distribute_map h p

theorem uniformity (f : A → _root_.StateT σ m (B ⊕ A))
    (g : C → _root_.StateT σ m (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g)) :
    iter f = (liftPure h >=> iter g) :=
  Silmaril.Proofs.Semantics.Elgot.StateT.uniformity f g h comm

instance : LawfulElgotMonad (_root_.StateT σ m) :=
  Silmaril.Proofs.Semantics.Elgot.StateT.instLawfulElgotMonadStateT

end Silmaril.Elgot.StateT

end

section

/-! ## Writer iteration over an Elgot monad -/

namespace Silmaril.Elgot.WriterT

universe u

variable {m : Type u → Type u} [Monad m] [LawfulMonad m]
  {W A B : Type u} [Monoid W]

omit [LawfulMonad m] in
@[simp] theorem run_iter [Iterate m] (f : A → _root_.WriterT W m (B ⊕ A)) (a : A) :
    (iter f a).run = iter (body f) (a, 1) :=
  Silmaril.Proofs.Semantics.Elgot.WriterT.run_iter f a

variable [Iterate m] [LawfulElgotMonad m]

instance : LawfulElgotMonad (_root_.WriterT W m) := stateEmbedding.lawful

section Examples

theorem twoSteps_run {W : Type} [Monoid W] (first second : W) :
    (iter (twoSteps first second) false).run = _root_.Part.some (PUnit.unit, first * second) :=
  Silmaril.Proofs.Semantics.Elgot.WriterT.twoSteps_run first second

/-- Ordinary partial writers lose their entire output when iteration never returns. -/
theorem forever_run (w : W) (a : A) :
    (iter (B := B) (fun a : A =>
      _root_.WriterT.mk (_root_.Part.some (Sum.inr a, w))) a).run = _root_.Part.none :=
  Silmaril.Proofs.Semantics.Elgot.WriterT.forever_run w a

end Examples

end Silmaril.Elgot.WriterT

end
