module

public import Mathlib.Data.Sum.Basic
public import Mathlib.Logic.Small.Basic
public import Mathlib.Logic.Equiv.Defs
public import Silmaril.Semantics.Elgot.Thms
public import Silmaril.Semantics.ITree.Thms

/-!
# ITreeInterpret

Source: interpretation of interaction trees into complete Elgot monads, after
Concrete Models, §Trace Models of the thesis [imbrem/thesis](https://github.com/imbrem/thesis) at `69a8126`.

-/

@[expose] public section

section

/-! ## Interpreting visible events in a complete Elgot monad

Only the iteration state is shrunk. The public tree representation and event
response types are unchanged, and the target computation universe is arbitrary.
Silent divergence is an explicit pure backedge, not an assumed handler effect.
-/

namespace Silmaril.Elgot.ITree

universe u v

abbrev Handler (E : Type u → Type u) (m : Type u → Type v) :=
  {R : Type u} → E R → m R

/-- Expose one event and return its response. -/
def trigger {E : Type u → Type u} {R : Type u} (e : E R) : Tree E R := vis e ret

namespace Interpret

variable {E : Type u → Type u} {m : Type u → Type v} [Monad m]

/-- One visible transition; an undefined observation silently repeats its state. -/
noncomputable def stepTree {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) (t : Tree E A) : m (A ⊕ Shrink.{u} (Tree E A)) := by
  classical
  exact if h : (out t).Dom then
    match (out t).get h with
    | .ret a => pure (.inl a)
    | .vis e next => handler e >>= fun r => pure (.inr (equivShrink _ (next r)))
  else pure (.inr (equivShrink _ t))

noncomputable def step {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) (state : Shrink.{u} (Tree E A)) :
    m (A ⊕ Shrink.{u} (Tree E A)) := stepTree (E := E) (m := m) handler ((equivShrink _).symm state)

@[simp] theorem step_shrink {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) (t : Tree E A) :
    step (E := E) (m := m) handler (equivShrink _ t) = stepTree (E := E) (m := m) handler t := by simp [step]

@[simp] theorem stepTree_ret {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) (a : A) : stepTree (E := E) (m := m) handler (ret a) = pure (.inl a) := by
  simp [stepTree, out_ret]

@[simp] theorem stepTree_vis {A : Type u} [Small.{u} (Tree E A)] {R : Type u}
    (handler : Handler E m) (e : E R) (next : R → Tree E A) :
    stepTree (E := E) (m := m) handler (vis e next) =
      handler e >>= fun r => pure (.inr (equivShrink _ (next r))) := by
  simp [stepTree, out_vis]

@[simp] theorem stepTree_diverge {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) : stepTree (E := E) (m := m) handler (diverge : Tree E A) =
      pure (.inr (equivShrink _ diverge)) := by simp [stepTree, out_diverge]

/-- Interpret a tree by complete iteration over a small equivalent state space. -/
noncomputable def fold [Iterate m] {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) (t : Tree E A) : m A := iter (step (E := E) (m := m) handler) (equivShrink _ t)

variable [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

theorem fold_unfold {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) (t : Tree E A) :
    fold (E := E) (m := m) handler t = stepTree (E := E) (m := m) handler t >>=
      Sum.elim pure (fun state => fold (E := E) (m := m) handler ((equivShrink _).symm state)) := by
  rw [fold, congrFun (LawfulElgotMonad.fixpoint (step (E := E) (m := m) handler)), step_shrink]
  congr 1
  funext result
  cases result <;> simp [fold]

@[simp] theorem fold_ret {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) (a : A) : fold (E := E) (m := m) handler (ret a) = pure a := by
  rw [fold_unfold]
  simp

@[simp] theorem fold_vis {A : Type u} [Small.{u} (Tree E A)] {R : Type u}
    (handler : Handler E m) (e : E R) (next : R → Tree E A) :
    fold (E := E) (m := m) handler (vis e next) = handler e >>= fun r => fold (E := E) (m := m) handler (next r) := by
  rw [fold_unfold]
  simp

@[simp] theorem fold_trigger {R : Type u} [Small.{u} (Tree E R)]
    (handler : Handler E m) (e : E R) : fold (E := E) (m := m) handler (trigger e) = handler e := by
  simp [trigger]

end Interpret

end Silmaril.Elgot.ITree

end

section

/-! ## Uniqueness of iteration-preserving event interpretations

The candidate morphisms preserve pure values, bind, requests, and complete
iteration. Reconstructing every tree from its visible transitions forces any
such candidate to equal the explicitly defined fold. Constructing a candidate
for that fold additionally requires proving its bind and iteration laws; this
module does not assume those laws for the fold or assert existence.
-/

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {E : Type u → Type u} {m : Type u → Type v} [Monad m] [Iterate m]

/-- A complete-iteration-preserving monad interpretation with the specified
meaning of every visible event. -/
structure Hom (handler : Handler E m) where
  map {A : Type u} : Tree E A → m A
  map_pure {A : Type u} (a : A) : map (pure a) = pure a
  map_bind {A B : Type u} (t : Tree E A) (k : A → Tree E B) :
    map (t >>= k) = map t >>= fun a => map (k a)
  map_trigger {R : Type u} (event : E R) : map (trigger event) = handler event
  map_iter {A B : Type u} (body : A → Tree E (B ⊕ A)) (a : A) :
    map (iter body a) = iter (fun state => map (body state)) a

namespace Hom

variable {handler : Handler E m} (f : Hom (E := E) (m := m) handler)

end Hom

end Silmaril.Elgot.ITree.Interpret

end

section

/-! ## Interpreting partial computations in a complete Elgot monad

Classical partiality has a canonical interpretation: successful values are
pure, and undefined values take a silent self-loop. Its compatibility with
iteration follows from the Elgot laws, including on infinite silent paths.
-/

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

def bottom {A : Type u} : m A :=
  iter (fun _ : PUnit.{u + 1} => pure (.inr PUnit.unit : A ⊕ PUnit)) PUnit.unit

theorem iter_of_pure_self {A B : Type u} (f : A → m (B ⊕ A)) (a : A)
    (loop : f a = pure (.inr a)) : iter f a = bottom := by
  let point : PUnit.{u + 1} → A := fun _ => a
  have square :
      ((fun _ : PUnit.{u + 1} => (pure (.inr PUnit.unit) : m (B ⊕ PUnit))) >=>
        liftPure (Sum.map id point)) = (liftPure point >=> f) := by
    funext x
    simp [Bind.kleisliRight, liftPure, point, loop]
  have h := congrFun (LawfulElgotMonad.uniformity _ f point square) PUnit.unit
  simpa only [bottom, Bind.kleisliRight, liftPure, point, Function.comp_apply, pure_bind] using h.symm

@[simp] theorem bottom_bind {A B : Type u} (k : A → m B) :
    (bottom >>= k) = (bottom : m B) := by
  have h := congrFun (LawfulElgotMonad.naturality
    (fun _ : PUnit.{u + 1} => (pure (.inr PUnit.unit) : m (A ⊕ PUnit))) k) PUnit.unit
  have bodies : mapReturn
      (fun _ : PUnit.{u + 1} => (pure (.inr PUnit.unit) : m (A ⊕ PUnit))) k =
      fun _ => (pure (.inr PUnit.unit) : m (B ⊕ PUnit)) := by
    funext x
    simp [mapReturn]
  rw [bodies] at h
  exact h

noncomputable def liftPart {A : Type u} (x : _root_.Part A) : m A := by
  classical
  exact if h : x.Dom then pure (x.get h) else bottom

omit [LawfulMonad m] [LawfulElgotMonad m] in
@[simp] theorem liftPart_some {A : Type u} (a : A) :
    liftPart (m := m) (_root_.Part.some a) = pure a := by simp [liftPart]

omit [LawfulMonad m] [LawfulElgotMonad m] in
@[simp] theorem liftPart_none {A : Type u} :
    liftPart (m := m) (_root_.Part.none : _root_.Part A) = bottom := by simp [liftPart]

private theorem pure_runs {A B : Type u} (f : A → B ⊕ A) {a : A} {b : B}
    (h : Part.Runs (fun a => _root_.Part.some (f a)) a b) :
    iter (m := m) (fun a => pure (f a)) a = pure b := by
  induction h with
  | @done a b found =>
    have eq : f _ = .inl b := (_root_.Part.mem_some_iff.mp found).symm
    rw [congrFun (LawfulElgotMonad.fixpoint (fun a => pure (f a))), eq]
    simp
  | more found run ih =>
    have eq : f _ = .inr _ := (_root_.Part.mem_some_iff.mp found).symm
    rw [congrFun (LawfulElgotMonad.fixpoint (fun a => pure (f a))), eq]
    simpa using ih

/-- Pure deterministic iteration has its unique finite result or silent bottom. -/
theorem iter_pure {A B : Type u} (f : A → B ⊕ A) (a : A) :
    iter (m := m) (fun a => pure (f a)) a =
      liftPart (m := m) (iter (m := _root_.Part) (fun a => _root_.Part.some (f a)) a) := by
  classical
  let run := iter (m := _root_.Part) (fun a => _root_.Part.some (f a))
  by_cases done : (run a).Dom
  · rw [show liftPart (m := m) (run a) = pure ((run a).get done) by simp [liftPart, done]]
    exact pure_runs f ((Part.mem_iter_iff ..).mp (_root_.Part.get_mem done))
  · have noResult (x : A) (h : ¬(run x).Dom) :
        ∃ y : {x : A // ¬(run x).Dom}, f x = .inr y.val := by
      cases eq : f x with
      | inl b =>
        apply False.elim
        apply h
        have witness : Part.Runs (fun a => _root_.Part.some (f a)) x b := .done (by simp [eq])
        exact ((Part.mem_iter_iff ..).mpr witness).fst
      | inr y =>
        refine ⟨⟨y, ?_⟩, rfl⟩
        intro hy
        apply h
        exact ((Part.mem_iter_iff ..).mpr
          (.more (by simp [eq]) ((Part.mem_iter_iff ..).mp (_root_.Part.get_mem hy)))).fst
    let next (x : {x : A // ¬(run x).Dom}) := Classical.choose (noResult x.val x.property)
    have next_eq (x : {x : A // ¬(run x).Dom}) : f x.val = .inr (next x).val :=
      Classical.choose_spec (noResult x.val x.property)
    let body : {x : A // ¬(run x).Dom} → m (B ⊕ {x : A // ¬(run x).Dom}) :=
      fun x => pure (.inr (next x))
    have project : (body >=> liftPure (Sum.map id Subtype.val)) =
        (liftPure Subtype.val >=> fun a => (pure (f a) : m (B ⊕ A))) := by
      funext x
      simp [body, Bind.kleisliRight, liftPure, next_eq]
    have forget : (body >=> liftPure (Sum.map id (fun _ => PUnit.unit))) =
        (liftPure (fun _ => PUnit.unit) >=>
          fun _ : PUnit.{u + 1} => (pure (.inr PUnit.unit) : m (B ⊕ PUnit))) := by
      funext x
      simp [body, Bind.kleisliRight, liftPure]
    have hp := congrFun (LawfulElgotMonad.uniformity _ _ _ project) ⟨a, done⟩
    have hf := congrFun (LawfulElgotMonad.uniformity _ _ _ forget) ⟨a, done⟩
    have result : iter (m := m) (fun a => pure (f a)) a = bottom := by
      simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, bottom] using hp.symm.trans hf
    rw [show liftPart (m := m) (run a) = bottom by simp [liftPart, done]]
    exact result

private noncomputable def partialLayer {A B : Type u} (f : A → _root_.Part (B ⊕ A))
    (a : A) : m ((B ⊕ A) ⊕ A) := by
  classical
  exact if h : (f a).Dom then pure (.inl ((f a).get h)) else pure (.inr a)

private theorem iter_partialLayer {A B : Type u} (f : A → _root_.Part (B ⊕ A)) :
    iter (partialLayer (m := m) f) = fun a => liftPart (m := m) (f a) := by
  classical
  funext a
  by_cases h : (f a).Dom
  · rw [congrFun (LawfulElgotMonad.fixpoint (partialLayer (m := m) f))]
    simp [partialLayer, liftPart, h]
  · rw [iter_of_pure_self _ a (by simp [partialLayer, h])]
    simp [liftPart, h]

@[simp] theorem liftPart_part {A : Type u} (x : _root_.Part A) :
    liftPart (m := _root_.Part) x = x := by
  induction x using _root_.Part.induction_on with
  | hnone =>
    rw [liftPart_none]
    exact Part.iter_forever PUnit.unit
  | hsome a => exact liftPart_some a

/-- The canonical partiality interpretation preserves complete iteration. -/
theorem liftPart_iter {A B : Type u} (f : A → _root_.Part (B ⊕ A)) (a : A) :
    liftPart (m := m) (iter f a) = iter (fun a => liftPart (m := m) (f a)) a := by
  classical
  let total (a : A) : B ⊕ A := if h : (f a).Dom then (f a).get h else .inr a
  have flatten_m : flattenBody (partialLayer (m := m) f) = fun a => pure (total a) := by
    funext a
    by_cases h : (f a).Dom <;> simp [flattenBody, partialLayer, total, Bind.kleisliRight, liftPure, h, flatten]
  have flatten_part : flattenBody (partialLayer (m := _root_.Part) f) =
      fun a => _root_.Part.some (total a) := by
    funext a
    by_cases h : (f a).Dom <;> simp [flattenBody, partialLayer, total, Bind.kleisliRight, liftPure, h, flatten]
  have normalized : iter (m := _root_.Part) f = iter (fun a => _root_.Part.some (total a)) := by
    have eq := LawfulElgotMonad.codiagonal (partialLayer (m := _root_.Part) f)
    simpa only [iter_partialLayer, liftPart_part, flatten_part] using eq
  rw [normalized, ← iter_pure, ← flatten_m, ← LawfulElgotMonad.codiagonal, iter_partialLayer]

end Silmaril.Elgot.ITree.Interpret

end

section

/-! ## Partial-root presentation of the handler fold

Replacing an undefined root's explicit self-loop by the canonical silent bottom
does not change complete iteration. This is a consequence of codiagonal.
-/

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {E : Type u → Type u} {m : Type u → Type v}
  [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

noncomputable def partialStepTree {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) (t : Tree E A) : m (A ⊕ Shrink.{u} (Tree E A)) := by
  classical
  exact if (out t).Dom then stepTree (E := E) (m := m) handler t else bottom

noncomputable def partialStep {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) (state : Shrink.{u} (Tree E A)) :
    m (A ⊕ Shrink.{u} (Tree E A)) :=
  partialStepTree (E := E) (m := m) handler ((equivShrink _).symm state)

omit [LawfulMonad m] [LawfulElgotMonad m] in
@[simp] theorem partialStepTree_ret {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) (a : A) :
    partialStepTree (E := E) (m := m) handler (ret a) = pure (.inl a) := by
  simp [partialStepTree]

omit [LawfulElgotMonad m] in
@[simp] theorem partialStepTree_vis {A : Type u} [Small.{u} (Tree E A)] {R : Type u}
    (handler : Handler E m) (e : E R) (next : R → Tree E A) :
    partialStepTree (E := E) (m := m) handler (vis e next) =
      handler e >>= fun r => pure (.inr (equivShrink _ (next r))) := by simp [partialStepTree]

omit [LawfulMonad m] [LawfulElgotMonad m] in
@[simp] theorem partialStepTree_diverge {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) :
    partialStepTree (E := E) (m := m) handler (diverge : Tree E A) = bottom := by
  simp [partialStepTree]

theorem fold_eq_iter_partialStep {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) (t : Tree E A) :
    fold (E := E) (m := m) handler t =
      iter (partialStep (E := E) (m := m) handler) (equivShrink _ t) := by
  classical
  let layer (s : Shrink.{u} (Tree E A)) : m ((A ⊕ Shrink.{u} (Tree E A)) ⊕ Shrink.{u} (Tree E A)) :=
    if (out ((equivShrink (Tree E A)).symm s)).Dom then
      step (E := E) (m := m) handler s >>= fun result => pure (.inl result)
    else pure (.inr s)
  have inner : iter layer = partialStep (E := E) (m := m) handler := by
    funext s
    by_cases h : (out ((equivShrink (Tree E A)).symm s)).Dom
    · rw [congrFun (LawfulElgotMonad.fixpoint layer)]
      simp [layer, h, partialStep, partialStepTree, step]
    · rw [iter_of_pure_self _ s (by simp [layer, h])]
      simp [partialStep, partialStepTree, h]
  have flat : flattenBody layer = step (E := E) (m := m) handler := by
    funext s
    by_cases h : (out ((equivShrink (Tree E A)).symm s)).Dom
    · simp [flattenBody, layer, h, Bind.kleisliRight, liftPure, flatten]
    · simp [flattenBody, layer, h, Bind.kleisliRight, liftPure, flatten, step, stepTree]
  have law := congrFun (LawfulElgotMonad.codiagonal layer) (equivShrink _ t)
  simpa only [inner, flat, fold] using law.symm

end Silmaril.Elgot.ITree.Interpret

end

section

/-! ## Silent normalization with residual continuations

Keep continuation bodies before resuming their recursive returns. This lets
the handler interpreter use one common state space for both visible steps and
silent returns when applying the codiagonal law.
-/

namespace Silmaril.Elgot.ITree.Interpret

universe u

variable {E : Type u → Type u} {A B : Type u}

abbrev ResidualRoot (E : Type u → Type u) (A B : Type u) :=
  Visible E B (Tree E (B ⊕ A))

private def rootInl : ResidualRoot E A B → Visible E (B ⊕ A) (Tree E (B ⊕ A))
  | .ret b => .ret (.inl b)
  | .vis e next => .vis e next

private theorem rootInl_injective : Function.Injective (rootInl (E := E) (A := A) (B := B)) := by
  intro x y eq
  cases x <;> cases y <;> cases eq <;> rfl

instance smallResidualRoot [Small.{u} (Tree E (B ⊕ A))] : Small.{u} (ResidualRoot E A B) :=
  small_of_injective (roll_injective.comp (_root_.Part.some_injective.comp rootInl_injective))

noncomputable def residualStep (f : A → Tree E (B ⊕ A)) (t : Tree E (B ⊕ A)) :
    _root_.Part (ResidualRoot E A B ⊕ Tree E (B ⊕ A)) :=
  out t >>= fun
    | .ret (.inl b) => _root_.Part.some (.inl (.ret b))
    | .ret (.inr a) => _root_.Part.some (.inr (f a))
    | .vis e next => _root_.Part.some (.inl (.vis e next))

theorem out_resume_residual (f : A → Tree E (B ⊕ A)) (t : Tree E (B ⊕ A)) :
    out (resume f t) = _root_.Part.map (Visible.map (resume f)) (iter (residualStep f) t) := by
  have bodies : mapReturn (residualStep f) (liftPure (Visible.map (resume f))) = normalizeStep f := by
    funext t
    simp only [mapReturn, residualStep, normalizeStep, _root_.Part.bind_eq_bind, _root_.Part.bind_assoc]
    apply congrArg (_root_.Part.bind (out t))
    funext node
    cases node with
    | ret result => cases result <;> simp [liftPure, Visible.map, Function.comp_def, _root_.Part.pure_eq_some]
    | vis e next => simp [liftPure, Visible.map, Function.comp_def, _root_.Part.pure_eq_some]
  have h := congrFun (LawfulElgotMonad.naturality (m := _root_.Part)
    (residualStep f) (liftPure (Visible.map (resume f)))) t
  rw [bodies] at h
  rw [out_resume]
  simpa only [Bind.kleisliRight, liftPure, Function.comp_def, _root_.Part.bind_eq_bind,
    _root_.Part.pure_eq_some, _root_.Part.bind_some_eq_map] using h.symm

end Silmaril.Elgot.ITree.Interpret

end

section

/-! ## Changing the universes of a partial iteration

Unlike monadic uniformity, this equivalence can change both value universes.
Its proof transports the existing finite `Part.Runs` derivations in both
directions, so it does not require iterating over a target computation carrier.
-/

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {A B : Type u} {C D : Type v}

def transportPart (state : A ≃ C) (value : B ≃ D) (f : A → _root_.Part (B ⊕ A)) :
    C → _root_.Part (D ⊕ C) :=
  fun c => _root_.Part.map (Sum.map value state) (f (state.symm c))

theorem runs_transport_iff (state : A ≃ C) (value : B ≃ D)
    (f : A → _root_.Part (B ⊕ A)) (a : A) (b : B) :
    Part.Runs (transportPart state value f) (state a) (value b) ↔ Part.Runs f a b := by
  have mem : ∀ a (s : B ⊕ A),
      Sum.map value state s ∈ transportPart state value f (state a) ↔ s ∈ f a := by
    intro a s
    simp only [transportPart, Equiv.symm_apply_apply, _root_.Part.mem_map_iff]
    refine ⟨fun ⟨r, hr, heq⟩ => ?_, fun hs => ⟨s, hs, rfl⟩⟩
    have hrs : r = s := Sum.map_injective.2 ⟨value.injective, state.injective⟩ heq
    exact hrs ▸ hr
  have back : ∀ {c d}, Part.Runs (transportPart state value f) c d →
      Part.Runs f (state.symm c) (value.symm d) := by
    intro c d h
    induction h with
    | @done c d found =>
        have found' : Sum.map value state (Sum.inl (value.symm d)) ∈
            transportPart state value f (state (state.symm c)) := by simpa using found
        exact .done ((mem _ _).1 found')
    | @more c c' d found _ ih =>
        have found' : Sum.map value state (Sum.inr (state.symm c')) ∈
            transportPart state value f (state (state.symm c)) := by simpa using found
        exact .more ((mem _ _).1 found') ih
  constructor
  · intro h
    simpa using back h
  · intro h
    induction h with
    | done found => exact .done ((mem _ (.inl _)).2 found)
    | more found _ ih => exact .more ((mem _ (.inr _)).2 found) ih

theorem iter_transport (state : A ≃ C) (value : B ≃ D)
    (f : A → _root_.Part (B ⊕ A)) (a : A) :
    _root_.Part.map value (iter f a) = iter (transportPart state value f) (state a) := by
  apply _root_.Part.ext
  intro d
  obtain ⟨b, rfl⟩ := value.surjective d
  simp only [_root_.Part.mem_map_iff, Part.mem_iter_iff, runs_transport_iff]
  constructor
  · rintro ⟨b', run, eq⟩
    exact value.injective eq ▸ run
  · intro run
    exact ⟨b, run, rfl⟩

end Silmaril.Elgot.ITree.Interpret

end

section

/-! ## Eliminating partial observations across universes

A partial observation may have a larger value universe than the target monad.
Its successful branch is interpreted directly; an undefined observation maps
to the target's silent bottom. Smallness permits iteration to be transported
without requiring the target monad to accept large state types.
-/

namespace Silmaril.Elgot.ITree.Interpret

universe u v w z

variable {m : Type u → Type v} [Monad m] [Iterate m]

noncomputable def partialCase {X : Type w} {B : Type u}
    (x : _root_.Part X) (k : X → m B) : m B := by
  classical
  exact if h : x.Dom then k (x.get h) else bottom

@[simp] theorem partialCase_some {X : Type w} {B : Type u} (x : X) (k : X → m B) :
    partialCase (_root_.Part.some x) k = k x := by simp [partialCase]

@[simp] theorem partialCase_none {X : Type w} {B : Type u} (k : X → m B) :
    partialCase (_root_.Part.none : _root_.Part X) k = bottom := by simp [partialCase]

theorem partialCase_map {X : Type w} {Y : Type z} {B : Type u}
    (x : _root_.Part X) (f : X → Y) (k : Y → m B) :
    partialCase (_root_.Part.map f x) k = partialCase x (k ∘ f) := by
  induction x using _root_.Part.induction_on with
  | hnone => simp
  | hsome x => simp

theorem partialCase_bind {X : Type w} {Y : Type z} {B : Type u}
    (x : _root_.Part X) (f : X → _root_.Part Y) (k : Y → m B) :
    partialCase (x.bind f) k = partialCase x (fun a => partialCase (f a) k) := by
  induction x using _root_.Part.induction_on with
  | hnone => simp
  | hsome x => simp

variable [LawfulMonad m] [LawfulElgotMonad m]

theorem partialCase_bind_right {X : Type w} {B C : Type u}
    (x : _root_.Part X) (k : X → m B) (g : B → m C) :
    (partialCase x k >>= g) = partialCase x (fun a => k a >>= g) := by
  induction x using _root_.Part.induction_on with
  | hnone => simp
  | hsome x => simp

theorem partialCase_eq_liftPart {X B : Type u} (x : _root_.Part X) (k : X → m B) :
    partialCase x k = liftPart (m := m) x >>= k := by
  induction x using _root_.Part.induction_on with
  | hnone => simp
  | hsome x => simp

theorem partialCase_shrink {X : Type w} [Small.{u} X] {B : Type u}
    (x : _root_.Part X) (k : X → m B) :
    partialCase x k = liftPart (m := m) (_root_.Part.map (equivShrink X) x) >>=
      fun y => k ((equivShrink X).symm y) := by
  induction x using _root_.Part.induction_on with
  | hnone => simp
  | hsome x => simp

/-- Interpret a possibly large partial iteration by iterating over a proved
small state type in the target monad. No iteration compatibility is assumed. -/
theorem partialCase_iter {S R : Type w} [Small.{u} S] [Small.{u} R] {B : Type u}
    (f : S → _root_.Part (R ⊕ S)) (s : S) (k : R → m B) :
    partialCase (iter f s) k =
      iter (fun state : Shrink.{u} S =>
        partialCase (f ((equivShrink S).symm state))
          (Sum.elim (fun r => k r >>= pure ∘ Sum.inl)
            (fun next => pure (.inr (equivShrink S next))))) (equivShrink S s) := by
  let transformed := transportPart (equivShrink S) (equivShrink R) f
  let result : Shrink.{u} R → m B := fun r => k ((equivShrink R).symm r)
  have body : ∀ state, mapReturn (fun state => liftPart (m := m) (transformed state)) result state =
      partialCase (f ((equivShrink S).symm state))
        (Sum.elim (fun r => k r >>= pure ∘ Sum.inl)
          (fun next => pure (.inr (equivShrink S next)))) := by
    intro state
    simp only [mapReturn, ← partialCase_eq_liftPart, transformed, transportPart,
      partialCase_map]
    apply congrArg (partialCase (f ((equivShrink S).symm state)))
    funext outcome
    cases outcome <;> simp [result, Function.comp_def]
  calc
    _ = liftPart (m := m) (_root_.Part.map (equivShrink R) (iter f s)) >>= result :=
      partialCase_shrink _ _
    _ = liftPart (m := m) (iter transformed (equivShrink S s)) >>= result := by
      rw [iter_transport]
    _ = iter (fun state => liftPart (m := m) (transformed state))
        (equivShrink S s) >>= result := by rw [liftPart_iter]
    _ = iter (mapReturn (fun state => liftPart (m := m) (transformed state)) result)
        (equivShrink S s) :=
      congrFun (LawfulElgotMonad.naturality _ result) (equivShrink S s)
    _ = _ := congrArg (fun body => iter body (equivShrink S s)) (funext body)

end Silmaril.Elgot.ITree.Interpret

end

section

/-! ## The handler fold preserves complete iteration

Visible events and silent recursive returns are flattened into one iteration
over residual trees. The comparison uses partial-root normalization and the
target's codiagonal and pure-uniformity laws.
-/

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {E : Type u → Type u} {m : Type u → Type v}
  [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  {A B : Type u} [Small.{u} (Tree E (B ⊕ A))]

/-- One combined visible or silent transition on residual iteration bodies. -/
noncomputable def wholeStepTree (handler : Handler E m) (f : A → Tree E (B ⊕ A))
    (t : Tree E (B ⊕ A)) : m (B ⊕ Shrink.{u} (Tree E (B ⊕ A))) :=
  partialStepTree (E := E) (m := m) handler t >>= Sum.elim
    (fun result => pure (Sum.map id (fun a => equivShrink _ (f a)) result))
    (fun state => pure (.inr state))

noncomputable def wholeStep (handler : Handler E m) (f : A → Tree E (B ⊕ A))
    (state : Shrink.{u} (Tree E (B ⊕ A))) : m (B ⊕ Shrink.{u} (Tree E (B ⊕ A))) :=
  wholeStepTree (E := E) (m := m) handler f ((equivShrink _).symm state)

theorem iter_fold_eq_whole (handler : Handler E m) (f : A → Tree E (B ⊕ A)) (a : A) :
    iter (fun a => fold (E := E) (m := m) handler (f a)) a =
      iter (wholeStep (E := E) (m := m) handler f) (equivShrink _ (f a)) := by
  let next (a : A) := equivShrink (Tree E (B ⊕ A)) (f a)
  let body := mapReturn (partialStep (E := E) (m := m) (A := B ⊕ A) handler)
    (liftPure (Sum.map id next))
  have inner (s : Shrink.{u} (Tree E (B ⊕ A))) :
      iter body s = fold (E := E) (m := m) handler ((equivShrink _).symm s) >>=
        liftPure (Sum.map id next) := by
    have h := congrFun (LawfulElgotMonad.naturality
      (partialStep (E := E) (m := m) (A := B ⊕ A) handler) (liftPure (Sum.map id next))) s
    simpa only [fold_eq_iter_partialStep, Equiv.apply_symm_apply, Bind.kleisliRight] using h.symm
  have square :
      ((fun a => fold (E := E) (m := m) handler (f a)) >=> liftPure (Sum.map id next)) =
      (liftPure next >=> iter body) := by
    funext a
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, inner,
      next, Equiv.symm_apply_apply]
  have flat : flattenBody body = wholeStep (E := E) (m := m) handler f := by
    funext s
    simp only [flattenBody, body, mapReturn, Bind.kleisliRight, liftPure,
      Function.comp_apply, LawfulMonad.bind_assoc, wholeStep, wholeStepTree, partialStep]
    congr 1
    funext result
    cases result with
    | inl result => cases result <;> simp [flatten, next]
    | inr state => simp [flatten]
  have law := congrFun (LawfulElgotMonad.uniformity _ _ next square) a
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind,
    LawfulElgotMonad.codiagonal, flat, next] using law

private def emitRoot {C D : Type u} {X : Type (u + 1)} (handler : Handler E m)
    (next : X → C) : Visible E D X → m (D ⊕ C)
  | .ret d => pure (.inl d)
  | .vis e continuation => handler e >>= fun r => pure (.inr (next (continuation r)))

omit [LawfulElgotMonad m] in
private theorem partialStepTree_eq_case {D : Type u} [Small.{u} (Tree E D)]
    (handler : Handler E m) (t : Tree E D) :
    partialStepTree (E := E) (m := m) handler t =
      partialCase (out t) (emitRoot (E := E) (m := m) handler (equivShrink _)) := by
  rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩ <;> simp [emitRoot]

theorem fold_resume_eq_whole [Small.{u} (Tree E B)]
    (handler : Handler E m) (f : A → Tree E (B ⊕ A)) (t : Tree E (B ⊕ A)) :
    fold (E := E) (m := m) handler (resume f t) =
      iter (wholeStep (E := E) (m := m) handler f) (equivShrink _ t) := by
  let next (s : Shrink.{u} (Tree E (B ⊕ A))) : Shrink.{u} (Tree E B) :=
    equivShrink _ (resume f ((equivShrink _).symm s))
  let emit : ResidualRoot E A B → m (B ⊕ Shrink.{u} (Tree E (B ⊕ A))) :=
    emitRoot (E := E) (m := m) handler (equivShrink _)
  let body (s : Shrink.{u} (Tree E (B ⊕ A))) :
      m ((B ⊕ Shrink.{u} (Tree E (B ⊕ A))) ⊕ Shrink.{u} (Tree E (B ⊕ A))) :=
    partialCase (residualStep f ((equivShrink _).symm s))
      (Sum.elim (fun root => emit root >>= pure ∘ Sum.inl)
        (fun child => pure (.inr (equivShrink _ child))))
  have inner (s : Shrink.{u} (Tree E (B ⊕ A))) :
      iter body s = partialCase (iter (residualStep f) ((equivShrink _).symm s)) emit := by
    simpa only [Equiv.apply_symm_apply] using
      (partialCase_iter (m := m) (residualStep f) ((equivShrink _).symm s) emit).symm
  have square : (iter body >=> liftPure (Sum.map id next)) =
      (liftPure next >=> partialStep (E := E) (m := m) (A := B) handler) := by
    funext s
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, inner,
      partialCase_bind_right, partialStep, next, Equiv.symm_apply_apply,
      partialStepTree_eq_case, out_resume_residual, partialCase_map]
    apply congrArg (partialCase (iter (residualStep f) ((equivShrink _).symm s)))
    funext root
    cases root <;> simp [emit, emitRoot, Visible.map, Function.comp_def]
  have flat : flattenBody body = wholeStep (E := E) (m := m) handler f := by
    funext s
    simp only [flattenBody, Bind.kleisliRight, liftPure, body,
      partialCase_bind_right, residualStep, _root_.Part.bind_eq_bind, partialCase_bind,
      wholeStep, wholeStepTree, partialStepTree_eq_case, partialCase_bind_right]
    apply congrArg (partialCase (out ((equivShrink _).symm s)))
    funext root
    cases root with
    | ret result => cases result <;> simp [emit, emitRoot, flatten]
    | vis e continuation => simp [emit, emitRoot, flatten]
  have law := congrFun (LawfulElgotMonad.uniformity _ _ next square) (equivShrink _ t)
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind,
    LawfulElgotMonad.codiagonal, flat, next, Equiv.symm_apply_apply,
    fold_eq_iter_partialStep] using law.symm

/-- Event interpretation preserves arbitrary, including unguarded, iteration. -/
theorem fold_iter [Small.{u} (Tree E B)]
    (handler : Handler E m) (f : A → Tree E (B ⊕ A)) (a : A) :
    fold (E := E) (m := m) handler (iter f a) =
      iter (fun a => fold (E := E) (m := m) handler (f a)) a := by
  rw [← resume_body f a, fold_resume_eq_whole, iter_fold_eq_whole]

end Silmaril.Elgot.ITree.Interpret

end

section

/-! ## Naturality of interaction-tree interpretation -/

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {E : Type u → Type u} {m : Type u → Type v}
  [Monad m] [LawfulMonad m]
  {A B : Type u} [Small.{u} (Tree E A)] [Small.{u} (Tree E B)]

private noncomputable def mapState (f : A → B) (state : Shrink.{u} (Tree E A)) :
    Shrink.{u} (Tree E B) :=
  equivShrink _ ((equivShrink (Tree E A)).symm state >>= pure ∘ f)

private theorem map_square (handler : Handler E m) (f : A → B) :
    (mapReturn (step (E := E) (m := m) handler) (liftPure f) >=>
      liftPure (Sum.map id (mapState f))) =
    (liftPure (mapState f) >=> step (E := E) (m := m) handler) := by
  funext state
  obtain ⟨t, rfl⟩ := (equivShrink (Tree E A)).surjective state
  simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind,
    mapReturn, step_shrink, mapState, Equiv.symm_apply_apply]
  rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, event, next, rfl⟩
  · simp [mapState]
  · have map_ret : (ret a >>= pure ∘ f : Tree E B) = ret (f a) := pure_bind a (pure ∘ f)
    simp [map_ret]
  · simp only [vis_bind, stepTree_vis]
    simp [mapState]

variable [Iterate m] [LawfulElgotMonad m]

/-- Interpretation commutes with changing the returned value, while preserving
all requested effects and the complete iteration chosen by the target model. -/
theorem fold_map (handler : Handler E m) (f : A → B) (t : Tree E A) :
    fold (E := E) (m := m) handler (t >>= pure ∘ f) =
      fold (E := E) (m := m) handler t >>= pure ∘ f := by
  have hn := congrFun (LawfulElgotMonad.naturality (m := m)
    (step (E := E) (m := m) handler) (liftPure f)) (equivShrink _ t)
  have hu := congrFun (LawfulElgotMonad.uniformity (m := m)
    (mapReturn (step (E := E) (m := m) handler) (liftPure f))
    (step (E := E) (m := m) handler) (mapState f) (map_square handler f))
    (equivShrink _ t)
  calc
    _ = iter (mapReturn (step (E := E) (m := m) handler) (liftPure f))
        (equivShrink _ t) := by
      simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind,
        mapState, Equiv.symm_apply_apply, fold] using hu.symm
    _ = _ := hn.symm

end Silmaril.Elgot.ITree.Interpret

end

section

/-! ## The initial complete Elgot interpretation of event trees

When the tree state spaces are small, every handler in a lawful complete Elgot
monad extends uniquely to a monad map preserving complete iteration. All four
map laws are proved for the concrete fold; none is an assumption of existence.
The target's computation universe may differ from its value universe.
-/

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {E : Type u → Type u} [∀ A : Type u, Small.{u} (Tree E A)]
  {m : Type u → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

theorem fold_bind (handler : Handler E m) {A B : Type u}
    (t : Tree E A) (k : A → Tree E B) :
    fold (E := E) (m := m) handler (t >>= k) =
      fold (E := E) (m := m) handler t >>= fun a => fold (E := E) (m := m) handler (k a) :=
  map_bind_of_map_iter (fun {_} => fold (E := E) (m := m) handler)
    (fun x f => fold_map (E := E) (m := m) handler f x)
    (fun f a => fold_iter (E := E) (m := m) handler f a) t k

/-- The canonical interpreter, with its monad and complete-iteration laws. -/
noncomputable def foldHom (handler : Handler E m) : Hom (E := E) (m := m) handler where
  map := fold (E := E) (m := m) handler
  map_pure := fold_ret (E := E) (m := m) handler
  map_bind := fold_bind (E := E) (m := m) handler
  map_trigger := fold_trigger (E := E) (m := m) handler
  map_iter := fold_iter (E := E) (m := m) handler

end Silmaril.Elgot.ITree.Interpret

end
