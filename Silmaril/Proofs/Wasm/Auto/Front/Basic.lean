module

public import Silmaril.Wasm.Auto.Front.Defs
public import Silmaril.Wasm.Verify.Check.Thms
public import Silmaril.Wasm.Verify.Kernel.Thms
public import Silmaril.Wasm.Spec.Run.Thms
public import Silmaril.Wasm.Game.Instantiate.Thms
public import Silmaril.Wasm.Behaviour.Refinement.Interpreter
public import Silmaril.Wasm.Execution.Core.SpecProfile

/-!
# The front end: soundness of differential testing

A counterexample found by the differential tester refutes the statement it tests:
`refutes_of_cexWith` (refinement, deterministic profile), `not_modEquiv_of_cexWith`
(equivalence), `not_modMeets_of_specCexWith` (reference functions, every profile admitting the
deterministic steps). Reflexivity gives the `identical` verdict (`modRefines_refl`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Front

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Front
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded.Exec.BehaviourRefinement
open Silmaril.Wasm.Verify (instance? instOf refOracle isInstance_of_instance?)
open Silmaril.Wasm.Spec (typedB typedB_sound invokeOk_of_wellFormed)

/-! ## Relations -/

theorem Rel.holdsB_iff (R : Rel) (b b' : Behaviour Val) :
    R.holdsB b b' = true ↔ R.toProp b b' := by
  cases R <;> simp [Rel.holdsB, Rel.toProp, Behaviour.TrapRefines]

theorem Rel.refl (R : Rel) (b : Behaviour Val) : R.toProp b b := by
  cases R
  · rfl
  · exact Or.inr rfl

/-! ## Instances and runs -/

theorem instOf_eq {m : Module} {mt : Validation.CModuleType} {I : ScalarInstance}
    (h : instance? m = some (mt, I)) : instOf m = I := by
  simp [instOf, h]

theorem addrOf_eq {m : Module} {mt : Validation.CModuleType} {I : ScalarInstance}
    (h : instance? m = some (mt, I)) (j : Nat) : addrOf m j = I.addrs.getD j 0 := by
  simp [addrOf, instOf_eq h]

theorem runK_eq : runK = Front.runC := by
  funext o
  exact Silmaril.Wasm.Verify.Kernel.runInvokeK_eq o

theorem outOf_inv {s : Store Nat} {a : Nat} {vs : List Val} {r : Result}
    (h : outOf Front.runC s a vs = some r) :
    ∃ c, Exec.runInvoke? refOracle diffFuel s a vs = some (c, true, some r) := by
  unfold outOf at h
  split at h
  · rename_i c r' heq
    cases h
    exact ⟨c, heq⟩
  · cases h

/-- Typed arguments of an export of a computed instance meet `$invoke`'s premises. -/
theorem invokeOk_of_params {m : Module} {mt : Validation.CModuleType} {I : ScalarInstance}
    (h : instance? m = some (mt, I)) {j : Nat} {ps : List ScalarType}
    (hp : paramsOf I j = some ps) {vs : List Val} (ht : typedB ps vs = true) :
    StoreOk I.store ∧ InvokeOk I.store (I.addrs.getD j 0) vs := by
  have hw : I.WellFormed I.store := (isInstance_of_instance? h).ok
  unfold paramsOf at hp
  obtain ⟨ft, hft, rfl⟩ := Option.map_eq_some_iff.1 hp
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hft
  exact ⟨hw.storeOk, invokeOk_of_wellFormed hw ⟨j, hj⟩ ⟨vs, typedB_sound ht⟩⟩

/-! ## What a hit records -/

/-- What a refinement counterexample records. -/
theorem cexWith_inv {R : Rel} {impl spec : Module} {j : Nat} {vs : List Val}
    (h : cexWith Front.runC R impl spec j vs = true) :
    ∃ mt₁ I₁ mt₂ I₂ ps₁ ps₂ r₁ r₂, instance? impl = some (mt₁, I₁) ∧
      instance? spec = some (mt₂, I₂) ∧ paramsOf I₁ j = some ps₁ ∧ paramsOf I₂ j = some ps₂ ∧
      typedB ps₁ vs = true ∧ typedB ps₂ vs = true ∧
      outOf Front.runC I₁.store (I₁.addrs.getD j 0) vs = some r₁ ∧
      outOf Front.runC I₂.store (I₂.addrs.getD j 0) vs = some r₂ ∧ badPair R r₁ r₂ = true := by
  unfold cexWith at h
  split at h
  · rename_i mt₁ I₁ mt₂ I₂ h₁ h₂
    split at h
    · rename_i ps₁ ps₂ hp₁ hp₂
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨ht₁, ht₂⟩, h⟩ := h
      split at h
      · rename_i r₁ r₂ ho₁ ho₂
        exact ⟨mt₁, I₁, mt₂, I₂, ps₁, ps₂, r₁, r₂, h₁, h₂, hp₁, hp₂, ht₁, ht₂, ho₁, ho₂, h⟩
      · cases h
    · cases h
  · cases h

/-- What a reference-function counterexample records. -/
theorem specCexWith_inv {R : Rel} {m : Module} {j : Nat} {f : List Val → Option Result}
    {vs : List Val} (h : specCexWith Front.runC R m j f vs = true) :
    ∃ mt I ps r₁ r₂, instance? m = some (mt, I) ∧ paramsOf I j = some ps ∧
      typedB ps vs = true ∧ outOf Front.runC I.store (I.addrs.getD j 0) vs = some r₁ ∧
      f vs = some r₂ ∧ R.holdsB r₁.toBehaviour r₂.toBehaviour = false := by
  unfold specCexWith at h
  split at h
  · rename_i mt I hI
    split at h
    · rename_i ps hp
      simp only [Bool.and_eq_true] at h
      obtain ⟨ht, h⟩ := h
      split at h
      · rename_i r₁ r₂ ho hf
        exact ⟨mt, I, ps, r₁, r₂, hI, hp, ht, ho, hf, by simpa using h⟩
      · cases h
    · cases h
  · cases h

/-! ## Refutations -/

/-- A bad pair is related neither to the specification's result nor to divergence. -/
theorem badPair_not {R : Rel} {r₁ r₂ : Result} (h : badPair R r₁ r₂ = true) :
    ∀ b' ∈ ({r₂.toBehaviour, Behaviour.diverges} : Set (Behaviour Val)),
      ¬ R.toProp r₁.toBehaviour b' := by
  simp only [badPair, Bool.and_eq_true, Bool.not_eq_true'] at h
  intro b' hb' hR
  rw [← Rel.holdsB_iff] at hR
  rcases hb' with rfl | hdiv
  · rw [hR] at h
    cases h.1
  · rw [Set.mem_singleton_iff] at hdiv
    subst hdiv
    rw [hR] at h
    cases h.2

/-- `ModRefines` at the computed instances. -/
theorem modRefines_at {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    {impl spec : Module} {j : Nat} {mt₁ mt₂ : Validation.CModuleType} {I₁ I₂ : ScalarInstance}
    (h₁ : instance? impl = some (mt₁, I₁)) (h₂ : instance? spec = some (mt₂, I₂))
    (h : ModRefines R P impl spec j) :
    ExportRefines R P I₁.store (I₁.addrs.getD j 0) I₂.store (I₂.addrs.getD j 0) := by
  unfold ModRefines at h
  rwa [instOf_eq h₁, instOf_eq h₂, addrOf_eq h₁, addrOf_eq h₂] at h

/-- **A counterexample refutes refinement** at the deterministic profile: on the arguments of
the hit, the implementation's result is a behaviour, and the specification's behaviours are its
result and possibly divergence (silmaril-lean's `behaviours_subset_of_runInvoke?`), neither
related to the implementation's result. -/
theorem refutes_of_cexWith {R : Rel} {impl spec : Module} {j : Nat} {vs : List Val}
    (h : cexWith Front.runC R impl spec j vs = true) :
    ¬ ModRefines R.toProp (profile refOracle) impl spec j := by
  obtain ⟨mt₁, I₁, mt₂, I₂, ps₁, ps₂, r₁, r₂, h₁, h₂, hp₁, hp₂, ht₁, ht₂, ho₁, ho₂, hbad⟩ :=
    cexWith_inv h
  obtain ⟨hs₁, hi₁⟩ := invokeOk_of_params h₁ hp₁ ht₁
  obtain ⟨hs₂, hi₂⟩ := invokeOk_of_params h₂ hp₂ ht₂
  obtain ⟨c₁, hr₁⟩ := outOf_inv ho₁
  obtain ⟨c₂, hr₂⟩ := outOf_inv ho₂
  have hin : r₁.toBehaviour ∈
      behaviours (profile refOracle) Det.noHost I₁.store (I₁.addrs.getD j 0) vs :=
    mem_behaviours_of_runInvoke? hs₁ hi₁ hr₁
  have hsub : behaviours (profile refOracle) Det.noHost I₂.store (I₂.addrs.getD j 0) vs ⊆
      {r₂.toBehaviour, Behaviour.diverges} :=
    behaviours_subset_of_runInvoke? hs₂ hi₂ hr₂
  intro href
  obtain ⟨b', hb', hR⟩ := modRefines_at h₁ h₂ href vs hi₁ _ hin
  exact badPair_not hbad b' (hsub hb') hR

/-- The same with the kernel-reducible interpreter (for `decide +kernel`). -/
theorem refutes_of_cexK {R : Rel} {impl spec : Module} {j : Nat} {vs : List Val}
    (h : cexK R impl spec j vs = true) :
    ¬ ModRefines R.toProp (profile refOracle) impl spec j := by
  unfold cexK at h
  rw [runK_eq] at h
  exact refutes_of_cexWith h

/-- **A counterexample refutes equivalence** (either direction, for equality). -/
theorem not_modEquiv_of_cexWith {R : Rel} {m₁ m₂ : Module} {j : Nat} {vs : List Val}
    (h : cexWith Front.runC R m₁ m₂ j vs = true) :
    ¬ ModEquiv R.toProp (profile refOracle) m₁ m₂ j :=
  fun he => refutes_of_cexWith h he.1

theorem modEquiv_eq_symm {P : Profile} {m₁ m₂ : Module} {j : Nat}
    (h : ModEquiv Rel.eq.toProp P m₁ m₂ j) : ModRefines Rel.eq.toProp P m₂ m₁ j := by
  intro vs hi b hb
  obtain ⟨b', hb', hR⟩ := h.2 vs hi b hb
  exact ⟨b', hb', hR.symm⟩

theorem not_modEquiv_of_cexWith_symm {m₁ m₂ : Module} {j : Nat} {vs : List Val}
    (h : cexWith Front.runC .eq m₂ m₁ j vs = true) :
    ¬ ModEquiv Rel.eq.toProp (profile refOracle) m₁ m₂ j :=
  fun he => refutes_of_cexWith h (modEquiv_eq_symm he)

theorem not_modEquiv_of_cexK {R : Rel} {m₁ m₂ : Module} {j : Nat} {vs : List Val}
    (h : cexK R m₁ m₂ j vs = true) :
    ¬ ModEquiv R.toProp (profile refOracle) m₁ m₂ j :=
  fun he => refutes_of_cexK h he.1

theorem not_modEquiv_of_cexK_symm {m₁ m₂ : Module} {j : Nat} {vs : List Val}
    (h : cexK .eq m₂ m₁ j vs = true) :
    ¬ ModEquiv Rel.eq.toProp (profile refOracle) m₁ m₂ j :=
  fun he => refutes_of_cexK h (modEquiv_eq_symm he)

theorem steps_mono {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    {c d : Config Nat} (h : Steps (profile refOracle) Det.noHost c d) : Steps P Det.noHost c d := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hP _ _ hs)

/-- **A counterexample refutes a reference function** at every profile admitting the
deterministic steps (every specification profile `Profile.spec nd {}` in particular): only the
soundness of the interpreter is needed. -/
theorem not_modMeets_of_specCexWith {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    {R : Rel} {m : Module} {j : Nat} {f : List Val → Option Result} {vs : List Val}
    (h : specCexWith Front.runC R m j f vs = true) :
    ¬ ModMeets R.toProp P m j f := by
  obtain ⟨mt, I, ps, r₁, r₂, hI, hp, ht, ho, hf, hbad⟩ := specCexWith_inv h
  obtain ⟨hs, hi⟩ := invokeOk_of_params hI hp ht
  obtain ⟨c, hr⟩ := outOf_inv ho
  obtain ⟨hst, -, hcode⟩ := runInvoke?_steps_nf hs hi hr
  have hst' : Steps P Det.noHost (invoke I.store (I.addrs.getD j 0) vs) c :=
    steps_mono hP hst
  have hin : r₁.toBehaviour ∈ behaviours P Det.noHost I.store (I.addrs.getD j 0) vs :=
    mem_behavioursOf hst' hcode
  intro hm
  unfold ModMeets at hm
  rw [instOf_eq hI, addrOf_eq hI] at hm
  obtain ⟨b', hb', hR⟩ := hm vs hi _ hin
  simp only [specOfFn, hf, Set.mem_singleton_iff] at hb'
  subst hb'
  rw [← Rel.holdsB_iff, hbad] at hR
  cases hR

theorem not_modMeets_of_specCexK {R : Rel} {m : Module} {j : Nat}
    {f : List Val → Option Result} {vs : List Val} (h : specCexK R m j f vs = true) :
    ¬ ModMeets R.toProp (profile refOracle) m j f := by
  unfold specCexK at h
  rw [runK_eq] at h
  exact not_modMeets_of_specCexWith (fun _ _ hs => hs) h

/-- A reference-function counterexample from the kernel check, at every specification profile
`Profile.spec nd {}` (silmaril-lean's `Step.deterministic_refines_spec`). -/
theorem not_modMeets_spec_of_specCexK (nd : Bool) {R : Rel} {m : Module} {j : Nat}
    {f : List Val → Option Result} {vs : List Val} (h : specCexK R m j f vs = true) :
    ¬ ModMeets R.toProp (Profile.spec nd {}) m j f := by
  unfold specCexK at h
  rw [runK_eq] at h
  exact not_modMeets_of_specCexWith (fun _ _ hs => Step.deterministic_refines_spec nd hs) h

/-! ## Reports -/

/-- The proving stage never refutes. -/
theorem proveStageBase_ne_refuted (m₁ m₂ : Module) (j n : Nat) :
    (proveStageBase m₁ m₂ j n).verdict ≠ .refuted := by
  unfold proveStageBase
  split
  · simp
  · split
    · split <;> simp
    · simp

/-- **A `refuted` report of the front end refutes the refinement.** -/
theorem checkRefinesBase_refuted {R : Rel} {impl spec : Module} {j n : Nat} {idt : Bool}
    (h : (checkRefinesBase R impl spec j n idt).verdict = .refuted) :
    ¬ ModRefines R.toProp (profile refOracle) impl spec j := by
  unfold checkRefinesBase at h
  split at h
  · simp at h
  dsimp only at h
  split at h
  · split at h
    · simp at h
    split at h
    · rename_i vs hf
      exact refutes_of_cexWith (List.find?_some hf)
    · exact absurd h (proveStageBase_ne_refuted _ _ _ _)
  · simp at h

/-- **A `refuted` report of the front end refutes the equivalence** (for `Rel.eq` either
direction may be the refuted one). -/
theorem checkEquivBase_refuted {R : Rel} {m₁ m₂ : Module} {j n : Nat} {idt : Bool}
    (h : (checkEquivBase R m₁ m₂ j n idt).verdict = .refuted) :
    ¬ ModEquiv R.toProp (profile refOracle) m₁ m₂ j := by
  intro he
  unfold checkEquivBase at h
  dsimp only at h
  split at h
  · cases R with
    | eq =>
      dsimp only at h
      split at h
      · exact checkRefinesBase_refuted h (modEquiv_eq_symm he)
      · exact checkRefinesBase_refuted h he.1
    | trap => exact checkRefinesBase_refuted h he.1
  · exact checkRefinesBase_refuted h he.1

/-- **A `refuted` report against a reference function** refutes `ModMeets` at every profile
admitting the deterministic steps. -/
theorem checkMeets_refuted {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    {R : Rel} {m : Module} {j : Nat} {f : List Val → Option Result} {n : Nat}
    (h : (checkMeets R m j f n).verdict = .refuted) : ¬ ModMeets R.toProp P m j f := by
  unfold checkMeets at h
  dsimp only at h
  split at h
  · split at h
    · simp at h
    split at h
    · rename_i vs hf
      exact not_modMeets_of_specCexWith hP (List.find?_some hf)
    · simp at h
  · simp at h

/-! ## Reflexivity -/

theorem modRefines_refl (R : Rel) (P : Profile) (m : Module) (j : Nat) :
    ModRefines R.toProp P m m j :=
  fun _ _ b hb => ⟨b, hb, Rel.refl R b⟩

theorem modEquiv_refl (R : Rel) (P : Profile) (m : Module) (j : Nat) :
    ModEquiv R.toProp P m m j :=
  ⟨modRefines_refl R P m j, fun _ _ b hb => ⟨b, hb, Rel.refl R b⟩⟩

end Silmaril.Proofs.Wasm.Auto.Front