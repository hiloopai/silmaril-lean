module

public import Silmaril.Wasm.Binaryen.Exe.Pipeline
public import Silmaril.Wasm.Binaryen.PassAPI.Instances

@[expose] public section

/-! # The stage contract of the `binaryen-lean` pipelines

What a pipeline stage must prove, `StageOk o H f`, with the invariant `ExeInv`, the
relation `EE` and the pass constructor `guardedP` (moved verbatim from
`Exe/PipelineSound.lean`, which imports this file). Kept import-light so that a pass's
soundness theorem can live in a leaf file that imports only this file and the pass,
and that `Exe/PipelineSound.lean` (verified pipeline) or a separate experimental pipeline proof (not included in this package)
(experimental pipeline) imports.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Execution.Core Numerics Validation ModuleWf

/-! ## The invariant -/

/-- Function types have profile parameters and results (numeric, `funcref` or
`externref`, `sigValType`). -/
def HTy (m : BModule) : Prop :=
  ∀ st ∈ m.base.typeDefinitions, ∀ ft : FuncType, st.body = .func ft →
    ∀ t ∈ ft.params ++ ft.results, sigValType t = true

/-- Export equivalence of two layer-D modules under the closed host. -/
abbrev EE (H : Type) (o : GrowKind → Nat → Nat → Nat → Bool) (a b : BModule) : Prop :=
  ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) a.lower b.lower

theorem exportEquiv_refl {P : Profile} {H : Type} {host : HostSemantics H} (a : Module) :
    ExportEquiv (· = ·) P host a a :=
  ⟨ExportRefines.refl (R := fun b b' => b = b') (fun _ => rfl) _,
    ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩

/-- The executable type-section check gives `HTy`. -/
theorem typesInProfile_sound {m : BModule} (h : typesInProfile m = true) : HTy m := by
  intro st hst ft hft t ht
  have := List.all_eq_true.mp h st hst
  rw [hft] at this
  exact List.all_eq_true.mp this t ht

/-- The type-section check is complete for `HTy`. -/
theorem typesInProfile_complete {m : BModule} (h : HTy m) : typesInProfile m = true := by
  unfold typesInProfile
  refine List.all_eq_true.mpr fun st hst => ?_
  split
  · next ft hb => exact List.all_eq_true.mpr (h st hst ft hb)
  · rfl

/-- **The pipeline invariant**: the executable profile check, and validity. -/
structure ExeInv (m : BModule) : Prop where
  prof : profileOk m = true
  ok : m.Ok

theorem ExeInv.inGcProfile {m : BModule} (h : ExeInv m) : m.inGcProfile = true := by
  have := h.prof
  simp only [profileOk, Bool.and_eq_true] at this
  exact this.1

/-- The pipeline profile's function types are GC-slice types. -/
theorem typesInGcProfile_of_typesInProfile {m : BModule} (h : typesInProfile m = true) :
    typesInGcProfile m = true := by
  unfold typesInProfile at h
  unfold typesInGcProfile
  refine List.all_eq_true.mpr fun st hst => ?_
  have := List.all_eq_true.mp h st hst
  split
  · next ft hb =>
    rw [hb] at this
    exact List.all_eq_true.mpr fun t ht => gcValType_of_sig (List.all_eq_true.mp this t ht)
  · rfl

/-- The pipeline profile passes the profile check. -/
theorem profileOk_of_inProfile {m : BModule} (hp : m.inProfile = true)
    (ht : typesInProfile m = true) : profileOk m = true := by
  simp only [profileOk, Bool.and_eq_true]
  exact ⟨BModule.inGcProfile_of_inProfile hp, typesInGcProfile_of_typesInProfile ht⟩


/-! ## The contract of the executable pipeline -/

section PassAPI

open PassAPI

variable (o : GrowKind → Nat → Nat → Nat → Bool) (H : Type)

/-- The semantic domain: `ExportEquiv Eq` under the closed host. -/
abbrev exeDomain : Domain Module := equivDomain (Profile.deterministic o) (closedHost (H := H))

/-- The IR of the executable pipeline: Binaryen modules, denotation `lower`, invariant
`ExeInv`. -/
abbrev exeIR : IR (exeDomain o H) := birIR (exeDomain o H) ExeInv

/-- **The contract of the executable pipeline.** -/
abbrev ExeC : PassAPI.Contract BModule := (exeIR o H).contract

theorem exeC_rel {a b : BModule} : (ExeC o H).Rel a b ↔ EE H o b a := Iff.rfl

/-- What a stage must prove: on `ExeInv` inputs, the output is valid and
export-equivalent to the input. (The profile part of the invariant is checked at run
time by `guardedP`, not proved.) -/
def StageOk (pass : BModule → BModule) : Prop :=
  ∀ m, ExeInv m → (pass m).Ok ∧ EE H o (pass m) m

variable {o H}

/-- **A profile-guarded stage as a pass**: `Pass.ofOption` of "run `pass`, keep the
result if it passes `profileOk`". -/
def guardedP (pass : BModule → BModule) (h : StageOk o H pass) : Pass (ExeC o H) :=
  Pass.ofOption (fun m => if profileOk (pass m) then some (pass m) else none)
    (fun {m y} hm e => by
      by_cases hc : profileOk (pass m) = true
      · simp only [hc, ite_true, Option.some.injEq] at e
        subst e
        exact ⟨hc, (h m hm).1⟩
      · simp [hc] at e)
    (fun {m y} hm e => by
      by_cases hc : profileOk (pass m) = true
      · simp only [hc, ite_true, Option.some.injEq] at e
        subst e
        exact (h m hm).2
      · simp [hc] at e)

/-- The run function of a guarded pass is the executable `guarded`. -/
theorem guardedP_run (pass : BModule → BModule) (h : StageOk o H pass) :
    (guardedP pass h).run = guarded pass := by
  funext m
  show ((if profileOk (pass m) then some (pass m) else none).getD m) = guarded pass m
  unfold guarded
  split <;> rfl

end PassAPI

end Silmaril.Wasm.Binaryen.Exe
