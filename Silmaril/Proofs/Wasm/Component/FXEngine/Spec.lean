module

public import Silmaril.Proofs.Wasm.Component.FXEngine.Sim

/-!
# On numeric modules the canonical-ABI specification over the FX engine is that over Core 3.0

Proofs for `Silmaril.Wasm.Component.FXEngine.Thms` (`exportSpecE_ofNum`).

* `diverges_core_SFX`, `diverges_of_SFX`: a Core thread in an `SFX` store diverges in the FX
  engine exactly when it diverges in `core3P P` (`InfiniteTrace.map`/`of_map` along
  `internalFX_core_SFX_iff`);
* `engineOut_SFX`, `engineDiverges_SFX`: the outcomes and the divergence of an export call of
  the FX instance `⟨SFX I.store, I.addrs⟩` are those of the `core3P P` instance `I`;
* `exportSpecE_ofNum`: so `exportSpecE (fxE P) ofNum = exportSpecE (core3P P) NumModule.mod`
  (with `instOf_ofNum`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXEngine

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine
open Silmaril.Wasm.Component.Reference (NumModule core3P Simple SimpleExport)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (Thread)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps Diverges)
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

/-- The FX image of a Core 3.0 configuration. -/
abbrev toFX (x : Store Nat × Thread) : Store (FXCode Nat) × ThreadFX Nat :=
  (SFX x.1, ThreadFX.core x.2)

/-- A Core 3.0 divergence is an FX divergence of the image. -/
theorem diverges_core_SFX {s : Store Nat} {t : Thread} (h : Diverges (core3P P) (s, t)) :
    Diverges (fxE P) (SFX s, ThreadFX.core t) :=
  Silmaril.InfiniteTrace.map toFX
    (fun x y hxy => internalFX_core_SFX (s := x.1) (t := x.2) (s' := y.1) (t' := y.2) hxy) h

/-- An FX divergence of a Core thread in an `SFX` store is a Core 3.0 divergence. -/
theorem diverges_of_SFX {s : Store Nat} {t : Thread}
    (h : Diverges (fxE P) (SFX s, ThreadFX.core t)) : Diverges (core3P P) (s, t) :=
  Silmaril.InfiniteTrace.of_map (a := (s, t)) toFX (fun _ => True)
    (fun x y _ hxy => by
      obtain ⟨s', t', rfl, h'⟩ := internalFX_core_SFX_iff.1 hxy
      exact ⟨(s', t'), h', trivial, rfl⟩) trivial h

/-- The FX image of a Core 3.0 engine instance. -/
abbrev instFX (I : EInstance (core3P P)) : EInstance (fxE P) := ⟨SFX I.store, I.addrs⟩

/-- **Export calls of the FX image of an instance have the Core 3.0 outcomes.** -/
theorem engineOut_SFX (I : EInstance (core3P P)) (k : Nat) (xs : List Flat) :
    engineOut (fxE P) (instFX I) k xs = engineOut (core3P P) I k xs := by
  ext r
  constructor
  · rintro ⟨a, s', t', ha, hrun, hst⟩
    obtain ⟨s₂, t₂, he, hrun'⟩ := steps_of_SFX (P := P) (s := I.store)
      (t := (core3P P).invoke a xs) hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have hs : (fxE P).status (SFX s₂) (ThreadFX.core t₂) = (core3P P).status s₂ t₂ :=
      statusFX_core_SFX s₂ t₂
    rw [hs] at hst
    exact ⟨a, s₂, t₂, ha, hrun', hst⟩
  · rintro ⟨a, s', t', ha, hrun, hst⟩
    have hs : (fxE P).status (SFX s') (ThreadFX.core t') = (core3P P).status s' t' :=
      statusFX_core_SFX s' t'
    refine ⟨a, SFX s', ThreadFX.core t', ha, ?_, ?_⟩
    · exact steps_core_SFX hrun
    · rw [hs]
      exact hst

/-- **Export calls of the FX image of an instance diverge exactly when the Core 3.0 ones do.** -/
theorem engineDiverges_SFX (I : EInstance (core3P P)) (k : Nat) (xs : List Flat) :
    engineDiverges (fxE P) (instFX I) k xs ↔ engineDiverges (core3P P) I k xs := by
  constructor
  · rintro ⟨a, ha, hd⟩
    exact ⟨a, ha, diverges_of_SFX (P := P) (s := I.store) (t := (core3P P).invoke a xs) hd⟩
  · rintro ⟨a, ha, hd⟩
    exact ⟨a, ha, diverges_core_SFX hd⟩

/-- **On numeric modules the canonical-ABI specification over the FX engine is the one over
Core 3.0.** -/
theorem exportSpecE_ofNum (c : Simple) (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val) :
    exportSpecE (fxE P) ofNum c x vs = exportSpecE (core3P P) NumModule.mod c x vs := by
  unfold exportSpecE
  cases checkLower x.ty.params vs with
  | none => rfl
  | some xs =>
    dsimp only
    rw [show instOf (fxE P) (ofNum c.mod) (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
        (instOf (core3P P) c.mod.mod (CoreModule.imports c.mod) (CoreModule.exports c.mod)).map
          instFX from instOf_ofNum c.mod]
    cases instOf (core3P P) c.mod.mod (CoreModule.imports c.mod) (CoreModule.exports c.mod) with
    | none => simp
    | some I =>
      simp only [Option.map_some, Option.some.injEq, exists_eq_left', engineOut_SFX,
        engineDiverges_SFX]

end Silmaril.Proofs.Wasm.Component.FXEngine
