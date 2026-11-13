module

public import Silmaril.Proofs.Wasm.Component.FXTypedEx.Inst
public import Silmaril.Proofs.Wasm.Component.FXTyped.Arity
public import Silmaril.Proofs.Wasm.Component.FXEngineV.Vals

/-!
# An ill-typed FX function: `badC` is not `Typed`

`badC`'s FX function `bad : [] → [i32]` has the body `i64.const 0`. In the `fxEV P` engine
instance of its module (`badHJ`, kernel-evaluated), the call of `bad` enters the function
(`internalV_enter`), leaves its label and its frame, and returns `[i64 0]` (`bad_run`,
`bad_status`). So `some [i64 0]` is an engine outcome of the export `bad: func() -> u32`, whose
flat result type is `i32`: **`¬ badC.Typed P`** at every profile, although `badC` meets `Good`,
`FloatFree`, `Inst` and `Arity` (`Inst.lean`). Arity holds (one value for one result,
`arityAt_fx`); only the type is wrong.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXTypedEx

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX (AdminFX FuncFX cvals)
open Silmaril.Wasm.Models.FXV (StepFX' FVal fvals)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.FXEngine
  Silmaril.Wasm.Component.FXEngineV Silmaril.Wasm.Component.FXRefV Silmaril.Wasm.Component.FXTypedEx
open Silmaril.Proofs.Wasm.Component.FXTyped (FXAt internalV_enter enterCode)
open Silmaril.Wasm.Numerics (Profile)

/-- The instantiation of `badC`'s module. -/
def badPrep : Option (Store (FXCode Nat) × InstFX × Option Nat) :=
  prepareFXV? {} (badC.emb badC.mod) []

/-- Its store. -/
def badS : Store (FXCode Nat) := (badPrep.map (·.1)).getD {}

/-- Its instance. -/
def badI : InstFX := (badPrep.map (·.2.1)).getD ⟨{}, []⟩

/-- The FX function `bad`, in the instance seen by FX code. -/
abbrev badF : FuncFX := badDecl.func (fxInst badI.core 0 1)

theorem badPrep_eq : badPrep = some (badS, badI, none) := by rfl

theorem bad_fxAt : FXAt badS 0 badF badDecl.type := ⟨by rfl, rfl⟩

/-- **The engine instance of `badC`'s module.** -/
theorem badHJ (P : Profile) :
    instOf (fxEV P) (badC.emb badC.mod) [] badC.mod.exports = some ⟨badS, [(0 : Nat)]⟩ := by
  unfold instOf
  rw [show (fxEV P).prepare? = prepareFXV? from rfl]
  change (match badPrep with | some (s', inst, none) => _ | _ => none) = _
  rw [badPrep_eq]
  rfl

/-- `i64 0`. -/
abbrev v0 : Execution.Core.Val := .num ⟨.int .i64, 0⟩

/-- The frame of `bad`. -/
abbrev frB : Frame := Frame.forCall badF.module [] badF.locals

/-- **The run of `bad`**: enter, leave the label, leave the frame. -/
theorem bad_run (P : Profile) :
    Silmaril.Wasm.Component.Engine.CoreEngine.Steps (fxEV P) (badS, (fxEV P).invoke (0 : Nat) [])
      (badS, ThreadV.fx [] {} (cvals [v0])) := by
  have e0 := internalV_enter (P := P) bad_fxAt (xs := []) rfl
  have e1 : StepFX' P (noHostFX Nat) fxOf
      ⟨badS, [], {}, [enterCode badF (([] : List Flat).map SingleThreaded.ofFlat)]⟩
      ⟨badS, [], {}, [.frame 1 frB (fvals [.val v0])]⟩ :=
    .ctxFrame (.labelVals (vs := [.val v0]))
  have e2 : StepFX' P (noHostFX Nat) fxOf ⟨badS, [], {}, [.frame 1 frB (fvals [.val v0])]⟩
      ⟨badS, [], {}, cvals [v0]⟩ :=
    .frameVals (vs := [.val v0]) rfl
  have i1 : InternalV P
      (badS, .fx [] {} [enterCode badF (([] : List Flat).map SingleThreaded.ofFlat)])
      (badS, .fx [] {} [.frame 1 frB (fvals [.val v0])]) := Or.inl ⟨_, _, _, rfl, e1⟩
  have i2 : InternalV P (badS, .fx [] {} [.frame 1 frB (fvals [.val v0])])
      (badS, .fx [] {} (cvals [v0])) := Or.inl ⟨_, _, _, rfl, e2⟩
  exact .head e0 <| .head i1 <| .single i2

/-- **The final status**: returned `[i64 0]`. -/
theorem bad_status (P : Profile) :
    (fxEV P).status badS (ThreadV.fx [] {} (cvals [v0])) =
      .returned (.values [⟨.int .i64, 0⟩]) :=
  (Silmaril.Proofs.Wasm.Component.FXEngineV.statusV_vals' (P := P) badS [] {} [v0]).trans rfl

/-- **`badC` is not `Typed`**, at every profile. -/
theorem bad_not_typed (P : Profile) : ¬ badC.Typed P := by
  intro ht
  have hm : some [(⟨.int .i64, 0⟩ : Flat)] ∈
      engineOut (fxEV P) ⟨badS, [(0 : Nat)]⟩ 0 (lowerArgs [] []) :=
    ⟨(0 : Nat), badS, _, rfl, bad_run P, Or.inl ⟨_, bad_status P, rfl⟩⟩
  have := ht _ (badHJ P) ⟨"bad", ⟨[], [.u32]⟩, 0⟩ (List.mem_singleton_self _) [] rfl _ hm
  exact absurd this (by decide)

end Silmaril.Proofs.Wasm.Component.FXTypedEx
