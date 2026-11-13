module

public import Silmaril.Wasm.Component.FXSuspend.Defs
public import Silmaril.Wasm.Component.FXEngineV.Thms
public import Silmaril.Proofs.Wasm.Component.FXEngineV.Vals

/-!
# A module whose code suspends: instantiation

Kernel evaluation (`rfl`, `decide +kernel`; no native evaluation) of the instantiation of `exMod`
by `prepareFXV?`: the store holds `sus` at address 0 and `run` at address 1, the tag at
address 0, and the engine instance is `⟨exS, [1]⟩`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXSuspend

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.FXEngine
  Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Component.FXSuspend
open Silmaril.Wasm.Numerics (Profile)

/-- The store after the Core part and `sus`, before `run` is allocated. -/
def exS₂ : Store (FXCode Nat) :=
  ((Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store (FXCode Nat)) tMod []).map
    (fun p => (Silmaril.Wasm.SingleThreaded.allocHost p.1 susDecl.type (.fx susF)).1)).getD {}

theorem prep_eq : exPrep = some (exS, exI, none) := by rfl

theorem exI_funcs : exI'.funcs = [0, 1] := by rfl

theorem exS_f0 : exS.funcs[0]?.map (·.code) = some (.host (.fx susF)) := by rfl

theorem exS_f1 : exS.funcs[1]?.map (·.code) = some (.host (.fx runF)) := by rfl

theorem exS_tag : (exS.tag? (Frame.forCall exI' [] []) ⟨0⟩).map (·.1) = some 0 := by rfl

theorem alloc_eq :
    Silmaril.Wasm.SingleThreaded.allocHost exS₂ runDecl.type (FXCode.fx runF) = (exS, 1) := by
  rfl

theorem hI (P : Profile) : instOf (fxEV P) exMod [] exIface = some ⟨exS, [(1 : Nat)]⟩ := by
  unfold instOf
  rw [show (fxEV P).prepare? = prepareFXV? from rfl]
  change (match exPrep with | some (s', inst, none) => _ | _ => none) = _
  rw [prep_eq]
  rfl

theorem hq (P : Profile) :
    callee? (E := fxEV P) [(1 : Nat)] exIface (⟨0, by decide⟩, .flat []) = some ((1 : Nat), []) := by
  rfl

theorem f0 : ∃ fi, exS.funcs[0]? = some fi ∧ fi.code = .host (.fx susF) := by
  rcases h : exS.funcs[0]? with _ | fi
  · exact absurd (congrArg (Option.map (·.code)) h) (by rw [exS_f0]; simp)
  · have hc : some fi.code = some (.host (.fx susF)) := by simpa [h] using exS_f0
    exact ⟨fi, rfl, Option.some.inj hc⟩

theorem f1 : ∃ fi, exS.funcs[1]? = some fi ∧ fi.code = .host (.fx runF) := by
  rcases h : exS.funcs[1]? with _ | fi
  · exact absurd (congrArg (Option.map (·.code)) h) (by rw [exS_f1]; simp)
  · have hc : some fi.code = some (.host (.fx runF)) := by simpa [h] using exS_f1
    exact ⟨fi, rfl, Option.some.inj hc⟩

theorem tag0 : ∃ ti, exS.tag? (Frame.forCall exI' [] []) ⟨0⟩ = some (0, ti) := by
  rcases h : exS.tag? (Frame.forCall exI' [] []) ⟨0⟩ with _ | ⟨a, ti⟩
  · exact absurd (congrArg (Option.map (·.1)) h) (by rw [exS_tag]; simp)
  · have ha : some a = some 0 := by simpa [h] using exS_tag
    exact ⟨ti, by rw [Option.some.inj ha]⟩

end Silmaril.Proofs.Wasm.Component.FXSuspend
