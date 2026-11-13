module

public import Silmaril.Wasm.Models.FX.Thms
public import Silmaril.Wasm.Models.FXV.Thms
public import Silmaril.Wasm.Models.FXAbort.Thms
public import Silmaril.Wasm.Models.FXLower.Thms

/-!
# The corrected WasmFX model: `StepFX'` as a Wasm model, conservative over Core 3.0

`StepFX` (`Silmaril.Wasm.Models.FX`) has a defect: continuation references are not values, so a
continuation cannot cross a label (`suspend_to_label_stuck`). `StepFX'`
(`Silmaril.Wasm.Models.FXV`) is the corrected relation, an inductive next to `StepFX`. This module
turns it into a model of the institution, next to `fxModel`, and carries the model-level results
of `fxModel` over:

* `fxModel' P H`: CoreFX with continuation values as a Wasm model (`feats = wasmFX`), with the
  same modules, points, calls and domain as `fxModel P H`, observing `behavioursFX'`;
* **`fxEmb' P H : (coreModel P H v30).Emb (fxModel' P H)`**, direction `eq` (conservativity
  over Core 3.0, from `behavioursFX'_ofCoreK`), with its equality transition `fxTrans'`, the
  realiser `fxRealiser'`, the identity comorphism `fxCoHom'` of behavioural institutions and the
  comorphism of game institutions `fxGInstCoHom'`;
* **`fxFix P H : (fxModel P H).Emb (fxModel' P H)`**, direction `sub` (identity on modules,
  points and calls; from `behavioursFX_incl`): every observation of the defective model is one
  of the corrected model;
* `fxFix_conservative_core`: on points without FX functions the two models observe the same
  (both are Core 3.0);
* **`fxFix_proper`**: the correction is proper. The smallest abortive handler, whose body
  suspends at once, has no `StepFX` behaviours after its first step, but under `StepFX'` the
  source itself returns the payload.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXVModel

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Compile.Category Silmaril.Wasm.Category
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **The corrected CoreFX model** (continuation references are values) at profile `P`. -/
def fxModel' (P : Profile) (H : Type) : WasmModel where
  feats := wasmFX
  Module := Silmaril.Wasm.Module
  Valid := ValidIn wasmFX
  Pt := Pt H
  Call := Core.Call
  Obs := Behaviour Val
  obs p c := behavioursFX' P p.2.1 p.2.2 (ofCore (invoke p.1 c.1 c.2))
  dom p := coreDom wasmFX (p.1, p.2.1)

/-- Core configurations have their Core behaviours under `StepFX'` (no FX functions). -/
theorem behavioursFX'_ofCore (P : Profile) (host : HostSemantics H) (c : Config H) :
    behavioursFX' P host noFX (ofCore c) = behavioursOf P host c :=
  behavioursFX'_ofCoreK [] c

/-- **The embedding `core|v30 → CoreFX'`** (direction `eq`). -/
def fxEmb' (P : Profile) (H : Type) : (coreModel P H v30).Emb (fxModel' P H) where
  mod m := m
  valid _ hm := validIn_mono v30_le_wasmFX hm
  pt p := (p.1, p.2, noFX)
  call c := c
  readback := some
  dom _ hp := coreDom_mono v30_le_wasmFX hp
  dir := .eq
  sat p _ c := (WasmModel.view_some (fxModel' P H) (p.1, p.2, noFX) c).trans
    (behavioursFX'_ofCore P p.2 (invoke p.1 c.1 c.2))

theorem fxEmb'_dir (P : Profile) (H : Type) : (fxEmb' P H).dir = .eq := rfl

/-- The read-back of `fxEmb'` is total (the identity). -/
def fxEmb'Total (P : Profile) (H : Type) : (fxEmb' P H).Total := ⟨id, fun _ => rfl⟩

/-- **The equality transition** of `fxEmb'`. -/
def fxTrans' (P : Profile) (H : Type) :
    Transition (coreModel P H v30).chart ((fxModel' P H).viewChart some) :=
  (fxEmb' P H).toTransition

/-- `core|v30 → CoreFX'` is a realiser. -/
def fxRealiser' (P : Profile) (H : Type) :
    Realiser (coreModel P H v30).lang (fxModel' P H).lang :=
  (fxEmb' P H).realiser (fxEmb'Total P H) Function.injective_id rfl

/-- **The identity comorphism** `core|v30 → CoreFX'` of behavioural institutions. -/
def fxCoHom' (P : Profile) (H : Type) :
    Silmaril.Logic.Institution.Inst.CoHom (behInst (coreModel P H v30).lang)
      (behInst (fxModel' P H).lang) :=
  (fxEmb' P H).coHom (fxEmb'Total P H) Function.injective_id rfl

/-- The comorphism of game institutions of `fxEmb'`. -/
def fxGInstCoHom' (P : Profile) (H : Type) :
    Silmaril.Logic.Institution.Inst.CoHom (coreModel P H v30).ginst (fxModel' P H).ginst :=
  (fxEmb' P H).ginstCoHom (fxEmb'Total P H)

/-- **The correction as an embedding** `CoreFX → CoreFX'` (direction `sub`): identity on
modules, points and calls. -/
def fxFix (P : Profile) (H : Type) : (fxModel P H).Emb (fxModel' P H) where
  mod m := m
  valid _ hm := hm
  pt p := p
  call c := c
  readback := some
  dom _ hp := hp
  dir := .sub
  sat _ _ _ := fun b hb => ⟨b, behavioursFX_incl _ hb, rfl⟩

theorem fxFix_dir (P : Profile) (H : Type) : (fxFix P H).dir = .sub := rfl

/-- The read-back of `fxFix` is total (the identity). -/
def fxFixTotal (P : Profile) (H : Type) : (fxFix P H).Total := ⟨id, fun _ => rfl⟩

/-- The comorphism of game institutions of the correction. -/
def fxFixGInstCoHom (P : Profile) (H : Type) :
    Silmaril.Logic.Institution.Inst.CoHom (fxModel P H).ginst (fxModel' P H).ginst :=
  (fxFix P H).ginstCoHom (fxFixTotal P H)

/-- On points without FX functions the two models observe the same: both are Core 3.0. -/
theorem fxFix_conservative_core (P : Profile) (s : Store H) (host : HostSemantics H)
    (c : Core.Call) :
    (fxModel P H).obs (s, host, noFX) c = (fxModel' P H).obs (s, host, noFX) c := by
  show behavioursFX P host noFX _ = behavioursFX' P host noFX _
  rw [behavioursFX_conservative, behavioursFX'_ofCore]

/-- **The correction is proper.** In the smallest abortive handler (its body suspends at once),
the defective model's `suspend` step reaches the branch that carries the continuation, and that
configuration has no behaviours at all; the corrected model runs the same source to its end and
returns the payload `W`. -/
theorem fxFix_proper {P : Profile} {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {hs : List HClause} {W : List Val} {x : TagIdx} {ta : Nat} {ti : TagInst}
    {ts : Ty (.list .val)} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
    (hn : W.length = ts.length)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0) :
    let y : ConfigFX H := ⟨s, K ++ [some ⟨Ctx.hole.plug⟩], f,
      [.label (W.length + 1) [.core .drop] (cvals W ++ .contRef K.length :: [.core (.plain (.br l))])]⟩
    StepFX P Silmaril.Wasm.SingleThreaded.Det.noHost noFX
        ⟨s, K, f, Silmaril.Wasm.Models.FXAbort.abortSrc hs W x []⟩ y ∧
      behavioursFX P Silmaril.Wasm.SingleThreaded.Det.noHost noFX y = ∅ ∧
      Behaviour.returns W ∈ behavioursFX' P Silmaril.Wasm.SingleThreaded.Det.noHost noFX
        ⟨s, K, f, Silmaril.Wasm.Models.FXAbort.abortSrc hs W x []⟩ :=
  ⟨Silmaril.Wasm.Models.FXLower.suspend_to_label (n := W.length + 1) (k := [.core .drop]) ht hc,
    Silmaril.Wasm.Models.FXLower.suspend_to_label_stuck s _ f _ _ W K.length l,
    (Silmaril.Wasm.Models.FXAbort.abort_returns ht he hn hc hl).1⟩

/-- info: 'Silmaril.Wasm.Models.FXVModel.fxFix_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fxFix_proper

end Silmaril.Wasm.Models.FXVModel
