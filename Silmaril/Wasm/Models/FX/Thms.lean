module

public import Silmaril.Proofs.Wasm.Models.FX.Behaviours
public import Silmaril.Wasm.Models.Realise.Thms
public import Silmaril.Wasm.Models.Game.Defs
public import Silmaril.Wasm.Models.Syntax.Thms
public import Silmaril.Wasm.Models.Charts.Thms

/-!
# CoreFX: conservativity over Core 3.0, as an equality transition and an identity comorphism

The header of the WasmFX extension (track H of
[wasm-models.md](../../../../docs/projects/spectec/README.md), §6). `StepFX` (`Defs`) extends Core 3.0's
`Step` with continuations, handler frames and the six stack-switching instructions.

* **`stepFX_conservative`**: on a Core configuration whose store has no FX functions, the FX
  steps are exactly the images of the Core steps (with the host `blockFX host fx`, which is
  `host` when there are no FX functions at all, `blockFX_noFX`);
* `stepsFX_conservative`, `divergesFX_conservative`, **`behavioursFX_conservative`**: without FX
  functions, CoreFX runs, divergence and behaviours of Core configurations are Core's;
* `fxModel P H`: CoreFX as a Wasm model (`feats = wasmFX`). Its modules are Core modules
  (FX module syntax is not modelled), its points are Core points with an FX function table, and
  its observations are the CoreFX behaviours of `$invoke`;
* **`fxEmb P H : (coreModel P H v30).Emb (fxModel P H)`**, direction `eq`, identity on modules
  and calls, a point gets the empty FX function table; with the identity read-back it is the
  **equality transition** `fxTrans`, the realiser `fxRealiser`, **the identity comorphism**
  `fxCoHom` of behavioural institutions, and the comorphism of game institutions
  `fxGInstCoHom`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models Silmaril.Wasm.Atlas
open Silmaril.Compile.Category Silmaril.Wasm.Category
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **Conservativity, one step**: on a Core configuration whose store has no FX functions, the
CoreFX steps are exactly the images of the Core steps. -/
theorem stepFX_conservative {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
    {c : Config H} (hno : NoFX fx c.store) {y : ConfigFX H} :
    StepFX P host fx (ofCore c) y ↔ ∃ c', Step P (blockFX host fx) c c' ∧ y = ofCore c' :=
  ⟨fun h => Silmaril.Proofs.Wasm.Models.FX.step_ofCore h c rfl hno,
    fun ⟨_, h, hy⟩ => hy ▸ Silmaril.Proofs.Wasm.Models.FX.ofCore_step h⟩

/-- Without FX functions, the Core host is the host. -/
theorem blockFX_noFX (host : HostSemantics H) : blockFX host (noFX (H := H)) = host :=
  Silmaril.Proofs.Wasm.Models.FX.blockFX_noFX host

/-- **Conservativity, runs.** -/
theorem stepsFX_conservative {P : Profile} {host : HostSemantics H} {c : Config H}
    {y : ConfigFX H} :
    StepsFX P host noFX (ofCore c) y ↔ ∃ c', Steps P host c c' ∧ y = ofCore c' :=
  Silmaril.Proofs.Wasm.Models.FX.stepsFX_iff

/-- **Conservativity, divergence.** -/
theorem divergesFX_conservative {P : Profile} {host : HostSemantics H} {c : Config H} :
    Silmaril.InfiniteTrace (StepFX P host noFX) (ofCore c) ↔ Diverges P host c :=
  Silmaril.Proofs.Wasm.Models.FX.divergesFX_iff

/-- **Conservativity, behaviours.** -/
theorem behavioursFX_conservative (P : Profile) (host : HostSemantics H) (c : Config H) :
    behavioursFX P host noFX (ofCore c) = behavioursOf P host c :=
  Silmaril.Proofs.Wasm.Models.FX.behavioursFX_ofCore c

/-! ## The extension is proper -/

/-- **`suspend` under a handler steps**: a handler with clause `(on x l)` around `suspend x`
captures the (empty) context as continuation `K.length` and branches to `l` with it. -/
theorem suspend_step {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
    {s : Store H} {K : List (Option ContFX)} {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst}
    {l : LabelIdx} (ht : s.tag? f x = some (ta, ti)) :
    StepFX P host fx ⟨s, K, f, [.handler [.onLabel ta l] [.fx (.suspend x)]]⟩
      ⟨s, K ++ [some ⟨Ctx.hole.plug⟩], f, [.contRef K.length, .core (.plain (.br l))]⟩ := by
  have h := StepFX.suspend (P := P) (host := host) (fx := fx) (K := K) (E := .hole) (vs := [])
    (hs := [.onLabel ta l]) (l := l) ht (fun h => h) (by simp [HClause.tag])
  simpa [Ctx.plug, cvals, vals] using h

/-- A configuration with FX code is not a Core configuration. -/
theorem ofCore_ne_fx (c : Config H) {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {pre rest : List AdminFX} (i : FXInstr) :
    ofCore c ≠ ⟨s, K, f, pre ++ .fx i :: rest⟩ := by
  intro h
  have h2 := congrArg (fun x : ConfigFX H => x.code.all Silmaril.Proofs.Wasm.Models.FX.isCore) h
  simp [ofCore, Silmaril.Proofs.Wasm.Models.FX.isCore] at h2

/-! ## CoreFX as a Wasm model -/

/-- CoreFX points: a Core point and an FX function table. -/
abbrev Pt (H : Type) := Store H × HostSemantics H × (H → Option FuncFX)

/-- **CoreFX as a Wasm model** at profile `P`. -/
def fxModel (P : Profile) (H : Type) : WasmModel where
  feats := wasmFX
  Module := Silmaril.Wasm.Module
  Valid := ValidIn wasmFX
  Pt := Pt H
  Call := Core.Call
  Obs := Behaviour Val
  obs p c := behavioursFX P p.2.1 p.2.2 (ofCore (invoke p.1 c.1 c.2))
  dom p := coreDom wasmFX (p.1, p.2.1)

/-- **The embedding `core|v30 → CoreFX`** (direction `eq`): identity on modules and calls, and a
Core point with no FX functions. -/
def fxEmb (P : Profile) (H : Type) : (coreModel P H v30).Emb (fxModel P H) where
  mod m := m
  valid _ hm := validIn_mono v30_le_wasmFX hm
  pt p := (p.1, p.2, noFX)
  call c := c
  readback := some
  dom _ hp := coreDom_mono v30_le_wasmFX hp
  dir := .eq
  sat p _ c := (WasmModel.view_some (fxModel P H) (p.1, p.2, noFX) c).trans
    (behavioursFX_conservative P p.2 (invoke p.1 c.1 c.2))

theorem fxEmb_dir (P : Profile) (H : Type) : (fxEmb P H).dir = .eq := rfl

/-- The read-back of `fxEmb` is total (the identity). -/
def fxEmbTotal (P : Profile) (H : Type) : (fxEmb P H).Total := ⟨id, fun _ => rfl⟩

/-- **The equality transition** of `fxEmb`. -/
def fxTrans (P : Profile) (H : Type) :
    Transition (coreModel P H v30).chart ((fxModel P H).viewChart some) :=
  (fxEmb P H).toTransition

/-- `core|v30 → CoreFX` is a realiser. -/
def fxRealiser (P : Profile) (H : Type) :
    Realiser (coreModel P H v30).lang (fxModel P H).lang :=
  (fxEmb P H).realiser (fxEmbTotal P H) Function.injective_id rfl

/-- **The identity comorphism** `core|v30 → CoreFX` of behavioural institutions. -/
def fxCoHom (P : Profile) (H : Type) :
    Silmaril.Logic.Institution.Inst.CoHom (behInst (coreModel P H v30).lang)
      (behInst (fxModel P H).lang) :=
  (fxEmb P H).coHom (fxEmbTotal P H) Function.injective_id rfl

/-- The comorphism of game institutions of `fxEmb`. -/
def fxGInstCoHom (P : Profile) (H : Type) :
    Silmaril.Logic.Institution.Inst.CoHom (coreModel P H v30).ginst (fxModel P H).ginst :=
  (fxEmb P H).ginstCoHom (fxEmbTotal P H)

end Silmaril.Wasm.Models.FX
