module

public import Silmaril.Wasm.Unified.Versions.OwnV.Defs
public import Silmaril.Wasm.Unified.Versions.Defs
public import Silmaril.Raw.Wasm.Unified.Own.SimL
public import Silmaril.Raw.Wasm.Unified.Own.Sim20

/-!
# The versions' own semantics refine the reducts of Core 3.0

The own models of `Silmaril.Wasm.Unified.Versions.OwnV` (silmaril's own Lime1, 1.0 and 2.0 machines
running own code, read through the own opcode algebras) are related to the reducts of the Core 3.0
model `model30` by **refinement**, at the Core image of the own point and frame:

* `cohL`, `coh10`, `coh20`: the own syntaxes are coherent, so the own meaning of code is the
  preimage of its Core meaning (`Own.mem_evalCode`);
* `codeSimL`, `codeSim10`, `codeSim20`: code-level simulations (own runs of own code are Core runs
  of its translation), from the copied configuration simulations (`Lime1.Execution.Sim`,
  `V1.Execution.Steps.toLime`, `V2.Execution.Sim`);
* **`lime1own_refines`**: `lime1ownAt okJ f p` refines `lime1At f.toCore okc p` (the Lime1 version
  model of `Versions`, the reduct of `model30` at `Lime1Core.ptCore p`);
* **`v20own_refines`**: `v20ownAt P okJ f p` refines `v20At P f.toCore okc p`, at every profile;
* **`v10own_refines`**: `v10ownAt okJ f p` refines the 1.0 reduct of `model30` at the **Lime1
  route** image of `p` (`Lime1Core.ptCore (V10.limeStore p, V10.limeHost p)`). The version model
  `v10At` sits at the 2.0 route image `V2Core.ptCore (V10.ptV2 p)` (the point map of `v10Emb`);
  relating the own 1.0 model to `v10At` itself needs a code-level 1.0 → 2.0 simulation, not
  built.

The hypotheses are the domains of the own models (`Lime1Core.dom`, `V2Core.dom`), that the frame's
module names allocated functions (`ModWF`), and that own validation implies Core validation of the
translation (`okJ ⇒ okc`, trivial for `okTrue`). The converse refinement fails
(`Silmaril.Wasm.Unified.Versions.OwnNeq`).

New statements over the proofs in `Silmaril/Raw/Wasm/Unified/Own`.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions.Own

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime Silmaril.Wasm.Unified Silmaril.Wasm.Unified.Core30
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Models

variable {H : Type}

theorem cohL : synL.Coh := Silmaril.Raw.Wasm.Unified.Own.cohL

theorem coh10 : syn10.Coh := Silmaril.Raw.Wasm.Unified.Own.coh10

theorem coh20 : syn20.Coh := Silmaril.Raw.Wasm.Unified.Own.coh20

/-- Lime1 code runs are Core runs. -/
theorem codeSimL {okJ : List Lime1.Instr → Prop} {okc : List Instr → Prop}
    (hok : ∀ js, okJ js → okc (js.map Lime1.Instr.toCore)) {p : Lime1Core.Pt H} {f : Frame}
    (hp : Lime1Core.dom p) (hm : Lime1.Execution.ModWF p.1 f.module) :
    CodeSim synL okJ (behL p.2 p.1 f) Profile.spec (Lime1Core.liftHostC p.2) p.1.toCore f.toCore
      okc :=
  Silmaril.Raw.Wasm.Unified.Own.codeSimL hok hp.1 hm hp.2.1 hp.2.2

/-- 1.0 code runs are Core runs (through Lime1). -/
theorem codeSim10 {okJ : List V1.Instr → Prop} {okc : List Instr → Prop}
    (hok : ∀ js, okJ js → okc (js.map fun j => j.toLime.toCore)) {p : V10.Pt H} {f : Frame}
    (hp : Lime1Core.dom (V10.limeStore p, V10.limeHost p))
    (hm : Lime1.Execution.ModWF (V10.limeStore p) f.module) :
    CodeSim syn10 okJ (beh10 p.2 p.1 f) Profile.spec (Lime1Core.liftHostC (V10.limeHost p))
      (V10.limeStore p).toCore f.toCore okc :=
  Silmaril.Raw.Wasm.Unified.Own.codeSim10 hok hp.1 hm hp.2.1 hp.2.2

/-- 2.0 code runs are Core runs, at every profile. -/
theorem codeSim20 (P : Profile) {okJ : List V2.Instr → Prop} {okc : List Instr → Prop}
    (hok : ∀ js is, syn20.Tr js is → okJ js → okc is) {p : V2Core.Pt H}
    {X : V2Core.CStore H} (hp : V2Core.dom p) (hX : V2.Execution.Store.toCore p.1 = some X)
    {f : V2.Execution.Frame} (hm : V2.Execution.ModWF p.1 f.module) :
    CodeSim syn20 okJ (beh20 P p.2 p.1 f) P (V2Core.liftHost p.2) X f.toCore okc :=
  Silmaril.Raw.Wasm.Unified.Own.codeSim20 P hok hp.1 hX hm hp.2.2.1 hp.2.2.2

/-- **Lime1's own semantics refines the Lime1 version model** (the reduct of `model30`). -/
theorem lime1own_refines {okJ : List Lime1.Instr → Prop} {okc : List Instr → Prop}
    (hok : ∀ js, okJ js → okc (js.map Lime1.Instr.toCore)) {p : Lime1Core.Pt H} {f : Frame}
    (hp : Lime1Core.dom p) (hm : Lime1.Execution.ModWF p.1 f.module) :
    Refines (lime1ownAt okJ f p) (lime1At f.toCore okc p) :=
  refines_reduct cohL (codeSimL hok hp hm) _

/-- **Wasm 1.0's own semantics refines the 1.0 reduct of `model30`** at the Lime1 image. -/
theorem v10own_refines {okJ : List V1.Instr → Prop} {okc : List Instr → Prop}
    (hok : ∀ js, okJ js → okc (js.map fun j => j.toLime.toCore)) {p : V10.Pt H} {f : Frame}
    (hp : Lime1Core.dom (V10.limeStore p, V10.limeHost p))
    (hm : Lime1.Execution.ModWF (V10.limeStore p) f.module) :
    Refines (v10ownAt okJ f p)
      (coreSAt v10 Profile.spec f.toCore okc (Lime1Core.ptCore (V10.limeStore p, V10.limeHost p))) :=
  refines_reduct coh10 (codeSim10 hok hp hm) _

/-- **Wasm 2.0's own semantics refines the 2.0 version model** (the reduct of `model30`), at
every profile. -/
theorem v20own_refines (P : Profile) {okJ : List V2.Instr → Prop} {okc : List Instr → Prop}
    (hok : ∀ js is, syn20.Tr js is → okJ js → okc is) {p : V2Core.Pt H} (hp : V2Core.dom p)
    {f : V2.Execution.Frame} (hm : V2.Execution.ModWF p.1 f.module) :
    Refines (v20ownAt P okJ f p) (v20At P f.toCore okc p) := by
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp hp.2.1
  have e : V2Core.ptCore p = (X, V2Core.liftHost p.2) := V2Core.ptCore_eq hX
  unfold v20At coreSAt at30
  rw [e]
  exact refines_reduct coh20 (codeSim20 P hok hp hX hm) _

end Silmaril.Wasm.Unified.Versions.Own
