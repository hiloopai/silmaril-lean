module

public import Silmaril.Proofs.Wasm.Models.FXAbort.Run

/-!
# Lowering abortive handlers to exceptions: the smallest fragment

The header of the abortive fragment (`Defs`). The source runs under `StepFX'` (continuation
references are values); under track H's `StepFX` the same source is stuck at the branch
(`Silmaril.Wasm.Models.FXLower.suspend_to_label_stuck`).

* **`src_runs`**: `abortSrc hs W x ks` reaches `abortJoin W ks = W; ks`, with the Core store
  unchanged and one dead continuation added (`kAbort K`);
* **`tgt_runs`**: `abortTgt W x l ks` reaches the same code, with one exception
  `⟨ta, W⟩` added to the store;
* `src_behaviours_sup`, `tgt_behaviours_sup`: each side has the Core behaviours of the join (the
  source at `s`, the target at `s.addExn ⟨ta, W⟩`);
* **`abort_returns`**: with nothing after the block, both sides return the payload `W`.

Not proved: that these are *all* the behaviours of each side (the untyped `suspend` may split
`W` between the captured context and the branch, and the other splits must be shown stuck), and
the comparison of the join's behaviours at `s` and at `s.addExn ⟨ta, W⟩` (a later `throw`
returns an exception address one higher in the target, so the relation must rename exception
addresses).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXAbort

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Proofs.Wasm.Models.FXLower (ofCoreK)
open Silmaril.Proofs.Wasm.Models.FXAbort (kAbort)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- **The source reaches the join** (`StepFX'`). -/
theorem src_runs {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
    {W : List Val} {x : TagIdx} {ks : List Instr} {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0) :
    StepsFX' P host fx ⟨s, K, f, abortSrc hs W x ks⟩
      (ofCoreK (kAbort K) ⟨s, f, abortJoin W ks⟩) :=
  Silmaril.Proofs.Wasm.Models.FXAbort.src_runs ht hc hl

/-- **The target reaches the join** (Core), with one more exception. -/
theorem tgt_runs {s : Store H} {f : Frame} {W : List Val} {x : TagIdx}
    {ks : List Instr} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
    (hn : W.length = ts.length) (hl : l.toNat = 0) :
    Steps P host ⟨s, f, abortTgt W x l ks⟩ ⟨s.addExn ⟨ta, W⟩, f, abortJoin W ks⟩ :=
  Silmaril.Proofs.Wasm.Models.FXAbort.tgt_runs ht he hn hl

/-- The source has the join's Core behaviours (no FX functions). -/
theorem src_behaviours_sup {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {hs : List HClause} {W : List Val} {x : TagIdx} {ks : List Instr} {ta : Nat} {ti : TagInst}
    {l : LabelIdx} (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0) :
    behavioursOf P host ⟨s, f, abortJoin W ks⟩ ⊆
      behavioursFX' P host noFX ⟨s, K, f, abortSrc hs W x ks⟩ :=
  Silmaril.Proofs.Wasm.Models.FXAbort.src_behaviours_sup ht hc hl

/-- The target has the join's Core behaviours at the extended store. -/
theorem tgt_behaviours_sup {s : Store H} {f : Frame} {W : List Val} {x : TagIdx}
    {ks : List Instr} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
    (hn : W.length = ts.length) (hl : l.toNat = 0) :
    behavioursOf P host ⟨s.addExn ⟨ta, W⟩, f, abortJoin W ks⟩ ⊆
      behavioursOf P host ⟨s, f, abortTgt W x l ks⟩ :=
  Silmaril.Proofs.Wasm.Models.FXAbort.tgt_behaviours_sup ht he hn hl

/-- **With nothing after the block, both sides return the payload.** -/
theorem abort_returns {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
    {W : List Val} {x : TagIdx} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
    (hn : W.length = ts.length)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0) :
    Behaviour.returns W ∈ behavioursFX' P host noFX ⟨s, K, f, abortSrc hs W x []⟩ ∧
      Behaviour.returns W ∈ behavioursOf P host ⟨s, f, abortTgt W x l []⟩ :=
  Silmaril.Proofs.Wasm.Models.FXAbort.abort_returns ht he hn hc hl

/-- info: 'Silmaril.Wasm.Models.FXAbort.abort_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abort_returns

end Silmaril.Wasm.Models.FXAbort
