module

public import Silmaril.Proofs.Wasm.Models.FXAbortConv.Tgt

/-!
# The abortive lowering: the converse, and equality up to exception renaming

The abortive lowering (`Silmaril.Wasm.Models.FXAbort`) compiles an `(on x l)` handler that drops
its continuation to `try_table (catch x l)`, and `suspend x` to `throw x`. With
`n = s.exns.length`, and stretch an earlier step proved the forward inclusion
`abort_rename'` (`Silmaril.Wasm.Models.FXRenameSim`): every behaviour of the source, renamed by
`rnBeh n`, is a behaviour of the target. This module proves the converse (no host calls, no FX
functions, any profile):

* **`tgt_behaviours_sub`**: the target has a single run to the join: every step of
  `abortTgt W x l ks` and of its two successors is the step of `tgt_runs`, so every behaviour of
  the target is one of `W; ks` at `s.addExn ⟨ta, W⟩`;
* **`abort_rename_conv`**: every behaviour of the target is the renaming of a behaviour of the
  source;
* **`abort_rename_eq`**: so `rnBeh n '' (source behaviours) = target behaviours`.

The renaming step uses `behaviours_rn_eq` (both directions of the exception-address renaming
bisimulation); its backward half is `Silmaril.Proofs.Wasm.Models.FXRenameSim.BackStep`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXAbortConv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAbort
open Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- **The target's behaviours are the join's at the extended store.** -/
theorem tgt_behaviours_sub {s : Store H} {f : Frame} {W : List Val} {x : TagIdx}
    {ks : List Instr} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
    (hn : W.length = ts.length) (hl : l.toNat = 0) :
    behavioursOf P noHost ⟨s, f, abortTgt W x l ks⟩ ⊆
      behavioursOf P noHost ⟨s.addExn ⟨ta, W⟩, f, abortJoin W ks⟩ :=
  Silmaril.Proofs.Wasm.Models.FXAbortConv.tgt_behaviours_sub ht he hn hl

/-- **The converse of the abortive lowering**: every behaviour of the target is the renaming of
a behaviour of the source. -/
theorem abort_rename_conv {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {hs : List HClause} {W : List Val} {x : TagIdx} {ks : List Instr} {ta : Nat} {ti : TagInst}
    {ts : Ty (.list .val)} {l : LabelIdx} (ht : s.tag? f x = some (ta, ti))
    (he : Expand ti.type (.func ts .nil)) (hn : W.length = ts.length)
    (hcl : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0)
    (hsb : StoreBelow s.exns.length s) (hfb : FrameBelow s.exns.length f)
    (hWb : ∀ v ∈ W, ValBelow s.exns.length v) :
    behavioursOf P noHost ⟨s, f, abortTgt W x l ks⟩ ⊆
      rnBeh s.exns.length '' behavioursFX' P noHost noFX ⟨s, K, f, abortSrc hs W x ks⟩ := by
  have hsrc : behavioursFX' P noHost noFX ⟨s, K, f, abortSrc hs W x ks⟩ =
      behavioursOf P noHost ⟨s, f, abortJoin W ks⟩ :=
    Silmaril.Wasm.Models.FXVRuns.abort_src_behaviours_eq ht hcl hl
  have hren : behavioursOf P noHost ⟨s.addExn ⟨ta, W⟩, f, abortJoin W ks⟩ =
      rnBeh s.exns.length '' behavioursOf P noHost ⟨s, f, abortJoin W ks⟩ := by
    have h := Silmaril.Wasm.Models.FXRenameSim.behaviours_rn_eq (P := P)
      (c := ⟨s, f, abortJoin W ks⟩) (exnRen_addExn hsb ⟨ta, W⟩)
    rwa [join_renamed hfb hWb] at h
  rw [hsrc, ← hren]
  exact tgt_behaviours_sub ht he hn hl

/-- **The abortive lowering is exact up to exception renaming**: the renamed behaviours of the
source are the behaviours of the target. -/
theorem abort_rename_eq {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {hs : List HClause} {W : List Val} {x : TagIdx} {ks : List Instr} {ta : Nat} {ti : TagInst}
    {ts : Ty (.list .val)} {l : LabelIdx} (ht : s.tag? f x = some (ta, ti))
    (he : Expand ti.type (.func ts .nil)) (hn : W.length = ts.length)
    (hcl : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0)
    (hsb : StoreBelow s.exns.length s) (hfb : FrameBelow s.exns.length f)
    (hWb : ∀ v ∈ W, ValBelow s.exns.length v) :
    rnBeh s.exns.length '' behavioursFX' P noHost noFX ⟨s, K, f, abortSrc hs W x ks⟩ =
      behavioursOf P noHost ⟨s, f, abortTgt W x l ks⟩ :=
  Set.Subset.antisymm
    (Silmaril.Wasm.Models.FXRenameSim.abort_rename' ht he hn hcl hl hsb hfb hWb)
    (abort_rename_conv ht he hn hcl hl hsb hfb hWb)

/--
info: 'Silmaril.Wasm.Models.FXAbortConv.abort_rename_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abort_rename_eq

end Silmaril.Wasm.Models.FXAbortConv
