module

public import Silmaril.Proofs.Wasm.Models.FXRenameSim.BackBehaviours

/-!
# The exception-address renaming simulation of Core 3.0: `Task.exnRenameBisim` proved

`Task.exnRenameBisim` (`Silmaril.Wasm.Models.FXRename`) asks that host-free Core behaviours commute
with the renaming `rnIdx n` of exception addresses over an `ExnRen n` target store. (pass
5) froze it and proved only the parametric, numeric and vector leaves. This module proves it:

* **`step_rn`** (forward): every host-free Core step of `c` is matched by one step of the renamed
  configuration `⟨t, rnFrame n c.frame, rnAdmins n c.code⟩`, reaching the renamed successor over
  an `ExnRen n` store. It covers the variable, reference, table, memory and aggregate families
  (`Silmaril.Proofs.Wasm.Models.FXRenameSim.Leaf`, `…Aggregate`), the control rules (blocks,
  branches, calls and tail calls, `throw`, `throw_ref` and the handler rules, traps) and the four
  contexts (`…Step`);
* **`step_rn_back`** (backward): every step of the renamed configuration is the renamed image of
  a step of `c` (`…Inv` reads renamed code and stores back; the case analyses are
  `Silmaril.Proofs.Wasm.Models.FXRenameSim.BackLeaf`, `…BackTable`, `…BackAggregate` and
  `…BackStep`). The renaming is a lock-step bisimulation;
* `behaviours_rn_sub`, `behaviours_rn_sup`, **`behaviours_rn_eq`**: the behaviours of the
  renamed configuration (results, traps, escaping exceptions, divergence) are exactly the renamed
  behaviours;
* **`exnRenameBisim_holds : Task.exnRenameBisim`**;
* **`abort_rename'`**: the abortive lowering, every continuation, up to exception renaming,
  without conditions (an earlier `abort_rename` assumed the task).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXRenameSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAbort
open Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

/-- **The forward renaming simulation, one step.** -/
theorem step_rn {H : Type} {P : Profile} {n : Nat} {c c' : Config H} (hs : Step P noHost c c')
    {t : Store H} (h : ExnRen n c.store t) :
    ∃ t', Step P noHost ⟨t, rnFrame n c.frame, rnAdmins n c.code⟩
        ⟨t', rnFrame n c'.frame, rnAdmins n c'.code⟩ ∧ ExnRen n c'.store t' :=
  Silmaril.Proofs.Wasm.Models.FXRenameSim.step_rn hs h

/-- **The forward half of `Task.exnRenameBisim`.** -/
theorem behaviours_rn_sub {H : Type} {P : Profile} {n : Nat} {c : Config H} {t : Store H}
    (h : ExnRen n c.store t) :
    rnBeh n '' behavioursOf P noHost c ⊆
      behavioursOf P noHost ⟨t, rnFrame n c.frame, rnAdmins n c.code⟩ :=
  Silmaril.Proofs.Wasm.Models.FXRenameSim.behaviours_rn_sub h

/-- **The backward renaming simulation, one step.** -/
theorem step_rn_back {H : Type} {P : Profile} {n : Nat} {c : Config H} {t : Store H}
    (h : ExnRen n c.store t) {d : Config H}
    (hs : Step P noHost ⟨t, rnFrame n c.frame, rnAdmins n c.code⟩ d) :
    ∃ (c' : Config H) (t' : Store H), Step P noHost c c' ∧
      d = ⟨t', rnFrame n c'.frame, rnAdmins n c'.code⟩ ∧ ExnRen n c'.store t' :=
  Silmaril.Proofs.Wasm.Models.FXRenameSim.step_rn_back hs h rfl

/-- **The renaming simulation on behaviours.** -/
theorem behaviours_rn_eq {H : Type} {P : Profile} {n : Nat} {c : Config H} {t : Store H}
    (h : ExnRen n c.store t) :
    behavioursOf P noHost ⟨t, rnFrame n c.frame, rnAdmins n c.code⟩ =
      rnBeh n '' behavioursOf P noHost c :=
  Silmaril.Proofs.Wasm.Models.FXRenameSim.behaviours_rn_eq h

/-- **`Task.exnRenameBisim` holds.** -/
theorem exnRenameBisim_holds : Task.exnRenameBisim :=
  fun _ _ _ _ _ h => behaviours_rn_eq h

/-- **The abortive lowering, every continuation, up to exception renaming** (unconditional):
each behaviour of the source, with exception addresses from `s.exns.length` on renamed, is a
behaviour of the target. -/
theorem abort_rename' {H : Type} {P : Profile} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {hs : List HClause} {W : List Val} {x : TagIdx}
    {ks : List Instr} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
    (hn : W.length = ts.length)
    (hcl : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0)
    (hsb : StoreBelow s.exns.length s) (hfb : FrameBelow s.exns.length f)
    (hWb : ∀ v ∈ W, ValBelow s.exns.length v) :
    rnBeh s.exns.length '' behavioursFX' P noHost noFX ⟨s, K, f, abortSrc hs W x ks⟩ ⊆
      behavioursOf P noHost ⟨s, f, abortTgt W x l ks⟩ := by
  have hsrc : behavioursFX' P noHost noFX ⟨s, K, f, abortSrc hs W x ks⟩ =
      behavioursOf P noHost ⟨s, f, abortJoin W ks⟩ :=
    Silmaril.Wasm.Models.FXVRuns.abort_src_behaviours_eq ht hcl hl
  have hren : rnBeh s.exns.length '' behavioursOf P noHost ⟨s, f, abortJoin W ks⟩ ⊆
      behavioursOf P noHost ⟨s.addExn ⟨ta, W⟩, f, abortJoin W ks⟩ := by
    have h := behaviours_rn_sub (P := P) (c := ⟨s, f, abortJoin W ks⟩)
      (exnRen_addExn hsb ⟨ta, W⟩)
    rwa [join_renamed hfb hWb] at h
  rw [hsrc]
  exact hren.trans (Silmaril.Wasm.Models.FXAbort.tgt_behaviours_sup ht he hn hl)

/--
info: 'Silmaril.Wasm.Models.FXRenameSim.abort_rename'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abort_rename'

/--
info: 'Silmaril.Wasm.Models.FXRenameSim.exnRenameBisim_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exnRenameBisim_holds

end Silmaril.Wasm.Models.FXRenameSim
