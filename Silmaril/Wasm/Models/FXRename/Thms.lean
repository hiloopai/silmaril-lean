module

public import Silmaril.Proofs.Wasm.Models.FXRename.Below
public import Silmaril.Wasm.Models.FXVRuns.Thms
public import Silmaril.Proofs.Wasm.Models.FXRename.Pure

/-!
# Comparing the two sides of the abortive lowering at the join, up to exception renaming

The source of the abortive lowering reaches `W; ks` at its store `s` (`abort_src_behaviours_eq`,
no host calls, no FX functions); the target reaches `W; ks` at `s.addExn ⟨ta, W⟩`
(`tgt_runs`). With `n = s.exns.length`:

* **`exnRen_addExn`**: when every exception address held by `s` is below `n`, the target's store
  is an `ExnRen n` target of `s` (the extra instance sits at `n`, where nothing refers);
* `join_renamed`: the renamed join configuration is the target's join configuration, when the
  frame and the payload hold no exception address from `n` on;
* `Task.exnRenameBisim` (**frozen**): host-free Core behaviours commute with `ExnRen` up to
  `rnBeh`: the renamed configuration over an `ExnRen n` target has exactly the renamed
  behaviours. This is the Core exception-address renaming simulation; it is stated, not proved;
* **`abort_rename`** (conditional on `Task.exnRenameBisim`): every behaviour of the abortive
  source, renamed, is a behaviour of the target, for every continuation `ks`.

First leaves of the simulation (`Silmaril.Proofs.Wasm.Models.FXRename.Pure`): `parametric_rn`,
`numeric_rn`, `vector_rn` (the store-free families). The other families, the control rules and
the contexts are not done.

`abort_returns` covered `ks = []`. The converse inclusion would also need the target's
step inversion (that the target's only runs go through `tgt_runs`), which is not proved.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXRename

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAbort
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

/-- **Frozen target: the Core exception-address renaming simulation.** Host-free Core
behaviours of the renamed configuration over an `ExnRen n` target are the renamed behaviours.
Expected true: `rnIdx n` is injective and avoids `n`, so the extra instance is never reached,
`throw` allocates at `s.exns.length` in the source and at `s.exns.length + 1 = rnIdx n
s.exns.length` in the target, and every lookup of an exception address `a` in the source is a
lookup of `rnIdx n a` in the target. Not proved. -/
def Task.exnRenameBisim : Prop :=
  ∀ (H : Type) (P : Profile) (n : Nat) (c : Config H) (t : Store H), ExnRen n c.store t →
    behavioursOf P noHost ⟨t, rnFrame n c.frame, rnAdmins n c.code⟩ =
      rnBeh n '' behavioursOf P noHost c

/-- The target's store is an `ExnRen` target of the source's. -/
theorem exnRen_addExn {H : Type} {s : Store H} (hb : StoreBelow s.exns.length s) (e : ExnInst) :
    ExnRen s.exns.length s (s.addExn e) :=
  Silmaril.Proofs.Wasm.Models.FXRename.exnRen_addExn hb e

/-- The renamed join is the target's join. -/
theorem join_renamed {H : Type} {s t : Store H} {f : Frame} {W : List Val} {ks : List Instr}
    {n : Nat} (hf : FrameBelow n f) (hW : ∀ v ∈ W, ValBelow n v) :
    (⟨t, rnFrame n (⟨s, f, abortJoin W ks⟩ : Config H).frame,
      rnAdmins n (⟨s, f, abortJoin W ks⟩ : Config H).code⟩ : Config H) =
      ⟨t, f, abortJoin W ks⟩ := by
  have hcode : rnAdmins n (abortJoin W ks) = abortJoin W ks := by
    rw [abortJoin, Silmaril.Proofs.Wasm.Models.FXRename.rnAdmins_append,
      Silmaril.Proofs.Wasm.Models.FXRename.rnAdmins_vals,
      Silmaril.Proofs.Wasm.Models.FXRename.rnAdmins_expression,
      Silmaril.Proofs.Wasm.Models.FXRename.map_rnVal_below hW]
  show (⟨t, rnFrame n f, rnAdmins n (abortJoin W ks)⟩ : Config H) = ⟨t, f, abortJoin W ks⟩
  rw [hcode, Silmaril.Proofs.Wasm.Models.FXRename.rnFrame_below hf]

/-- **The abortive lowering, every continuation, up to exception renaming** (conditional on
`Task.exnRenameBisim`): each behaviour of the source, with exception addresses from
`s.exns.length` on renamed, is a behaviour of the target. -/
theorem abort_rename (hT : Task.exnRenameBisim) {H : Type} {P : Profile} {s : Store H}
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
  have hren : behavioursOf P noHost ⟨s.addExn ⟨ta, W⟩, f, abortJoin W ks⟩ =
      rnBeh s.exns.length '' behavioursOf P noHost ⟨s, f, abortJoin W ks⟩ := by
    have h := hT H P s.exns.length ⟨s, f, abortJoin W ks⟩ (s.addExn ⟨ta, W⟩)
      (exnRen_addExn hsb ⟨ta, W⟩)
    rwa [join_renamed hfb hWb] at h
  have htgt : behavioursOf P noHost ⟨s.addExn ⟨ta, W⟩, f, abortJoin W ks⟩ ⊆
      behavioursOf P noHost ⟨s, f, abortTgt W x l ks⟩ :=
    Silmaril.Wasm.Models.FXAbort.tgt_behaviours_sup ht he hn hl
  rw [hsrc, ← hren]
  exact htgt

/--
info: 'Silmaril.Wasm.Models.FXRename.abort_rename' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abort_rename

/--
info: 'Silmaril.Wasm.Models.FXRename.exnRen_addExn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exnRen_addExn

end Silmaril.Wasm.Models.FXRename
