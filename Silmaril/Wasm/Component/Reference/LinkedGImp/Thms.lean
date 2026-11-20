module

public import Silmaril.Wasm.Component.Reference.LinkedGImp.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp.Inv
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp.Unbounded

/-!
# The importer's side of linking with an abstract exporter: theorems

**Scope.** Every profile `P`; the reference machine over `core3P P`; the exporter interface of
`LinkedGRef` (R1–R5) with R6 (`RefData.Bounded`, `Defs`).

**Proved.** `Simple.expSpec_refAdeqB`: in the split fragment, with `Simple.Inst` and export
names that are not generated type names (the hypotheses of `Simple.expSpec_refAdeq`), a simple
exporter meets R1–R6 with the data of `Simple.expSpec_refAdeq` (its footprint is the image of
its `PartRel`, which is allocated).

**Proved (R6 is needed).** `ExpSpec.refAdeq_allStructs`: every `RefAdeq` exporter has data
meeting R1–R5 whose footprints own every struct address (`allData` in
`Proofs.….LinkedGImp.Unbounded`: `d`'s relation at a smaller footprint), so footprints that are
not allocated, and disjoint from no importer owning a struct. A client of `RefAdeq` receives
some data and cannot exclude these; the importer's side is stated against R6.

**The importer's invariant against an abstract exporter** (proof-internal, in
`Proofs.….LinkedGImp.Inv`; blocker (b) of `LinkedGRef.Thms`): `LInvG d pl …` relates the
importer's part as `LInv` does (`LinkSt`) and replaces the exporter's half of `Rel4` by
`d.Hold pl s S F`, with the importer's image disjoint from the footprint `F` and `F` allocated
(`FootDisj`). Against it:

* `LInvG.reach_fwd`: a run of the importer's part is a core run of the shared thread, keeping
  `LInvG` with the same exporter state and footprint (from R1 alone);
* `LInvG.callout_fwd`: a callout of the part is a callout of the shared thread to the
  trampoline of the import, on flat arguments of the import's parameter types;
* `LInvG.resume_fwd`: after a change of the component store inside the footprint and by fresh
  addresses, holding a new exporter state with a grown, allocated footprint (what R2's return
  `Ends` gives, with R6), the resumed threads satisfy `LInvG` again.

The importer's static facts (`ImpStatG`) abstract `LStat`'s trampolines: a renaming `g` of host
codes and the trampoline `tr k` of import `k` with `g (tr k) = k`, so that any instance indices
and function ids of the `canon lower` trampolines are allowed.

**Not claimed** (what remains):

* **`LinkedG.linkCall_fwd`/`linkCall_inv`**: one session round of `LinkedG` as a reference run.
  It composes `LInvG.callout_fwd`, the parameterised cross-instance call (`nest_atG`,
  `nest_backG` of `LinkedGRef`), R2/R3 for the exporter's core activation and
  `LInvG.resume_fwd` (or the trapping variants), at the machine level: the machine invariants
  `CallAtLKTS`/`ReadyL` of `Linked2` restated for `LInvG` and an arbitrary placement.
* `LinkedG.sess_specToRef`, `sess_refToSpec`, `sessObs_eq`, `LinkedG.toExp_refAdeq` and
  `LinkedN.sessAdequacy_full`: they rest on the previous item.
* **R2's return does not constrain the saved continuations or the component store enough for
  the caller's resumption**: `Ends` lets the exporter's run end with any continuation slots
  `C'` and a `StoreExt` of the store (records appended to the subtask, caller, task and thread
  arenas, its own instances changed), while the return half of `nest_atG`/`nest_backG` (via
  `lift_body_atG` and `nest_preG`) starts from the callee's frame `M₁` with only the core store
  replaced (`retCfg M₁ … y zs`), its proofs reading the callee's records as the *last* of
  each arena. A `Simple` exporter ends with `C' = M.conts` and `S' = { S with core := … }`,
  so `Linked2` is not affected. For a nested linked exporter, `linkCall_fwd` needs (i) the
  return half of `nest_atG` from a `StoreExt` of `M₁.store` with records looked up by index,
  and `nest_atG` exposing the callee's thread and its instance (`instOfThread?`). Both are
  done in `LinkedGCall` (`nest_atX`); strengthening `Ends` to keep the continuation slots
  turned out unnecessary, since nothing on this path reads the slots it does not itself write.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

/-- **A simple exporter meets R1–R6** (proved, every profile), in the split fragment, with
export names that are not generated type names. -/
theorem Simple.expSpec_refAdeqB (P : Profile) {c : Simple} (hc : c.Good) (hi : c.Inst)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I)
    (hS : Linked2.ModSplitOk c.mod.mod) (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) :
    (Simple.expSpec c I).RefAdeqB P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp.simple_refAdeqB P hc hi hI hS hN

/-- **R1–R5 allow footprints owning every struct address** (proved): every `RefAdeq` exporter
has data meeting R1–R5 all of whose footprints own every struct address. -/
theorem ExpSpec.refAdeq_allStructs {P : Profile} {e : ExpSpec} (h : e.RefAdeq P) :
    ∃ d : e.RefData P, d.Frame ∧ d.Fwd ∧ d.Bwd ∧ d.Init ∧ d.Resume ∧
      ∀ (pl : d.Pl) (s : e.St) (S : RefStore (core3P P)) (F : CoreFoot),
        d.Hold pl s S F → ∀ a, F.st a :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp.refAdeq_allStructs h

end Silmaril.Wasm.Component.Reference
