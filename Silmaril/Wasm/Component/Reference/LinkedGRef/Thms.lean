module

public import Silmaril.Wasm.Component.Reference.LinkedGRef.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef.SimpleInit
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef.Nest

/-!
# The reference side of an abstract exporter: theorems

**Scope.** The interface `ExpSpec.RefAdeq` (`Defs`, R1–R5) and a simple exporter: every profile
`P`, every component choice profile, host state type and host functions `impl` (under
`linkHost impl`), the reference machine `Machine.Step` over `core3P P`.

**Proved.** `Simple.expSpec_refFwd`: under `Simple.Good` and `IsInst`, `Simple.expSpec c I`
has reference data meeting

* **R1** (`Frame`): its relation is kept when the core store agrees on the exporter's footprint
  (functions a prefix), the component function arena grows and its instance is unchanged; it does
  not depend on the export instance's thread table; it gives the lifted record of each export;
* **R2** (`Fwd`): each returned (`RetAt`) and trapped (`TrapAt`) call of its specification is a
  run of its core activation on the machine, in any frame and on any thread, without host events
  or `internal` faults: a return of flat results of the result types that lift to the call's
  results, or that do not lift (a trap of the lift), or a core trap (`coreTrap`), the relation
  holding the store after the call at the core store reached, its writes inside its footprint
  and fresh addresses, its footprint growing by fresh addresses. This repackages
  `LInv.resume_fwd` and `LInv.expTrap_fwd` (`exp_fwd`, `status_of_values`, `status_of_trap`,
  `coreCfg_steps_of`) without the importer's part: `Rel4` is replaced by the exporter's
  `PartRel` alone, its footprint stated in the shared store's addresses;
* **R5** (`Resume`): the relation survives `resumeCfg`;

and this data is not vacuous: after every instantiation of a `Linked2` with this exporter
(`Linked2.Adequate`), the relation holds at the instance's store, at placement instance `1`
with the export `w` the function `w` and the core address `I.addrs.getD x.core 0` (from
`instBehavioursL_inst`, `lready_init`).

**Proved (R3, R4).** `Simple.expSpec_refFwdBwd`: the same data meets

* **R3** (`Bwd`): every machine run of the core activation of an export, without host events, in
  any frame and on any thread, is still in the core phase (live), or passed through a return of
  R2's shape (`Ends`) for a specification step (`ret` when the results lift, `trap` when they do
  not), or ended in a core trap, the step `trap` holding at the trapped core store. This is the
  backward simulation of `exp_run` (`LinkExp`) with the importer's half of `Rel4` dropped
  (`exp_back1`), and the machine's core phase (`coreCfg_steps_inv`); a simple exporter's core
  activation makes no callout, so no nested call is involved.

`Simple.expSpec_refAdeq`: in the split fragment (`Linked2.ModSplitOk`), with `Simple.Inst` and
export names that are not generated type names (as `Linked2.NamesOk`), the same data also meets

* **R4** (`Init`): the nested instantiation of `c.toRef` under any enclosing frames, from any
  configuration with an empty core store, runs without host events or traps to its exports, at
  the placement `(k, [o, o + 1, …])` for the next component instance `k` and the number `o` of
  component functions before it (so at every placement nested instantiation produces, e.g. a
  chain's base at instance `n` of an `n`-link chain); the relation holds with the identity
  renaming and the ownership of the instance store.

So `Simple.expSpec c I` is `RefAdeq`. The proof of R4 uses its extra hypotheses as follows (their
necessity is not claimed): `Simple.Inst` gives the core instantiation (`CoreFacts`),
`ModSplitOk` the footprint relation of `Hold` at the instance store (`StoreGood`), and the
names keep the lookup of an export by name from finding a type export `tag "t" n` of
`c.toRef`'s export map.

**The cross-instance call at arbitrary instances** (step (a); proof-internal, in
`Proofs.….LinkedGRef.Nest`): `lift_body_atG`, `lift_body_trapG`, `nest_preG`, `nest_atG`,
`nest_trap_argsG` are the nested-call lemmas of `LinkCallout` and `LinkedSessionFwd.TrapS` with
the callee's `canon lift` instance `ie`, the caller's `canon lower` instance `ii`, the lifted
function `f` and an arbitrary caller frame `M` (not locked down) as parameters; `nest_backG` and
`nest_trap_args_backG` are the read-back of their runs. The fixed-index lemmas (`nest_at`,
`nest_pre`, `lift_body_at`, `lift_body_trap`, `nest_trap_args`, `nest_atTSH`, `lift_body_atTSH`,
`lift_body_trapTSH`, `nest_trap_argsTSH`) are proved again as instances at `ie = 1`, `ii = 2`,
`M = extN B ιe N C` (`…_inst`). The machine's behaviour on these runs depends on the instance
indices only through lookups (`calloutEntry`, the instance arena); no distinctness is used.

**Not claimed** (what remains):

* **`LinkedG.sess_specToRef`, `sess_refToSpec`, `sessObs_eq` for a `RefAdeq` exporter**, and
  `Linked2` as an instance of them. The `Linked2` proofs do not consume an interface of this
  kind: the importer's invariants (`LInv`, `LReady`, `LStat`, `CallAtLKTS`) carry the exporter as
  the provider part of `Rel4`, and the nested call (`nest_pre`, `lift_body_at`, `nest_atTS` and
  their trapping variants) hardcodes the exporter's `canon lift` at instance `1`, the importer's
  `canon lower` at instance `2`, and the instance list `[{}, ιe, ιi]`. Restating them needs
  (a) the `canon lower`/`canon lift` wrapper with both instance indices as parameters (done,
  above, not yet used by the importer's proofs), and
  (b) the importer's invariant with the exporter's part replaced by `Hold` and a footprint
  disjoint from the importer's `PartRel` image (kept by `CoreFoot.Agree`, `Within`, `Grows`).
* **`LinkedG.toExp_refAdeq` and `LinkedN.sessAdequacy_full`**: they rest on the previous item.
* Divergence, host observations, the parser and F6, as for `Linked2`.

**On the sketch of #839.** R1–R5 as sketched (a relation on the exporter's part of the
configuration, forward runs of a cross-instance call per `Step`, read-back, instantiation,
`resumeCfg`) need three precisions, all taken in `Defs`; no counterexample to the sketch was
found:

* **The boundary is the core activation, not the cross-instance call.** For a linked exporter the
  call into its export `w` is its importer's `canon lift` of its importer's core function, and
  that core activation makes nested callouts into its own exporter. The `canon lower`/`canon
  lift` wrapper is the same program for every exporter whose exports are lifted core functions,
  so it is a lemma (`nest_atG` of (a)), and the interface describes only
  the core activation, by machine runs (`Steps`), not by core runs.
* **Placement.** Nested instantiation allocates the exporter's instances after its parent's, so a
  chain's base sits at instance `2` inside a two-link chain and an importer after all of its
  exporter's instances; every law quantifies over the placement `RefData.Pl`.
* **Footprints.** "Kept by the importer's steps" needs the part of the shared core store the
  exporter owns: `Hold` carries a footprint in the shared store's addresses (globals, structs,
  arrays, as in `Split`), which the importer leaves alone and the exporter's runs grow by fresh
  addresses only. The machine checks nothing else that distinguishes nested instances on these
  paths: `calloutEntry` compares the trampoline's instance with the current thread's, and
  `canon lift` has no reentrance check.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef.Simple`, `SimpleBwd`, `SimpleInit`,
`Nest`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)

/-- **A simple exporter meets R1, R2 and R5 of the reference interface** (proved, every profile),
with data that holds where `Linked2` starts its sessions: at placement instance `1`, export `w`
the function `w` and core address `I.addrs.getD x.core 0`. -/
theorem Simple.expSpec_refFwd (P : Profile) {c : Simple} (hc : c.Good)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I) :
    ∃ d : (Simple.expSpec c I).RefData P, d.Frame ∧ d.Fwd ∧ d.Resume ∧
      ∀ (l : Linked2), l.exp = c → l.Adequate →
      ∀ (prof : ProfileKind) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
        (m₀ : Machine.Config (core3P P) σ) (inst : InstId) (es : List (String × FuncId)),
        InstResult.instance m₀ inst es ∈
          instBehaviours prof (linkHost impl) (initConfig h₀) l.toRef [] →
        ∃ (pl : d.Pl) (F : CoreFoot), d.Hold pl I.store m₀.ref F ∧
          (∀ i, d.block pl i ↔ i = 1) ∧
          ∀ (w : Nat) (xe : SimpleExport), c.exports[w]? = some xe →
            d.addr pl w = I.addrs.getD xe.core 0 ∧ d.inst pl w = 1 ∧ d.fid pl w = w :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef.simple_refFwd P hc hI

/-- **A simple exporter meets R1, R2, R3 and R5 of the reference interface** (proved, every
profile), with data that holds where `Linked2` starts its sessions. -/
theorem Simple.expSpec_refFwdBwd (P : Profile) {c : Simple} (hc : c.Good)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I) :
    ∃ d : (Simple.expSpec c I).RefData P, d.Frame ∧ d.Fwd ∧ d.Bwd ∧ d.Resume ∧
      ∀ (l : Linked2), l.exp = c → l.Adequate →
      ∀ (prof : ProfileKind) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
        (m₀ : Machine.Config (core3P P) σ) (inst : InstId) (es : List (String × FuncId)),
        InstResult.instance m₀ inst es ∈
          instBehaviours prof (linkHost impl) (initConfig h₀) l.toRef [] →
        ∃ (pl : d.Pl) (F : CoreFoot), d.Hold pl I.store m₀.ref F ∧
          (∀ i, d.block pl i ↔ i = 1) ∧
          ∀ (w : Nat) (xe : SimpleExport), c.exports[w]? = some xe →
            d.addr pl w = I.addrs.getD xe.core 0 ∧ d.inst pl w = 1 ∧ d.fid pl w = w :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef.simple_refFwdBwd P hc hI

/-- **A simple exporter meets the reference interface** (R1–R5, proved, every profile), in the
split fragment, with export names that are not generated type names. -/
theorem Simple.expSpec_refAdeq (P : Profile) {c : Simple} (hc : c.Good) (hi : c.Inst)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I)
    (hS : Linked2.ModSplitOk c.mod.mod) (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) :
    (Simple.expSpec c I).RefAdeq P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef.simple_refAdeq P hc hi hI hS hN

end Silmaril.Wasm.Component.Reference
