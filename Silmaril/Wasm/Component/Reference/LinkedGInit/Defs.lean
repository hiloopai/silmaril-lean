module

public import Silmaril.Wasm.Component.Reference.LinkedGRound.Defs

/-!
# The instantiation of a linked component with an abstract exporter: definitions

**Scope.** `LinkedG.toRef` on the reference machine over `core3P P` under `linkHost impl`, the
exporter given by reference data `d` (`ExpSpec.RefData`).

## What R4 does not say

The parent's instantiation runs the exporter's nested instantiation (R4, `RefData.Init`) as one
piece of its own run, then instantiates the importer over the shared store and ends between
calls. R4 describes the configuration `m` after the exporter's nested instantiation only by its
control, its lockdown flag, the arena prefixes, `Hold` and the export map. The rest of the
parent's run, and the importer's invariant between calls (`LReadyG`, `StatB` of
`LinkedGRound`), also read:

* **the trace's observations**: the parent's result is decoded from the *first* instantiation
  observation of its trace (`Instantiates`), and R4 allows the exporter's run to emit any
  observation;
* **the top-level call records and the nesting depth**: between calls there is no pending call
  or result with an id at or above the next call id, and the nesting depth is `0`; R4 says
  nothing of `m.pending`, `m.results` or `m.store.nestingDepth`;
* **the host code of the exporter's core store**: the importer's static facts (`ImpStatG`) were
  first stated reading every host function of the shared core store as one of the importer's
  trampolines, so the exporter's core store after instantiation had to have none
  (`InitAt.hostFree`). They now read host code through a renaming inverted on every host
  function present, and `InitAtX`/`InitSX` drop `hostFree`; `InitAt`/`InitS` are kept as
  stated, and imply them;
* **the exporter's globals**: the importer's image must be disjoint from the exporter's
  footprint (`FootDisj`); its globals are allocated after the exporter's, and R1–R6 leave the
  footprint's globals unconstrained (R6 bounds structs and arrays only), so the footprint must
  own only globals allocated at the exporter's instantiation;
* **distinct function ids of distinct exports**: the trampoline of import `k` lowers the
  function id of its wired export; the importer's host-code renaming sends trampoline `k` back
  to `k` (`ImpStatG.inv`), which needs distinct wired exports to have distinct function ids.

`RefData.InitAt` collects R4's facts with these, and `RefData.InitS` is R4 with them (R4 from
`InitS`: `Thms`). `ExpSpec.RefAdeqS` is `RefAdeqT` of `LinkedGRound` with `InitS` for R4; a
simple exporter meets it (`Thms`).

## Observations

`LinkedG.sessObs prof lg impl h₀ calls`: the resumable-session outcomes of `lg.toRef` (as
`Linked2.sessObs`), calling the importer's exports `calls` by index on IR values.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace ExpSpec.RefData

variable {P : Profile} {e : ExpSpec} (d : e.RefData P)

/-- **What R4 shows of the configuration `m` after the exporter's nested instantiation** from
`M`, at placement `pl`, footprint `F` and export map `es`: R4's facts (lockdown, arena prefixes,
`Hold` of `e.init`, new instances, the export map and empty thread tables), and the top-level
call records and the nesting depth of `M`, a host-free core store, footprint globals allocated
in it, and distinct function ids of distinct exports. -/
structure InitAt {σ : Type} (pl : d.Pl) (F : CoreFoot) (es : List (String × Instantiate.ItemVal (core3P P)))
    (M m : Machine.Config (core3P P) σ) : Prop where
  lock : m.store.lockdown = false
  ext : Instantiate.ArenasExtend M.store m.store
  hold : d.Hold pl e.init m.ref F
  block : ∀ i, d.block pl i → M.store.insts.length ≤ i ∧ i < m.store.insts.length
  exports : ∀ (w : Nat) (x : Export), e.comp.exports[w]? = some x →
    es.lookup x.name = some (.func ⟨d.fid pl w⟩) ∧
    ∃ ι : InstState, m.store.insts[d.inst pl w]? = some ι ∧ ι.threads = ⟨#[none], []⟩
  pending : m.pending = M.pending
  results : m.results = M.results
  nest : m.store.nestingDepth = M.store.nestingDepth
  hostFree : ∀ (a : Nat) (fi : Silmaril.Wasm.Execution.Core.FuncInst (CanonHost (core3P P)))
    (h : CanonHost (core3P P)), (m.core : Store (CanonHost (core3P P))).funcs[a]? = some fi →
    fi.code ≠ .host h
  globals : ∀ a, F.gl a → a < (m.core : Store (CanonHost (core3P P))).globals.length
  fidInj : ∀ (w w' : Nat) (x x' : Export), e.comp.exports[w]? = some x →
    e.comp.exports[w']? = some x' → d.fid pl w = d.fid pl w' → w = w'

/-- **R4, with what the parent reads** (`InitAt`): the nested instantiation of `e.ref` from a
configuration with an empty core store runs, without host events, traps or observations, to its
exports, at a placement where `InitAt` holds. -/
def InitS : Prop :=
  ∀ {σ : Type} (prof : ProfileKind) (impl : HostImpl (core3P P) σ)
    (M : Machine.Config (core3P P) σ) (th : Option ThreadId)
    (outer : List (Instantiate.Frame (core3P P)))
    (k : Ret (core3P P) → Canon.P (core3P P) σ (Ret (core3P P)))
    (segs : List (Seg (core3P P) σ)) (rest : List (Activation (core3P P) σ)),
    M.core = (core3P P).empty (CanonHost (core3P P)) → M.store.lockdown = false →
    ∃ (tr : List (Label (core3P P) σ)) (m : Machine.Config (core3P P) σ) (pl : d.Pl)
      (F : CoreFoot) (es : List (String × Instantiate.ItemVal (core3P P))),
      Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch
        { M with ctl := ⟨th, .prog (callRet (.instantiate ⟨e.ref, outer⟩ []) >>= k), segs⟩ ::
          rest } tr m ∧
      (∀ ev, Label.host ev ∉ tr) ∧ (∀ r, Label.trap r ∉ tr) ∧ traceObs tr = [] ∧
      m.ctl = ⟨th, .prog (k (.items es)), segs⟩ :: rest ∧ d.InitAt pl F es M m

/-- **`InitAt` with any host code in the exporter's core store**: `InitAt` without `hostFree`.
The importer's static facts read the host code of the shared store through a renaming that is
inverted on every host function present (`trX`/`gX` of the proofs), so the exporter's own host
functions (a linked exporter's trampolines) need not be excluded. -/
structure InitAtX {σ : Type} (pl : d.Pl) (F : CoreFoot)
    (es : List (String × Instantiate.ItemVal (core3P P))) (M m : Machine.Config (core3P P) σ) :
    Prop where
  lock : m.store.lockdown = false
  ext : Instantiate.ArenasExtend M.store m.store
  hold : d.Hold pl e.init m.ref F
  block : ∀ i, d.block pl i → M.store.insts.length ≤ i ∧ i < m.store.insts.length
  exports : ∀ (w : Nat) (x : Export), e.comp.exports[w]? = some x →
    es.lookup x.name = some (.func ⟨d.fid pl w⟩) ∧
    ∃ ι : InstState, m.store.insts[d.inst pl w]? = some ι ∧ ι.threads = ⟨#[none], []⟩
  pending : m.pending = M.pending
  results : m.results = M.results
  nest : m.store.nestingDepth = M.store.nestingDepth
  globals : ∀ a, F.gl a → a < (m.core : Store (CanonHost (core3P P))).globals.length
  fidInj : ∀ (w w' : Nat) (x x' : Export), e.comp.exports[w]? = some x →
    e.comp.exports[w']? = some x' → d.fid pl w = d.fid pl w' → w = w'

/-- **`InitS` with any host code in the exporter's core store** (`InitAtX` for `InitAt`). -/
def InitSX : Prop :=
  ∀ {σ : Type} (prof : ProfileKind) (impl : HostImpl (core3P P) σ)
    (M : Machine.Config (core3P P) σ) (th : Option ThreadId)
    (outer : List (Instantiate.Frame (core3P P)))
    (k : Ret (core3P P) → Canon.P (core3P P) σ (Ret (core3P P)))
    (segs : List (Seg (core3P P) σ)) (rest : List (Activation (core3P P) σ)),
    M.core = (core3P P).empty (CanonHost (core3P P)) → M.store.lockdown = false →
    ∃ (tr : List (Label (core3P P) σ)) (m : Machine.Config (core3P P) σ) (pl : d.Pl)
      (F : CoreFoot) (es : List (String × Instantiate.ItemVal (core3P P))),
      Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch
        { M with ctl := ⟨th, .prog (callRet (.instantiate ⟨e.ref, outer⟩ []) >>= k), segs⟩ ::
          rest } tr m ∧
      (∀ ev, Label.host ev ∉ tr) ∧ (∀ r, Label.trap r ∉ tr) ∧ traceObs tr = [] ∧
      m.ctl = ⟨th, .prog (k (.items es)), segs⟩ :: rest ∧ d.InitAtX pl F es M m

end ExpSpec.RefData

/-- **The reference interface of an exporter, with R4 as the parent reads it** (R1, R2, the
corrected R3 of `LinkedGRound`, `InitS`, R5, R6). -/
def ExpSpec.RefAdeqS (P : Profile) (e : ExpSpec) : Prop :=
  ∃ d : e.RefData P, d.Frame ∧ d.Fwd ∧ d.BwdT ∧ d.InitS ∧ d.Resume ∧ d.Bounded

/-- **The session observations of a linked component with an abstract exporter**: the outcomes
of calling the importer's exports `calls` (by index, on IR values) as a resumable session of
`lg.toRef` on the reference machine, under `linkHost impl` from host state `h₀`. -/
noncomputable def LinkedG.sessObs (prof : ProfileKind) {P : Profile} (lg : LinkedG) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin lg.imp.exports.length × List IVal)) :
    Set (List (Option (List Silmaril.Wasm.Component.Value.Val))) :=
  sessBehaviours prof (linkHost impl) h₀ lg.toRef
    (calls.map fun q => (lg.imp.exports[q.1].name, q.2.map toRefVal))

end Silmaril.Wasm.Component.Reference
