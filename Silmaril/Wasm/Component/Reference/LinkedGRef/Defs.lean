module

public import Silmaril.Wasm.Component.Reference.LinkedG.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionRef.Defs

/-!
# The reference side of an abstract exporter: definitions

**Scope.** What linking (`LinkedG`) would use of an exporter on the reference machine
(`Machine.Step` over `core3P P`, the dispatcher of `linkHost impl`), as an interface
`ExpSpec.RefAdeq P e` with five parts R1–R5. Only the definitions are here; `Thms` says which
parts are proved, for which exporters.

## Where the exporter's part of a call begins and ends

A call of the importer B into the exporter A runs, on the machine, B's `canon lower` (a callout
of B's core activation to a trampoline `.lowered f ft {} ⟨ib⟩`), then the `canon lift` of the
function value `f` (a `.lifted a ft {} ⟨i⟩` record: a task and a thread of instance `i`, the
lift of the arguments), then the **core activation** of the core function `a` on the lowered
arguments, then the lift of its flat results and the return into B. Everything but the core
activation is the same program for every exporter whose exports are `canon lift`s of core
functions (`Simple`, and linked components, whose exports are aliases of their importer's
lifts). So the interface describes A by:

* for each export `w`, the lifted record it is (`RefData.addr`, `RefData.inst`, `RefData.fid`:
  core address, component instance, function id), and
* the machine runs of the core activation of `addr w`: a run of core steps of the shared core
  store for `Simple`; for a linked exporter, a run with nested `canon lower`/`canon lift` calls
  into its own exporter. This is why the interface is stated against machine runs and not
  against core runs (`exp_fwd`): the core-level simulation of `Linked2` does not apply to a
  linked exporter.

The `canon lower`/`canon lift` wrapper around it is then a lemma about every such exporter,
not a part of the interface (it is `nest_atTS` of `LinkedSessionFwd` with the instance
indices generalised, `nest_atG`; see `Thms`).

## Placement and footprints

Nested instantiation places an exporter anywhere: in `LinkedG.toRef` the exporter is
instantiated first, at component instance `1` of its parent, and its own nested instances
follow (so a chain's base sits at instance `2` inside a two-link chain, and the importer of a
link sits after all of its exporter's instances). `RefData.Pl` is the exporter's placement
(instances, function ids, core addresses); every law quantifies over it.

The core store is shared by all instances, and A's and B's allocations interleave. A's part of
it is described by `Hold pl s S F`: the exporter's state `s` at the component store `S`, with
footprint `F` (a `CoreFoot`: globals, struct and array addresses of the shared core store that
A owns). The importer keeps `Hold` by not writing into `F` (`CoreFoot.Agree`), and A's runs
write only into `F` and fresh addresses (`CoreFoot.Within`), its footprint growing by fresh
addresses only (`CoreFoot.Grows`). This is the `Rel4` discipline of `Split`, stated in the
shared store's addresses, so that it composes for nested exporters. Like `Split`, footprints
cover globals, structs and arrays only (the split fragment: no memories or tables).

## The parts

* **R1** (`RefData.Frame`): `Hold` is kept by the importer's changes: the core store agreeing on
  `F` (functions a prefix), the component function arena a prefix, the exporter's instances
  (`RefData.block`) unchanged; it does not depend on the thread tables of the export instances
  (which the `canon lift` wrapper fills and empties); it gives the lifted record of each export.
* **R2** (`RefData.Fwd`): for each `Step P s ⟨(w, vals vs), R⟩ s'`, from `Hold pl s S F`, the
  machine runs the core activation of `addr w` on `lowerArgs params vs` (on a thread of instance
  `inst w`, in any frame) without host events or `internal` traps either to a return of flat
  results of the result types (lifting to `ws` when `R = some (vals ws)`, not lifting when
  `R = none`) in a store extending `S` by the exporter's changes only (`StoreExt`), with
  `Hold pl s' …`, or (when `R = none`) to a trapped configuration whose core store `Hold`s `s'`.
* **R3** (`RefData.Bwd`): the converse read-back: a run of that core activation without host
  events is still running, or passed through a return as in R2 for some `Step`, or trapped
  (without `internal` faults) where some trapped `Step` holds.
* **R4** (`RefData.Init`): the nested instantiation of `e.ref` (`Call.instantiate`) from a
  configuration with an empty core store runs to its exports, with `Hold pl e.init` and the
  export of each `w` named as in `e.comp` and bound to `fid w`, the export instances' thread
  tables empty.
* **R5** (`RefData.Resume`): `Hold` survives `resumeCfg`: the component part of an earlier
  store with the core store of a later one.

`ExpSpec.RefAdeq P e`: some data meeting R1–R5.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## The component store with the shared core store -/

/-- **The component store with the shared core store**: the machine's `Config.store` and
`Config.core` together. The exporter's relation `Hold` and the store relations of the interface
are stated on it (the component store `CStore` does not hold the core store, which lives in the
machine configuration). -/
structure RefStore (E : CoreEngine) extends CStore E where
  /-- The shared core-engine store. -/
  core : E.Store (CanonHost E)

instance {E : CoreEngine} : Coe (RefStore E) (CStore E) := ⟨RefStore.toCStore⟩

/-- The component store and the shared core store of a configuration. -/
def _root_.Silmaril.Wasm.Component.Machine.Config.ref {E : CoreEngine} {σ : Type}
    (m : Machine.Config E σ) : RefStore E :=
  { m.store with core := m.core }

/-- `m` with the component store and the shared core store of `S`. -/
def _root_.Silmaril.Wasm.Component.Machine.Config.withRef {E : CoreEngine} {σ : Type}
    (m : Machine.Config E σ) (S : RefStore E) : Machine.Config E σ :=
  { m with store := S.toCStore, core := S.core }

@[simp] theorem _root_.Silmaril.Wasm.Component.Machine.Config.ref_toCStore {E : CoreEngine}
    {σ : Type} (m : Machine.Config E σ) : m.ref.toCStore = m.store := rfl

@[simp] theorem _root_.Silmaril.Wasm.Component.Machine.Config.ref_core {E : CoreEngine}
    {σ : Type} (m : Machine.Config E σ) : m.ref.core = m.core := rfl

@[simp] theorem _root_.Silmaril.Wasm.Component.Machine.Config.withRef_ref {E : CoreEngine}
    {σ : Type} (m : Machine.Config E σ) (S : RefStore E) : (m.withRef S).ref = S := rfl

/-! ## Footprints in the shared core store -/

/-- **A footprint in a shared core store**, in the shared store's addresses: the globals, the
structs and the arrays a part owns. -/
structure CoreFoot where
  /-- Owned globals. -/
  gl : Nat → Prop
  /-- Owned struct addresses. -/
  st : Nat → Prop
  /-- Owned array addresses. -/
  ar : Nat → Prop

namespace CoreFoot

variable {H : Type}

/-- **`σ'` agrees with `σ` on `F`**: the functions of `σ` are a prefix of those of `σ'`, and the
owned globals, structs and arrays are unchanged. What another part may do to `σ`. -/
structure Agree (F : CoreFoot) (σ σ' : Store H) : Prop where
  funcs : σ.funcs <+: σ'.funcs
  globals : ∀ a, F.gl a → σ'.globals[a]? = σ.globals[a]?
  structs : ∀ a, F.st a → σ'.structs[a]? = σ.structs[a]?
  arrays : ∀ a, F.ar a → σ'.arrays[a]? = σ.arrays[a]?

/-- **`σ'` differs from `σ` only inside `F` and by allocation**, with the same functions. What
the part owning `F` may do to `σ`. -/
structure Within (F : CoreFoot) (σ σ' : Store H) : Prop where
  funcs : σ'.funcs = σ.funcs
  globals : ∀ a, ¬ F.gl a → σ'.globals[a]? = σ.globals[a]?
  structs : ∀ a, ¬ F.st a → a < σ.structs.length → σ'.structs[a]? = σ.structs[a]?
  arrays : ∀ a, ¬ F.ar a → a < σ.arrays.length → σ'.arrays[a]? = σ.arrays[a]?
  structs_len : σ.structs.length ≤ σ'.structs.length
  arrays_len : σ.arrays.length ≤ σ'.arrays.length

/-- **`F'` extends `F` by addresses fresh in `σ`**; the globals are fixed. -/
structure Grows (F F' : CoreFoot) (σ : Store H) : Prop where
  gl : ∀ a, F'.gl a ↔ F.gl a
  st : ∀ a, F.st a → F'.st a
  ar : ∀ a, F.ar a → F'.ar a
  stNew : ∀ a, F'.st a → F.st a ∨ σ.structs.length ≤ a
  arNew : ∀ a, F'.ar a → F.ar a ∨ σ.arrays.length ≤ a

end CoreFoot

/-! ## The exporter's data -/

/-- **The reference data of an exporter**: its placement, the lifted record of each export, its
component instances and the relation `Hold` between its state and the component store. -/
structure ExpSpec.RefData (P : Profile) (e : ExpSpec) where
  /-- Placements (instances, function ids, core addresses). -/
  Pl : Type
  /-- The core address of the core function export `w` lifts. -/
  addr : Pl → Nat → Nat
  /-- The component instance of export `w`'s `canon lift`. -/
  inst : Pl → Nat → Nat
  /-- The function id of export `w`. -/
  fid : Pl → Nat → Nat
  /-- The component instances of the exporter. -/
  block : Pl → Nat → Prop
  /-- The exporter's state `s` at the component store `S`, with footprint `F` in its core
  store. -/
  Hold : Pl → e.St → RefStore (core3P P) → CoreFoot → Prop

namespace ExpSpec.RefData

variable {P : Profile} {e : ExpSpec} (d : e.RefData P)

/-- **The exporter's changes to the component store** during the core activation of one of its
exports: the core store, its own instances (not the export instances), and records appended to
the subtask, caller, task and thread arenas; nothing else. -/
structure StoreExt (pl : d.Pl) (S S' : RefStore (core3P P)) : Prop where
  eq : S' = { S with
    core := S'.core
    insts := S'.insts
    subtasks := S'.subtasks
    callers := S'.callers
    tasks := S'.tasks
    threads := S'.threads }
  insts_len : S'.insts.length = S.insts.length
  insts_out : ∀ i, ¬ d.block pl i → S'.insts[i]? = S.insts[i]?
  insts_exp : ∀ w, S'.insts[d.inst pl w]? = S.insts[d.inst pl w]?
  subtasks : S.subtasks <+: S'.subtasks
  callers : S.callers <+: S'.callers
  tasks : S.tasks <+: S'.tasks
  threads : S.threads <+: S'.threads

/-- The configuration `M` running the core activation of export `w` (of type `x`) on the IR
values `vs`, on thread `th`, its returned values going to `K`. -/
def startCfg {σ : Type} (pl : d.Pl) (w : Nat) (x : Export) (vs : List IVal)
    (M : Machine.Config (core3P P) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P))) (segs : List (Seg (core3P P) σ))
    (rest : List (Activation (core3P P) σ)) : Machine.Config (core3P P) σ :=
  { M with ctl := ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (d.addr pl w)
    (lowerArgs x.ty.params vs)) K, segs⟩ :: rest }

/-- The configuration `M` at store `S'` and continuation slots `C'` once the core activation
returned `zs` to `K`. -/
def retCfg' {σ : Type} (M : Machine.Config (core3P P) σ) (S' : RefStore (core3P P))
    (C' : List (Option (Activation (core3P P) σ))) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P))) (segs : List (Seg (core3P P) σ))
    (rest : List (Activation (core3P P) σ)) (zs : List FlatValue) : Machine.Config (core3P P) σ :=
  { M with
    store := S'.toCStore
    core := S'.core
    conts := C'
    ctl := ⟨th, .prog (K zs), segs⟩ :: rest }

/-- **The ways the core activation of a call ends** (from `S` with footprint `F`, the round's
answer `R`, the exporter's state `s'` after it): a return of flat results of the result types
of `x` at the configuration `m`, lifting to the answer (`R = some (vals ws)`), or not lifting
(`R = none`), at a store extending `S` (`StoreExt`) that holds `s'`; or (`R = none`) a trapped
configuration `m` whose core store holds `s'`. A's writes stay in `F` and fresh addresses,
its footprint growing by fresh addresses. -/
def Ends {σ : Type} (pl : d.Pl) (x : Export) (S : RefStore (core3P P)) (F : CoreFoot)
    (M : Machine.Config (core3P P) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P))) (segs : List (Seg (core3P P) σ))
    (rest : List (Activation (core3P P) σ)) (R : Option Payload) (s' : e.St)
    (m : Machine.Config (core3P P) σ) : Prop :=
  (∃ (S' : RefStore (core3P P)) (C' : List (Option (Activation (core3P P) σ))) (zs : List Flat)
      (F' : CoreFoot),
    m = retCfg' M S' C' th K segs rest zs ∧ zs.map (·.type) = ValTy.flatList x.ty.results ∧
    (match R with
      | some (.vals ws) => liftArgs x.ty.results zs = some ws
      | none => liftArgs x.ty.results zs = none
      | some _ => False) ∧
    d.StoreExt pl S S' ∧ d.Hold pl s' S' F' ∧
    F.Within (S.core : Store (CanonHost (core3P P))) S'.core ∧ F.Grows F' (S.core : Store _)) ∨
  (R = none ∧ m.store.lockdown = true ∧
    ∃ (S' : RefStore (core3P P)) (F' : CoreFoot), S'.core = m.core ∧ S'.funcs = S.funcs ∧
      d.Hold pl s' S' F' ∧
      F.Within (S.core : Store (CanonHost (core3P P))) m.core ∧ F.Grows F' (S.core : Store _))

/-! ## The parts R1–R5 -/

/-- **R1: the relation is kept by the importer**, does not depend on the thread tables of the
export instances, and gives the lifted record of each export. -/
structure Frame : Prop where
  agree : ∀ (pl : d.Pl) (s : e.St) (S S' : RefStore (core3P P)) (F : CoreFoot),
    d.Hold pl s S F → F.Agree (S.core : Store (CanonHost (core3P P))) S'.core →
    S.funcs <+: S'.funcs → (∀ i, d.block pl i → S'.insts[i]? = S.insts[i]?) → d.Hold pl s S' F
  threads : ∀ (pl : d.Pl) (s : e.St) (S : RefStore (core3P P)) (F : CoreFoot) (w : Nat)
    (ι : InstState) (t : Silmaril.Wasm.Component.Runtime.Table ThreadId), d.Hold pl s S F → S.insts[d.inst pl w]? = some ι →
    d.Hold pl s { S with insts := S.insts.set (d.inst pl w) { ι with threads := t } } F
  lifted : ∀ (pl : d.Pl) (s : e.St) (S : RefStore (core3P P)) (F : CoreFoot) (w : Nat)
    (x : Export),
    d.Hold pl s S F → e.comp.exports[w]? = some x →
    ArenaField.funcs.get? S.toCStore ⟨d.fid pl w⟩ =
      some (.lifted (d.addr pl w) (witFt x.ty) {} ⟨d.inst pl w⟩) ∧ d.block pl (d.inst pl w)

/-- **R2: forward runs of the exporter's core activation**, one for each step of its
specification, in any frame. -/
def Fwd : Prop :=
  ∀ (pl : d.Pl) (s s' : e.St) (w : Nat) (vs : List IVal) (R : Option Payload) (x : Export),
    e.Step P s ⟨(w, .vals vs), R⟩ s' → e.comp.exports[w]? = some x →
    ∀ (S : RefStore (core3P P)) (F : CoreFoot), d.Hold pl s S F →
    ∀ {σ : Type} (prof : ProfileKind) (impl : HostImpl (core3P P) σ)
      (M : Machine.Config (core3P P) σ) (th : Option ThreadId)
      (K : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P)))
      (segs : List (Seg (core3P P) σ)) (rest : List (Activation (core3P P) σ)),
      M.ref = S → S.lockdown = false → instOfThread? S.toCStore th = some ⟨d.inst pl w⟩ →
      ∃ (tr : List (Label (core3P P) σ)) (m : Machine.Config (core3P P) σ),
        Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch
          (d.startCfg pl w x vs M th K segs rest) tr m ∧
        (∀ ev, Label.host ev ∉ tr) ∧ (∀ msg, Label.trap (.internal msg) ∉ tr) ∧
        d.Ends pl x S F M th K segs rest R s' m

/-- **R3: the read-back of the exporter's core activation**: a run of it without host events is
still running, or passed through an end of R2 for some step of the specification, or trapped
(without `internal` faults) where some trapped step holds. -/
def Bwd : Prop :=
  ∀ (pl : d.Pl) (s : e.St) (w : Nat) (vs : List IVal) (x : Export),
    e.comp.exports[w]? = some x → ValTy.checkList x.ty.params vs = true →
    ∀ (S : RefStore (core3P P)) (F : CoreFoot), d.Hold pl s S F →
    ∀ {σ : Type} (prof : ProfileKind) (impl : HostImpl (core3P P) σ)
      (M : Machine.Config (core3P P) σ) (th : Option ThreadId)
      (K : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P)))
      (segs : List (Seg (core3P P) σ)) (rest : List (Activation (core3P P) σ)),
      M.ref = S → S.lockdown = false → instOfThread? S.toCStore th = some ⟨d.inst pl w⟩ →
      ∀ (tr : List (Label (core3P P) σ)) (m' : Machine.Config (core3P P) σ),
        Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch
          (d.startCfg pl w x vs M th K segs rest) tr m' → (∀ ev, Label.host ev ∉ tr) →
        (m'.ctl ≠ [] ∧ m'.store.lockdown = false) ∨
        (∃ (tr₁ tr₂ : List (Label (core3P P) σ)) (m : Machine.Config (core3P P) σ)
            (R : Option Payload) (s' : e.St),
          tr = tr₁ ++ tr₂ ∧
          Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch
            (d.startCfg pl w x vs M th K segs rest) tr₁ m ∧
          Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch m tr₂ m' ∧
          e.Step P s ⟨(w, .vals vs), R⟩ s' ∧ d.Ends pl x S F M th K segs rest R s' m ∧
          m.ctl ≠ []) ∨
        (m'.store.lockdown = true ∧ ((∀ msg, Label.trap (.internal msg) ∉ tr) →
          ∃ (s' : e.St) (S' : RefStore (core3P P)) (F' : CoreFoot),
            e.Step P s ⟨(w, .vals vs), none⟩ s' ∧
            S'.core = m'.core ∧ S'.funcs = S.funcs ∧ d.Hold pl s' S' F'))

/-- **R4: instantiation**: the nested instantiation of `e.ref` (closure under the outer frames
`outer`, no arguments) from a configuration with an empty core store runs, without host events
or traps, to its exports: the exporter's state `e.init` holds at a placement whose instances
are new, export `w` is named as in `e.comp` and bound to `fid w`, and the thread tables of the
export instances are empty. -/
def Init : Prop :=
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
      (∀ ev, Label.host ev ∉ tr) ∧ (∀ r, Label.trap r ∉ tr) ∧
      m.ctl = ⟨th, .prog (k (.items es)), segs⟩ :: rest ∧ m.store.lockdown = false ∧
      Instantiate.ArenasExtend M.store m.store ∧ d.Hold pl e.init m.ref F ∧
      (∀ i, d.block pl i → M.store.insts.length ≤ i ∧ i < m.store.insts.length) ∧
      ∀ (w : Nat) (x : Export), e.comp.exports[w]? = some x →
        es.lookup x.name = some (.func ⟨d.fid pl w⟩) ∧
        ∃ ι : InstState, m.store.insts[d.inst pl w]? = some ι ∧ ι.threads = ⟨#[none], []⟩

/-- **R5: the relation survives `resumeCfg`**: the component part of an earlier store at which
`Hold` held, with the core store of a later one, holds the later state. -/
def Resume : Prop :=
  ∀ (pl : d.Pl) (s s' : e.St) (S₀ S' : RefStore (core3P P)) (F₀ F' : CoreFoot),
    d.Hold pl s S₀ F₀ → d.Hold pl s' S' F' → S'.funcs = S₀.funcs →
    d.Hold pl s' { S₀ with core := S'.core } F'

end ExpSpec.RefData

/-- **The reference interface of an exporter** (R1–R5). -/
def ExpSpec.RefAdeq (P : Profile) (e : ExpSpec) : Prop :=
  ∃ d : e.RefData P, d.Frame ∧ d.Fwd ∧ d.Bwd ∧ d.Init ∧ d.Resume

end Silmaril.Wasm.Component.Reference
