module

public import Silmaril.Wasm.Component.Reference.Sound.Defs

/-!
# Two components linked: an exporter answering an importer's imports

`Linked2`: an import-free simple component `exp` (the exporter) and a simple component with
imports `imp` (the importer) whose component import `k` is answered by export `wire[k]` of
`exp`.

* `Linked2.toComp : Comp ImpModule`: the IR composition, a parent component without imports
  with two nested instances, `exp` (through `SimpleI.ofSimple`) and `imp` with its import `k`
  wired to environment function `wire[k]` (the exporter's exports come first), exporting the
  importer's exports (environment functions `exp.exports.length + i`).
* `Linked2.toRef : Core3Component`: the reference translation, a parent component that defines
  both children (`component`), instantiates the exporter, aliases the wired exports of instance
  `0` (component functions `0, …, n - 1`, `n = wire.length`), instantiates the importer with them
  (`instantiate 1 (with "name_k" (func k))`), aliases the importer's exports from instance `1`
  (component functions `n, …, n + m - 1`) and exports them. Exports add component functions, so
  all aliases precede the exports, and export `i` names function `n + i`.

The IR side:

* `Linked2.ExpRun P l I s ds`: the importer's component import calls `ds`, in order, answered
  by the exporter's canonical-ABI specification at its instance `I`, the exporter's Core store
  threaded from `s` (returned calls, `RetAt`; a last trap, `specAt`).
* `Linked2.SpecToIR`: an importer play (as in `SimpleI.SpecToIR`) whose import calls are
  answered by `ExpRun` from the exporter instance's store is a two-move play of
  `l.toComp.den (impSem P)` (proved: `Linked2.specToIR`, re-exported from `Sound.Thms`).

Proved so far (`Silmaril.Proofs.Wasm.Component.Reference.{LinkIR,LitmusLink,LitmusLinkIR}`,
re-exported from `Sound.Thms` and `Litmus.Thms`): the IR side above (single calls; sequences of
linked calls at proof level, `linked_seq_den`), validity and a closed reference run of the
litmus `dblFwdL` (the doubler `dblS` answering `fwdS`'s import `g`: `f(3)` returns `6`) and its
IR play at every profile (`dblFwd_ir`). Conditions of the reference side: `WireTy` (one wired
export per import, of the import's type), `NamesOk` (export names are no generated type names)
and `wireFid`; for the split of the shared core store, `WireNodup` with `trampIdxL` (the import
index of a trampoline) and the fragment `SplitOk` (no tags, memories, tables or segments). The instantiation of `toRef` is proved at proof level given the importer's core
instantiation in the shared core store (`Silmaril.Proofs.Wasm.Component.Reference.InstLink`,
`instBehavioursL_toRef`); single calls are sound at every profile (`Linked2.sound`,
`Silmaril.Wasm.Component.Reference.LinkSound`); sequences of calls are not done.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component

/-- **Two components linked**: import `k` of the importer `imp` is answered by export
`wire[k]` of the import-free exporter `exp`. -/
structure Linked2 where
  /-- The exporter. -/
  exp : Simple
  /-- The importer. -/
  imp : SimpleI
  /-- For each import of `imp`, the index of the export of `exp` answering it. -/
  wire : List Nat

namespace Linked2

/-- The name of export `w` of the exporter (`""` out of range). -/
def expName (l : Linked2) (w : Nat) : String :=
  ((l.exp.exports[w]?).map (·.name)).getD ""

/-- **The IR composition**: a parent component without imports instantiating the exporter and
the importer, import `k` of the importer wired to the exporter's export `wire[k]`; it exports
the importer's exports. -/
def toComp (l : Linked2) : Comp ImpModule :=
  .mk [] [.inst (SimpleI.ofSimple l.exp).toComp [],
      .inst l.imp.toComp (l.wire.map fun w => ⟨[], .call w⟩)]
    (l.imp.exports.mapIdx fun i x =>
      { name := x.name, ty := x.ty, impl := ⟨[], .call (l.exp.exports.length + i)⟩ })

/-- **The reference translation**: the parent component defining both children, instantiating
the exporter, aliasing its wired exports, instantiating the importer with them, aliasing the
importer's exports and exporting them. -/
def toRef (l : Linked2) : Core3Component :=
  [.component l.exp.toRef, .component l.imp.toRef, .instance_ (.instantiate 0 [])] ++
    (l.wire.map fun w => .alias (.export_ 0 (l.expName w) .func)) ++
    [.instance_ (.instantiate 1 (l.imp.imports.mapIdx fun k p => (p.1, ⟨.func, k⟩)))] ++
    (l.imp.exports.map fun x => .alias (.export_ 1 x.name .func)) ++
    (l.imp.exports.mapIdx fun i x => .export_ { name := x.name } ⟨.func, l.wire.length + i⟩ none)


/-! ## Conditions on the wiring -/

/-- **The wiring is well typed**: one wired export per import of the importer, and the export
`wire[k]` answering import `k` is an export of the exporter of the import's type. -/
structure WireTy (l : Linked2) : Prop where
  length : l.wire.length = l.imp.imports.length
  ty : ∀ (k w : Nat), l.wire[k]? = some w →
    ∃ x : SimpleExport, l.exp.exports[w]? = some x ∧
      (l.imp.imports[k]?).map (fun p : String × FuncTy => p.2) = some x.ty

/-- **The export names avoid the generated type names**: the reference translations export the
type definitions they emit under the names `tag "t" n`, and the parent aliases function exports
of its children by name, which finds the first export of that name. -/
structure NamesOk (l : Linked2) : Prop where
  exp : ∀ x ∈ l.exp.exports, ∀ n, x.name ≠ tag "t" n
  imp : ∀ x ∈ l.imp.exports, ∀ n, x.name ≠ tag "t" n

/-- The component function of the exporter answering import `k` of the importer in the parent
of `toRef`: the lifted function of export `wire[k]`, after no other component function. -/
def wireFid (l : Linked2) (k : Nat) : Silmaril.Wasm.Component.Runtime.FuncId :=
  ⟨l.wire.getD k 0⟩

/-- **One import per wired export**: no export of the exporter answers two imports. The shared
store's trampoline of import `k` names the exporter's lifted function `wire[k]`, so the import
index of a trampoline is recovered from it (`trampIdxL`) exactly when the wiring is injective. -/
def WireNodup (l : Linked2) : Prop := l.wire.Nodup

section Trampolines

open Silmaril.Wasm.Component.Runtime

/-- The import index of a `canon lower` trampoline of the importer in the shared store: the
position, in the wiring, of the exporter's function it lowers (the inverse of `wireFid`). -/
def trampIdxL {E : Engine} (l : Linked2) : CanonHost E → Nat
  | .lowered f _ _ _ => l.wire.idxOf f.idx
  | _ => 0

end Trampolines

/-- **A Core module of the split fragment**: function imports only, no start function, and no
tags, memories, tables, data or element segments (globals, functions and GC types are allowed;
the profile `inProfile` of silmaril-lean's GC linker). Its module
instances are the module instances the store split of `Silmaril.Wasm.Game.Linking` relates
(`Own.ModGood`). -/
structure ModSplitOk (m : Silmaril.Wasm.Module) : Prop where
  imports : m.imports.all (fun i => match i.type with | .func _ => true | _ => false) = true
  tags : m.tags = []
  memories : m.memories = []
  tables : m.tables = []
  data : m.data = []
  elems : m.elems = []
  start : m.start = none

/-- **Both core modules are in the split fragment.** -/
structure SplitOk (l : Linked2) : Prop where
  exp : ModSplitOk l.exp.mod.mod
  imp : ModSplitOk l.imp.mod.mod

/-! ## The IR side -/

section IR

open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

/-- **Import calls of the importer answered by the exporter's specification**, the exporter's
Core store threaded from call to call: each call of import `k` on `ws` is a returned call
(`RetAt`) of the wired export `wire[k]` from the current store `s`, answered with the IR results
`us` and moving to `s'`, or, last, a trap of that export at the current store (`specAt`;
answered `none`). -/
inductive ExpRun (P : Profile) (l : Linked2) (I : ScalarInstance) :
    Store Nat → List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload) → Prop
  | nil (s : Store Nat) : ExpRun P l I s []
  | ret {s s' : Store Nat} {k : Fin l.imp.imports.length} {ws us : List Silmaril.Wasm.Component.Val}
      {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
      (w : Fin l.exp.exports.length) :
      l.wire[k.val]? = some w.val → RetAt P l.exp I l.exp.exports[w] ws s us s' →
      ExpRun P l I s' ds → ExpRun P l I s (⟨(k, .vals ws), some (.vals us)⟩ :: ds)
  | trap {s : Store Nat} {k : Fin l.imp.imports.length} {ws : List Silmaril.Wasm.Component.Val}
      (w : Fin l.exp.exports.length) :
      l.wire[k.val]? = some w.val → Outcome.traps ∈ specAt P l.exp I l.exp.exports[w] ws s →
      ExpRun P l I s [⟨(k, .vals ws), none⟩]

theorem exports_length_toComp (l : Linked2) : l.toComp.exports.length = l.imp.exports.length := by
  simp [toComp]

/-- **The IR side of a linked call**: an export call of the importer on `vs` whose argument
check fails is a trap of the linked IR; otherwise, for every play of the importer's core
instance answering the lifted core export on the lowered arguments after the import calls `cs`,
and every choice of component import calls `dss` related to them by `ImpRel` and answered by the
exporter's specification from the exporter instance's initial store (`ExpRun`), the linked IR
denotation (no imports) plays the export question and the lifted answer. -/
def SpecToIR : Prop :=
  ∀ (P : Profile) (l : Linked2), l.exp.Good → l.imp.Good →
    ∀ (Ie : ScalarInstance), l.exp.mod.IsInst Ie → ∀ (Ii : ScalarInstance), l.imp.mod.IsInst Ii →
    ∀ (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val),
      (checkLower l.imp.exports[j].ty.params vs = none →
        [.inr (.ask (⟨j, by simp [exports_length_toComp]⟩, .vals vs)),
          .inr (.ans (m := (⟨j, by simp [exports_length_toComp]⟩, .vals vs)) none)] ∈
          l.toComp.den (impSem P)) ∧
      ∀ (xs : List Flat), checkLower l.imp.exports[j].ty.params vs = some xs →
      ∀ (f : Ii.F.Op), f.1.val = l.imp.exports[j].core →
        f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat →
      ∀ (cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)) (w : Ii.F.Ar f) (q : Ii.HState),
        Ii.Path P (.idle Ii.store) (.inr (.ask f) :: callMoves cs ++ [.inr (.ans f w)]) q →
      ∀ (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload))),
        List.Forall₂ (ImpRel l.imp Ii) cs dss → ExpRun P l Ie Ie.store dss.flatten →
        [.inr (.ask (⟨j, by simp [exports_length_toComp]⟩, .vals vs)),
          .inr (.ans (m := (⟨j, by simp [exports_length_toComp]⟩, .vals vs))
            ((answerPayload w).bind (Adapter.up (.lift l.imp.exports[j].ty))))] ∈
          l.toComp.den (impSem P)

end IR

end Linked2

end Silmaril.Wasm.Component.Reference
