module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat.Common
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat.Lime1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat

open Execution
open Execution.Runtime (Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {entry : Entry} {program : Graph.Program} {tables : Source.Tables}
  {outerFrame : Runtime.Frame} {index : FuncIdx} {args : List Value}

/-- The same static guard supplies fresh numeric and lookup evidence for
any live local vector of the declared types. -/
theorem site_exists (guard : Guard entry program tables) {locals : List Value}
    (typed : locals.map Value.type = entry.owner.localTypes) :
    Nonempty (Site entry program tables locals) :=
  Proofs.site_exists guard typed

section Core

open Execution.Core

variable {H : Type} {P : Numerics.Profile} {s : Store H}

/-- Exact finite readback from typed invocation, through any number of
lookups and back edges, including partial prefixes and cleanup. -/
theorem core_run_iff (ready : entry.Checked program tables outerFrame index args)
    (guard : Guard entry program tables)
    (allocated : s.funcs[entry.address.value]? = some entry.coreInstance)
    (table : Source.Tables.CoreAllocated tables s)
    (targets : ∀ active : Source.Activation, active.Checked program tables → active.binding.site.CoreAllocated program s)
    (links : program.CoreLinksAllocated s) {dst : Config H} :
    let start := coreSource s outerFrame index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).coreInvoke s outerFrame args
    Steps P noHost start dst ↔ dst ∈ [start, invoke] ∨
      Readback entry program guard.indices (coreRecipes entry program tables s outerFrame) (corePhase entry s outerFrame)
        (Stop entry program (Resume.corePhase entry s outerFrame) (Graph.coreConfig s outerFrame entry.cont.target)
          (entry.insideTail.map Graph.coreEmit)) (entry.initial args) dst :=
  Proofs.Core.whole_run (P := P) ready guard allocated table targets links

end Core

section Lime1

open Wasm.Lime1.Execution

variable {H : Type} {s : Store H}

/-- Exact finite readback from typed invocation, through any number of
lookups and back edges, including partial prefixes and cleanup. -/
theorem lime_run_iff (ready : entry.Checked program tables outerFrame index args)
    (guard : Guard entry program tables)
    (allocated : s.funcs[entry.address.value]? = some entry.limeInstance)
    (table : Source.Tables.LimeAllocated tables s)
    (targets : ∀ active : Source.Activation, active.Checked program tables → active.binding.site.LimeAllocated program s)
    (links : program.LimeLinksAllocated s) {dst : Config H} :
    let start := limeSource s outerFrame index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).limeInvoke s outerFrame args
    Steps CallFrame.limeNoHost start dst ↔ dst ∈ [start, invoke] ∨
      Readback entry program guard.indices (limeRecipes entry program tables s outerFrame) (limePhase entry s outerFrame)
        (Stop entry program (Resume.limePhase entry s outerFrame) (Graph.limeConfig s outerFrame entry.cont.target)
          (entry.insideTail.map Graph.limeEmit)) (entry.initial args) dst :=
  Proofs.Lime1.whole_run ready guard allocated table targets links

end Lime1

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat
