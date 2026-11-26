module

import Silmaril.Languages.Python.Compile.Closure.Link.Thms
meta import Silmaril.Languages.Python.Compile.Closure.Link.Defs
meta import Silmaril.Languages.Python.Compile.Closure.Body.Defs
meta import Silmaril.Languages.Python.Compile.Closure.Defs
meta import Silmaril.Languages.Python.Core.Closure.Dispatch.Defs
meta import Silmaril.Languages.Python.Core.Closure.Call.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Silmaril.Languages.Python.Source.Scope.Defs
meta import Silmaril.Languages.Python.Source.Syntax.Defs

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Source
open Silmaril.Languages.Python.Compile.Closure.Link

private def source : Module :=
  ⟨[.functionDef "outer" [{ name := "seed" }] [
    .functionDef "child" [{ name := "x" }] [
      .return_ (some (.binary .add (.name "seed") (.name "x")))],
    .return_ (some (.call (.name "child") [.integer 2]))]]⟩

private abbrev Cont (_ : Core.Closure.Layout) := Unit

private def intAt {layout : Core.Closure.Layout} (frame : Core.Closure.Frame layout)
    (heap : Core.Closure.Heap) (slot : Core.Closure.Slot layout) : Option Int :=
  match frame.read heap slot with
  | .ok (.int value) => some value
  | _ => none

private def observation : Option (List BlockPath × Nat × Int × Int) := do
  let compiled ← (Compile.Closure.Body.compile source).toOption
  let program := link compiled
  let heap := Core.Closure.Heap.empty
  let (_, callerFrame) := Core.Closure.Frame.fresh (layout := ⟨0, 0, 0⟩) heap (fun _ => ⟨0⟩)
  let caller : Core.Closure.Call.Saved Cont := ⟨_, callerFrame, ()⟩
  let root : Core.Closure.Function := { code := program.entry, captures := Vector.ofFn (fun _ => ⟨0⟩) }
  let outer ← (Core.Closure.Dispatch.dispatch program.table (.function root) [.int 41] heap caller []).toOption
  let .closure bind [0, 0] ref captures (.ret (.call (.read name) [.integer 2])) := outer.definition.body
    | none
  let (heap, frame) := outer.entered.environment
  let (heap, frame) ← (frame.write heap bind (.function (frame.closure ref captures))).toOption
  let fn ← (frame.read heap name).toOption
  let callSite : Core.Closure.Call.Saved Cont := ⟨outer.layout, frame, ()⟩
  let entered ← (Core.Closure.Dispatch.dispatch program.table fn [.int 2] heap callSite outer.entered.stack).toOption
  let .ret (.add (.read free) (.read localSlot)) := entered.definition.body | none
  let (heap, frame) := entered.entered.environment
  let captured ← intAt frame heap free
  let argument ← intAt frame heap localSlot
  return (program.blocks.map Block.path, ref.key, captured, argument)

#guard observation == some ([[0], [0, 0]], 1, 41, 2)

#print axioms paths
#print axioms distinctPaths
#print axioms resolve_entry
#print axioms resolve_reference
