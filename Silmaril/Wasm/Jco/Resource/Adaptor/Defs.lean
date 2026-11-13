module

public import Silmaril.Wasm.Jco.Resource.Basic.Defs
public import Silmaril.Wasm.Jco.Adaptor.Defs

/-!
# Adaptor modules with resource built-ins, and components with handle types

An adaptor module of `Silmaril.Wasm.Jco.Adaptor` may also import the canonical built-ins
`resource.new r`, `resource.rep r` and `resource.drop r` of the component's resource types.

* `RInstr`: an `AInstr` (run over the core instance inside the component instance,
  `withTab M H.T`), or a call of a resource built-in: it pops its one argument and pushes its
  results.
* `RFn`: an adaptor function in three parts: a prologue `pre` over the parameters (no extra
  locals; it must leave the operand stack empty), an `AFn` `core`, and an epilogue `post` over the
  results of `core` (as its operand stack, with no locals). This is a function whose body is
  `pre`, then the body of `core` (with its extra locals after the parameters), then `post`; the
  three parts are kept apart so that `core` can be an export shim of `Silmaril.Wasm.Jco.Wrap`
  unchanged.
* `RComp`: a component with one core instance `M`, one such adaptor, its handle table, and
  `canon lift` exports with handle types (`canonCallR`); `RComp.callExport`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Component (Flat)

/-- Adaptor instructions: plain ones and the resource built-ins. -/
inductive RInstr where
  | base (i : AInstr)
  | resNew (r : RtId)
  | resRep (r : RtId)
  | resDrop (r : RtId)
  deriving Repr, Inhabited, DecidableEq

/-- An adaptor function: prologue, core shim, epilogue. -/
structure RFn where
  pre : List RInstr := []
  core : AFn
  post : List RInstr := []
  deriving Repr, Inhabited, DecidableEq

variable (M : CoreInst) (H : HTab)

/-- Call a built-in on the top of the stack. -/
def callTop (b : List Flat → RM (withTab M H.T).St (List Flat)) (f : Frame) :
    RM (withTab M H.T).St Frame :=
  match f.stack with
  | x :: st => do
    let ys ← b [x]
    pure ⟨f.locals, ys.reverse ++ st⟩
  | [] => RM.fail

/-- One instruction. -/
def RInstr.step : RInstr → Frame → RM (withTab M H.T).St Frame
  | .base i, f => i.step (withTab M H.T) f
  | .resNew r, f => callTop M H (builtinNew M H r) f
  | .resRep r, f => callTop M H (builtinRep M H r) f
  | .resDrop r, f => callTop M H (builtinDrop M H r) f

/-- A sequence of instructions. -/
def execR : List RInstr → Frame → RM (withTab M H.T).St Frame
  | [], f => pure f
  | i :: is, f => do
    let f' ← i.step M H f
    execR is f'

/-- Run an adaptor function on its arguments. -/
def RFn.run (fn : RFn) (args : List Flat) : RM (withTab M H.T).St (List Flat) := do
  let f ← execR M H fn.pre ⟨args, []⟩
  RM.check f.stack.isEmpty
  let rs ← fn.core.run (withTab M H.T) f.locals
  let g ← execR M H fn.post ⟨[], rs.reverse⟩
  pure g.stack.reverse

/-- A `canon lift` export with handle types. -/
structure RLift where
  sig : RSig
  callee : CRef
  realloc : CRef
  deriving Repr, Inhabited, DecidableEq

/-- A wrapper-style component with handle types: the wrapped instance and the handle table (the
parameters of the semantics), one adaptor module, and lifted exports. -/
structure RComp where
  adaptor : List (String × RFn) := []
  lifts : List RLift
  deriving Repr, Inhabited, DecidableEq

namespace RComp

/-- Calling a core function of the component. -/
def callRef (c : RComp) : CRef → List Flat → RM (withTab M H.T).St (List Flat)
  | .core n, xs => (withTab M H.T).call n xs
  | .adapt i, xs =>
    match c.adaptor[i]? with
    | some (_, fn) => fn.run M H xs
    | none => RM.fail

/-- The behaviour of calling the export `name` on boundary values. -/
def callExport (c : RComp) (name : String) (vs : List RVal) :
    RM (withTab M H.T).St (Option RVal) :=
  match c.lifts.find? (·.sig.name == name) with
  | some l => canonCallR M H (c.callRef M H l.realloc) (c.callRef M H l.callee) l.sig vs
  | none => RM.fail

end RComp

end Silmaril.Wasm.Jco.Res
