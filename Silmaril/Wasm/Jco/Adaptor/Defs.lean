module

public import Silmaril.Wasm.Jco.Canon.Defs

/-!
# Adaptor modules and wrapper-style components

**Adaptor modules.** An adaptor is a core module without memory or state of its own that imports
the exports of the wrapped core instance `M` and calls them. Its functions are written in a Wasm
instruction subset (`AInstr`): `local.get`, `local.set`, `i32.const` and `call` of an `M`
export with a given number of arguments. `AFn.run` runs a function: the arguments must match the
declared parameter count (what core validation of the call guarantees), extra locals start at
`i32 0`, and the results are the final operand stack. The operand stack is a list with its top
first; `call f n` pops `n` arguments (the deepest is the first) and pushes the results.

**Wrapper-style components.** `Comp` is a component consisting of the core instance `M`, one
adaptor instance, and `canon lift` exports. A lift names its callee and its `realloc` by `CRef`:
an export of `M` (`core name`) or function `i` of the adaptor (`adapt i`). Every lift uses `M`'s
memory (the only memory). `Comp.callExport M c name vs` is the behaviour of calling the export
`name` on component values: `canonCall` of the first lift with that name, a trap if there is
none. Instantiation is not modelled: the behaviours are those from an instance state of `M`
(the adaptor has no state and no start function).

A thin wrapper (only `canon lift`s of `M`'s exports) is a `Comp` with no adaptor functions
and `core` references only.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)

/-- Instructions of adaptor functions (a Wasm subset). -/
inductive AInstr where
  | localGet (i : Nat)
  | localSet (i : Nat)
  | i32Const (c : BitVec 32)
  /-- Call the export `f` of the wrapped instance with `arity` arguments. -/
  | call (f : String) (arity : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- An adaptor function: parameter count, extra `i32` locals, body. -/
structure AFn where
  params : Nat
  locals : Nat := 0
  body : List AInstr
  deriving Repr, Inhabited, DecidableEq

/-- An adaptor module: named functions, referred to by position. -/
structure AMod where
  funcs : List (String × AFn)
  deriving Repr, Inhabited, DecidableEq

/-- The locals and the operand stack (top first) of a running adaptor function. -/
structure Frame where
  locals : List Flat
  stack : List Flat

variable (M : CoreInst)

/-- One instruction. -/
def AInstr.step : AInstr → Frame → RM M.St Frame
  | .localGet i, f =>
    match f.locals[i]? with
    | some v => pure ⟨f.locals, v :: f.stack⟩
    | none => RM.fail
  | .localSet i, f =>
    match f.stack with
    | v :: st => if i < f.locals.length then pure ⟨f.locals.set i v, st⟩ else RM.fail
    | [] => RM.fail
  | .i32Const c, f => pure ⟨f.locals, Flat.i32 c :: f.stack⟩
  | .call g n, f =>
    if n ≤ f.stack.length then do
      let rs ← M.call g (f.stack.take n).reverse
      pure ⟨f.locals, rs.reverse ++ f.stack.drop n⟩
    else RM.fail

/-- A sequence of instructions. -/
def exec : List AInstr → Frame → RM M.St Frame
  | [], f => pure f
  | i :: is, f => do
    let f' ← i.step M f
    exec is f'

/-- Run an adaptor function on its arguments; the results are the final stack, deepest first. -/
def AFn.run (fn : AFn) (args : List Flat) : RM M.St (List Flat) := do
  RM.check (args.length == fn.params)
  let f ← exec M fn.body ⟨args ++ List.replicate fn.locals (i32n 0), []⟩
  pure f.stack.reverse

/-- A core function of a wrapper-style component. -/
inductive CRef where
  /-- The export `name` of the wrapped instance. -/
  | core (name : String)
  /-- Function `i` of the adaptor module. -/
  | adapt (i : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- A `canon lift` export: the world function, its core callee, and the `realloc` option. -/
structure Lift where
  sig : Sig
  callee : CRef
  realloc : CRef
  deriving Repr, Inhabited, DecidableEq

/-- A wrapper-style component: the wrapped instance (a parameter of the semantics), one adaptor
module, and lifted exports. -/
structure Comp where
  adaptor : AMod := ⟨[]⟩
  lifts : List Lift
  deriving Repr, Inhabited, DecidableEq

namespace Comp

/-- Calling a core function of the component. -/
def callRef (c : Comp) : CRef → List Flat → RM M.St (List Flat)
  | .core n, xs => M.call n xs
  | .adapt i, xs =>
    match c.adaptor.funcs[i]? with
    | some (_, fn) => fn.run M xs
    | none => RM.fail

/-- The behaviour of calling the export `name` on component values. -/
def callExport (c : Comp) (name : String) (vs : List PVal) : RM M.St (Option PVal) :=
  match c.lifts.find? (·.sig.name == name) with
  | some l => canonCall M (c.callRef M l.realloc) (c.callRef M l.callee) l.sig vs
  | none => RM.fail

/-- The world (exported signatures) of a component. -/
def world (c : Comp) : List Sig := c.lifts.map (·.sig)

end Comp

end Silmaril.Wasm.Jco
