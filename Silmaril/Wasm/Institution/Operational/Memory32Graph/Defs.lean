module

public import Silmaril.Wasm.Institution.Operational.Memory32Context.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Memory32Graph

open Execution.Runtime (Value Frame FuncAddr)
open CallContinuation
open CallContinuation.OuterCall (CallTarget Declaration)
open CallContinuation.OuterCall.Computed

inductive Op where
  | numeric (op : Prefix.Op)
  | load
  | store
  | call (target : CallTarget)
  | unreachable

structure Function where
  decl : Declaration
  initial : List Value
  code : List Op

abbrev Program := List (Option Function)
abbrev Program.lookup (p : Program) (a : FuncAddr) : Option Function := p[a.value]?.join
abbrev i32 : NumType := .int .i32
abbrev Function.localTypes (f : Function) := f.decl.params ++ f.decl.locals

/-- Source typing in operand delivery order. Each direct index resolves in the
declaring module to the exact checked function declaration. -/
inductive Typed (p : Program) (decl : Declaration) : List NumType → List Op → Prop where
  | done {stack} (types : stack = decl.results) : Typed p decl stack []
  | numeric {stack next op rest}
      (check : Prefix.checkOp (decl.params ++ decl.locals) stack.reverse op = some next.reverse)
      (tail : Typed p decl next rest) : Typed p decl stack (.numeric op :: rest)
  | load {stack saved rest} (types : stack = saved ++ [i32])
      (tail : Typed p decl (saved ++ [i32]) rest) : Typed p decl stack (.load :: rest)
  | store {stack saved rest} (types : stack = saved ++ [i32, i32])
      (tail : Typed p decl saved rest) : Typed p decl stack (.store :: rest)
  | call {stack saved rest target callee} (types : stack = saved ++ target.declaration.params)
      (link : decl.module.funcs[target.index.toNat]? = some target.address)
      (found : p.lookup target.address = some callee) (same : callee.decl = target.declaration)
      (tail : Typed p decl (saved ++ target.declaration.results) rest) :
      Typed p decl stack (.call target :: rest)
  | unreachable {stack rest} : Typed p decl stack (.unreachable :: rest)

def Program.Checked (p : Program) : Prop :=
  ∀ a f, p.lookup a = some f → Typed p f.decl (f.initial.map Value.type) f.code

/-- One active child per frame. The store lives once, outside the entire phase. -/
inductive Phase where
  | call (args : List Value)
  | invoke (args : List Value)
  | running (locals stack : List Value) (rest : List Op)
  | pending (locals saved : List Value) (target : CallTarget) (args : List Value) (rest : List Op)
  | active (locals saved : List Value) (target : CallTarget) (child : Phase) (rest : List Op)
  | trapped (locals saved : List Value) (rest : List Op)
  | exit (locals : List Value) (result : Nested.Result)
  | done (result : Nested.Result)

structure State where
  bytes : ByteArray
  phase : Phase

def resultTyped (decl : Declaration) : Nested.Result → Prop
  | .values vs => vs.map Value.type = decl.results
  | .trap => True

def Phase.Frame : Phase → Prop
  | .running .. | .pending .. | .active .. | .trapped .. | .exit .. => True
  | _ => False

def afterChild (locals saved : List Value) (target : CallTarget) (rest : List Op) : Phase → Phase
  | .done (.values out) => .running locals (saved ++ out) rest
  | .done .trap => .trapped locals saved rest
  | child => .active locals saved target child rest

def afterNumeric (locals : List Value) (rest : List Op) : Prefix.Outcome → Phase
  | .values out => .running locals out rest
  | .trap saved => .trapped locals saved rest

def afterAccess (locals saved : List Value) (rest : List Op) : Memory32Context.Outcome → Phase
  | .value bits => .running locals (saved ++ [.int .i32 bits]) rest
  | .written _ => .running locals saved rest
  | .trap => .trapped locals saved rest

def nextBytes (bytes : ByteArray) : Memory32Context.Outcome → ByteArray
  | .written out => out
  | _ => bytes

inductive Ready (p : Program) : Function → Phase → Prop where
  | call {f args} (typed : args.map Value.type = f.decl.params) : Ready p f (.call args)
  | invoke {f args} (typed : args.map Value.type = f.decl.params) : Ready p f (.invoke args)
  | running {f locals stack rest} (typed : locals.map Value.type = f.localTypes)
      (code : Typed p f.decl (stack.map Value.type) rest) : Ready p f (.running locals stack rest)
  | pending {f locals saved target args rest callee} (typed : locals.map Value.type = f.localTypes)
      (found : p.lookup target.address = some callee) (same : callee.decl = target.declaration)
      (inputs : args.map Value.type = target.declaration.params)
      (resume : Typed p f.decl (saved.map Value.type ++ target.declaration.results) rest) :
      Ready p f (.pending locals saved target args rest)
  | active {f locals saved target child rest callee} (typed : locals.map Value.type = f.localTypes)
      (found : p.lookup target.address = some callee) (same : callee.decl = target.declaration)
      (frame : child.Frame) (inside : Ready p callee child)
      (resume : Typed p f.decl (saved.map Value.type ++ target.declaration.results) rest) :
      Ready p f (.active locals saved target child rest)
  | trapped {f locals saved rest} : Ready p f (.trapped locals saved rest)
  | exit {f locals result} (typed : resultTyped f.decl result) : Ready p f (.exit locals result)
  | done {f result} (typed : resultTyped f.decl result) : Ready p f (.done result)

/-- Independent finite rules for the checked instruction fragment. Only the
active-child rule has a recursive premise, and all descendants share the bytes. -/
inductive Step (p : Program) : Function → State → State → Prop where
  | resolve {f bytes args} : Step p f ⟨bytes, .call args⟩ ⟨bytes, .invoke args⟩
  | enter {f bytes args} :
      Step p f ⟨bytes, .invoke args⟩ ⟨bytes, .running (f.decl.frame args).locals f.initial f.code⟩
  | numeric {f bytes locals stack op rest out} (move : Prefix.Reduce locals stack op out) :
      Step p f ⟨bytes, .running locals stack (.numeric op :: rest)⟩ ⟨bytes, afterNumeric locals rest out⟩
  | load {f bytes locals saved address rest out} (move : Memory32Context.Edge bytes (.load address) out) :
      Step p f ⟨bytes, .running locals (saved ++ [.int .i32 address]) (.load :: rest)⟩
        ⟨nextBytes bytes out, afterAccess locals saved rest out⟩
  | store {f bytes locals saved address word rest out}
      (move : Memory32Context.Edge bytes (.store address word) out) :
      Step p f ⟨bytes, .running locals (saved ++ [.int .i32 address, .int .i32 word]) (.store :: rest)⟩
        ⟨nextBytes bytes out, afterAccess locals saved rest out⟩
  | call {f bytes locals saved args target rest} (typed : args.map Value.type = target.declaration.params) :
      Step p f ⟨bytes, .running locals (saved ++ args) (.call target :: rest)⟩
        ⟨bytes, .pending locals saved target args rest⟩
  | pending {f bytes locals saved target args rest callee}
      (found : p.lookup target.address = some callee) :
      Step p f ⟨bytes, .pending locals saved target args rest⟩
        ⟨bytes, .active locals saved target (.running (callee.decl.frame args).locals callee.initial callee.code) rest⟩
  | active {f bytes locals saved target child rest callee next}
      (found : p.lookup target.address = some callee) (move : Step p callee ⟨bytes, child⟩ next) :
      Step p f ⟨bytes, .active locals saved target child rest⟩
        ⟨next.bytes, afterChild locals saved target rest next.phase⟩
  | unreachable {f bytes locals stack rest} :
      Step p f ⟨bytes, .running locals stack (.unreachable :: rest)⟩ ⟨bytes, .trapped locals stack rest⟩
  | discard {f bytes locals stack rest kept tail} (move : Prefix.Discard stack rest kept tail) :
      Step p f ⟨bytes, .trapped locals stack rest⟩ ⟨bytes, .trapped locals kept tail⟩
  | complete {f bytes locals stack} :
      Step p f ⟨bytes, .running locals stack []⟩ ⟨bytes, .exit locals (.values stack)⟩
  | trapExit {f bytes locals} : Step p f ⟨bytes, .trapped locals [] []⟩ ⟨bytes, .exit locals .trap⟩
  | exit {f bytes locals result} : Step p f ⟨bytes, .exit locals result⟩ ⟨bytes, .done result⟩

abbrev Runs (p : Program) (f : Function) := Relation.ReflTransGen (Step p f)

end Silmaril.Wasm.Institution.Operational.Memory32Graph
