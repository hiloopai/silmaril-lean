module

public import Silmaril.Wasm.Institution.Operational.Memory32Graph.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Memory32Graph

open Execution
open Execution.Runtime (Value Frame MemAddr)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation

def Op.core : Op → Instr
  | .numeric op => Prefix.emit Ranked.Graph.coreCodeSyntax.ops op
  | .load => .intLoad .i32 none MemoryQuery.index MemoryQuery.arg.toCore
  | .store => .intStore .i32 none MemoryQuery.index MemoryQuery.arg.toCore
  | .call target => .call target.index
  | .unreachable => .unreachable

def Op.lime : Op → Wasm.Lime1.Instr
  | .numeric op => Prefix.emit Ranked.Graph.limeCodeSyntax.ops op
  | .load => .intLoad .i32 none MemoryQuery.arg
  | .store => .intStore .i32 none MemoryQuery.arg
  | .call target => .call target.index
  | .unreachable => .unreachable

def Function.coreFunc (f : Function) : Wasm.Func :=
  ⟨f.decl.typeIndex, f.decl.locals.map Wasm.V1.ValType.toCore,
    f.initial.map Ranked.Graph.coreCodeSyntax.ops.value ++ f.code.map Op.core⟩

def Function.limeFunc (f : Function) : Wasm.Lime1.Func :=
  ⟨f.decl.typeIndex, f.decl.locals, f.initial.map Ranked.Graph.limeCodeSyntax.ops.value ++ f.code.map Op.lime⟩

def Function.coreInstance {H : Type} (f : Function) : Core.FuncInst H :=
  ⟨f.decl.type.toDefType, f.decl.module.toCore, .wasm f.coreFunc⟩

/-- Existing graph entry, value and frame syntax, with a new source emitter. -/
structure Syntax (A : Type) where
  admin : Ranked.Graph.Syntax A
  emit : Op → A

def coreSyntax : Syntax Core.Admin := ⟨Ranked.Graph.coreAdmin, .plain ∘ Op.core⟩
def limeSyntax : Syntax Wasm.Lime1.Execution.Admin := ⟨Ranked.Graph.limeAdmin, .source ∘ Op.lime⟩

def renderFrame {A : Type} (syn : Syntax A) (t : CallTarget) (locals : List Value) (code : List A) : A :=
  syn.admin.frame t.declaration.results.length ⟨locals, t.declaration.module⟩ code

def renderLabel {A : Type} (syn : Syntax A) (t : CallTarget) (locals : List Value) (code : List A) : List A :=
  [renderFrame syn t locals [syn.admin.label t.declaration.results.length .exit code]]

def Phase.render {A : Type} (syn : Syntax A) (t : CallTarget) : Phase → List A
  | .call args => syn.admin.values args ++ [syn.admin.ops.call t.index]
  | .invoke args => syn.admin.values args ++ syn.admin.invoke t
  | .running locals stack rest => renderLabel syn t locals (syn.admin.values stack ++ rest.map syn.emit)
  | .pending locals saved target args rest =>
      renderLabel syn t locals (syn.admin.values (saved ++ args) ++ syn.admin.invoke target ++ rest.map syn.emit)
  | .active locals saved target child rest =>
      renderLabel syn t locals (syn.admin.values saved ++ child.render syn target ++ rest.map syn.emit)
  | .trapped locals saved rest => renderLabel syn t locals (syn.admin.values saved ++ syn.admin.trap :: rest.map syn.emit)
  | .exit locals result => [renderFrame syn t locals (Nested.resultCode syn.admin.values syn.admin.trap result)]
  | .done result => Nested.resultCode syn.admin.values syn.admin.trap result

def coreStore {H : Type} (s : Core.Store H) (a : MemAddr) (m : Core.MemInst) (bytes : ByteArray) :=
  s.setMem a.value { m with bytes := bytes }

def limeStore {H : Type} (s : Wasm.Lime1.Execution.Store H) (a : MemAddr) (m : Execution.Runtime.MemInst)
    (bytes : ByteArray) := Wasm.Lime1.Execution.setMemory s a { m with data := bytes }

def coreConfig {H : Type} (s : Core.Store H) (a : MemAddr) (m : Core.MemInst) (caller : Frame)
    (t : CallTarget) (q : State) : Core.Config H :=
  ⟨coreStore s a m q.bytes, caller.toCore, q.phase.render coreSyntax t⟩

def limeConfig {H : Type} (s : Wasm.Lime1.Execution.Store H) (a : MemAddr) (m : Execution.Runtime.MemInst)
    (caller : Frame) (t : CallTarget) (q : State) : Wasm.Lime1.Execution.Config H :=
  ⟨limeStore s a m q.bytes, caller, q.phase.render limeSyntax t⟩

structure CoreLayout {H : Type} (p : Program) (s : Core.Store H) (a : MemAddr) (m : Core.MemInst) : Prop where
  mem : s.mems[a.value]? = some m
  width : m.type.address = .i32
  funcs : ∀ addr f, p.lookup addr = some f → s.funcs[addr.value]? = some f.coreInstance
  slot : ∀ addr f, p.lookup addr = some f → f.decl.module.memories[0]? = some a

structure LimeLayout {H : Type} (p : Program) (s : Wasm.Lime1.Execution.Store H) (a : MemAddr)
    (m : Execution.Runtime.MemInst) : Prop where
  mem : s.memories[a.value]? = some m
  funcs : ∀ addr f, p.lookup addr = some f →
    s.funcs[addr.value]? = some (.wasm f.decl.type f.decl.module f.limeFunc)
  slot : ∀ addr f, p.lookup addr = some f → f.decl.module.memories[0]? = some a

structure Root (p : Program) (caller : Frame) (t : CallTarget) (f : Function) : Prop where
  found : p.lookup t.address = some f
  same : f.decl = t.declaration
  resolves : t.Resolves caller

end Silmaril.Wasm.Institution.Operational.Memory32Graph
