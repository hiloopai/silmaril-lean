module

public import Silmaril.Wasm.V1.Modules
public import Silmaril.Wasm.Execution.Host

/-!
# Runtime carriers for the scalar WebAssembly languages

The common store and administrative control forms are parameterized by the
source function code and instruction language. They give WebAssembly 1.0 and
Wasm Lime shared runtime data without defining either language's transitions
in terms of the other. Runtime addresses are natural numbers, distinct from
the bounded indices local to a source module.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Runtime

structure Value where
  type : NumType
  bits : BitVec type.width
  deriving DecidableEq, Repr

def Value.int (t : IntType) (bits : BitVec t.width) : Value := ⟨.int t, bits⟩
def Value.float (t : FloatType) (bits : BitVec t.width) : Value := ⟨.float t, bits⟩
def Value.zero (t : NumType) : Value := ⟨t, 0⟩

inductive AddrKind where
  | func | table | memory | global
  deriving DecidableEq, Repr

structure Addr (kind : AddrKind) where
  value : Nat
  deriving DecidableEq, Repr

abbrev FuncAddr := Addr .func
abbrev TableAddr := Addr .table
abbrev MemAddr := Addr .memory
abbrev GlobalAddr := Addr .global

inductive ExternVal where
  | func (address : FuncAddr)
  | table (address : TableAddr)
  | memory (address : MemAddr)
  | global (address : GlobalAddr)
  deriving DecidableEq, Repr

structure ExportInst where
  name : String
  value : ExternVal
  deriving DecidableEq, Repr

structure ModuleInst where
  types : List V1.FuncType := []
  funcs : List FuncAddr := []
  tables : List TableAddr := []
  memories : List MemAddr := []
  globals : List GlobalAddr := []
  exports : List ExportInst := []
  deriving DecidableEq, Repr

inductive FuncInst (Code Host : Type*) where
  | wasm (type : V1.FuncType) (module : ModuleInst) (code : Code)
  | host (type : V1.FuncType) (code : Host)
  deriving Repr

def FuncInst.type {Code Host : Type*} : FuncInst Code Host → V1.FuncType
  | .wasm t _ _ | .host t _ => t

structure TableInst where
  refs : List (Option FuncAddr)
  max : Option Nat
  deriving DecidableEq, Repr

structure MemInst where
  data : ByteArray
  max : Option Nat
  deriving DecidableEq, Repr

structure GlobalInst where
  value : Value
  mutability : Mutability
  deriving DecidableEq, Repr

structure Store (Code Host : Type*) where
  funcs : List (FuncInst Code Host) := []
  tables : List TableInst := []
  memories : List MemInst := []
  globals : List GlobalInst := []
  deriving Repr

structure Frame where
  locals : List Value := []
  module : ModuleInst
  deriving DecidableEq, Repr

inductive AdminInstr (I : Type*) where
  | source (instruction : I)
  | invoke (function : FuncAddr)
  | label (arity : Nat) (continuation : List I) (body : List (AdminInstr I))
  | frame (arity : Nat) (locals : Frame) (body : List (AdminInstr I))
  | trap
  deriving Repr

structure Config (Code Host I : Type*) where
  store : Store Code Host
  frame : Frame
  code : List (AdminInstr I)
  deriving Repr

inductive Result where
  | values (values : List Value)
  | trap
  deriving DecidableEq, Repr

/-- Host outcomes explicitly include divergence, independently of finite reductions.
`Silmaril.Wasm.Execution.Host.Outcome` is the shared carrier; see
`Silmaril/Wasm/Execution/Host.lean`. -/
abbrev HostOutcome (Code Host : Type*) :=
  Silmaril.Wasm.Execution.Host.Outcome (Store Code Host) Result

/-- Embeddings supply this relation; well-typed host behavior is a separate contract.
`Silmaril.Wasm.Execution.Host.Semantics` is the shared carrier. -/
abbrev HostSemantics (Code Host : Type*) :=
  Silmaril.Wasm.Execution.Host.Semantics Host (Store Code Host) Value Result

def FuncInst.mapCode {A B H : Type*} (f : A → B) : FuncInst A H → FuncInst B H
  | .wasm t m c => .wasm t m (f c)
  | .host t h => .host t h

@[simp] theorem FuncInst.mapCode_type {A B H : Type*} (f : A → B) (c : FuncInst A H) :
    (c.mapCode f).type = c.type := by cases c <;> rfl

def Store.mapCode {A B H : Type*} (f : A → B) (s : Store A H) : Store B H where
  funcs := s.funcs.map (FuncInst.mapCode f)
  tables := s.tables
  memories := s.memories
  globals := s.globals

mutual
def AdminInstr.map {I J : Type*} (f : I → J) : AdminInstr I → AdminInstr J
  | .source i => .source (f i)
  | .invoke a => .invoke a
  | .label n cont body => .label n (cont.map f) (AdminInstr.mapList f body)
  | .frame n fr body => .frame n fr (AdminInstr.mapList f body)
  | .trap => .trap

def AdminInstr.mapList {I J : Type*} (f : I → J) : List (AdminInstr I) → List (AdminInstr J)
  | [] => []
  | i :: is => AdminInstr.map f i :: AdminInstr.mapList f is
end

end Silmaril.Wasm.Execution.Runtime
