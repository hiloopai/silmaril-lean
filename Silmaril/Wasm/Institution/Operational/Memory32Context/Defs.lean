module

public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Memory32Context

open Execution

/-- Full-width access to slot zero at static offset zero. -/
inductive Access where
  | load (address : BitVec 32)
  | store (address word : BitVec 32)

inductive Outcome where
  | value (bits : BitVec 32)
  | written (bytes : ByteArray)
  | trap

inductive Edge (bytes : ByteArray) : Access → Outcome → Prop where
  | load {address bits} (read : MemoryQuery.Edge bytes (.load address) (.value bits)) :
      Edge bytes (.load address) (.value bits)
  | loadTrap {address} (read : MemoryQuery.Edge bytes (.load address) .trap) :
      Edge bytes (.load address) .trap
  | store {address word out} (write : MemoryWrite.Edge bytes (.store address word) (.written out)) :
      Edge bytes (.store address word) (.written out)
  | storeTrap {address word} (write : MemoryWrite.Edge bytes (.store address word) .trap) :
      Edge bytes (.store address word) .trap

def Access.args : Access → List Runtime.Value
  | .load a => [.int .i32 a]
  | .store a v => [.int .i32 a, .int .i32 v]

def Access.coreOp : Access → Core.Admin
  | .load _ => .plain (.intLoad .i32 none MemoryQuery.index MemoryQuery.arg.toCore)
  | .store .. => .plain (.intStore .i32 none MemoryQuery.index MemoryQuery.arg.toCore)

def Access.limeOp : Access → Wasm.Lime1.Execution.Admin
  | .load _ => .source (.intLoad .i32 none MemoryQuery.arg)
  | .store .. => .source (.intStore .i32 none MemoryQuery.arg)

def Outcome.code {A : Type} (value : Runtime.Value → A) (trap : A) : Outcome → List A
  | .value v => [value (.int .i32 v)]
  | .written _ => []
  | .trap => [trap]

def Outcome.coreStore {H : Type} (s : Core.Store H) (a : Nat) (m : Core.MemInst) :
    Outcome → Core.Store H
  | .written bytes => s.setMem a { m with bytes := bytes }
  | _ => s

def Outcome.limeStore {H : Type} (s : Wasm.Lime1.Execution.Store H) (a : Runtime.MemAddr)
    (m : Runtime.MemInst) : Outcome → Wasm.Lime1.Execution.Store H
  | .written bytes => Wasm.Lime1.Execution.setMemory s a { m with data := bytes }
  | _ => s

end Silmaril.Wasm.Institution.Operational.Memory32Context
