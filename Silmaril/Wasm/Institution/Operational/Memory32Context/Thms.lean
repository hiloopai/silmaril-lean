module

public import Silmaril.Wasm.Institution.Operational.Memory32Context.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.Memory32Context.Core
import Silmaril.Proofs.Wasm.Institution.Operational.Memory32Context.Lime1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Memory32Context

open Execution Core Numerics
open Silmaril.Wasm.SingleThreaded.Det

theorem core_iff {H : Type} {P : Profile} {s : Store H} {f : Frame} {a : Nat} {m : MemInst}
    {q : Access} {saved : List Val} {rest : List Admin} {dst : Config H}
    (lookup : s.mem? f MemoryQuery.index = some (a, m)) (is32 : m.type.address = .i32) :
    Step P noHost ⟨s, f, vals (saved ++ q.args.map Runtime.Value.toCore) ++ q.coreOp :: rest⟩ dst ↔
      ∃ out, Edge m.bytes q out ∧
        dst = ⟨out.coreStore s a m, f, vals saved ++ out.code (Val.toAdmin ∘ Runtime.Value.toCore) .trap ++ rest⟩ :=
  Proofs.core_iff lookup is32

open Execution.Runtime (Value MemAddr)

open Wasm.Lime1.Execution in

theorem lime_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {f : Execution.Runtime.Frame} {a : MemAddr} {m : Execution.Runtime.MemInst}
    {q : Access} {saved : List Value} {rest : List Wasm.Lime1.Execution.Admin} {dst : Wasm.Lime1.Execution.Config H}
    (lookup : frameMemory s f = some (a, m)) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost ⟨s, f, values (saved ++ q.args) ++ q.limeOp :: rest⟩ dst ↔
      ∃ out, Edge m.data q out ∧
        dst = ⟨out.limeStore s a m, f, values saved ++ out.code value .trap ++ rest⟩ :=
  Proofs.lime_iff lookup

end Silmaril.Wasm.Institution.Operational.Memory32Context
