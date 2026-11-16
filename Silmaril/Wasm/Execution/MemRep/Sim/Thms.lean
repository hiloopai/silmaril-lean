module

public import Silmaril.Wasm.Execution.MemRep.Sim.Defs
public import Silmaril.Wasm.Execution.MemRep.Thms
public import Silmaril.Wasm.SingleThreaded.Exec.Memory
import Silmaril.Proofs.Wasm.Execution.MemRepSim

/-! # The memory-family interpreter step over a lawful representation

At a lawful representation `R` (`LawfulMemRep R`), reading every memory through
`MemRep.toBytes` commutes with the memory family of the computable interpreter:

* `memoryStep?_toBytes`: `memoryStep?` on `s : Store H R`, then `Config.toBytes`, is
  `memoryStep?` on `s.toBytes`, the `ByteArray` store that `stepI` runs on;
* `Mem.stepArgs_toBytes`: the same for each memory instruction on its exact arguments.

So every load, store, `memory.size`/`grow`/`fill`/`copy`/`init` and `data.drop` step run on
`R` (for example `KMem`) is, read through `toBytes`, the specification's step; with
`memoryStep?_sound` it is a Core `MemoryStep`. The store lemmas: `Store.mem?_toBytes`,
`Store.setMem_toBytes`, `MemInst.pages_toBytes`, `MemInst.grow?_toBytes`.

The other instruction families do not read memory bytes, but `stepI` is not yet generic in
`R`; lifting this to `stepI` is the next step (see `docs/projects/wasm-memrep.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Core

variable {H R : Type} [MemRep R]

theorem Store.mem?_toBytes (s : Store H R) (f : Frame) (x : MemIdx) :
    s.toBytes.mem? f x = (s.mem? f x).map (fun p => (p.1, p.2.toBytes)) :=
  Silmaril.Proofs.Wasm.Execution.MemRepSim.mem?_toBytes s f x

theorem Store.setMem_toBytes (s : Store H R) (a : Nat) (mi : MemInst R) :
    (s.setMem a mi).toBytes = s.toBytes.setMem a mi.toBytes :=
  Silmaril.Proofs.Wasm.Execution.MemRepSim.setMem_toBytes s a mi

variable [LawfulMemRep R]

theorem MemInst.pages_toBytes (mi : MemInst R) : mi.toBytes.pages = mi.pagesR :=
  Silmaril.Proofs.Wasm.Execution.MemRepSim.pages_toBytes mi

theorem MemInst.grow?_toBytes (mi : MemInst R) (n : Nat) :
    (mi.growR? n).map MemInst.toBytes = mi.toBytes.grow? n :=
  Silmaril.Proofs.Wasm.Execution.MemRepSim.grow?_toBytes mi n

end Silmaril.Wasm.Execution.Core

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution (MemRep LawfulMemRep)

variable {H R : Type} [MemRep R] [LawfulMemRep R]

theorem Mem.stepArgs_toBytes (o : GrowOracle) (s : Store H R) (f : Frame) (args : List Val)
    (e : Admin) :
    (Mem.stepArgs o s f args e).map Config.toBytes = Mem.stepArgs o s.toBytes f args e :=
  Silmaril.Proofs.Wasm.Execution.MemRepSim.stepArgs_toBytes s f args o e

/-- **Simulation**: the memory-family head step on a lawful representation, read through
`toBytes`, is the head step on the specification store. -/
theorem memoryStep?_toBytes (o : GrowOracle) (s : Store H R) (f : Frame) (vs : List Val)
    (e : Admin) :
    (memoryStep? o s f vs e).map (fun p => (p.1, p.2.toBytes)) =
      memoryStep? o s.toBytes f vs e :=
  Silmaril.Proofs.Wasm.Execution.MemRepSim.memoryStep?_toBytes o s f vs e

end Silmaril.Wasm.SingleThreaded.Exec
