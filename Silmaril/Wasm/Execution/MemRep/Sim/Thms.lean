module

public import Silmaril.Wasm.Execution.MemRep.Sim.Defs
public import Silmaril.Wasm.Execution.MemRep.Thms
public import Silmaril.Wasm.SingleThreaded.Exec.Interp
import Silmaril.Proofs.Wasm.Execution.MemRepSim
import Silmaril.Proofs.Wasm.Execution.MemRepStep

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

The other instruction families do not read memory bytes: each commutes with `toBytes` at any
`R` (`parametricStep?_toBytes`, …, `adminStep?_toBytes`), with no law needed. Together:

* `interpHead_toBytes`: the full head step `interpHead o` commutes with `toBytes`;
* `step?_toBytes`: the driver `step?` commutes with `toBytes` whenever its head step does;
* `stepI_toBytes`: **the interpreter step** on `Config H R`, then `Config.toBytes`, is the
  interpreter step on `c.toBytes`;
* `runI_toBytes`: so is the fuelled run loop `runI o n` (with the same stop flag).

The thread level used by the component engine `core3Exec` follows: `statusC_toBytes`,
`internalC_toBytes`, `runC_toBytes`, `resume_toBytes` and `decompose?_toBytes`.

With `stepI_sound` and `runI_steps` (stated at `ByteArray`), every step or run on `R` is,
read through `toBytes`, a Core reduction.

**Host calls.** `stepI` never performs a host call: it is the host-free step (`noHost`), and a
call to a host function stops it with the call as the next instruction. The thread status
(`statusC`) reports it as a `callout` to the embedder, which resumes the thread with the result.
So host calls need no representation-level interface at this layer.
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

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Execution (MemRep LawfulMemRep)

variable {H R : Type} [MemRep R]

/-! ## The non-memory families (any representation) -/

section Families
variable (o : GrowOracle) (s : Store H R) (f : Frame) (vs : List Val) (e : Admin)

theorem parametricStep?_toBytes :
    (parametricStep? o s f vs e).map (fun p => (p.1, p.2.toBytes)) =
      parametricStep? o s.toBytes f vs e :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.parametricStep?_toBytes o s f vs e

theorem numericStep?_toBytes :
    (numericStep? o s f vs e).map (fun p => (p.1, p.2.toBytes)) =
      numericStep? o s.toBytes f vs e :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.numericStep?_toBytes o s f vs e

theorem vectorStep?_toBytes :
    (vectorStep? o s f vs e).map (fun p => (p.1, p.2.toBytes)) =
      vectorStep? o s.toBytes f vs e :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.vectorStep?_toBytes o s f vs e

theorem variableStep?_toBytes :
    (variableStep? o s f vs e).map (fun p => (p.1, p.2.toBytes)) =
      variableStep? o s.toBytes f vs e :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.variableStep?_toBytes o s f vs e

theorem tableStep?_toBytes :
    (tableStep? o s f vs e).map (fun p => (p.1, p.2.toBytes)) =
      tableStep? o s.toBytes f vs e :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.tableStep?_toBytes o s f vs e

theorem referenceStep?_toBytes :
    (referenceStep? o s f vs e).map (fun p => (p.1, p.2.toBytes)) =
      referenceStep? o s.toBytes f vs e :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.referenceStep?_toBytes o s f vs e

theorem aggNewStep?_toBytes :
    (aggNewStep? o s f vs e).map (fun p => (p.1, p.2.toBytes)) =
      aggNewStep? o s.toBytes f vs e :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.aggNewStep?_toBytes o s f vs e

theorem aggAccessStep?_toBytes :
    (aggAccessStep? o s f vs e).map (fun p => (p.1, p.2.toBytes)) =
      aggAccessStep? o s.toBytes f vs e :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.aggAccessStep?_toBytes o s f vs e

theorem refOk?_toBytes (r : Ref) (rt : Validation.CRefType) :
    refOk? s.toBytes r rt = refOk? s r rt :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.refOk?_toBytes s r rt

theorem controlStep?_toBytes :
    (controlStep? refOk? o s f vs e).map (fun p => (p.1, p.2.toBytes)) =
      controlStep? refOk? o s.toBytes f vs e :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.controlStep?_toBytes o s f vs e

theorem adminStep?_toBytes :
    (adminStep? o s f vs e).map (fun p => (p.1, p.2.toBytes)) =
      adminStep? o s.toBytes f vs e :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.adminStep?_toBytes o s f vs e

end Families

/-- **The driver** commutes with `toBytes` whenever its head step does. -/
theorem step?_toBytes {head : HeadFn H R} {head' : HeadFn H}
    (hh : ∀ s f vs e, (head s f vs e).map (fun p => (p.1, p.2.toBytes)) = head' s.toBytes f vs e)
    (c : Config H R) : (step? head c).map Config.toBytes = step? head' c.toBytes :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.step?_toBytes head head' hh _ c rfl

/-! ## The interpreter (lawful representation) -/

variable [LawfulMemRep R]

/-- **The head step** commutes with `toBytes`. -/
theorem interpHead_toBytes (o : GrowOracle) (s : Store H R) (f : Frame) (vs : List Val)
    (e : Admin) :
    (interpHead o s f vs e).map (fun p => (p.1, p.2.toBytes)) = interpHead o s.toBytes f vs e :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.interpHead_toBytes o s f vs e

/-- **Simulation of the interpreter step**: `stepI` on a configuration over a lawful
representation, read through `toBytes`, is `stepI` on the specification configuration. -/
theorem stepI_toBytes (o : GrowOracle) (c : Config H R) :
    (stepI o c).map Config.toBytes = stepI o c.toBytes :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.stepI_toBytes o c

/-- **Simulation of the run loop**: `runI` on a lawful representation, read through
`toBytes`, is `runI` on the specification configuration, with the same stop flag. -/
theorem runI_toBytes (o : GrowOracle) (n : Nat) (c : Config H R) :
    Prod.map Config.toBytes id (runI o n c) = runI o n c.toBytes :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.runI_toBytes o n c

/-! ## Threads: status, internal step, fuelled runner, resumption -/

omit [LawfulMemRep R] in
theorem config_toBytes_thread (s : Store H R) (t : Thread) :
    (t.config s).toBytes = t.config s.toBytes :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.config_toBytes_thread s t

omit [LawfulMemRep R] in
/-- Host-call redexes are found the same way on `s` and on `s.toBytes`. -/
theorem decompose?_toBytes (s : Store H R) (code : List Admin) :
    decompose? s.toBytes code = decompose? s code :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.decompose?_toBytes s _ code rfl

omit [LawfulMemRep R] in
theorem resume_toBytes (s : Store H R) (t : Thread) (r : CallResult) :
    resume s.toBytes t r = resume s t r :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.resume_toBytes s t r

/-- The computable thread status (`returned`, `callout` to the host, `running`, `stuck`) is the
same on `s` and on `s.toBytes`. -/
theorem statusC_toBytes (o : GrowOracle) (s : Store H R) (t : Thread) :
    statusC (stepI o) s.toBytes t = statusC (stepI o) s t :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.statusC_toBytes o s t

/-- The computable internal step (`core3Exec`'s stepper) commutes with `toBytes`. -/
theorem internalC_toBytes (o : GrowOracle) (s : Store H R) (t : Thread) :
    (internalC (stepI o) (s, t)).map (fun p => (p.1.toBytes, p.2)) =
      internalC (stepI o) (s.toBytes, t) :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.internalC_toBytes o s t

/-- The fuelled runner commutes with `toBytes` (same thread and status). -/
theorem runC_toBytes (o : GrowOracle) (n : Nat) (s : Store H R) (t : Thread) :
    (fun r => (r.1.toBytes, r.2)) (runC (stepI o) n s t) = runC (stepI o) n s.toBytes t :=
  Silmaril.Proofs.Wasm.Execution.MemRepStep.runC_toBytes o n s t

end Silmaril.Wasm.SingleThreaded.Exec
