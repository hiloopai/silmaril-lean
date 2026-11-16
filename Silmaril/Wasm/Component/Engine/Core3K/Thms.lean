module

public import Silmaril.Wasm.Component.Engine.Core3K.Defs
public import Silmaril.Wasm.Component.Engine.Sim.Thms
public import Silmaril.Wasm.Execution.MemRep.Inst.Thms
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Instance.Defs
import Silmaril.Proofs.Wasm.Component.Core3K

/-!
# The Core 3.0 engine over a lawful representation simulates `core3`

At a lawful representation `R` (`LawfulMemRep R`), every store operation of `core3On o R` read
through `Store.toBytes` is that operation of `core3 o` (`Execution.MemRep.Sim.Thms`,
`Execution.MemRep.Inst.Thms`, and here `Core3.externTypeE?_toBytes`,
`Core3.prepareE?_toBytes`, `Core3.statusE_toBytes`):

* `core3Sim o R : (core3 o).StoreSim (core3Impl o R)`, with store map `Store.toBytes`: the engine
  simulation (`CoreEngine.StoreSim`). Its internal-step fields are `internalC_toBytes`.
* `core3ExecSim o R`: the steppers `core3Exec o` and `core3ExecOn o R` commute with it.

Consequences (`Engine.Sim.Thms`): runs of `core3On o R` map to runs of `core3 o` and back
(`core3On_steps`, `core3On_steps_lift`), divergence agrees (`core3On_diverges_iff`), the fuel
loops agree (`core3ExecOn_runCore`), and the engine laws hold (`core3On_lawful`, from
`core3_lawful`). In particular all of this holds for `core3K o` (memories as `KMem` trees).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution (MemRep LawfulMemRep)

namespace Core3

variable {H R : Type} [MemRep R]

theorem externTypeE?_toBytes (s : Store H R) (xa : ExternAddr) :
    externTypeE? s.toBytes xa = externTypeE? s xa :=
  Silmaril.Proofs.Wasm.Component.Core3K.externTypeE?_toBytes s xa

theorem funcTypeE?_toBytes (s : Store H R) (a : Nat) : funcTypeE? s.toBytes a = funcTypeE? s a :=
  rfl

/-- **Instantiation of the engine commutes with `toBytes`.** -/
theorem prepareE?_toBytes [LawfulMemRep R] (s : Store H R) (m : Module) (xas : List ExternAddr) :
    prepareE? s.toBytes m xas = (prepareE? s m xas).map fun r => (r.1.toBytes, r.2) :=
  Silmaril.Proofs.Wasm.Component.Core3K.prepareE?_toBytes s m xas

theorem statusE_toBytes [LawfulMemRep R] (o : SingleThreaded.GrowOracle) (s : Store H R)
    (t : SingleThreaded.Thread) : statusE o s.toBytes t = statusE o s t :=
  Silmaril.Proofs.Wasm.Component.Core3K.statusE_toBytes o s t

/-- An internal step on `Store H R` is, through `toBytes`, an internal step of `core3 o`. -/
theorem internalC_some_toBytes [LawfulMemRep R] (o : SingleThreaded.GrowOracle)
    {s s' : Store H R} {t t' : SingleThreaded.Thread}
    (h : SingleThreaded.internalC (SingleThreaded.Exec.stepI o) (s, t) = some (s', t')) :
    SingleThreaded.internalC (SingleThreaded.Exec.stepI o) (s.toBytes, t) = some (s'.toBytes, t') :=
  Silmaril.Proofs.Wasm.Component.Core3K.internalC_some_toBytes o h

/-- An internal step from `s.toBytes` is the image of an internal step from `s`. -/
theorem internalC_lift_toBytes [LawfulMemRep R] (o : SingleThreaded.GrowOracle) {s : Store H R}
    {t : SingleThreaded.Thread} {c' : Store H × SingleThreaded.Thread}
    (h : SingleThreaded.internalC (SingleThreaded.Exec.stepI o) (s.toBytes, t) = some c') :
    ∃ s' t', SingleThreaded.internalC (SingleThreaded.Exec.stepI o) (s, t) = some (s', t') ∧
      c' = (s'.toBytes, t') :=
  Silmaril.Proofs.Wasm.Component.Core3K.internalC_lift_toBytes o h

end Core3

open Core3

variable (o : SingleThreaded.GrowOracle) (R : Type) [MemRep R] [LawfulMemRep R]

/-- **`core3On o R` simulates `core3 o`** through `Store.toBytes`. -/
def core3Sim : (core3 o).StoreSim (core3Impl o R) where
  φ := Store.toBytes
  empty _ := rfl
  externType? s v := externTypeE?_toBytes s v
  prepare? s m vs := prepareE?_toBytes s m vs
  allocHost s ft h := SingleThreaded.allocHost_toBytes s ft h
  funcType? s a := funcTypeE?_toBytes s a
  memAddrType? s m := SingleThreaded.memAddrType?_toBytes s m
  memSize? s m := SingleThreaded.memSize?_toBytes s m
  memRead? s m st len := SingleThreaded.memRead?_toBytes s m st len
  memWrite? s m st bs := SingleThreaded.memWrite?_toBytes s m st bs
  tableAddrType? s t := SingleThreaded.tableAddrType?_toBytes s t
  tableFunc? s t i := SingleThreaded.tableFunc?_toBytes s t i
  status s t := statusE_toBytes o s t
  internal h := internalC_some_toBytes o h
  internal_lift h := internalC_lift_toBytes o h
  resume s t r := SingleThreaded.Exec.resume_toBytes s t (toCR r)

/-- The steppers commute with the simulation. -/
theorem core3ExecSim : CoreEngine.ExecSim (core3Sim o R) (core3Exec o) (core3ExecOn o R) where
  step? c := (SingleThreaded.Exec.internalC_toBytes o c.1 c.2).symm

variable {o R}

/-- Runs of `core3On o R` are, through `toBytes`, runs of `core3 o`. -/
theorem core3On_steps {H : Type} {c c' : (core3On o R).Config H} (h : (core3On o R).Steps c c') :
    (core3 o).Steps (c.1.toBytes, c.2) (c'.1.toBytes, c'.2) :=
  (core3Sim o R).steps h

/-- Runs of `core3 o` from a configuration read through `toBytes` are images of runs of
`core3On o R`. -/
theorem core3On_steps_lift {H : Type} {c : (core3On o R).Config H} {d : (core3 o).Config H}
    (h : (core3 o).Steps (c.1.toBytes, c.2) d) :
    ∃ c', (core3On o R).Steps c c' ∧ d = (c'.1.toBytes, c'.2) :=
  (core3Sim o R).steps_lift h

theorem core3On_diverges_iff {H : Type} {c : (core3On o R).Config H} :
    (core3On o R).Diverges c ↔ (core3 o).Diverges (c.1.toBytes, c.2) :=
  (core3Sim o R).diverges_iff

/-- The fuel loop of `core3ExecOn o R`, read through `toBytes`, is that of `core3Exec o`. -/
theorem core3ExecOn_runCore {H : Type} (n : Nat) (c : (core3On o R).Config H) :
    (core3Exec o).runCore n (c.1.toBytes, c.2) =
      Prod.map (fun c' => (c'.1.toBytes, c'.2)) id ((core3ExecOn o R).runCore n c) :=
  (core3ExecSim o R).runCore n c

/-- **The engine laws hold over a lawful representation**, from those of `core3 o`. -/
instance core3On_lawful : (core3On o R).Lawful :=
  (core3Sim o R).lawful

end Silmaril.Wasm.Component.Engine
