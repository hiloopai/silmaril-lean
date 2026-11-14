module

public import Silmaril.X86.MemoryModel.Lattice.Defs
public import Silmaril.X86.MemoryModel.Xl.Thms

/-!
# The lattice's witness executions, as hardware litmus outcomes

`tools/litmus-hw/lattice_hw.c` runs, on the host CPU, one litmus test per separating
execution of the memory-model lattice (`Lattice.Thms`); `tools/litmus-hw/lattice.py`
compares the observed outcomes with the verdicts proved in `Lattice.Witness.Thms`. This file
names, for each test, the candidate execution of its **witness outcome** (the outcome some
model of the lattice forbids), and the **row** of verdicts the models give it.

| hardware test | witness outcome | execution |
|---|---|---|
| `SB` | `0:r0=0 1:r0=0` | `Sanity.sb` |
| `SB+mfences` | `0:r0=0 1:r0=0` | `Sanity.sbMfence` |
| `SB+xchgs` | `0:r0=0 1:r0=0` | `sbXchg` |
| `MP` | `1:r0=1 1:r1=0` | `Lattice.mp` |
| `LB` | `0:r0=1 1:r0=1` | `Lattice.lb` |
| `IRIW` | `2:r0=1 2:r1=0 3:r0=1 3:r1=0` | `Lattice.iriw` |
| `2+2W` | `x=1 y=1` | `Lattice.w22` |
| `MP+movnti` | `1:r0=1 1:r1=0` | `Sanity.mpNt` |
| `MP+movnti+sfence` | `1:r0=1 1:r1=0` | `Sanity.mpNtSfence` |
| `TORN2-inline`, `TORN2-cross`, `SPLIT8` | `1:r0=torn` | `Sanity.torn` |
| `INC2` | `x=1` | `inc2` |
| `LOCKINC2` | `x=1` | `Sanity.lockInc` |
| `CoWR` | `0:r0=0` | `coWR2` |
| `CoWR` | `0:r0=2 x=1` | `coWR2b` |

`Sanity.torn` is a misaligned 2-byte store and load, split per byte: the models do not distinguish an access inside
a cache line from one that crosses it, and the 8-byte `SPLIT8` tears the same way (the
execution would split it into eight bytes instead of two).

A `Row` lists the verdicts of `sc`, `tso`, `ra`, `xl`, `cf` and `cfPlain` (`top` allows
everything). `Exec.row` computes them with the Boolean checks of `Lattice.Defs`; it is exact
when `hb` and `hbL` are closed (`Witness.Thms.verdict_of_row`).
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Lattice.Witness

open Silmaril.X86.MemoryModel.Axiomatic

/-- SB with `xchg` stores (each a locked read and a locked write), both plain loads reading
the initial zero. -/
def sbXchg : Exec where
  evs := [{ tid := 0, pos := 0, act := .read, addr := 0, size := 1, locked := true },
          { tid := 0, pos := 1, act := .write, addr := 0, size := 1, locked := true, data := [1] },
          { tid := 0, pos := 2, act := .read, addr := 1, size := 1 },
          { tid := 1, pos := 0, act := .read, addr := 1, size := 1, locked := true },
          { tid := 1, pos := 1, act := .write, addr := 1, size := 1, locked := true, data := [1] },
          { tid := 1, pos := 2, act := .read, addr := 0, size := 1 }]
  co := fun y => if y = 0 then [1] else if y = 1 then [4] else []
  rmw := [(0, 1), (3, 4)]

/-- Two unlocked increments (`inc [x]`: a read and a write), both reading the initial zero:
the lost update. -/
def inc2 : Exec where
  evs := [{ tid := 0, pos := 0, act := .read, addr := 0, size := 1 },
          { tid := 0, pos := 1, act := .write, addr := 0, size := 1, data := [1] },
          { tid := 1, pos := 0, act := .read, addr := 0, size := 1 },
          { tid := 1, pos := 1, act := .write, addr := 0, size := 1, data := [1] }]
  co := fun y => if y = 0 then [1, 3] else []

/-- CoWR with a second writer: `x := 1; r0 := x (= 0) ∥ x := 2`. -/
def coWR2 : Exec where
  evs := [{ tid := 0, pos := 0, act := .write, addr := 0, size := 1, data := [1] },
          { tid := 0, pos := 1, act := .read, addr := 0, size := 1 },
          { tid := 1, pos := 0, act := .write, addr := 0, size := 1, data := [2] }]
  co := fun y => if y = 0 then [0, 2] else []

/-- CoWR with a second writer, the other coherence violation: `x := 1; r0 := x (= 2) ∥ x := 2`,
ending with `x = 1` (the read takes a write that is coherence-before its own thread's write). -/
def coWR2b : Exec where
  evs := [{ tid := 0, pos := 0, act := .write, addr := 0, size := 1, data := [1] },
          { tid := 0, pos := 1, act := .read, addr := 0, size := 1 },
          { tid := 1, pos := 0, act := .write, addr := 0, size := 1, data := [2] }]
  rf := fun r y => if r = 1 ∧ y = 0 then some 2 else none
  co := fun y => if y = 0 then [2, 0] else []

/-- The verdicts of the lattice's models on one execution (`true`: allowed). -/
structure Row where
  sc : Bool
  tso : Bool
  ra : Bool
  xl : Bool
  cf : Bool
  cfPlain : Bool
  deriving DecidableEq, Repr

/-- The verdicts, by the Boolean checks. -/
def _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.row (x : Exec) : Row where
  sc := decide x.Sc
  tso := decide x.Tso
  ra := x.atomicB && x.uniproc.acyclicB && x.thinAir.acyclicB && x.raCohB
  xl := decide x.Xl
  cf := decide x.Sc || !x.unsplitB || !x.drfLB
  cfPlain := decide x.Sc || !x.unsplitB || !x.drfB

/-- `x` has the verdicts `r`. -/
def Verdict (x : Exec) (r : Row) : Prop :=
  (x.Sc ↔ r.sc = true) ∧ (x.Tso ↔ r.tso = true) ∧ (x.Ra ↔ r.ra = true) ∧
    (x.Xl ↔ r.xl = true) ∧ (x.Cf ↔ r.cf = true) ∧ (x.CfPlain ↔ r.cfPlain = true)

end Silmaril.X86.MemoryModel.Lattice.Witness
