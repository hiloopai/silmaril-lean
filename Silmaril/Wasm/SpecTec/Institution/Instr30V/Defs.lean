module

public import Silmaril.Wasm.SpecTec.Institution.Instr30W.Defs

/-!
# Module typing of the wasm-3.0 script, ws5 definitions

`Instr30W` validated modules of memories and passive data segments at the repaired
primitives `withClosMod BI`. This topic adds **active data segments** whose offset is one integer
constant, and states `Module_ok` at modules of memories and arbitrary data images.

* `modeV m`: the image of a data mode, `PASSIVE` or `ACTIVE(x, instr*)`.
* `dataVA d`: `DATA(b*, modeV d.mode)`, the image of any data segment (`dataVA d = dataV d` when
  `d` is passive).
* `mdvModuleV mts dvs`: the shape of `Module_ok`'s conclusion with the memories `mts` and the data
  images `dvs` (arbitrary values), everything else empty. `mdvModuleV mts (ds.map dataVA)` is the
  image of `Instr30W.mdModule mts ds`.
* `ConstActive mts d`: `d` is active in memory `x`, `mts[x] = at lim`, and its offset is the single
  instruction `at.const n`. `DataShape mts d`: `d` is passive or `ConstActive mts d`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30V

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Institution.Instr30 (pctNil)
open Silmaril.Wasm.SpecTec.Institution.Instr30Z (memV)

/-- The image of a data mode: `PASSIVE`, or `ACTIVE(x, instr*)`. -/
def modeV : Silmaril.Wasm.DataMode → Value
  | .passive => .case "PASSIVE" (.tuple [])
  | .active x off => .case "ACTIVE" (.tuple [Encode.toValue x,
      .list (Silmaril.Wasm.SpecTec.Sim.instrsToV off)])

/-- `DATA(b*, mode)`: the image of a data segment. -/
def dataVA (d : Silmaril.Wasm.Data) : Value :=
  .case "DATA" (.tuple [.list (Silmaril.Wasm.SpecTec.Sim.FwdMem.bytesV d.bytes), modeV d.mode])

/-- **The shape of `Module_ok`'s conclusion at memories `mts` and data images `dvs`.** -/
def mdvModuleV (mts : List Silmaril.Wasm.MemoryType) (dvs : List Value) : Value :=
  .case "MODULE" (.tuple [pctNil, pctNil, pctNil, pctNil, .case "%" (.tuple [.list (mts.map memV)]),
    pctNil, pctNil, .case "%" (.tuple [.list dvs]), pctNil, .opt none, pctNil])

/-- The data segment `d` is active in a memory `x` of `mts` at address type `at`, and its offset
is the one instruction `at.const n`. -/
def ConstActive (mts : List Silmaril.Wasm.MemoryType) (d : Silmaril.Wasm.Data) : Prop :=
  ∃ (x : Silmaril.Wasm.MemIdx) (mt : Silmaril.Wasm.MemoryType)
    (b : BitVec mt.address.intType.width),
    d.mode = .active x [.intConst mt.address.intType b] ∧ mts[x.toNat]? = some mt

/-- The data segment `d` is passive, or active with a constant offset in a memory of `mts`. -/
def DataShape (mts : List Silmaril.Wasm.MemoryType) (d : Silmaril.Wasm.Data) : Prop :=
  Instr30W.Passive d ∨ ConstActive mts d

end Silmaril.Wasm.SpecTec.Institution.Instr30V
