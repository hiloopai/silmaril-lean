module

public import Silmaril.Machine.Abi.Conformance.SysvScalar.Defs
public import Silmaril.Machine.Abi.Conformance.LeafArith.Witness.Defs

/-!
# `sysvScalar`: a call with a MEMORY result, for the result-storage requirements

`sretProto` is `struct big f(void)` with `struct big` a 24-byte, 8-aligned MEMORY aggregate:
its result is returned through the hidden pointer in RDI. `sretSt r` is the leaf-arith witness
state (`LeafArith.Witness.ffiSt`: the 181 code bytes at `0x401370`, `rsp = 0x8ff8`, one region
mapping every address read-write) entered at the start of the code with RDI = `r`.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.SysvScalar.Sret

open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV.Scalar (Proto Arg Agg Eights)

/-- `struct big`: 24 bytes, aligned to 8, MEMORY. -/
def bigAgg : Agg := ⟨"struct big", 24, 8, .memory⟩

theorem bigAgg_ok : bigAgg.ok = true := by decide

/-- `struct big f(void)`. -/
def sretProto : Proto := ⟨[], some (.agg bigAgg bigAgg_ok), by decide⟩

/-- The leaf-arith witness state, entered at the code's start, with RDI = `r`. -/
def sretSt (r : Silmaril.X86.Word) : Ffi.State := LeafArith.Witness.ffiSt 0 r 0 0

/-- The code: the leaf-arith region, entered at its start (181 bytes). -/
def sretCode : Code := LeafArith.region 0 181

/-- The argument tuple of `f(void)`. -/
def sretArgs : sysvScalar.V.Args sretProto := PUnit.unit

end Silmaril.Machine.Abi.Conformance.SysvScalar.Sret

end
