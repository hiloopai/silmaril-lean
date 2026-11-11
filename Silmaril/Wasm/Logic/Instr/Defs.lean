module

public import Silmaril.Wasm.Logic.Hoare.Defs

/-!
# Instruction rules for the every-run logic: definitions

The instruction rules of `Silmaril.Wasm.Logic.Instr.Thms` are stated once for both
readings of the every-run logic (`Silmaril.Wasm.Logic.Hoare`):

* `Corr.part`: `Wp .part = HWP`, partial correctness and safety;
* `Corr.total`: `Wp .total = TWP`, total correctness.

`ProfileFree i` says that the head steps of the instruction `i` do not consult
the numeric profile: all instructions except the scalar float unary and binary
operations and conversions, the vector float and relaxed operations, and
`memory.grow`/`table.grow`. For a profile-free family instruction one head step
is the only one, so its rule needs one witness (`Wp.det`); the others are
covered by quantifying over all head steps (`Wp.fam`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type}

/-- The two readings of the every-run logic. -/
inductive Corr where
  /-- Partial correctness and safety (`HWP`). -/
  | part
  /-- Total correctness (`TWP`). -/
  | total
  deriving DecidableEq

/-- The every-run weakest precondition in either reading. -/
def Wp : Corr → Profile → HostSemantics H → Store H → Frame → List Admin → Post H → Prop
  | .part => HWP
  | .total => TWP

@[simp] theorem wp_part (P : Profile) (host : HostSemantics H) :
    (Wp .part P host : Store H → Frame → List Admin → Post H → Prop) = HWP P host := rfl

@[simp] theorem wp_total (P : Profile) (host : HostSemantics H) :
    (Wp .total P host : Store H → Frame → List Admin → Post H → Prop) = TWP P host := rfl

/-- Instructions whose head steps do not consult the numeric profile. -/
def ProfileFree : Instr → Prop
  | .floatUnOp .. | .floatBinOp .. | .convert _ | .memoryGrow _ | .tableGrow _
  | .vecFloatUnOp .. | .vecFloatBinOp .. | .vecFloatTernOp .. | .vecIntBinOp ..
  | .vecIntTernOp .. | .vecSwizzle .relaxedSwizzle | .vecExtBinOp .. | .vecExtTernOp ..
  | .vecConvert .. => False
  | _ => True

/-- The deterministic profile used to compare profile-free steps. -/
abbrev detP : Profile := Profile.deterministic fun _ _ _ _ => false

end Silmaril.Wasm.Logic.Hoare
