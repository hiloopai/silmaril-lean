module

public import Silmaril.Wasm.Auto.EquivFwd.Thms

/-!
# Store-to-load forwarding: tests
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivFwd.Tests

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto.Equiv Silmaril.Wasm.Auto.EquivFwd

/-- `*p = 5; return *p`. -/
def storeLoad : List Instr :=
  [.localGet ⟨0⟩, .intConst .i32 5, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩, .localGet ⟨0⟩,
    .intLoad .i32 none ⟨0⟩ ⟨0, 0⟩]

/-- `*p = 5; return 5`. -/
def storeConst : List Instr :=
  [.localGet ⟨0⟩, .intConst .i32 5, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩, .intConst .i32 5]

/-- Without forwarding the extended checker cannot tell. -/
theorem storeLoad_checkX : checkX [.i32] [] [] true storeLoad storeConst = false := by decide

/-- **Forwarding**: the load reads the stored value (its in-bounds guard repeats the store's and is
dropped). -/
theorem storeLoad_fwd : SegEquivX [.i32] [] [] true storeLoad storeConst :=
  segEquivX_of_checkXF (by decide)

/-- `p[0] = 7; p[1] = y; return p[0]` (byte offsets `0` and `4`): the load skips the store to the
disjoint word and forwards the first. -/
def skipLoad : List Instr :=
  [.localGet ⟨0⟩, .intConst .i32 7, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
    .localGet ⟨0⟩, .localGet ⟨1⟩, .intStore .i32 none ⟨0⟩ ⟨0, 4⟩,
    .localGet ⟨0⟩, .intLoad .i32 none ⟨0⟩ ⟨0, 0⟩]

def skipConst : List Instr :=
  [.localGet ⟨0⟩, .intConst .i32 7, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
    .localGet ⟨0⟩, .localGet ⟨1⟩, .intStore .i32 none ⟨0⟩ ⟨0, 4⟩, .intConst .i32 7]

theorem skipLoad_fwd : SegEquivX [.i32, .i32] [] [] true skipLoad skipConst :=
  segEquivX_of_checkXF (by decide)

/-- A load at an overlapping offset is not forwarded (`p[0]` written, bytes `2 … 5` read). -/
theorem overlap_not_fwd : checkXF [.i32, .i32] [] [] true
    [.localGet ⟨0⟩, .localGet ⟨1⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩, .localGet ⟨0⟩,
      .intLoad .i32 none ⟨0⟩ ⟨0, 2⟩]
    [.localGet ⟨0⟩, .localGet ⟨1⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩, .localGet ⟨1⟩] = false := by
  decide

/-- info: 'Silmaril.Wasm.Auto.EquivFwd.Tests.skipLoad_fwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms skipLoad_fwd

end Silmaril.Wasm.Auto.EquivFwd.Tests
