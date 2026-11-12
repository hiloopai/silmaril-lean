module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.MemoryFwd

/-!
# The wrap at a full-size memory (gap G1)

For tables the no-wrap hypotheses of `Memory/TableFwd.lean` follow from Core's growth bound
(`TableInst.grow?` keeps `|refs| ≤ 2 ^ |at| - 1`) whenever the operand's address type is the
table's. For memories they do not: `MemInst.grow?` allows `2 ^ (|at| - 16)` pages, i.e. exactly
`2 ^ |at|` bytes, and on such a memory `memory.fill` (likewise `memory.copy-le`,
`memory.init-succ`) at the last byte produces a successor address `i + 1 = 2 ^ |at|`:

* `grow_full`: growing an empty `i32` memory without maximum by `2 ^ 16` pages succeeds and
  yields `2 ^ 32` bytes;
* `fillSucc_full`: on such a memory, `memory.fill` at `i = 2 ^ 32 - 1`, `n = 1` is a Core step
  (`MemoryStep.fillSucc`);
* `fillSucc_full_ne`: Core's successor operand `CONST I32 (i + 1)` wraps to `% 0`, while
  `memory.fill-succ`'s right-hand side has `CONST I32 % (i + 1) = % 2 ^ 32`, a constant outside
  `num_(I32)`. So the image of Core's successor is not the right-hand side of the only SpecTec
  rule for that left-hand side, and `Forward.memory` fails there as stated.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Memory

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV)

/-- The last address of a 32-bit memory, `2 ^ 32 - 1`. -/
abbrev last32 : BitVec AddrType.i32.intType.width := BitVec.allOnes _

/-- An empty `i32` memory with no maximum. -/
def emptyMem32 : MemInst := ⟨⟨.i32, ⟨0, none⟩⟩, ByteArray.empty⟩

/-- **A full-size memory is reachable**: `memory.grow` by `2 ^ 16` pages succeeds on an empty
`i32` memory with no maximum, and the result holds `2 ^ 32` bytes. -/
theorem grow_full : ∃ mi', emptyMem32.grow? (2 ^ 16) = some mi' ∧ mi'.bytes.size = 2 ^ 32 := by
  have hc₁ : emptyMem32.bytes.size / Silmaril.Wasm.Execution.Memory.pageSize + 2 ^ 16 ≤
      2 ^ (emptyMem32.type.address.width - 16) := by decide
  have hmax : emptyMem32.type.limits.max = none := rfl
  cases hg : emptyMem32.grow? (2 ^ 16) with
  | none =>
    simp only [MemInst.grow?, hc₁, hmax, reduceCtorEq, false_implies, implies_true, and_self,
      ↓reduceIte] at hg
  | some mi' =>
    refine ⟨mi', rfl, ?_⟩
    simp only [MemInst.grow?, hc₁, hmax, reduceCtorEq, false_implies, implies_true, and_self,
      ↓reduceIte, Option.some.injEq] at hg
    rw [← hg]
    simp [emptyMem32, Silmaril.Wasm.Execution.Memory.pageSize, ByteArray.size]

/-- **Core steps at the last byte of a full-size memory**: `memory.fill` at `i = 2 ^ 32 - 1`,
`n = 1`. -/
theorem fillSucc_full {H : Type} {P : Numerics.Profile} {s : Store H} {f : Frame} {x : MemIdx}
    {v : Val} {ma : Nat} {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
    (hfull : mi.bytes.size = 2 ^ 32) :
    MemoryStep P ⟨s, f, [aconst .i32 (last32), v.toAdmin, aconst .i32 1,
        .plain (.memoryFill x)]⟩
      ⟨s, f, [aconst .i32 (last32), v.toAdmin, store8 x,
        aconst .i32 (last32 + 1), v.toAdmin, aconst .i32 (1 - 1),
        .plain (.memoryFill x)]⟩ :=
  .fillSucc hm (by rw [hfull]; decide) (by decide)

/-- **The images disagree there**: Core's successor operand encodes `% 0`, the SpecTec rule's
right-hand side has `% 2 ^ 32`. -/
theorem fillSucc_full_ne :
    adminToV (aconst .i32 (last32 + 1)) ≠
      aconstV (Encode.toValue AddrType.i32) ((last32).toNat + 1) := by
  rw [State.adminToV_aconst]
  intro h
  have h1 : (last32 + 1).toNat = last32.toNat + 1 := by
    simpa only [aconstV, State.idxV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.num.injEq, Num.natN.injEq, true_and, and_true] using h
  have h2 : (last32 + 1).toNat = 0 := by decide
  have h3 : last32.toNat = 2 ^ 32 - 1 := by decide
  omega

end Silmaril.Wasm.SpecTec.Sim.Memory
