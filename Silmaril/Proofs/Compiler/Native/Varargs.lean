module

public import Silmaril.Compiler.Native.Varargs.Defs
public import Silmaril.Machine.SystemV.Abi.Thms
/-! Exact named stack extents and compatibility with the existing abstract
System V va_list cursors. No emitted-machine execution theorem is asserted. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Varargs
open Silmaril.Machine.SystemV.Abi

private theorem foldl_extent_le_iff (arguments : List Argument) (initial limit : Nat) :
    arguments.foldl (fun finish argument => match argument.stackOffset with
      | none => finish
      | some offset => max finish (offset + alignUp argument.object.size 8)) initial ≤ limit ↔
    initial ≤ limit ∧ ∀ argument ∈ arguments, ∀ offset,
      argument.stackOffset = some offset → offset + alignUp argument.object.size 8 ≤ limit := by
  induction arguments generalizing initial with
  | nil => simp
  | cons argument rest ih =>
    rw [List.foldl_cons, ih]
    cases selected : argument.stackOffset with
    | none => simp [selected]
    | some offset => simp [selected, and_assoc]

/-- The exact least upper bound of actual named stack-slot ends. This reads
`plan.arguments`; final call-area padding and non-stack arguments contribute no
extent. It does not assume the plan came from a successful ABI classification. -/
theorem namedStackEnd_le_iff (plan : CallPlan) (limit : Nat) :
    namedStackEnd plan ≤ limit ↔ ∀ argument ∈ plan.arguments, ∀ offset,
      argument.stackOffset = some offset → offset + alignUp argument.object.size 8 ≤ limit := by
  unfold namedStackEnd
  constructor
  · intro bound
    exact ((foldl_extent_le_iff plan.arguments 0 limit).mp bound).2
  · intro bounded
    exact (foldl_extent_le_iff plan.arguments 0 limit).mpr ⟨Nat.zero_le _, bounded⟩

/-- Every actual named stack slot lies below the computed unpadded end. -/
theorem namedStackEnd_member_le (plan : CallPlan) (argument : Argument)
    (member : argument ∈ plan.arguments) (offset : Nat)
    (selected : argument.stackOffset = some offset) :
    offset + alignUp argument.object.size 8 ≤ namedStackEnd plan :=
  (namedStackEnd_le_iff plan (namedStackEnd plan)).mp (Nat.le_refl _) argument member offset selected

/-- Absence of named stack arguments yields no overflow offset, independently
of whatever final alignment padding is reserved by the call plan. -/
theorem namedStackEnd_no_stack (plan : CallPlan)
    (registers : ∀ argument ∈ plan.arguments, argument.stackOffset = none) :
    namedStackEnd plan = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (namedStackEnd_le_iff plan 0).mpr
  intro argument member offset selected
  rw [registers argument member] at selected
  cases selected

/-- The exact bound is determined by the actual argument list. -/
theorem namedStackEnd_congr {first second : CallPlan} (same : first.arguments = second.arguments) :
    namedStackEnd first = namedStackEnd second := by
  simp only [namedStackEnd, same]

/-- Final high-address call-area padding cannot move the first unnamed slot. -/
theorem namedStackEnd_stackSize (plan : CallPlan) (paddedSize : Nat) :
    namedStackEnd {plan with stackSize := paddedSize} = namedStackEnd plan := rfl

/-- Bounds for a supplied actual argument inventory lift to its exact end.
A general invariant for all successful `plan` executions is a separate result. -/
theorem namedStackEnd_le_stackSize (plan : CallPlan)
    (bounded : ∀ argument ∈ plan.arguments, ∀ offset,
      argument.stackOffset = some offset → offset + alignUp argument.object.size 8 ≤ plan.stackSize) :
    namedStackEnd plan ≤ plan.stackSize :=
  (namedStackEnd_le_iff plan plan.stackSize).mpr bounded

/-- Starting from the actual named extent retains both register-bank cursors,
the unpadded overflow position and the unchanged register-save base. -/
theorem start_named_extent (plan : CallPlan) (overflowBase save : Nat) :
    VaList.start plan (overflowBase + namedStackEnd plan) save =
      ⟨8 * plan.gpUsed, 48 + 16 * plan.vectorUsed,
        overflowBase + namedStackEnd plan, save⟩ := rfl

/-- Overflow-pointer bounds are exactly bounds on all actual named stack ends. -/
theorem start_overflow_le_iff (plan : CallPlan) (overflowBase save limit : Nat) :
    (VaList.start plan (overflowBase + namedStackEnd plan) save).overflowArgArea ≤ overflowBase + limit ↔
      ∀ argument ∈ plan.arguments, ∀ offset,
        argument.stackOffset = some offset → offset + alignUp argument.object.size 8 ≤ limit := by
  change overflowBase + namedStackEnd plan ≤ overflowBase + limit ↔ _
  rw [Nat.add_le_add_iff_left, namedStackEnd_le_iff]

/-- Existing register-bank bounds suffice for the concrete named-extent start.
Memory, pointer arithmetic and emitted stores remain separate obligations. -/
theorem start_named_valid (plan : CallPlan) (overflowBase save : Nat)
    (gp : plan.gpUsed ≤ 6) (fp : plan.vectorUsed ≤ 8) :
    (VaList.start plan (overflowBase + namedStackEnd plan) save).valid :=
  VaList.start_valid plan _ save gp fp

/-- The actual overflow branch consumes neither GP nor FP save slots. -/
theorem next_stack_preserves_banks (state : VaList) (object : Object) (address : Nat)
    (stack : (state.next object).1 = .stack address) :
    (state.next object).2.gpOffset = state.gpOffset ∧
    (state.next object).2.fpOffset = state.fpOffset ∧
    (state.next object).2.regSaveArea = state.regSaveArea := by
  unfold VaList.next
  split
  · rename_i available
    simp only [VaList.next, available, ↓reduceIte] at stack
    cases stack
  · exact ⟨rfl, rfl, rfl⟩

/-- Insufficient GP capacity sends the entire object to the real stack branch. -/
theorem next_stack_of_gp_insufficient (state : VaList) (object : Object)
    (insufficient : 48 < state.gpOffset + 8 * gpCount object) :
    state.next object =
      (.stack (alignUp state.overflowArgArea (max 8 object.align)),
        { state with
          overflowArgArea := alignUp (alignUp state.overflowArgArea (max 8 object.align) + object.size) 8}) := by
  unfold VaList.next
  split
  · rename_i available
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at available
    omega
  · rfl

/-- Insufficient FP capacity likewise rolls back the entire mixed-class object. -/
theorem next_stack_of_fp_insufficient (state : VaList) (object : Object)
    (insufficient : 176 < state.fpOffset + 16 * vectorCount object) :
    state.next object =
      (.stack (alignUp state.overflowArgArea (max 8 object.align)),
        { state with
          overflowArgArea := alignUp (alignUp state.overflowArgArea (max 8 object.align) + object.size) 8}) := by
  unfold VaList.next
  split
  · rename_i available
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at available
    omega
  · rfl

/-- The register branch is the actual next operation, with separate bank counts
and unchanged overflow position/save base. This is a cursor theorem, not a read. -/
theorem next_registers (state : VaList) (object : Object)
    (memory : memoryClass object = false) (wide : needsWideVector object = false)
    (gp : state.gpOffset + 8 * gpCount object ≤ 48)
    (fp : state.fpOffset + 16 * vectorCount object ≤ 176) :
    state.next object = (.registers state.gpOffset state.fpOffset,
      { state with
        gpOffset := state.gpOffset + 8 * gpCount object
        fpOffset := state.fpOffset + 16 * vectorCount object}) := by
  simp only [VaList.next, memory, wide, Bool.not_false, Bool.true_and,
    decide_eq_true gp, decide_eq_true fp, ↓reduceIte]

/-- After a real stack rollback, a following compatible object still sees the
original bank cursors. Its successful memory reconstruction is not assumed. -/
theorem next_registers_after_rollback (state : VaList) (blocked object : Object) (address : Nat)
    (stack : (state.next blocked).1 = .stack address)
    (memory : memoryClass object = false) (wide : needsWideVector object = false)
    (gp : state.gpOffset + 8 * gpCount object ≤ 48)
    (fp : state.fpOffset + 16 * vectorCount object ≤ 176) :
    ((state.next blocked).2.next object).1 = .registers state.gpOffset state.fpOffset := by
  obtain ⟨gpSame, fpSame, _⟩ := next_stack_preserves_banks state blocked address stack
  have gpBound : (state.next blocked).2.gpOffset + 8 * gpCount object ≤ 48 := by
    rw [gpSame]
    exact gp
  have fpBound : (state.next blocked).2.fpOffset + 16 * vectorCount object ≤ 176 := by
    rw [fpSame]
    exact fp
  rw [next_registers _ object memory wide gpBound fpBound]
  simp only [gpSame, fpSame]

end Silmaril.Compiler.Native.Varargs
