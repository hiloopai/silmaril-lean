module

public import Silmaril.Machine.SystemV.Abi.Defs

@[expose] public section
namespace Silmaril.Machine.SystemV.Abi

@[simp] theorem merge_self (cls : Class) : merge cls cls = cls := by
  cases cls <;> rfl

@[simp] theorem merge_noClass_left (cls : Class) : merge .noClass cls = cls := by
  cases cls <;> rfl

@[simp] theorem merge_noClass_right (cls : Class) : merge cls .noClass = cls := by
  cases cls <;> rfl

/-- Field order does not affect pairwise class merging, including union fields. -/
theorem merge_comm (first second : Class) : merge first second = merge second first := by
  cases first <;> cases second <;> rfl

@[simp] theorem merge_memory_left (cls : Class) : merge .memory cls = .memory := by
  cases cls <;> rfl

@[simp] theorem alignUp_zero (offset : Nat) : alignUp offset 0 = offset := by
  simp [alignUp]

/-- Every stack offset produced by nonzero alignment has the required residue. -/
theorem alignUp_mod (offset alignment : Nat) (nonzero : alignment ≠ 0) :
    alignUp offset alignment % alignment = 0 := by
  simp [alignUp, nonzero]

/-- Advancing varargs never changes the base of the register save area. -/
@[simp] theorem VaList.next_regSaveArea (state : VaList) (object : Object) :
    (state.next object).2.regSaveArea = state.regSaveArea := by
  unfold VaList.next
  split <;> rfl

/-- A varargs start state is well formed whenever the named call respected the
six GP/eight vector register limits. -/
theorem VaList.start_valid (named : CallPlan) (overflow save : Nat)
    (gp : named.gpUsed ≤ 6) (vector : named.vectorUsed ≤ 8) :
    (VaList.start named overflow save).valid := by
  simp only [VaList.start, VaList.valid]
  omega

/-- Register-save offsets stay inside their slots across both register and
stack overflow transitions. Pointer arithmetic bounds are separate obligations. -/
theorem VaList.next_valid (state : VaList) (object : Object) (valid : state.valid) :
    (state.next object).2.valid := by
  unfold VaList.next
  split
  · rename_i available
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at available
    rcases valid with ⟨gpBound, gpAligned, fpLower, fpBound, fpAligned⟩
    rcases available with ⟨⟨⟨_, _⟩, gpAvailable⟩, fpAvailable⟩
    dsimp [VaList.valid]
    refine ⟨gpAvailable, ?_, by omega, fpAvailable, ?_⟩
    · simp [Nat.add_mod, gpAligned]
    · have offset : state.fpOffset + 16 * vectorCount object - 48 =
          state.fpOffset - 48 + 16 * vectorCount object := by omega
      rw [offset]
      simp [Nat.add_mod, fpAligned]
  · exact valid

end Silmaril.Machine.SystemV.Abi
