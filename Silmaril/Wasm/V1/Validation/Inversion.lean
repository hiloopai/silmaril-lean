module

public import Silmaril.Wasm.V1.Validation.Instructions

/-! # Inversion through stack framing -/

@[expose] public section

namespace Silmaril.Wasm.V1.Validation

namespace InstrType

variable {C : Context} {a b : ResultType}

/-- Stack framing cannot make a write to a missing or immutable global valid. -/
theorem globalSet_lookup {i : GlobalIdx} (h : InstrType C (.globalSet i) a b) :
    ∃ t, C.globals[i.toNat]? = some ⟨.var, t⟩ := by
  generalize he : Instr.globalSet i = e at h
  induction h using InstrType.rec (motive_2 := fun _ _ _ _ _ => True) <;> simp_all

/-- The selector operand is not a substitute for an actual table. -/
theorem callIndirect_table {i : TypeIdx} (h : InstrType C (.callIndirect i) a b) :
    C.tables ≠ [] := by
  generalize he : Instr.callIndirect i = e at h
  induction h using InstrType.rec (motive_2 := fun _ _ _ _ _ => True) <;> simp_all

/-- Framing preserves both the memory existence and packed-access side conditions. -/
theorem intLoad_access {t : IntType} {p : Option (PackSize × Signedness)} {arg : MemArg}
    (h : InstrType C (.intLoad t p arg) a b) :
    C.memories ≠ [] ∧ IntAccess t (p.map Prod.fst) arg := by
  generalize he : Instr.intLoad t p arg = e at h
  induction h using InstrType.rec (motive_2 := fun _ _ _ _ _ => True) <;> simp_all

end InstrType

namespace ExprType

variable {C : Context} {a b : ResultType} {i : Instr} {is : Expr}

theorem cons_iff : ExprType C (i :: is) a b ↔
    ∃ mid, InstrType C i a mid ∧ ExprType C is mid b := by
  constructor
  · intro h; cases h with
    | cons hi his => exact ⟨_, hi, his⟩
  · rintro ⟨_, hi, his⟩; exact .cons hi his

theorem singleton_iff : ExprType C [i] a b ↔ InstrType C i a b := by
  rw [cons_iff]
  constructor
  · rintro ⟨mid, hi, his⟩
    cases (nil_iff.mp his)
    exact hi
  · intro hi; exact ⟨b, hi, .nil b⟩

end ExprType

end Silmaril.Wasm.V1.Validation
