module

public import Silmaril.Wasm.SingleThreaded.Determinism.Family

@[expose] public section

/-! # Determinism of the reduction families in the deterministic profile

For each family: two steps on left-hand sides `vals p ++ l` and `l` (the
second a suffix of the first) have `p = []` (the arity is fixed by the
instruction) and the same result. The profile matters for the float and relaxed
rules (canonical NaNs, `$ND = false`) and for `grow` (the oracle).
-/

namespace Silmaril.Wasm.SingleThreaded.Det

open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation

variable {H : Type}

@[simp] theorem AddrType.intType_inj {a b : AddrType} : a.intType = b.intType ↔ a = b := by
  cases a <;> cases b <;> simp [AddrType.intType]

@[simp] theorem constI32_inj {b c : BitVec 32} : constI32 b = constI32 c ↔ b = c := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; rfl

theorem Memory.load_bound {m : Memory.Bytes} {st n : Nat} {c : BitVec (8 * n)}
    (h : Memory.load m st n = some c) : st + n ≤ m.size := by
  unfold Memory.load Memory.readBytes at h
  split at h
  · assumption
  · simp at h

theorem Memory.store_bound {m b : Memory.Bytes} {st n : Nat} {c : BitVec (8 * n)}
    (h : Memory.store m st c = some b) : st + n ≤ m.size := by
  unfold Memory.store at h
  have := ((Memory.writeBytes_eq_some_iff _ _ _ _).mp h).1
  simpa using this

theorem Expand.det {d : DefType} {c₁ c₂ : CCompType} (h₁ : Expand d c₁) (h₂ : Expand d c₂) :
    c₁ = c₂ := by
  rw [Expand.iff] at h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

section
variable {o : GrowKind → Nat → Nat → Nat → Bool}

@[simp] theorem convertP_det {op : ConvertOp} {x : NumValue op.source}
    {r : Except FloatTrap (NumValue op.target)} :
    convertP (Profile.deterministic o) op x r ↔ convert op x = r := eq_comm
@[simp] theorem floatUnOpP_det {t : FloatType} {op : FloatUnOp} {x z : FloatValue t} :
    floatUnOpP (Profile.deterministic o) t op x z ↔ floatUnOp t op x = z := eq_comm
@[simp] theorem floatBinOpP_det {t : FloatType} {op : FloatBinOp} {x y z : FloatValue t} :
    floatBinOpP (Profile.deterministic o) t op x y z ↔ floatBinOp t op x y = z := eq_comm
@[simp] theorem growMayFail_det {k : GrowKind} {a sz d : Nat} :
    (Profile.deterministic o).growMayFail k a sz d ↔ o k a sz d = true := Iff.rfl
@[simp] theorem growMaySucceed_det {k : GrowKind} {a sz d : Nat} :
    (Profile.deterministic o).growMaySucceed k a sz d ↔ o k a sz d = false := Iff.rfl
end

/-- The common simp set for comparing two family rules. -/
macro "fam_inj" : tactic => `(tactic| simp only [vals_nil, List.nil_append, List.cons.injEq,
  Admin.plain.injEq, Admin.ref.injEq, Instr.intConst.injEq, Instr.floatConst.injEq,
  Instr.vecConst.injEq, toAdmin_inj, constI32_inj, AddrType.intType_inj, Val.num.injEq,
  NumVal.mk.injEq, Val.ref.injEq, Val.vec.injEq, Ref.struct.injEq, Ref.array.injEq,
  heq_eq_eq, and_true, true_and, reduceCtorEq, and_false, false_and] at *)

set_option hygiene false in
/-- Compare two family rules: close a different instruction; for the same
instruction, show the arity is the same and inject the left-hand sides. -/
macro "fam_pre" : tactic => `(tactic| first
  | (have hlast := congrArg List.getLast? hl
     simp [List.getLast?_append] at hlast; done)
  | (have hlen := congrArg List.length hl
     simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at hlen
     have hp : p = [] := List.eq_nil_of_length_eq_zero (by omega)
     subst hp
     refine ⟨rfl, ?_⟩
     try simp [toAdmin_eq_iff, eq_toAdmin_iff] at hl
     try casesm* _ ∧ _
     try subst_vars
     try simp at *
     try casesm* _ ∧ _
     try subst_vars))

/-- Close the same rule (equal results) or two exclusive rules. -/
macro "fam_post" : tactic => `(tactic| first
  | rfl
  | (simp_all [VecFloatUnOpRel, VecFloatBinOpRel, VecFloatTernOpRel, VecExtUnOpRel,
       VecExtBinOpRel, VecExtTernOpRel, VecNarrowRel, Expand.iff]; done)
  | (try simp_all [VecFloatUnOpRel, VecFloatBinOpRel, VecFloatTernOpRel, VecExtUnOpRel,
       VecExtBinOpRel, VecExtTernOpRel, VecNarrowRel, Expand.iff]
     try casesm* _ ∧ _
     try subst_vars
     try simp_all [Expand.iff]
     try casesm* _ ∧ _
     try subst_vars
     try simp_all
     try omega
     done))

macro "fam_det" : tactic => `(tactic| (fam_pre <;> fam_post))

theorem ParametricStep.det {l₁ l₂ r₁ r₂ : List Admin} {p : List Val}
    (h₁ : ParametricStep l₁ r₁) (h₂ : ParametricStep l₂ r₂) (hl : l₁ = vals p ++ l₂) :
    p = [] ∧ r₁ = r₂ := by
  cases h₁ <;> cases h₂ <;> fam_det

theorem NumericStep.det {o : GrowKind → Nat → Nat → Nat → Bool} {l₁ l₂ r₁ r₂ : List Admin}
    {p : List Val} (h₁ : NumericStep (Profile.deterministic o) l₁ r₁)
    (h₂ : NumericStep (Profile.deterministic o) l₂ r₂) (hl : l₁ = vals p ++ l₂) :
    p = [] ∧ r₁ = r₂ := by
  cases h₁ <;> cases h₂ <;> fam_det

theorem VariableStep.det {s : Store H} {f : Frame} {l₁ l₂ : List Admin} {c₁ c₂ : Config H}
    {p : List Val} (h₁ : VariableStep ⟨s, f, l₁⟩ c₁) (h₂ : VariableStep ⟨s, f, l₂⟩ c₂)
    (hl : l₁ = vals p ++ l₂) : p = [] ∧ c₁ = c₂ := by
  cases h₁ <;> cases h₂ <;> fam_det

theorem RefStep.det {s : Store H} {f : Frame} {l₁ l₂ : List Admin} {c₁ c₂ : Config H}
    {p : List Val} (h₁ : RefStep ⟨s, f, l₁⟩ c₁) (h₂ : RefStep ⟨s, f, l₂⟩ c₂)
    (hl : l₁ = vals p ++ l₂) : p = [] ∧ c₁ = c₂ := by
  cases h₁ <;> cases h₂ <;> fam_det

end Silmaril.Wasm.SingleThreaded.Det
