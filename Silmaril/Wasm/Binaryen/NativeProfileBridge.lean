module

public import Silmaril.Wasm.Binaryen.NativeProfile
public import Silmaril.Wasm.Binaryen.NoThrow

@[expose] public section

/-! # Native profile inclusion and the invariant on function bodies

The native profile is smaller than the optimizer profile. This inclusion lets
native adequacy reuse the existing no-throw and function-store preservation proofs.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core

theorem instrInNativeProfile_flat {i : Instr} (h : structuredInstr i = false) :
    instrInNativeProfile i ↔ nativeInstr i = true := by
  rw [instrInNativeProfile.eq_def]
  split <;> simp_all [structuredInstr]

/-- The flat case of `instrInNativeProfile`, with side conditions `simp` discharges on
constructors. -/
theorem instrInNativeProfile_flat' {i : Instr} (h₁ : ∀ bt body, i ≠ .block bt body)
    (h₂ : ∀ bt body, i ≠ .loop bt body) (h₃ : ∀ bt b₁ b₂, i ≠ .if_ bt b₁ b₂) :
    instrInNativeProfile i ↔ nativeInstr i = true := by
  rw [instrInNativeProfile.eq_def]
  split <;> simp_all

theorem instrInNativeProfile_block {bt : BlockType} {body : List Instr} :
    instrInNativeProfile (.block bt body) ↔
      nativeBlockType bt = true ∧ ∀ i ∈ body, instrInNativeProfile i := by
  rw [instrInNativeProfile.eq_def]
  simp only
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hi => h2 ⟨i, hi⟩ (List.mem_attach _ _)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i _ => h2 i.1 i.2⟩

theorem instrInNativeProfile_loop {bt : BlockType} {body : List Instr} :
    instrInNativeProfile (.loop bt body) ↔ nativeBlockType bt = true ∧ ∀ i ∈ body, instrInNativeProfile i := by
  rw [instrInNativeProfile.eq_def]
  simp only
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hi => h2 ⟨i, hi⟩ (List.mem_attach _ _)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i _ => h2 i.1 i.2⟩

theorem instrInNativeProfile_if {bt : BlockType} {b₁ b₂ : List Instr} :
    instrInNativeProfile (.if_ bt b₁ b₂) ↔ nativeBlockType bt = true ∧
      (∀ i ∈ b₁, instrInNativeProfile i) ∧ ∀ i ∈ b₂, instrInNativeProfile i := by
  rw [instrInNativeProfile.eq_def]
  simp only
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun i hi => h2 ⟨i, hi⟩ (List.mem_attach _ _),
      fun i hi => h3 ⟨i, hi⟩ (List.mem_attach _ _)⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, fun i _ => h2 i.1 i.2, fun i _ => h3 i.1 i.2⟩

theorem not_instrInNativeProfile_tryTable {bt : BlockType} {cs : List Catch} {body : List Instr} :
    ¬ instrInNativeProfile (.tryTable bt cs body) := by
  rw [instrInNativeProfile.eq_def]
  simp [nativeInstr]

/-- Native flat instructions belong to the optimizer profile. -/
theorem nativeInstr_profile {i : Instr} (h : nativeInstr i = true) :
    profileInstr i = true := by
  cases i <;> simp_all [nativeInstr, profileInstr]
  case select ts => cases ts <;> simp_all

theorem nativeBlockType_profile {bt : BlockType} (h : nativeBlockType bt = true) :
    profileBlockType bt = true := by
  cases bt with
  | value t => cases t <;> simp_all [nativeBlockType, nativeValType, profileBlockType, profileValType]
  | _ => rfl

/-- Every native instruction is also in the optimizer's base profile. -/
theorem instrInNativeProfile_profile : ∀ i : Instr, instrInNativeProfile i → instrInProfile i
  | i, h => by
    by_cases hs : structuredInstr i = false
    · exact (instrInProfile_flat hs).2
        (nativeInstr_profile ((instrInNativeProfile_flat hs).1 h))
    · cases i <;> simp only [structuredInstr, not_true_eq_false] at hs
      case block bt body =>
        rw [instrInNativeProfile_block] at h
        exact instrInProfile_block.mpr ⟨nativeBlockType_profile h.1,
          fun j hj => instrInNativeProfile_profile j (h.2 j hj)⟩
      case loop bt body =>
        rw [instrInNativeProfile_loop] at h
        exact instrInProfile_loop.mpr ⟨nativeBlockType_profile h.1,
          fun j hj => instrInNativeProfile_profile j (h.2 j hj)⟩
      case if_ bt t e =>
        rw [instrInNativeProfile_if] at h
        exact instrInProfile_if.mpr ⟨nativeBlockType_profile h.1,
          (fun j hj => instrInNativeProfile_profile j (h.2.1 j hj)),
          fun j hj => instrInNativeProfile_profile j (h.2.2 j hj)⟩
      case tryTable => exact False.elim (not_instrInNativeProfile_tryTable h)
termination_by i => sizeOf i

/-- Every function is Wasm code in the native interpreter's integer fragment. -/
def NativeFuncsOk {H : Type} (F : List (FuncInst H)) : Prop :=
  ∀ fi ∈ F, ∃ fn, fi.code = .wasm fn ∧ ∀ i ∈ fn.body, instrInNativeProfile i

theorem NativeFuncsOk.funcsOk {H : Type} {F : List (FuncInst H)} (h : NativeFuncsOk F) :
    FuncsOk F := by
  intro fi hfi
  obtain ⟨fn, hc, hp⟩ := h fi hfi
  exact ⟨fn, hc, fun i hi => instrInNativeProfile_profile i (hp i hi)⟩

end Silmaril.Wasm.Binaryen
