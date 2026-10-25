module

public import Silmaril.Wasm.Binaryen.Pass.RUMESim.Basic
public import Silmaril.Wasm.Binaryen.RenTyping

@[expose] public section

/-! # Renamed profile code is related code

A profile instruction whose function and global indices are kept is related to
its renaming (`irel_ren_fwd`), and the renaming to it (`irel_ren_bwd`), as soon
as the index relations contain the renaming on kept indices.
-/

namespace Silmaril.Wasm.Binaryen.RUMESim

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.RenTyping

/-- The flat profile instructions: calls, global accesses, and simple instructions. -/
theorem profile_flat_cases {i : Instr} (h : profileInstr i = true) :
    (∃ x, i = .call x) ∨ (∃ x, i = .globalGet x) ∨ (∃ x, i = .globalSet x) ∨
      (simpleI i = true ∧ Instr.freeFuncs i = [] ∧ instrGlobals i = [] ∧
        structuredInstr i = false) := by
  cases i with
  | select ts =>
    cases ts with
    | none => exact .inr (.inr (.inr ⟨rfl, by simp [Instr.freeFuncs], by simp [instrGlobals], rfl⟩))
    | some _ => simp [profileInstr] at h
  | call x => exact .inl ⟨x, rfl⟩
  | globalGet x => exact .inr (.inl ⟨x, rfl⟩)
  | globalSet x => exact .inr (.inr (.inl ⟨x, rfl⟩))
  | _ =>
    first
    | exact .inr (.inr (.inr ⟨rfl, by simp [Instr.freeFuncs], by simp [instrGlobals], rfl⟩))
    | (exfalso; simp [profileInstr] at h)

theorem irels_of_mem {X : SimCtx} (ρ : Ren) :
    ∀ (b : List Instr), (∀ j ∈ b, IRel X j (ρ.instr j)) → IRels X b (ρ.instrs b)
  | [], _ => .nil
  | j :: b, h => .cons (h j (by simp)) (irels_of_mem ρ b fun k hk => h k (by simp [hk]))

theorem irels_of_mem' {X : SimCtx} (ρ : Ren) :
    ∀ (b : List Instr), (∀ j ∈ b, IRel X (ρ.instr j) j) → IRels X (ρ.instrs b) b
  | [], _ => .nil
  | j :: b, h => .cons (h j (by simp)) (irels_of_mem' ρ b fun k hk => h k (by simp [hk]))

theorem freeFuncs_mem {b : List Instr} {j : Instr} (hj : j ∈ b) {x : Nat}
    (hx : x ∈ Instr.freeFuncs j) : x ∈ Expr.freeFuncs b := by
  simp only [Expr.freeFuncs, List.mem_flatMap]
  exact ⟨j, hj, hx⟩

theorem globals_mem {b : List Instr} {j : Instr} (hj : j ∈ b) {x : Nat}
    (hx : x ∈ instrGlobals j) : x ∈ instrsGlobals b := by
  simp only [instrsGlobals, List.mem_flatMap]
  exact ⟨j, hj, hx⟩

theorem sizeOf_mem_block {bt : BlockType} {b : List Instr} {j : Instr} (hj : j ∈ b) :
    sizeOf j < sizeOf (Instr.block bt b) := by
  have := List.sizeOf_lt_of_mem hj
  simp only [Instr.block.sizeOf_spec]; omega

theorem sizeOf_mem_loop {bt : BlockType} {b : List Instr} {j : Instr} (hj : j ∈ b) :
    sizeOf j < sizeOf (Instr.loop bt b) := by
  have := List.sizeOf_lt_of_mem hj
  simp only [Instr.loop.sizeOf_spec]; omega

theorem sizeOf_mem_if₁ {bt : BlockType} {b₁ b₂ : List Instr} {j : Instr} (hj : j ∈ b₁) :
    sizeOf j < sizeOf (Instr.if_ bt b₁ b₂) := by
  have := List.sizeOf_lt_of_mem hj
  simp only [Instr.if_.sizeOf_spec]; omega

theorem sizeOf_mem_if₂ {bt : BlockType} {b₁ b₂ : List Instr} {j : Instr} (hj : j ∈ b₂) :
    sizeOf j < sizeOf (Instr.if_ bt b₁ b₂) := by
  have := List.sizeOf_lt_of_mem hj
  simp only [Instr.if_.sizeOf_spec]; omega




/-- **Code is related to its renaming.** -/
theorem irel_ren_fwd (X : SimCtx) (ρ : Ren) (kf kg : Nat → Prop)
    (hKF : ∀ x : FuncIdx, kf x.toNat → X.KF x.toNat (ρ.funcIdx x).toNat)
    (hKG : ∀ x : GlobalIdx, kg x.toNat → X.KG x.toNat (ρ.globalIdx x).toNat) :
    ∀ (n : Nat) (i : Instr), sizeOf i < n → instrInProfile i → (∀ x ∈ Instr.freeFuncs i, kf x) →
      (∀ x ∈ instrGlobals i, kg x) → IRel X i (ρ.instr i)
  | 0, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, i, hn, hp, hf, hg => by
    cases hsi : structuredInstr i
    · rcases profile_flat_cases (profileInstr_of hp hsi) with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩ |
          ⟨hs, hff, hgg, -⟩
      · rw [ren_call]
        exact .call (hKF x (hf _ (by simp [Instr.freeFuncs])))
      · rw [ren_globalGet]
        exact .globalGet (hKG x (hg _ (by simp [instrGlobals])))
      · rw [ren_globalSet]
        exact .globalSet (hKG x (hg _ (by simp [instrGlobals])))
      · rw [ren_fixed ρ hsi hff hgg]
        exact .simple hs
    · cases i <;> simp [structuredInstr] at hsi
      case block bt body =>
        rw [ren_block]
        refine .block (irels_of_mem ρ body fun j hj => ?_)
        exact irel_ren_fwd X ρ kf kg hKF hKG n j (by have := sizeOf_mem_block (bt := bt) hj; omega)
          (instrInProfile_block hp j hj) (fun x hx => hf x (freeFuncs_block (freeFuncs_mem hj hx)))
          (fun x hx => hg x (globals_block (globals_mem hj hx)))
      case loop bt body =>
        rw [ren_loop]
        refine .loop (irels_of_mem ρ body fun j hj => ?_)
        exact irel_ren_fwd X ρ kf kg hKF hKG n j (by have := sizeOf_mem_loop (bt := bt) hj; omega)
          (instrInProfile_loop hp j hj) (fun x hx => hf x (freeFuncs_loop (freeFuncs_mem hj hx)))
          (fun x hx => hg x (globals_loop (globals_mem hj hx)))
      case if_ bt b₁ b₂ =>
        rw [ren_if]
        refine .if_ (irels_of_mem ρ b₁ fun j hj => ?_) (irels_of_mem ρ b₂ fun j hj => ?_)
        · exact irel_ren_fwd X ρ kf kg hKF hKG n j (by have := sizeOf_mem_if₁ (bt := bt) (b₂ := b₂) hj; omega)
            ((instrInProfile_if hp).1 j hj)
            (fun x hx => hf x (freeFuncs_if₁ (freeFuncs_mem hj hx)))
            (fun x hx => hg x (globals_if₁ (globals_mem hj hx)))
        · exact irel_ren_fwd X ρ kf kg hKF hKG n j (by have := sizeOf_mem_if₂ (bt := bt) (b₁ := b₁) hj; omega)
            ((instrInProfile_if hp).2 j hj)
            (fun x hx => hf x (freeFuncs_if₂ (freeFuncs_mem hj hx)))
            (fun x hx => hg x (globals_if₂ (globals_mem hj hx)))
      case tryTable bt cs body =>
        unfold instrInProfile at hp
        simp [profileInstr] at hp

/-- **A renaming is related to its code.** -/
theorem irel_ren_bwd (X : SimCtx) (ρ : Ren) (kf kg : Nat → Prop)
    (hKF : ∀ x : FuncIdx, kf x.toNat → X.KF (ρ.funcIdx x).toNat x.toNat)
    (hKG : ∀ x : GlobalIdx, kg x.toNat → X.KG (ρ.globalIdx x).toNat x.toNat) :
    ∀ (n : Nat) (i : Instr), sizeOf i < n → instrInProfile i → (∀ x ∈ Instr.freeFuncs i, kf x) →
      (∀ x ∈ instrGlobals i, kg x) → IRel X (ρ.instr i) i
  | 0, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, i, hn, hp, hf, hg => by
    cases hsi : structuredInstr i
    · rcases profile_flat_cases (profileInstr_of hp hsi) with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩ |
          ⟨hs, hff, hgg, -⟩
      · rw [ren_call]
        exact .call (hKF x (hf _ (by simp [Instr.freeFuncs])))
      · rw [ren_globalGet]
        exact .globalGet (hKG x (hg _ (by simp [instrGlobals])))
      · rw [ren_globalSet]
        exact .globalSet (hKG x (hg _ (by simp [instrGlobals])))
      · rw [ren_fixed ρ hsi hff hgg]
        exact .simple hs
    · cases i <;> simp [structuredInstr] at hsi
      case block bt body =>
        rw [ren_block]
        refine .block (irels_of_mem' ρ body fun j hj => ?_)
        exact irel_ren_bwd X ρ kf kg hKF hKG n j (by have := sizeOf_mem_block (bt := bt) hj; omega)
          (instrInProfile_block hp j hj) (fun x hx => hf x (freeFuncs_block (freeFuncs_mem hj hx)))
          (fun x hx => hg x (globals_block (globals_mem hj hx)))
      case loop bt body =>
        rw [ren_loop]
        refine .loop (irels_of_mem' ρ body fun j hj => ?_)
        exact irel_ren_bwd X ρ kf kg hKF hKG n j (by have := sizeOf_mem_loop (bt := bt) hj; omega)
          (instrInProfile_loop hp j hj) (fun x hx => hf x (freeFuncs_loop (freeFuncs_mem hj hx)))
          (fun x hx => hg x (globals_loop (globals_mem hj hx)))
      case if_ bt b₁ b₂ =>
        rw [ren_if]
        refine .if_ (irels_of_mem' ρ b₁ fun j hj => ?_) (irels_of_mem' ρ b₂ fun j hj => ?_)
        · exact irel_ren_bwd X ρ kf kg hKF hKG n j (by have := sizeOf_mem_if₁ (bt := bt) (b₂ := b₂) hj; omega)
            ((instrInProfile_if hp).1 j hj)
            (fun x hx => hf x (freeFuncs_if₁ (freeFuncs_mem hj hx)))
            (fun x hx => hg x (globals_if₁ (globals_mem hj hx)))
        · exact irel_ren_bwd X ρ kf kg hKF hKG n j (by have := sizeOf_mem_if₂ (bt := bt) (b₁ := b₁) hj; omega)
            ((instrInProfile_if hp).2 j hj)
            (fun x hx => hf x (freeFuncs_if₂ (freeFuncs_mem hj hx)))
            (fun x hx => hg x (globals_if₂ (globals_mem hj hx)))
      case tryTable bt cs body =>
        unfold instrInProfile at hp
        simp [profileInstr] at hp

/-- Sequences: code is related to its renaming. -/
theorem irels_ren_fwd (X : SimCtx) (ρ : Ren) (kf kg : Nat → Prop)
    (hKF : ∀ x : FuncIdx, kf x.toNat → X.KF x.toNat (ρ.funcIdx x).toNat)
    (hKG : ∀ x : GlobalIdx, kg x.toNat → X.KG x.toNat (ρ.globalIdx x).toNat) (b : List Instr)
    (hp : ∀ i ∈ b, instrInProfile i) (hf : ∀ x ∈ Expr.freeFuncs b, kf x)
    (hg : ∀ x ∈ instrsGlobals b, kg x) : IRels X b (ρ.instrs b) :=
  irels_of_mem ρ b fun j hj => irel_ren_fwd X ρ kf kg hKF hKG _ j (Nat.lt_succ_self _) (hp j hj)
    (fun x hx => hf x (freeFuncs_mem hj hx)) (fun x hx => hg x (globals_mem hj hx))

/-- Sequences: a renaming is related to its code. -/
theorem irels_ren_bwd (X : SimCtx) (ρ : Ren) (kf kg : Nat → Prop)
    (hKF : ∀ x : FuncIdx, kf x.toNat → X.KF (ρ.funcIdx x).toNat x.toNat)
    (hKG : ∀ x : GlobalIdx, kg x.toNat → X.KG (ρ.globalIdx x).toNat x.toNat) (b : List Instr)
    (hp : ∀ i ∈ b, instrInProfile i) (hf : ∀ x ∈ Expr.freeFuncs b, kf x)
    (hg : ∀ x ∈ instrsGlobals b, kg x) : IRels X (ρ.instrs b) b :=
  irels_of_mem' ρ b fun j hj => irel_ren_bwd X ρ kf kg hKF hKG _ j (Nat.lt_succ_self _) (hp j hj)
    (fun x hx => hf x (freeFuncs_mem hj hx)) (fun x hx => hg x (globals_mem hj hx))



end Silmaril.Wasm.Binaryen.RUMESim
