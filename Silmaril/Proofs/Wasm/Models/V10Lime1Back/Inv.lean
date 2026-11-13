module

public import Silmaril.Wasm.Models.V10Lime1Back.Defs

/-!
# Inverting the 1.0 → Lime1 code map

`codeToLime` maps 1.0 administrative code to Lime1 code instruction by instruction
(`AdminInstr.map V1.Instr.toLime`). A Lime1 rule matches a code pattern; on the image of 1.0
code the pattern has a unique 1.0 preimage. These are the inversion facts, as `iff`s:

* list level: `code_nil`, `code_cons`, `code_append`, `code_values`, `code_values_append`;
* instruction level: `map_source`, `map_invoke`, `map_trap`, `map_label`, `map_frame`,
  `map_value`;
* stores: `funcInst_injective`, `store_injective` (from `V1.Func.toLime_injective`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V10Lime1Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution (codeToLime)

/-- The 1.0 administrative code. -/
abbrev VAdmin := Silmaril.Wasm.V1.Execution.Admin
/-- The Lime1 administrative code. -/
abbrev LAdmin := Silmaril.Wasm.Lime1.Execution.Admin
/-- The instruction map. -/
abbrev mapI : VAdmin → LAdmin := AdminInstr.map Silmaril.Wasm.V1.Instr.toLime

theorem codeToLime_eq (A : List VAdmin) : codeToLime A = A.map mapI :=
  AdminInstr.mapList_eq_map _ _

theorem code_nil {A : List VAdmin} : codeToLime A = [] ↔ A = [] := by
  rw [codeToLime_eq, List.map_eq_nil_iff]

theorem code_cons {A : List VAdmin} {x : LAdmin} {l : List LAdmin} :
    codeToLime A = x :: l ↔ ∃ a A', A = a :: A' ∧ mapI a = x ∧ codeToLime A' = l := by
  rw [codeToLime_eq, List.map_eq_cons_iff]
  simp only [codeToLime_eq]

theorem code_append {A : List VAdmin} {l₁ l₂ : List LAdmin} :
    codeToLime A = l₁ ++ l₂ ↔
      ∃ A₁ A₂, A = A₁ ++ A₂ ∧ codeToLime A₁ = l₁ ∧ codeToLime A₂ = l₂ := by
  rw [codeToLime_eq, List.map_eq_append_iff]
  simp only [codeToLime_eq]

theorem map_source {a : VAdmin} {j : Lime1.Instr} :
    mapI a = .source j ↔ ∃ j₀, a = .source j₀ ∧ j₀.toLime = j := by
  cases a <;> simp [mapI, AdminInstr.map]

theorem map_invoke {a : VAdmin} {x : FuncAddr} : mapI a = .invoke x ↔ a = .invoke x := by
  cases a <;> simp [mapI, AdminInstr.map]

theorem map_trap {a : VAdmin} : mapI a = .trap ↔ a = .trap := by
  cases a <;> simp [mapI, AdminInstr.map]

theorem map_label {a : VAdmin} {n : Nat} {cont : Lime1.Expr} {body : List LAdmin} :
    mapI a = .label n cont body ↔
      ∃ cont₀ body₀, a = .label n cont₀ body₀ ∧ cont₀.map Silmaril.Wasm.V1.Instr.toLime = cont ∧
        codeToLime body₀ = body := by
  cases a <;> simp [mapI, AdminInstr.map, codeToLime, and_assoc, eq_comm]

theorem map_frame {a : VAdmin} {n : Nat} {fr : Frame} {body : List LAdmin} :
    mapI a = .frame n fr body ↔ ∃ body₀, a = .frame n fr body₀ ∧ codeToLime body₀ = body := by
  cases a <;> simp [mapI, AdminInstr.map, codeToLime, and_assoc, eq_comm]

/-- Values have exactly values as preimages. -/
theorem map_value {a : VAdmin} {v : Value} :
    mapI a = Silmaril.Wasm.Lime1.Execution.value v ↔ a = Silmaril.Wasm.V1.Execution.value v := by
  constructor
  · intro h
    rcases v with ⟨t, bits⟩
    cases t with
    | int t =>
      obtain ⟨j, rfl, hj⟩ := map_source.mp (show mapI a = .source (.intConst t bits) from h)
      exact congrArg AdminInstr.source
        (Silmaril.Wasm.V1.Instr.toLime_injective (a₂ := .intConst t bits) hj)
    | float t =>
      obtain ⟨j, rfl, hj⟩ := map_source.mp (show mapI a = .source (.floatConst t bits) from h)
      exact congrArg AdminInstr.source
        (Silmaril.Wasm.V1.Instr.toLime_injective (a₂ := .floatConst t bits) hj)
  · rintro rfl
    exact Silmaril.Wasm.V1.Execution.map_value v

theorem code_values {A : List VAdmin} {vs : List Value} :
    codeToLime A = Silmaril.Wasm.Lime1.Execution.values vs ↔
      A = Silmaril.Wasm.V1.Execution.values vs := by
  induction vs generalizing A with
  | nil =>
    simp [Silmaril.Wasm.Lime1.Execution.values, Silmaril.Wasm.V1.Execution.values]
  | cons v vs ih =>
    rw [show Silmaril.Wasm.Lime1.Execution.values (v :: vs) =
        Silmaril.Wasm.Lime1.Execution.value v :: Silmaril.Wasm.Lime1.Execution.values vs from rfl,
      show Silmaril.Wasm.V1.Execution.values (v :: vs) =
        Silmaril.Wasm.V1.Execution.value v :: Silmaril.Wasm.V1.Execution.values vs from rfl,
      code_cons]
    simp only [map_value, ih]
    constructor
    · rintro ⟨a, A', rfl, rfl, rfl⟩; rfl
    · rintro rfl; exact ⟨_, _, rfl, rfl, rfl⟩

theorem code_values_append {A : List VAdmin} {vs : List Value} {l : List LAdmin} :
    codeToLime A = Silmaril.Wasm.Lime1.Execution.values vs ++ l ↔
      ∃ A₂, A = Silmaril.Wasm.V1.Execution.values vs ++ A₂ ∧ codeToLime A₂ = l := by
  rw [code_append]
  simp only [code_values]
  constructor
  · rintro ⟨A₁, A₂, rfl, rfl, h⟩; exact ⟨A₂, rfl, h⟩
  · rintro ⟨A₂, rfl, h⟩; exact ⟨_, A₂, rfl, rfl, h⟩

/-- `FuncInst.mapCode V1.Func.toLime` is injective. -/
theorem funcInst_injective {H : Type} :
    Function.Injective (FuncInst.mapCode (H := H) Silmaril.Wasm.V1.Func.toLime) := by
  intro x y h
  cases x <;> cases y <;> simp only [FuncInst.mapCode, FuncInst.wasm.injEq,
    FuncInst.host.injEq, reduceCtorEq] at h ⊢
  · exact ⟨h.1, h.2.1, Silmaril.Wasm.V1.Func.toLime_injective h.2.2⟩
  · exact h

/-- `Store.mapCode V1.Func.toLime` is injective. -/
theorem store_injective {H : Type} :
    Function.Injective (Store.mapCode (H := H) Silmaril.Wasm.V1.Func.toLime) := by
  intro x y h
  rcases x with ⟨fx, tx, mx, gx⟩
  rcases y with ⟨fy, ty, my, gy⟩
  simp only [Store.mapCode, Store.mk.injEq] at h ⊢
  exact ⟨List.map_injective_iff.mpr funcInst_injective h.1, h.2⟩

end Silmaril.Proofs.Wasm.Models.V10Lime1Back
