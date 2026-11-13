module

public import Silmaril.Proofs.Wasm.LimeCompile.Tail.Ident
public import Silmaril.Wasm.LimeCompile.Select.Defs

/-!
# Counting tail calls through the other rewrites

The `select` rewrites (`Direct.lowerL`, `Select.selL`) do not create or remove tail calls
(`tailCountL_lowerL`, `tailCountL_selL`), and Lime1 code has none (`tailCountL_toCore`). So a
module that is a Lime1 image up to `select` annotations has no tail call left after the select
lowering (`noTail_of_selM`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.AgreeTail

open Silmaril.Wasm
open Silmaril.Wasm.LimeCompile.Tail Silmaril.Wasm.LimeCompile

set_option linter.unusedTactic false in
mutual
theorem tailCountI_lowerI (i : Instr) : tailCountI (Direct.lowerI i) = tailCountI i := by
  cases i with
  | select ts =>
    cases ts with
    | none => rw [Direct.lowerI] <;> simp
    | some ts => rw [Direct.lowerI]; split <;> simp [tailCountI]
  | block bt b => rw [Direct.lowerI, tailCountI, tailCountI, tailCountL_lowerL b]
  | loop bt b => rw [Direct.lowerI, tailCountI, tailCountI, tailCountL_lowerL b]
  | if_ bt b₁ b₂ =>
    rw [Direct.lowerI, tailCountI, tailCountI, tailCountL_lowerL b₁, tailCountL_lowerL b₂]
  | tryTable bt cs b => rw [Direct.lowerI, tailCountI, tailCountI] <;> simp
  | _ => rw [Direct.lowerI] <;> simp
termination_by sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

theorem tailCountL_lowerL (is : List Instr) : tailCountL (Direct.lowerL is) = tailCountL is := by
  cases is with
  | nil => rw [Direct.lowerL]
  | cons i is =>
    rw [Direct.lowerL, tailCountL, tailCountL, tailCountI_lowerI i, tailCountL_lowerL is]
termination_by sizeOf is
decreasing_by all_goals simp_wf; all_goals omega
end

set_option linter.unusedTactic false in
mutual
theorem tailCountI_selI (i : Instr) : tailCountI (Select.selI i) = tailCountI i := by
  cases i with
  | select ts => rw [Select.selI, tailCountI, tailCountI] <;> simp
  | block bt b => rw [Select.selI, tailCountI, tailCountI, tailCountL_selL b]
  | loop bt b => rw [Select.selI, tailCountI, tailCountI, tailCountL_selL b]
  | if_ bt b₁ b₂ =>
    rw [Select.selI, tailCountI, tailCountI, tailCountL_selL b₁, tailCountL_selL b₂]
  | tryTable bt cs b => rw [Select.selI, tailCountI, tailCountI] <;> simp
  | _ => rw [Select.selI] <;> simp
termination_by sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

theorem tailCountL_selL (is : List Instr) : tailCountL (Select.selL is) = tailCountL is := by
  cases is with
  | nil => rw [Select.selL]
  | cons i is => rw [Select.selL, tailCountL, tailCountL, tailCountI_selI i, tailCountL_selL is]
termination_by sizeOf is
decreasing_by all_goals simp_wf; all_goals omega
end

set_option linter.unusedTactic false in
mutual
theorem tailCountI_toCore (j : Lime1.Instr) : tailCountI (Lime1.Instr.toCore j) = 0 := by
  cases j with
  | block t b => rw [Lime1.Instr.toCore, tailCountI, tailCountL_toCore b]
  | loop t b => rw [Lime1.Instr.toCore, tailCountI, tailCountL_toCore b]
  | if_ t b₁ b₂ => rw [Lime1.Instr.toCore, tailCountI, tailCountL_toCore b₁, tailCountL_toCore b₂]
  | _ => rw [Lime1.Instr.toCore, tailCountI] <;> simp
termination_by sizeOf j
decreasing_by all_goals simp_wf; all_goals omega

theorem tailCountL_toCore (es : Lime1.Expr) : tailCountL (Lime1.Expr.toCore es) = 0 := by
  cases es with
  | nil => rw [Lime1.Expr.toCore, tailCountL]
  | cons j es => rw [Lime1.Expr.toCore, tailCountL, tailCountI_toCore j, tailCountL_toCore es]
termination_by sizeOf es
decreasing_by all_goals simp_wf; all_goals omega
end

/-- A module that is a Lime1 image up to `select` annotations has no tail call after the select
lowering. -/
theorem noTail_of_selM {m : Module} {L : Lime1.Module} (h : L.toCore = Select.selM m) :
    ∀ f ∈ (Direct.lowerModule m).funcs, tailCountL f.body = 0 := by
  intro f hf
  simp only [Direct.lowerModule, List.mem_map] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  have hsel : Select.selFn g ∈ L.toCore.funcs := by
    rw [h]
    exact List.mem_map.2 ⟨g, hg, rfl⟩
  obtain ⟨k, -, hk⟩ : ∃ k ∈ L.funcs, Lime1.Func.toCore k = Select.selFn g := by
    simpa [Lime1.Module.toCore] using hsel
  have hb : Lime1.Expr.toCore k.body = Select.selL g.body := by
    have := congrArg Func.body hk
    simpa [Lime1.Func.toCore, Select.selFn] using this
  have h0 : tailCountL (Select.selL g.body) = 0 := by rw [← hb]; exact tailCountL_toCore _
  show tailCountL (Direct.lowerL g.body) = 0
  rw [tailCountL_lowerL, ← tailCountL_selL]
  exact h0

end Silmaril.Proofs.Wasm.LimeCompile.AgreeTail
