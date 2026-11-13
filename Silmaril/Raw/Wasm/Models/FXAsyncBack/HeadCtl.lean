module

public import Silmaril.Wasm.SingleThreaded.Determinism

/-!
# Core head steps of plain control instructions are deterministic (unrefined)

`head_plain_ctl`: two head steps (`Silmaril.Wasm.SingleThreaded.Det.Head`, deterministic
profile) of the same plain instruction of the control family, whose arguments are suffixes of
each other, take the same arguments and reach the same configuration. The proof is a case
analysis on both steps, closed by automation (`pfam_excl`, `pctl_close`) and nine explicit
arms; it is kept here, unrefined, rather than in Isar style. The statement is re-exported by
`Silmaril.Proofs.Wasm.Models.FXAsyncBack.head_plain_det`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head famOf Fam famOf_of_shape singleton_hp last_hp
  p_nil_of_len Expand.det)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type}

set_option hygiene false in
/-- A head step of a family rule at a control instruction is impossible. -/
macro "pfam_excl" : tactic => `(tactic| (exfalso; first
  | exact hc (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.ParametricStep.shape ‹_›)).2
      (by decide)
  | exact hc (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.NumericStep.shape ‹_›)).2
      (by decide)
  | exact hc (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.VectorStep.shape ‹_›)).2
      (by decide)
  | exact hc (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.VariableStep.shape ‹_›)).2
      (by decide)
  | exact hc (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.TableStep.shape ‹_›)).2
      (by decide)
  | exact hc (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.MemoryStep.shape ‹_›)).2
      (by decide)
  | exact hc (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.RefStep.shape ‹_›)).2
      (by decide)
  | exact hc (famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.AggregateStep.shape ‹_›)).2
      (by decide)))

set_option hygiene false in
/-- Close a pair of head steps of the same plain control rule. -/
macro "pctl_close" : tactic => `(tactic| first
  | (exfalso; assumption)
  | (subst_vars; exact ⟨by simpa using hp, rfl⟩)
  | (obtain ⟨rfl, hx⟩ := singleton_hp hp
     cases hx
     first
     | exact ⟨rfl, rfl⟩
     | (exfalso; contradiction)
     | (exfalso; simp_all; done))
  | (exfalso; simp_all; done))

set_option linter.unusedTactic false in
theorem head_plain_ctl {o : GrowKind → Nat → Nat → Nat → Bool} {s : Store H} {f : Frame}
    {args₁ args₂ p : List Val} {i : Instr} {c₁ c₂ : Config H}
    (hk : famOf (.plain i) = .control)
    (h₁ : Head (Profile.deterministic o) s f args₁ (.plain i) c₁)
    (h₂ : Head (Profile.deterministic o) s f args₂ (.plain i) c₂) (hp : args₁ = p ++ args₂) :
    p = [] ∧ c₁ = c₂ := by
  have hc : ∀ {k : Fam}, famOf (.plain i) = k → k ≠ .control → False :=
    fun h hk' => hk' (h ▸ hk)
  generalize he : Admin.plain i = e at h₁ h₂ hc
  cases h₁ <;> try pfam_excl
  all_goals (cases h₂ <;> try pfam_excl)
  all_goals (try cases he)
  all_goals (try pctl_close)
  case block.block.refl | loop.loop.refl =>
    rename_i t₁ t₂ hbt hm t₁' t₂' hm' hbt'
    rw [hbt] at hbt'
    cases hbt'
    obtain rfl := p_nil_of_len hp (by omega)
    simp only [List.nil_append] at hp
    subst hp
    exact ⟨rfl, rfl⟩
  case tryTable.tryTable.refl =>
    rename_i t₁ t₂ hbt hm t₁' t₂' hm' hbt'
    rw [hbt] at hbt'
    cases hbt'
    obtain rfl := p_nil_of_len hp (by omega)
    simp only [List.nil_append] at hp
    subst hp
    exact ⟨rfl, rfl⟩
  case brTableLt.brTableLt.refl =>
    rename_i hi _ _ hi'
    obtain ⟨rfl, hx⟩ := singleton_hp hp
    cases hx
    rw [hi] at hi'
    cases hi'
    exact ⟨rfl, rfl⟩
  case call.call.refl | returnCall.returnCall.refl =>
    rename_i a fi hf hx a' fi' hf' hx'
    rw [hx] at hx'
    cases hx'
    rw [hf] at hf'
    cases hf'
    exact ⟨by simpa using hp, rfl⟩
  case callRefNull.callRefFunc.refl =>
    exfalso
    rename_i vs a fi ps rs code hf he hn hcode ha _ _
    subst ha
    have h := congrArg List.getLast? hp
    simp at h
  case callRefFunc.callRefFunc.refl =>
    rename_i vs a fi ps rs code hf he hn hcode ha vs' a' fi' ps' rs' code' hf' he' hn' hcode'
      ha' _ _
    subst ha ha'
    obtain ⟨hvs, hr⟩ := last_hp hp
    cases hr
    rw [hf] at hf'
    cases hf'
    have hpr := Expand.det he he'
    injection hpr with h1 h2
    subst h1 h2
    rw [hcode] at hcode'
    cases hcode'
    obtain rfl := p_nil_of_len hvs (by omega)
    simp only [List.nil_append] at hvs
    subst hvs
    exact ⟨rfl, rfl⟩
  case throw.throw.refl =>
    rename_i ta ti ts he ht hn ta' ti' ts' he' hn' ht'
    rw [ht] at ht'
    cases ht'
    have hts := Expand.det he he'
    injection hts with h1 h2
    subst h1
    obtain rfl := p_nil_of_len hp (by omega)
    simp only [List.nil_append] at hp
    subst hp
    exact ⟨rfl, rfl⟩

end Silmaril.Raw.Wasm.Models.FXAsyncBack
