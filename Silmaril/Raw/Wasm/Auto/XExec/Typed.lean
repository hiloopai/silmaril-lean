module

public import Silmaril.Proofs.Wasm.Auto.XExec.Sound

/-! # Typed straight-line code is never stuck

`tstep1_progress`: an instruction that `tstep1` types, run in a frame whose locals have the
types `Γ` (`LocalsOk`) on a stack whose top has the types `st` (`StackOk`), either succeeds,
keeping both invariants at the new types, or traps (`traps1`). `xexec_ne_stuck` lifts this to
sequences: typed code ends normally or traps.

Unrefined proofs (an instruction-by-instruction case split).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.XExec

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.XExec
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core

variable {H : Type}

theorem popInt_int (t : IntType) (x : BitVec t.width) (rs : List Val) :
    popInt t (.num ⟨.int t, x⟩ :: rs) = some (x, rs) := by
  cases t <;> rfl

theorem localsOk_set {Γ : List IntType} {f : Frame} {x : LocalIdx} {t : IntType}
    (hf : LocalsOk Γ f) (hx : Γ[x.toNat]? = some t) (y : BitVec t.width) :
    LocalsOk Γ (f.setLocal x (.num ⟨.int t, y⟩)) := by
  obtain ⟨hl, hv⟩ := hf
  refine ⟨by simpa [Frame.setLocal] using hl, ?_⟩
  intro i u hu
  simp only [Frame.setLocal, List.getElem?_set]
  by_cases hi : x.toNat = i
  · subst hi
    have hlt : x.toNat < f.locals.length := by
      have := (List.getElem?_eq_some_iff.mp hx).1; omega
    rw [hx] at hu
    cases hu
    exact ⟨y, by simp [hlt]⟩
  · simpa [hi] using hv i u hu

theorem localsOk_lt {Γ : List IntType} {f : Frame} {x : LocalIdx} {t : IntType}
    (hf : LocalsOk Γ f) (hx : Γ[x.toNat]? = some t) : x.toNat < f.locals.length := by
  have := (List.getElem?_eq_some_iff.mp hx).1
  have := hf.1
  omega

theorem stackOk_cons {t : IntType} {st : List IntType} {v : Val} {rs : List Val} :
    StackOk (t :: st) (v :: rs) ↔ (∃ x : BitVec t.width, v = .num ⟨.int t, x⟩) ∧ StackOk st rs :=
  Iff.rfl

theorem stackOk_nil {t : IntType} {st : List IntType} : ¬ StackOk (t :: st) [] := fun h => h

/-- **One typed instruction succeeds or traps**, keeping the store and the module. -/
theorem tstep1_progress {Γ st st' : List IntType} {f : Frame} {rs : List Val} {i : Instr}
    (ht : tstep1 Γ st i = some st') (hf : LocalsOk Γ f) (hs : StackOk st rs) (s : Store H) :
    (∃ f₁ rs₁, exec1S s f rs i = some (s, f₁, rs₁) ∧ f₁.module = f.module ∧ LocalsOk Γ f₁ ∧
        StackOk st' rs₁) ∨
      (exec1S s f rs i = none ∧ traps1 rs i = true) := by
  cases i
  case nop =>
    simp only [tstep1, Option.some.injEq] at ht
    subst ht; exact .inl ⟨f, rs, rfl, rfl, hf, hs⟩
  case drop =>
    rcases st with _ | ⟨t, st⟩
    · simp [tstep1] at ht
    · simp only [tstep1, Option.some.injEq] at ht
      subst ht
      rcases rs with _ | ⟨v, rs⟩
      · exact (stackOk_nil hs).elim
      · exact .inl ⟨f, rs, rfl, rfl, hf, (stackOk_cons.mp hs).2⟩
  case intConst t c =>
    simp only [tstep1, Option.some.injEq] at ht
    subst ht; exact .inl ⟨f, _, rfl, rfl, hf, stackOk_cons.mpr ⟨⟨c, rfl⟩, hs⟩⟩
  case localGet x =>
    simp only [tstep1] at ht
    obtain ⟨t, hx, rfl⟩ := Option.map_eq_some_iff.mp ht
    obtain ⟨y, hy⟩ := hf.2 _ t hx
    refine .inl ⟨f, _, ?_, rfl, hf, stackOk_cons.mpr ⟨⟨y, rfl⟩, hs⟩⟩
    simp [exec1S, exec1, localVal?, Frame.local?, hy]
  case localSet x =>
    rcases st with _ | ⟨t, st⟩
    · simp [tstep1] at ht
    · simp only [tstep1, Option.ite_none_right_eq_some, Option.some.injEq] at ht
      obtain ⟨hx, rfl⟩ := ht
      rcases rs with _ | ⟨v, rs⟩
      · exact (stackOk_nil hs).elim
      · obtain ⟨⟨y, rfl⟩, hs'⟩ := stackOk_cons.mp hs
        refine .inl ⟨f.setLocal x (.num ⟨.int t, y⟩), rs, ?_, rfl, localsOk_set hf hx y, hs'⟩
        simp [exec1S, exec1, localsOk_lt hf hx]
  case localTee x =>
    rcases st with _ | ⟨t, st⟩
    · simp [tstep1] at ht
    · simp only [tstep1, Option.ite_none_right_eq_some, Option.some.injEq] at ht
      obtain ⟨hx, rfl⟩ := ht
      rcases rs with _ | ⟨v, rs⟩
      · exact (stackOk_nil hs).elim
      · obtain ⟨⟨y, rfl⟩, hs'⟩ := stackOk_cons.mp hs
        refine .inl ⟨f.setLocal x (.num ⟨.int t, y⟩), _, ?_, rfl, localsOk_set hf hx y,
          stackOk_cons.mpr ⟨⟨y, rfl⟩, hs'⟩⟩
        simp [exec1S, exec1, localsOk_lt hf hx]
  case intUnOp t op =>
    rcases st with _ | ⟨t', st⟩
    · simp [tstep1] at ht
    · simp only [tstep1, Option.ite_none_right_eq_some, Option.some.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      rcases rs with _ | ⟨v, rs⟩
      · exact (stackOk_nil hs).elim
      · obtain ⟨⟨x, rfl⟩, hs'⟩ := stackOk_cons.mp hs
        refine .inl ⟨f, _, ?_, rfl, hf, stackOk_cons.mpr ⟨⟨intUnOp t' op x, rfl⟩, hs'⟩⟩
        simp [exec1S, exec1, popInt_int]
  case intTestOp t op =>
    rcases st with _ | ⟨t', st⟩
    · simp [tstep1] at ht
    · simp only [tstep1, Option.ite_none_right_eq_some, Option.some.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      rcases rs with _ | ⟨v, rs⟩
      · exact (stackOk_nil hs).elim
      · obtain ⟨⟨x, rfl⟩, hs'⟩ := stackOk_cons.mp hs
        refine .inl ⟨f, _, ?_, rfl, hf, stackOk_cons.mpr ⟨⟨intTestOp t' op x, rfl⟩, hs'⟩⟩
        simp [exec1S, exec1, popInt_int]; rfl
  case intBinOp t op =>
    rcases st with _ | ⟨t₂, _ | ⟨t₁, st⟩⟩
    · simp [tstep1] at ht
    · simp [tstep1] at ht
    · simp only [tstep1, Option.ite_none_right_eq_some, Option.some.injEq] at ht
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ht
      rcases rs with _ | ⟨v₂, _ | ⟨v₁, rs⟩⟩
      · exact (stackOk_nil hs).elim
      · exact (stackOk_nil (stackOk_cons.mp hs).2).elim
      · obtain ⟨⟨y, rfl⟩, hs₁⟩ := stackOk_cons.mp hs
        obtain ⟨⟨x, rfl⟩, hs'⟩ := stackOk_cons.mp hs₁
        cases hz : intBinOp _ op x y with
        | ok z =>
          refine .inl ⟨f, _, ?_, rfl, hf, stackOk_cons.mpr ⟨⟨z, rfl⟩, hs'⟩⟩
          simp [exec1S, exec1, popInt_int, hz]
        | error e =>
          refine .inr ⟨?_, ?_⟩
          · simp [exec1S, exec1, popInt_int, hz]
          · simp [traps1, popInt_int, hz]
  case intRelOp t op =>
    rcases st with _ | ⟨t₂, _ | ⟨t₁, st⟩⟩
    · simp [tstep1] at ht
    · simp [tstep1] at ht
    · simp only [tstep1, Option.ite_none_right_eq_some, Option.some.injEq] at ht
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ht
      rcases rs with _ | ⟨v₂, _ | ⟨v₁, rs⟩⟩
      · exact (stackOk_nil hs).elim
      · exact (stackOk_nil (stackOk_cons.mp hs).2).elim
      · obtain ⟨⟨y, rfl⟩, hs₁⟩ := stackOk_cons.mp hs
        obtain ⟨⟨x, rfl⟩, hs'⟩ := stackOk_cons.mp hs₁
        refine .inl ⟨f, _, ?_, rfl, hf, stackOk_cons.mpr ⟨⟨intRelOp _ op x y, rfl⟩, hs'⟩⟩
        simp [exec1S, exec1, popInt_int]; rfl
  case select ts =>
    rcases st with _ | ⟨c, _ | ⟨t₂, _ | ⟨t₁, st⟩⟩⟩
    · simp [tstep1] at ht
    · simp [tstep1] at ht
    · simp [tstep1] at ht
    · simp only [tstep1, Option.ite_none_right_eq_some, Option.some.injEq] at ht
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ht
      rcases rs with _ | ⟨vc, _ | ⟨v₂, _ | ⟨v₁, rs⟩⟩⟩
      · exact (stackOk_nil hs).elim
      · exact (stackOk_nil (stackOk_cons.mp hs).2).elim
      · exact (stackOk_nil (stackOk_cons.mp (stackOk_cons.mp hs).2).2).elim
      · obtain ⟨⟨k, rfl⟩, hs₁⟩ := stackOk_cons.mp hs
        obtain ⟨⟨y, rfl⟩, hs₂⟩ := stackOk_cons.mp hs₁
        obtain ⟨⟨x, rfl⟩, hs'⟩ := stackOk_cons.mp hs₂
        by_cases hk : k = 0
        · refine .inl ⟨f, _, ?_, rfl, hf, stackOk_cons.mpr ⟨⟨y, rfl⟩, hs'⟩⟩
          simp [exec1S, selectV, popInt_int, hk]
        · refine .inl ⟨f, _, ?_, rfl, hf, stackOk_cons.mpr ⟨⟨x, rfl⟩, hs'⟩⟩
          simp only [exec1S, selectV, popInt_int, Option.map_some, Option.some.injEq,
            Prod.mk.injEq, true_and, List.cons.injEq, and_true]
          rw [ite_eq_right_of_eq_false _ _ (eq_false hk)]
  all_goals simp [tstep1] at ht

/-- **Typed code ends normally or traps**: `xexec` is never stuck. -/
theorem xexec_typed {Γ : List IntType} :
    ∀ {is : List Instr} {st st' : List IntType} {s : Store H} {f : Frame} {rs : List Val},
      tsteps Γ st is = some st' → LocalsOk Γ f → StackOk st rs →
        (∃ f' rs', xexec s f rs is = .ok s f' rs' ∧ f'.module = f.module) ∨
          (∃ f', xexec s f rs is = .trap s f' ∧ f'.module = f.module)
  | [], _, _, s, f, rs, _, _, _ => .inl ⟨f, rs, rfl, rfl⟩
  | i :: is, st, st', s, f, rs, ht, hf, hs => by
    simp only [tsteps] at ht
    split at ht
    · rename_i st₁ h₁
      rw [xexec_cons]
      rcases tstep1_progress h₁ hf hs s with ⟨f₁, rs₁, he, hm, hf₁, hs₁⟩ | ⟨he, htr⟩
      · rw [he]
        rcases xexec_typed ht hf₁ hs₁ with ⟨f', rs', h', hm'⟩ | ⟨f', h', hm'⟩
        · exact .inl ⟨f', rs', h', hm'.trans hm⟩
        · exact .inr ⟨f', h', hm'.trans hm⟩
      · rw [he]
        exact .inr ⟨f, by simp [htr], rfl⟩
    · cases ht

/-- Typed code without division ends normally. -/
theorem xexec_typed_noTrap {Γ : List IntType} :
    ∀ {is : List Instr} {st st' : List IntType} {s : Store H} {f : Frame} {rs : List Val},
      tsteps Γ st is = some st' → LocalsOk Γ f → StackOk st rs →
        (∀ t d, .intBinOp t (.div d) ∉ is) → (∀ t d, .intBinOp t (.rem d) ∉ is) →
        ∃ f' rs', xexec s f rs is = .ok s f' rs' ∧ f'.module = f.module
  | [], _, _, s, f, rs, _, _, _, _, _ => ⟨f, rs, rfl, rfl⟩
  | i :: is, st, st', s, f, rs, ht, hf, hs, hd, hr => by
    simp only [tsteps] at ht
    split at ht
    · rename_i st₁ h₁
      rw [xexec_cons]
      rcases tstep1_progress h₁ hf hs s with ⟨f₁, rs₁, he, hm, hf₁, hs₁⟩ | ⟨he, htr⟩
      · rw [he]
        obtain ⟨f', rs', h', hm'⟩ := xexec_typed_noTrap ht hf₁ hs₁
          (fun t d h => hd t d (List.mem_cons_of_mem _ h))
          (fun t d h => hr t d (List.mem_cons_of_mem _ h))
        exact ⟨f', rs', h', hm'.trans hm⟩
      · exfalso
        obtain ⟨t, op, x, y, e, rs₀, rfl, -, hz⟩ := traps1_eq htr
        rcases op with _ | _ | _ | d | d | _ | _ | _ | _ | sg | _ | _
        · exact absurd hz (by simp [intBinOp])
        · exact absurd hz (by simp [intBinOp])
        · exact absurd hz (by simp [intBinOp])
        · exact hd _ d List.mem_cons_self
        · exact hr _ d List.mem_cons_self
        · exact absurd hz (by simp [intBinOp])
        · exact absurd hz (by simp [intBinOp])
        · exact absurd hz (by simp [intBinOp])
        · exact absurd hz (by simp [intBinOp])
        · cases sg <;> exact absurd hz (by simp [intBinOp])
        · exact absurd hz (by simp [intBinOp])
        · exact absurd hz (by simp [intBinOp])
    · cases ht

end Silmaril.Proofs.Wasm.Auto.XExec