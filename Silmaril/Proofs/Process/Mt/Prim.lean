module

public import Silmaril.Process.Mt.Prim.Defs

/-!
# Proofs: the executable primitives implement their specifications

The header is `Silmaril/Process/Mt/Prim/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.Process.Mt.Prim

open Silmaril.X86 (Word)
open Silmaril.Process.Mt
open Silmaril.Process.Mt.Prim

variable {γ : Type}

theorem execRmw_sound {n t : Nat} {f : Nat → List Word → Option Nat × Nat} {args : List Word}
    {sh sh2 : Sh γ} {w : Word} (h : execRmw n f args sh = some (w, sh2)) :
    (rmw n f).pre t args sh ∧ (rmw n f).post t args sh w sh2 := by
  unfold execRmw at h
  split at h
  · rename_i hpre
    refine ⟨hpre, ?_⟩
    split at h
    · rename_i o ho
      refine ⟨o, ho, ?_⟩
      split at h
      · rename_i hf
        cases h
        exact ⟨rfl, rfl, rfl, by simp⟩
      · rename_i v hf
        cases hw : wr sh.mem (arg args 0) n v with
        | none => rw [hw] at h; cases h
        | some m =>
          rw [hw] at h; cases h
          exact ⟨rfl, rfl, rfl, by simp⟩
    · cases h
  · cases h

theorem exec_sound {s : Std} {t : Nat} {args : List Word} {sh sh2 : Sh γ} {w : Word}
    (h : s.exec t args sh = some (w, sh2)) : s.spec.pre t args sh ∧ s.spec.post t args sh w sh2 := by
  cases s with
  | fence =>
    simp only [Std.exec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Std.spec, Prim.fence]
  | load n => exact execRmw_sound h
  | store n => exact execRmw_sound h
  | xchg n => exact execRmw_sound h
  | cas n => exact execRmw_sound h
  | fadd n => exact execRmw_sound h
  | mutexLock =>
    simp only [Std.exec] at h
    split at h
    · rename_i hl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Std.spec, Prim.mutexLock, Prim.SetLocks]
      constructor
      · intro d e; rw [hl] at e; cases e
      · simp [hl]
    · cases h
  | mutexUnlock =>
    simp only [Std.exec] at h
    split at h
    · rename_i hl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Std.spec, Prim.mutexUnlock, Prim.SetLocks]
      simp [hl]
    · cases h
  | _ => simp [Std.exec] at h

theorem execTable_sound {p t : Nat} {args : List Word} {sh sh2 : Sh γ} {w : Word}
    (h : execTable p t args sh = some (w, sh2)) :
    ∃ sp, (table : PrimTable γ) p = some sp ∧ sp.pre t args sh ∧ sp.post t args sh w sh2 := by
  unfold execTable at h
  cases hf : Std.all.find? (·.id == p) with
  | none => rw [hf] at h; cases h
  | some s =>
    rw [hf] at h
    exact ⟨s.spec, by simp [table, hf], exec_sound h⟩

end Silmaril.Proofs.Process.Mt.Prim
