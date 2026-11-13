module

public import Silmaril.Wasm.FX.Asyncify.Host.Defs
public import Silmaril.Proofs.Wasm.FX.Asyncify.SelSim

/-!
# Asyncify with a host: the closed machines step as the open ones

Away from a blocking call (`blockedOn`) the host-closed source `hsstep` is the kernel; away from
the root of an unwinding (`atRoot`) the host-closed target `htstep` is the asyncify machine
`tstep`, and at the root `tstep` traps. So every `tstep` run that continues, or returns, is a
run of `htstep` with the host state unchanged (`runN_h_next`, `runN_h_done`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Host

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify
open Silmaril.Wasm.FX.Asyncify.Host

variable {V σ : Type}

/-- `n` steps then the rest. -/
theorem runN_cat {C : Type} {step : C → Res C V} {a : Nat} {c c' : C}
    (h : runN step a c = .next c') (b : Nat) : runN step (a + b) c = runN step b c' := by
  induction a generalizing c with
  | zero =>
    have hc : c = c' := by simpa only [runN, Res.next.injEq] using h
    rw [Nat.zero_add, hc]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [runN] at h ⊢
    cases hs : step c with
    | next c₁ =>
      have h' : runN step a c₁ = .next c' := by rw [hs] at h; exact h
      exact ih h'
    | stop o => rw [hs] at h; cases h

/-- One step of a run. -/
theorem runN_one_eq {C : Type} {step : C → Res C V} {c : C} {r : Res C V} (h : step c = r) :
    runN step 1 c = r := by
  rw [← h]
  simp only [runN]
  cases step c <;> rfl

/-- At the root of an unwinding the asyncify machine traps. -/
theorem tstep_atRoot {Q : Prog (TIns V)} {test : V → Bool} {y : TCfg V}
    {r : Nat × List (SV V) × List (TFrame V)} (h : atRoot y = some r) :
    tstep Q test y = .stop .trap := by
  rcases y with ⟨hp, _ | ⟨t, p, buf⟩ | ⟨pend, a⟩, _ | ⟨b, rest⟩⟩ <;> first | rfl | cases h

/-- Away from the root, the closed target is the asyncify machine. -/
theorem htstep_of_none {Q : Prog (TIns V)} {test : V → Bool} {H : KHost V σ} {y : TCfg V}
    (h : atRoot y = none) (s : σ) :
    htstep Q test H (y, s) = (tstep Q test y).map (·, s) := by
  simp only [htstep, h]

/-- A continuing step of the asyncify machine is a step of the closed target. -/
theorem htstep_next {Q : Prog (TIns V)} {test : V → Bool} (H : KHost V σ) {y z : TCfg V}
    (h : tstep Q test y = .next z) (s : σ) : htstep Q test H (y, s) = .next (z, s) := by
  cases hr : atRoot y with
  | some r => rw [tstep_atRoot hr] at h; cases h
  | none => rw [htstep_of_none hr, h]; rfl

/-- A returning step of the asyncify machine is a step of the closed target. -/
theorem htstep_stop {Q : Prog (TIns V)} {test : V → Bool} (H : KHost V σ) {y : TCfg V}
    {o : Outcome V} (h : tstep Q test y = .stop o) (ho : o ≠ .trap ∨ atRoot y = none) (s : σ) :
    htstep Q test H (y, s) = .stop o := by
  cases hr : atRoot y with
  | some r =>
    rw [tstep_atRoot hr] at h
    cases h
    rcases ho with ho | ho
    · exact absurd rfl ho
    · cases hr.symm.trans ho
  | none => rw [htstep_of_none hr, h]; rfl

/-- In normal mode, or on a non-empty stack, the closed target is the asyncify machine. -/
theorem atRoot_normal {y : TCfg V} (h : y.mode = .normal) : atRoot y = none := by
  rcases y with ⟨hp, m, stk⟩
  cases h
  rfl

theorem atRoot_cons {hp : List (Option (List (TFrame V)))} {m : Mode V} {b : TFrame V}
    {rest : List (TFrame V)} : atRoot (⟨hp, m, b :: rest⟩ : TCfg V) = none := by
  cases m <;> rfl

/-- **A continuing run of the asyncify machine is a run of the closed target.** -/
theorem runN_h_next {Q : Prog (TIns V)} {test : V → Bool} (H : KHost V σ) (s : σ) :
    ∀ (n : Nat) (y z : TCfg V), runN (tstep Q test) n y = .next z →
      runN (htstep Q test H) n (y, s) = .next (z, s)
  | 0, y, z, h => by
    have hz : y = z := by simpa only [runN, Res.next.injEq] using h
    rw [hz]
    rfl
  | n + 1, y, z, h => by
    cases hs : tstep Q test y with
    | next y₁ =>
      have h' : runN (tstep Q test) n y₁ = .next z := by simp only [runN, hs] at h; exact h
      simp only [runN, htstep_next H hs s]
      exact runN_h_next H s n y₁ z h'
    | stop o => simp only [runN, hs] at h; cases h

/-- **A returning run of the asyncify machine is a run of the closed target.** -/
theorem runN_h_done {Q : Prog (TIns V)} {test : V → Bool} (H : KHost V σ) (s : σ)
    (vs : List (SV V)) : ∀ (n : Nat) (y : TCfg V),
      runN (tstep Q test) n y = .stop (.done vs) →
      runN (htstep Q test H) n (y, s) = .stop (.done vs)
  | 0, y, h => by cases h
  | n + 1, y, h => by
    cases hs : tstep Q test y with
    | next y₁ =>
      have h' : runN (tstep Q test) n y₁ = .stop (.done vs) := by
        simp only [runN, hs] at h; exact h
      simp only [runN, htstep_next H hs s]
      exact runN_h_done H s vs n y₁ h'
    | stop o =>
      have ho : o = .done vs := by simpa only [runN, hs, Res.stop.injEq] using h
      have hstep : htstep Q test H (y, s) = .stop (.done vs) :=
        htstep_stop H (hs.trans (congrArg _ ho)) (.inl (by intro h; cases h)) s
      simp only [runN, hstep]

/-- Away from a blocking call, the closed source is the kernel. -/
theorem hsstep_of_none {P : Prog (Ins V)} {test : V → Bool} {H : KHost V σ} {x : SCfg V}
    (h : blockedOn x.stack = none) (s : σ) :
    hsstep P test H (x, s) = (sstep P test x).map (·, s) := by
  simp only [hsstep, h]

/-- The shape of a blocking call. -/
theorem blockedOn_some {L : List (SFrame V)} {t : Nat} {p : List (SV V)} {fr : SFrame V}
    (h : blockedOn L = some (t, p, fr)) :
    ∃ n c ops w rest o', L = ⟨.suspend t n :: c, ops, w⟩ :: rest ∧
      popN n ops = some (p, o') ∧ split t rest = none ∧ fr = ⟨c, o', w⟩ := by
  rcases L with _ | ⟨⟨_ | ⟨i, c⟩, ops, w⟩, rest⟩
  · cases h
  · cases h
  cases i with
  | suspend t' n =>
    rcases hp : popN n ops with _ | ⟨p', o'⟩ <;> rcases hsp : split t' rest with _ | q <;>
      simp only [blockedOn, hp, hsp, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨n, c, ops, w, rest, o', rfl, hp, hsp, rfl⟩
  | _ => cases h

/-- No blocking call unless the top instruction is a `suspend`. -/
theorem blockedOn_of_not {top : SFrame V} {rest : List (SFrame V)}
    (h : ∀ t n c, top.code ≠ .suspend t n :: c) : blockedOn (top :: rest) = none := by
  rcases top with ⟨_ | ⟨i, c⟩, ops, w⟩
  · rfl
  cases i with
  | suspend t n => exact absurd rfl (h t n c)
  | _ => rfl

end Silmaril.Proofs.Wasm.FX.Asyncify.Host
