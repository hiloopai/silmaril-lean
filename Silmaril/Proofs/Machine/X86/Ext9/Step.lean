module

public import Silmaril.Machine.X86.Ext9.Defs

/-!
# `Ext9` step agreement with `Ext8`

`step_eq_of_ne_undecodable`: whenever `Ext8.step` does anything but report undecodable bytes,
the variant's step is that outcome. Hence every `Ext8` retirement is an `Ext9` retirement
(`stepOpt_of_ext8`, `run_of_ext8`) and every `Ext8.Returns` (and `Ext.Returns`) run is an
`Ext9.Returns` run (`returns_of_ext8`, `returns_of_ext`).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.Ext9

open Silmaril.X86 (Word MState)
open Silmaril.Machine.X86.Ext9

theorem step_eq_of_ne_undecodable {exit : Word} {m : MState}
    (h : Silmaril.X86.Ext8.step exit m ≠ .ext .undecodable) :
    step exit m = .ext8 (Silmaril.X86.Ext8.step exit m) := by
  unfold step
  split
  · rename_i e; exact absurd e h
  · rfl

theorem stepOpt_of_ext8 {exit : Word} {m next : MState}
    (h : Silmaril.X86.Ext8.stepOpt exit m = some next) : stepOpt exit m = some next := by
  unfold Silmaril.X86.Ext8.stepOpt at h
  split at h
  · rename_i n e
    simp only [Option.some.injEq] at h; subst h
    have := step_eq_of_ne_undecodable (exit := exit) (m := m) (by rw [e]; simp)
    simp [stepOpt, this, e]
  · rename_i n e
    simp only [Option.some.injEq] at h; subst h
    have := step_eq_of_ne_undecodable (exit := exit) (m := m) (by rw [e]; simp)
    simp [stepOpt, this, e]
  · cases h

theorem run_of_ext8 {exit : Word} : ∀ (n : Nat) {initial mid : MState},
    Silmaril.Machine.Execution.run (Silmaril.X86.Ext8.stepOpt exit) n initial = some mid →
    Silmaril.Machine.Execution.run (stepOpt exit) n initial = some mid
  | 0, _, _, h => h
  | n + 1, initial, mid, h => by
    simp only [Silmaril.Machine.Execution.run] at h ⊢
    cases e : Silmaril.X86.Ext8.stepOpt exit initial with
    | none => simp [e] at h
    | some next =>
      rw [e] at h
      simp only [Option.bind_some] at h
      rw [stepOpt_of_ext8 e]
      exact run_of_ext8 n h

theorem returns_of_ext8 {exit : Word} {initial final : MState}
    (h : Silmaril.X86.Ext8.Returns exit initial final) : Returns exit initial final := by
  obtain ⟨n, mid, hrun, hstep⟩ := h
  refine ⟨n, mid, run_of_ext8 n hrun, ?_⟩
  rw [step_eq_of_ne_undecodable (by rw [hstep]; simp), hstep]

end Silmaril.Proofs.Machine.X86.Ext9
