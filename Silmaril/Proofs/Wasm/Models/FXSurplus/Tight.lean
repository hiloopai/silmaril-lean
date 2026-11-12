module

public import Silmaril.Wasm.Models.FXAsyncSus.Thms

/-!
# Determinism of FX runs on the tight fragment

A deterministic machine has at most one behaviour (`beh_subsingleton`: a stopped run fixes the
outcome of every longer run, and excludes divergence). Through `FXAsyncSus.beh_eq_tight`, the
`StepFX'` behaviours of an encoded kernel program on the tight fragment (deterministic profile,
no host calls) are the image of the kernel's, so they form a subsingleton too
(`behFX_subsingleton_tight`), although `StepFX'` itself is not deterministic there
(`FXAsyncBack.suspend_nondet`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXSurplus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Wasm.Models.FXAsync (SCfg Ins Prog sstep beh runN Res Outcome)
open Silmaril.Proofs.Wasm.Models.FXAsyncSus (TightSupported)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

/-- Once a run stops, every longer run stops with the same outcome. -/
theorem runN_stop_mono {C V : Type} {step : C → Res C V} {o : Outcome V} :
    ∀ {n : Nat} {c : C}, runN step n c = .stop o → ∀ m, n ≤ m → runN step m c = .stop o := by
  intro n
  induction n with
  | zero => intro c h; exact absurd h (by simp [runN])
  | succ n ih =>
    intro c h m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    unfold runN at h ⊢
    cases hs : step c with
    | next c' =>
      rw [hs] at h
      exact ih h m (by omega)
    | stop o' =>
      rw [hs] at h
      exact h

/-- **A deterministic machine has at most one behaviour.** -/
theorem beh_subsingleton {C V : Type} (step : C → Res C V) (c : C) :
    (beh step c).Subsingleton := by
  have stop_stop : ∀ {n m : Nat} {o o' : Outcome V}, runN step n c = .stop o →
      runN step m c = .stop o' → o = o' := by
    intro n m o o' h h'
    have h₁ := runN_stop_mono h _ (Nat.le_max_left n m)
    have h₂ := runN_stop_mono h' _ (Nat.le_max_right n m)
    rw [h₁] at h₂
    exact Res.stop.inj h₂
  have stop_div : ∀ {n : Nat} {o : Outcome V}, runN step n c = .stop o →
      ¬ ∀ k, ∃ c', runN step k c = .next c' := by
    intro n o h hd
    obtain ⟨c', hc'⟩ := hd n
    rw [h] at hc'
    exact absurd hc' (by simp)
  rintro b (⟨n, o, hn, rfl⟩ | ⟨rfl, hd⟩) b' (⟨m, o', hm, rfl⟩ | ⟨rfl, hd'⟩)
  · rw [stop_stop hn hm]
  · exact absurd hd' (stop_div hn)
  · exact absurd hd (stop_div hm)
  · rfl

/-- **FX runs are deterministic on the tight fragment**: at most one `StepFX'` behaviour. -/
theorem behFX_subsingleton_tight {H : Type} (S : Setup H) {W : Prog (Ins Val)}
    {o : GrowKind → Nat → Nat → Nat → Bool} (hP : S.P = Profile.deterministic o)
    (hH : S.host = noHost) (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hsup : TightSupported W x) :
    (behavioursFX' S.P S.host S.fx c).Subsingleton := by
  rw [Silmaril.Wasm.Models.FXAsyncSus.beh_eq_tight S hP hH hok hR hsup]
  exact (beh_subsingleton _ _).image _

end Silmaril.Proofs.Wasm.Models.FXSurplus
