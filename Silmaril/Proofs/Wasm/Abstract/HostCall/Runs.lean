module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Execution.Core.Inversion.Thms
public import Silmaril.Proofs.Wasm.Abstract.HostCall.Split

/-!
# Counted Core runs and their splits (proofs)

The whole-run backward simulation is an induction on the length of a Core run
(a loop re-runs the same tree, on a strictly shorter remaining run). So the
splits are restated on counted runs (`StepsN`):

* `stepsN_seq_split`: a run of `es ++ rest` in `n` steps to a stuck
  configuration runs `es` alone in `n₁ ≤ n` steps to a stuck `c₁`; when `c₁` is
  values, the continuation takes the remaining `n - n₁` steps;
* `stepsN_label_split`: a run of `[label k cont is]` in `n` steps runs `is` in
  `n₁ ≤ n` steps to some `c₁`; then either the label is still there and `c₁` is
  stuck, or the label exits (`LabelExit`) and the rest takes `n - n₁ - 1` steps.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostCall

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

theorem _root_.Silmaril.Wasm.Abstract.StepsN.steps {n : Nat} {c c' : Config H} (h : StepsN P host n c c') : Steps P host c c' := by
  induction h with
  | refl => exact .refl
  | head hs _ ih => exact .head hs ih

theorem stepsN_of_steps {c c' : Config H} (h : Steps P host c c') : ∃ n, StepsN P host n c c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head hs _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .head hs h⟩

theorem _root_.Silmaril.Wasm.Abstract.StepsN.refl_eq {c c' : Config H} (h : StepsN P host 0 c c') : c' = c := by
  cases h; rfl

/-- The conclusion of `stepsN_seq_split`. -/
def SeqSplitN (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (n : Nat)
    (s : Store H) (f : Frame) (es rest : List Admin) (c : Config H) : Prop :=
  ∃ (c₁ : Config H) (n₁ : Nat), StepsN P host n₁ ⟨s, f, es⟩ c₁ ∧ n₁ ≤ n ∧
    (∀ c', ¬ Step P host c₁ c') ∧
    ((∃ ws, c₁.code = vals ws ∧ StepsN P host (n - n₁) ⟨c₁.store, c₁.frame, vals ws ++ rest⟩ c) ∨
      (c₁.code = [.trap] ∧ c = c₁) ∨ (∃ x, c₁.code = throwing x ∧ c = c₁) ∨
      c = ⟨c₁.store, c₁.frame, c₁.code ++ rest⟩)

theorem seqSplitN_trap {m : Nat} {s : Store H} {f : Frame} {ws : List Val} {r rest : List Admin}
    {c : Config H} (hrun : StepsN P host m ⟨s, f, vals ws ++ .trap :: r ++ rest⟩ c)
    (hend : ∀ c', ¬ Step P host c c') : SeqSplitN P host m s f (vals ws ++ .trap :: r) rest c := by
  have hc := steps_trap_head (by simpa using hrun.steps) hend
  subst hc
  by_cases hne : ws ≠ [] ∨ r ≠ []
  · rcases m with _ | m
    · exfalso
      have h0 := hrun.refl_eq
      have hne' : ws ≠ [] ∨ r ++ rest ≠ [] := by
        rcases hne with h | h
        · exact .inl h
        · exact .inr (by simp [h])
      have hst := Step.trapInstrs (P := P) (host := host) (s := s) (f := f) hne'
      apply hend _
      rw [h0]
      simpa using hst
    · have hst := Step.trapInstrs (P := P) (host := host) (s := s) (f := f) hne
      exact ⟨_, 1, .head (by simpa using hst) (.refl _), by omega, fun _ => trap_stuck,
        .inr (.inl ⟨rfl, rfl⟩)⟩
  · simp only [ne_eq, not_or, Decidable.not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    exact ⟨_, 0, .refl _, by omega, fun _ => trap_stuck, .inr (.inl ⟨rfl, rfl⟩)⟩

theorem seqSplitN_throw {m : Nat} {s : Store H} {f : Frame} {ws : List Val} {x : Nat}
    {r rest : List Admin} {c : Config H}
    (hrun : StepsN P host m ⟨s, f, vals ws ++ throwing x ++ r ++ rest⟩ c)
    (hend : ∀ c', ¬ Step P host c c') :
    SeqSplitN P host m s f (vals ws ++ throwing x ++ r) rest c := by
  have hc := steps_throw_head (r := r ++ rest) (by simpa using hrun.steps) hend
  subst hc
  by_cases hne : ws ≠ [] ∨ r ≠ []
  · rcases m with _ | m
    · exfalso
      have h0 := hrun.refl_eq
      have hne' : ws ≠ [] ∨ r ++ rest ≠ [] := by
        rcases hne with h | h
        · exact .inl h
        · exact .inr (by simp [h])
      have hst := Step.throwRefInstrs (P := P) (host := host) (s := s) (f := f) (a := x) hne'
      apply hend _
      rw [h0]
      simpa using hst
    · exact ⟨_, 1, .head (Step.throwRefInstrs hne) (.refl _), by omega, fun _ => throw_stuck,
        .inr (.inr (.inl ⟨x, rfl, rfl⟩))⟩
  · simp only [ne_eq, not_or, Decidable.not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    exact ⟨⟨s, f, throwing x⟩, 0, by simpa [vals] using StepsN.refl (P := P) (host := host) _,
      by omega, fun _ => throw_stuck, .inr (.inr (.inl ⟨x, rfl, rfl⟩))⟩

/-- **Splitting a counted run of a sequence.** -/
theorem stepsN_seq_split {n : Nat} {s : Store H} {f : Frame} {es rest : List Admin} {c : Config H}
    (hrun : StepsN P host n ⟨s, f, es ++ rest⟩ c) (hend : ∀ c', ¬ Step P host c c') :
    SeqSplitN P host n s f es rest c := by
  suffices key : ∀ n y, StepsN P host n y c → ∀ s f es, y = ⟨s, f, es ++ rest⟩ →
      SeqSplitN P host n s f es rest c from key _ _ hrun s f es rfl
  clear hrun
  intro n y hy
  induction hy with
  | refl =>
    intro s f es hy
    subst hy
    rcases head_cases es with ⟨ws, rfl⟩ | ⟨ws, r, rfl⟩ | ⟨ws, x, r, rfl⟩ | ⟨vs, a, r, rfl, -, -, -⟩
    · exact ⟨_, 0, .refl _, le_refl _, fun _ => Sim.Step.not_vals, .inl ⟨ws, rfl, .refl _⟩⟩
    · exact seqSplitN_trap (.refl _) hend
    · exact seqSplitN_throw (.refl _) hend
    · refine ⟨_, 0, .refl _, le_refl _, fun c' hc' => ?_, .inr (.inr (.inr rfl))⟩
      rcases c' with ⟨s', f', es'⟩
      exact hend _ (Sim.Step.append_right hc' rest)
  | @head m y b _ hstep hrest ih =>
    intro s f es hy
    subst hy
    rcases head_cases es with ⟨ws, rfl⟩ | ⟨ws, r, rfl⟩ | ⟨ws, x, r, rfl⟩ |
        ⟨vs, a, r, rfl, ha, hat, hax⟩
    · exact ⟨_, 0, .refl _, by omega, fun _ => Sim.Step.not_vals,
        .inl ⟨ws, rfl, .head hstep hrest⟩⟩
    · exact seqSplitN_trap (.head hstep hrest) hend
    · exact seqSplitN_throw (.head hstep hrest) hend
    rcases b with ⟨s', f', es'⟩
    have hstep' : Step P host ⟨s, f, vals vs ++ a :: (r ++ rest)⟩ ⟨s', f', es'⟩ := by
      simpa using hstep
    rcases Sim.Step.split_head ha hstep' with ⟨ws, us, is', rfl, hst, rfl⟩ |
        ⟨rfl, -⟩ | ⟨rfl, -, -, ws, us, x, r₁, r₂, rfl, -, -, -⟩
    · obtain ⟨c₁, n₁, h₁, hn₁, hs₁, hk⟩ := ih hend s' f' (vals ws ++ is' ++ r) (by simp)
      have hst' := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) ws r hst
      refine ⟨c₁, n₁ + 1, .head (by simpa using hst') h₁, by omega, hs₁, ?_⟩
      rwa [Nat.add_sub_add_right]
    · exact absurd rfl hat
    · exact absurd ⟨rfl, by simp⟩ (hax (ws ++ us) x)

/-- The conclusion of `stepsN_label_split`. -/
def LabelSplitN (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (n : Nat)
    (s : Store H) (f : Frame) (k : Nat) (cont : List Instr) (is : List Admin) (c : Config H) :
    Prop :=
  ∃ (c₁ : Config H) (n₁ : Nat), StepsN P host n₁ ⟨s, f, is⟩ c₁ ∧ n₁ ≤ n ∧
    ((c = ⟨c₁.store, c₁.frame, [.label k cont c₁.code]⟩ ∧ ∀ c', ¬ Step P host c₁ c') ∨
      ∃ out, n₁ < n ∧ LabelExit k cont c₁.code out ∧
        StepsN P host (n - n₁ - 1) ⟨c₁.store, c₁.frame, out⟩ c)

/-- **Splitting a counted run of a label**: the body runs inside until the label
is stuck or exits. -/
theorem stepsN_label_split {n : Nat} {s : Store H} {f : Frame} {k : Nat} {cont : List Instr}
    {is : List Admin} {c : Config H} (hrun : StepsN P host n ⟨s, f, [.label k cont is]⟩ c)
    (hend : ∀ c', ¬ Step P host c c') : LabelSplitN P host n s f k cont is c := by
  suffices key : ∀ n y, StepsN P host n y c → ∀ s f is, y = ⟨s, f, [.label k cont is]⟩ →
      LabelSplitN P host n s f k cont is c from key _ _ hrun s f is rfl
  clear hrun
  intro n y hy
  induction hy with
  | refl =>
    intro s f is hy
    subst hy
    refine ⟨_, 0, .refl _, le_refl _, .inl ⟨rfl, fun c' hc' => ?_⟩⟩
    rcases c' with ⟨s', f', is'⟩
    exact hend _ (Step.ctxtLabel hc')
  | @head m y b _ hstep hrest ih =>
    intro s f is hy
    subst hy
    rcases Step.label_inv hstep with ⟨s', f', is', hin, rfl⟩ | ⟨out, hex, rfl⟩
    · obtain ⟨c₁, n₁, h₁, hn₁, hk⟩ := ih hend s' f' is' rfl
      refine ⟨c₁, n₁ + 1, .head hin h₁, by omega, ?_⟩
      rcases hk with hk | ⟨out, hlt, hex, hr⟩
      · exact .inl hk
      · refine .inr ⟨out, by omega, hex, ?_⟩
        have : m + 1 - (n₁ + 1) - 1 = m - n₁ - 1 := by omega
        rwa [this]
    · exact ⟨_, 0, .refl _, by omega, .inr ⟨out, by omega, hex, by simpa using hrest⟩⟩

end Silmaril.Proofs.Wasm.Abstract.HostCall
