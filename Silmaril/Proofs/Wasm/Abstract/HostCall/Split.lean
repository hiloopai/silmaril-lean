module

public import Silmaril.Wasm.Execution.Core.Inversion.Thms
public import Silmaril.Wasm.Execution.Core.Sim.Context
public import Silmaril.Wasm.Logic.Core.Thms

/-!
# Splitting a Core run of a sequence (proofs)

A trap or exception at the head of the code only bubbles: from
`vals ws ++ trap :: r` every step keeps the form `vals ws' ++ trap :: r'`,
strictly shorter, in the same store and frame (`trap_step`), so every run to a
stuck configuration ends at `[trap]` (`steps_trap_head`). The same holds for the
canonical thrown form `throwing x = [ref.exn x, throw_ref]`
(`throw_step`, `steps_throw_head`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostCall

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- A step under a head trap is a bubbling step. -/
theorem trap_step {s : Store H} {f : Frame} {ws : List Val} {r : List Admin} {c : Config H}
    (h : Step P host ⟨s, f, vals ws ++ .trap :: r⟩ c) :
    ∃ ws' r', c = ⟨s, f, vals ws' ++ .trap :: r'⟩ ∧ ws'.length + r'.length < ws.length + r.length := by
  rcases c with ⟨s', f', es'⟩
  rcases Sim.Step.split_head Sim.val?_trap h with ⟨w₀, us, is', rfl, hst, rfl⟩ |
      ⟨-, rfl, rfl, w₀, us, r₁, r₂, rfl, rfl, hne, rfl⟩ | ⟨hx, -⟩
  · obtain ⟨w, hc, hw⟩ := Step.trap_vals_inv hst
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨w₀ ++ w, r, by simp, by simp; omega⟩
  · refine ⟨w₀, r₂, by simp, ?_⟩
    rcases hne with h | h
    · have := List.length_pos_iff.2 h; simp; omega
    · have := List.length_pos_iff.2 h; simp; omega
  · cases hx

/-- `[trap]` has no step. -/
theorem trap_stuck {s : Store H} {f : Frame} {c : Config H} : ¬ Step P host ⟨s, f, [.trap]⟩ c := by
  intro h
  obtain ⟨ws', r', -, hl⟩ := trap_step (ws := []) (r := []) (by simpa [vals] using h)
  simp at hl

/-- A head trap reaches `[trap]`. -/
theorem steps_to_trap (s : Store H) (f : Frame) (ws : List Val) (r : List Admin) :
    Steps P host ⟨s, f, vals ws ++ .trap :: r⟩ ⟨s, f, [.trap]⟩ := by
  by_cases hne : ws ≠ [] ∨ r ≠ []
  · exact .single (by simpa using Step.trapInstrs (P := P) (host := host) (s := s) (f := f) hne)
  · simp only [ne_eq, not_or, Decidable.not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    exact .refl

/-- **A head trap only bubbles**: every run from `vals ws ++ trap :: r` to a
stuck configuration ends at `[trap]`, in the same store and frame. -/
theorem steps_trap_head {s : Store H} {f : Frame} {ws : List Val} {r : List Admin} {c : Config H}
    (hrun : Steps P host ⟨s, f, vals ws ++ .trap :: r⟩ c) (hend : ∀ c', ¬ Step P host c c') :
    c = ⟨s, f, [.trap]⟩ := by
  suffices key : ∀ x, Steps P host x c → ∀ ws r, x = ⟨s, f, vals ws ++ .trap :: r⟩ →
      c = ⟨s, f, [.trap]⟩ from key _ hrun ws r rfl
  intro x hx
  induction hx using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro ws r hx
    subst hx
    by_cases hne : ws ≠ [] ∨ r ≠ []
    · exact (hend _ (by simpa using Step.trapInstrs (P := P) (host := host) (s := s) (f := f) hne)).elim
    · simp only [ne_eq, not_or, Decidable.not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      simp [vals]
  | head hstep _ ih =>
    intro ws r hx
    subst hx
    obtain ⟨ws', r', rfl, -⟩ := trap_step hstep
    exact ih ws' r' rfl

theorem throwing_code (ws : List Val) (x : Nat) (r : List Admin) :
    vals ws ++ throwing x ++ r = vals (ws ++ [.ref (.exn x)]) ++ .plain .throwRef :: r := by
  simp [throwing, vals, Val.toAdmin]

/-- A step under a head exception is a bubbling step. -/
theorem throw_step {s : Store H} {f : Frame} {ws : List Val} {x : Nat} {r : List Admin}
    {c : Config H} (h : Step P host ⟨s, f, vals ws ++ throwing x ++ r⟩ c) :
    ∃ ws' r', c = ⟨s, f, vals ws' ++ throwing x ++ r'⟩ ∧
      ws'.length + r'.length < ws.length + r.length := by
  rcases c with ⟨s', f', es'⟩
  rw [throwing_code] at h
  rcases Sim.Step.split_head Sim.val?_throwRef h with ⟨w₀, us, is', hsplit, hst, rfl⟩ |
      ⟨hx, -⟩ | ⟨-, rfl, rfl, w₀, us, y, r₁, r₂, hsplit, rfl, hne, rfl⟩
  · rcases Step.throwRef_vals_inv hst with ⟨w, rfl, hc⟩ | ⟨w, w', y, rfl, hne, hc⟩
    · rw [← List.append_assoc] at hsplit
      have := (List.append_inj' hsplit rfl).2
      simp at this
    · simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      rw [← List.append_assoc, ← List.append_assoc] at hsplit
      obtain ⟨rfl, hy⟩ := List.append_inj' hsplit rfl
      simp only [List.cons.injEq, Val.ref.injEq, Ref.exn.injEq, and_true] at hy
      subst hy
      refine ⟨w₀ ++ w, r, by simp, ?_⟩
      have := List.length_pos_iff.2 hne
      simp; omega
  · cases hx
  · obtain ⟨rfl, hy⟩ := List.append_inj' hsplit rfl
    simp only [List.cons.injEq, Val.ref.injEq, Ref.exn.injEq, and_true] at hy
    subst hy
    refine ⟨w₀, r₂, by simp, ?_⟩
    rcases hne with h | h
    · have := List.length_pos_iff.2 h; simp; omega
    · have := List.length_pos_iff.2 h; simp; omega

/-- `throwing x` has no step. -/
theorem throw_stuck {s : Store H} {f : Frame} {x : Nat} {c : Config H} :
    ¬ Step P host ⟨s, f, throwing x⟩ c := by
  intro h
  obtain ⟨ws', r', -, hl⟩ := throw_step (ws := []) (r := []) (by simpa [vals] using h)
  simp at hl

/-- A head exception reaches `throwing x`. -/
theorem steps_to_throw (s : Store H) (f : Frame) (ws : List Val) (x : Nat) (r : List Admin) :
    Steps P host ⟨s, f, vals ws ++ throwing x ++ r⟩ ⟨s, f, throwing x⟩ := by
  by_cases hne : ws ≠ [] ∨ r ≠ []
  · exact .single (Step.throwRefInstrs hne)
  · simp only [ne_eq, not_or, Decidable.not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simpa [vals] using .refl

/-- **A head exception only bubbles**: every run from `vals ws ++ throwing x ++ r`
to a stuck configuration ends at `throwing x`, in the same store and frame. -/
theorem steps_throw_head {s : Store H} {f : Frame} {ws : List Val} {x : Nat} {r : List Admin}
    {c : Config H} (hrun : Steps P host ⟨s, f, vals ws ++ throwing x ++ r⟩ c)
    (hend : ∀ c', ¬ Step P host c c') : c = ⟨s, f, throwing x⟩ := by
  suffices key : ∀ y, Steps P host y c → ∀ ws r, y = ⟨s, f, vals ws ++ throwing x ++ r⟩ →
      c = ⟨s, f, throwing x⟩ from key _ hrun ws r rfl
  intro y hy
  induction hy using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro ws r hy
    subst hy
    by_cases hne : ws ≠ [] ∨ r ≠ []
    · exact (hend _ (Step.throwRefInstrs hne)).elim
    · simp only [ne_eq, not_or, Decidable.not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      simp [vals]
  | head hstep _ ih =>
    intro ws r hy
    subst hy
    obtain ⟨ws', r', rfl, -⟩ := throw_step hstep
    exact ih ws' r' rfl

/-! ## Splitting a run of `es ++ rest` -/

/-- The head of a code sequence: all values, a trap, a thrown exception, or
another non-value. -/
theorem head_cases (es : List Admin) :
    (∃ ws, es = vals ws) ∨ (∃ ws r, es = vals ws ++ .trap :: r) ∨
      (∃ ws x r, es = vals ws ++ throwing x ++ r) ∨
      ∃ vs a r, es = vals vs ++ a :: r ∧ a.val? = none ∧ a ≠ .trap ∧
        ∀ ws x, ¬ (a = .plain .throwRef ∧ vs = ws ++ [.ref (.exn x)]) := by
  cases hall : es.all Admin.isVal
  · obtain ⟨vs, a, r, ha, rfl⟩ := Sim.exists_head_of_not_all hall
    by_cases ht : a = .trap
    · subst ht; exact .inr (.inl ⟨vs, r, rfl⟩)
    by_cases hx : ∃ ws x, a = .plain .throwRef ∧ vs = ws ++ [.ref (.exn x)]
    · obtain ⟨ws, x, rfl, rfl⟩ := hx
      exact .inr (.inr (.inl ⟨ws, x, r, (throwing_code ws x r).symm⟩))
    · refine .inr (.inr (.inr ⟨vs, a, r, rfl, ha, ht, fun ws x h => hx ⟨ws, x, h⟩⟩))
  · exact .inl (Sim.exists_vals_of_all hall)

/-- The conclusion of `steps_seq_split`: `es` runs to a stuck `c₁`, and the run of
`es ++ rest` is its continuation. -/
def SeqSplit (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (f : Frame) (es rest : List Admin) (c : Config H) : Prop :=
  ∃ c₁ : Config H, Steps P host ⟨s, f, es⟩ c₁ ∧ (∀ c', ¬ Step P host c₁ c') ∧
    ((∃ ws, c₁.code = vals ws ∧ Steps P host ⟨c₁.store, c₁.frame, vals ws ++ rest⟩ c) ∨
      (c₁.code = [.trap] ∧ c = c₁) ∨ (∃ x, c₁.code = throwing x ∧ c = c₁) ∨
      c = ⟨c₁.store, c₁.frame, c₁.code ++ rest⟩)

theorem seqSplit_trap {s : Store H} {f : Frame} {ws : List Val} {r rest : List Admin}
    {c : Config H} (hrun : Steps P host ⟨s, f, vals ws ++ .trap :: r ++ rest⟩ c)
    (hend : ∀ c', ¬ Step P host c c') : SeqSplit P host s f (vals ws ++ .trap :: r) rest c := by
  have hc := steps_trap_head (by simpa using hrun) hend
  exact ⟨_, steps_to_trap s f ws r, fun _ => trap_stuck, .inr (.inl ⟨rfl, hc⟩)⟩

theorem seqSplit_throw {s : Store H} {f : Frame} {ws : List Val} {x : Nat} {r rest : List Admin}
    {c : Config H} (hrun : Steps P host ⟨s, f, vals ws ++ throwing x ++ r ++ rest⟩ c)
    (hend : ∀ c', ¬ Step P host c c') : SeqSplit P host s f (vals ws ++ throwing x ++ r) rest c := by
  have hc := steps_throw_head (r := r ++ rest) (by simpa using hrun) hend
  exact ⟨_, steps_to_throw s f ws x r, fun _ => throw_stuck, .inr (.inr (.inl ⟨x, rfl, hc⟩))⟩

/-- **Splitting a run of a sequence.** A run of `es ++ rest` to a stuck
configuration first runs `es` alone to a stuck `c₁`. Then either `c₁` is values
`ws` and the run continues from `ws ++ rest`; or `c₁` is `[trap]` or
`throwing x` and the run ends there (it only bubbles past `rest`); or `c₁` is
stuck on another head and so is `c₁.code ++ rest`. -/
theorem steps_seq_split {s : Store H} {f : Frame} {es rest : List Admin} {c : Config H}
    (hrun : Steps P host ⟨s, f, es ++ rest⟩ c) (hend : ∀ c', ¬ Step P host c c') :
    SeqSplit P host s f es rest c := by
  suffices key : ∀ y, Steps P host y c → ∀ s f es, y = ⟨s, f, es ++ rest⟩ →
      SeqSplit P host s f es rest c from key _ hrun s f es rfl
  intro y hy
  induction hy using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro s f es hy
    subst hy
    rcases head_cases es with ⟨ws, rfl⟩ | ⟨ws, r, rfl⟩ | ⟨ws, x, r, rfl⟩ | ⟨vs, a, r, rfl, -, -, -⟩
    · exact ⟨_, .refl, fun _ => Sim.Step.not_vals, .inl ⟨ws, rfl, .refl⟩⟩
    · exact seqSplit_trap .refl hend
    · exact seqSplit_throw .refl hend
    · refine ⟨_, .refl, fun c' hc' => ?_, .inr (.inr (.inr rfl))⟩
      rcases c' with ⟨s', f', es'⟩
      exact hend _ (Sim.Step.append_right hc' rest)
  | @head y b hstep hrest ih =>
    intro s f es hy
    subst hy
    rcases head_cases es with ⟨ws, rfl⟩ | ⟨ws, r, rfl⟩ | ⟨ws, x, r, rfl⟩ |
        ⟨vs, a, r, rfl, ha, hat, hax⟩
    · exact ⟨_, .refl, fun _ => Sim.Step.not_vals, .inl ⟨ws, rfl, .head hstep hrest⟩⟩
    · exact seqSplit_trap (.head hstep hrest) hend
    · exact seqSplit_throw (.head hstep hrest) hend
    rcases b with ⟨s', f', es'⟩
    have hstep' : Step P host ⟨s, f, vals vs ++ a :: (r ++ rest)⟩ ⟨s', f', es'⟩ := by
      simpa using hstep
    rcases Sim.Step.split_head ha hstep' with ⟨ws, us, is', rfl, hst, rfl⟩ |
        ⟨rfl, -⟩ | ⟨rfl, -, -, ws, us, x, r₁, r₂, rfl, -, -, -⟩
    · obtain ⟨c₁, h₁, hs₁, hk⟩ := ih s' f' (vals ws ++ is' ++ r) (by simp)
      have hst' := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) ws r hst
      exact ⟨c₁, .head (by simpa using hst') h₁, hs₁, hk⟩
    · exact absurd rfl hat
    · exact absurd ⟨rfl, by simp⟩ (hax (ws ++ us) x)

end Silmaril.Proofs.Wasm.Abstract.HostCall
