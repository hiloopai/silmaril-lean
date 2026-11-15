module

public import Silmaril.Proofs.Wasm.Abstract.HostCall.Split

/-!
# Splitting a divergent Core run (proofs)

The divergent analogues of `steps_seq_split`, any profile and host:

* `trap_not_diverges`, `throw_not_diverges`: a head trap or `throwing x` only bubbles,
  so it does not diverge;
* `diverges_seq_split`: an infinite run of `es ++ rest` diverges in `es` itself, or `es`
  first runs to values `ws` and the run of `vals ws ++ rest` diverges;
* `diverges_label_split`, `diverges_frame_split`: an infinite run of a `LABEL` or `FRAME`
  diverges inside it, or its body first runs to an exit form (`LabelExit`, `FrameExit`)
  and the run of what it exits to diverges.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostCall

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- A head trap does not diverge. -/
theorem trap_not_diverges {s : Store H} {f : Frame} {ws : List Val} {r : List Admin} :
    ¬ Diverges P host ⟨s, f, vals ws ++ .trap :: r⟩ := by
  suffices key : ∀ n (ws : List Val) (r : List Admin), ws.length + r.length = n →
      ¬ Diverges P host ⟨s, f, vals ws ++ .trap :: r⟩ from key _ ws r rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ws r hn hd
    obtain ⟨b, hb, hd'⟩ := hd.unfold
    obtain ⟨ws', r', rfl, hlt⟩ := trap_step hb
    exact ih _ (hn ▸ hlt) ws' r' rfl hd'

/-- A head exception does not diverge. -/
theorem throw_not_diverges {s : Store H} {f : Frame} {ws : List Val} {x : Nat}
    {r : List Admin} : ¬ Diverges P host ⟨s, f, vals ws ++ throwing x ++ r⟩ := by
  suffices key : ∀ n (ws : List Val) (r : List Admin), ws.length + r.length = n →
      ¬ Diverges P host ⟨s, f, vals ws ++ throwing x ++ r⟩ from key _ ws r rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ws r hn hd
    obtain ⟨b, hb, hd'⟩ := hd.unfold
    obtain ⟨ws', r', rfl, hlt⟩ := throw_step hb
    exact ih _ (hn ▸ hlt) ws' r' rfl hd'

/-- `es` finishes as values and the continuation diverges. -/
def DivAfter (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (f : Frame) (es rest : List Admin) : Prop :=
  ∃ (c₁ : Config H) (ws : List Val), Steps P host ⟨s, f, es⟩ c₁ ∧ c₁.code = vals ws ∧
    Diverges P host ⟨c₁.store, c₁.frame, vals ws ++ rest⟩

/-- **Splitting a divergent run of a sequence.** -/
theorem diverges_seq_split {s : Store H} {f : Frame} {es rest : List Admin}
    (h : Diverges P host ⟨s, f, es ++ rest⟩) :
    Diverges P host ⟨s, f, es⟩ ∨ DivAfter P host s f es rest := by
  classical
  by_cases hA : DivAfter P host s f es rest
  · exact .inr hA
  left
  refine Silmaril.InfiniteTrace.coinduct
    (fun c : Config H => Diverges P host ⟨c.store, c.frame, c.code ++ rest⟩ ∧
      ¬ DivAfter P host c.store c.frame c.code rest) ?_ (a := ⟨s, f, es⟩) ⟨h, hA⟩
  rintro ⟨s, f, es⟩ ⟨hd, hna⟩
  dsimp only at hd hna
  obtain ⟨⟨s', f', es'⟩, hb, hd'⟩ := hd.unfold
  rcases head_cases es with ⟨ws, rfl⟩ | ⟨ws, r, rfl⟩ | ⟨ws, x, r, rfl⟩ |
      ⟨vs, a, r, rfl, ha, hat, hax⟩
  · exact (hna ⟨_, ws, .refl, rfl, hd⟩).elim
  · exact (trap_not_diverges (P := P) (host := host) (r := r ++ rest) (by simpa using hd)).elim
  · exact (throw_not_diverges (P := P) (host := host) (r := r ++ rest) (by simpa using hd)).elim
  have hstep' : Step P host ⟨s, f, vals vs ++ a :: (r ++ rest)⟩ ⟨s', f', es'⟩ := by
    simpa using hb
  rcases Sim.Step.split_head ha hstep' with ⟨ws, us, is', rfl, hst, rfl⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -, -, ws, us, x, r₁, r₂, rfl, -, -, -⟩
  · have hst' := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) ws r hst
    refine ⟨⟨s', f', vals ws ++ is' ++ r⟩, by simpa using hst', ?_, ?_⟩
    · show Diverges P host ⟨s', f', vals ws ++ is' ++ r ++ rest⟩
      simpa [Diverges] using hd'
    · dsimp only
      rintro ⟨c₁, w, h₁, hc₁, hk⟩
      exact hna ⟨c₁, w, .head (by simpa using hst') h₁, hc₁, hk⟩
  · exact absurd rfl hat
  · exact absurd ⟨rfl, by simp⟩ (hax (ws ++ us) x)

/-- The label's body runs to an exit, and what it exits to diverges. -/
def DivLabelAfter (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (f : Frame) (k : Nat) (cont : List Instr) (is : List Admin) : Prop :=
  ∃ (c₁ : Config H) (out : List Admin), Steps P host ⟨s, f, is⟩ c₁ ∧
    LabelExit k cont c₁.code out ∧ Diverges P host ⟨c₁.store, c₁.frame, out⟩

/-- **Splitting a divergent run of a label.** -/
theorem diverges_label_split {s : Store H} {f : Frame} {k : Nat} {cont : List Instr}
    {is : List Admin} (h : Diverges P host ⟨s, f, [.label k cont is]⟩) :
    Diverges P host ⟨s, f, is⟩ ∨ DivLabelAfter P host s f k cont is := by
  classical
  by_cases hA : DivLabelAfter P host s f k cont is
  · exact .inr hA
  left
  refine Silmaril.InfiniteTrace.coinduct
    (fun c : Config H => Diverges P host ⟨c.store, c.frame, [.label k cont c.code]⟩ ∧
      ¬ DivLabelAfter P host c.store c.frame k cont c.code) ?_ (a := ⟨s, f, is⟩) ⟨h, hA⟩
  rintro ⟨s, f, is⟩ ⟨hd, hna⟩
  dsimp only at hd hna
  obtain ⟨b, hb, hd'⟩ := hd.unfold
  rcases Step.label_inv hb with ⟨s', f', is', hin, rfl⟩ | ⟨out, hex, rfl⟩
  · refine ⟨⟨s', f', is'⟩, hin, hd', ?_⟩
    dsimp only
    rintro ⟨c₁, out, h₁, hex, hk⟩
    exact hna ⟨c₁, out, .head hin h₁, hex, hk⟩
  · exact (hna ⟨⟨s, f, is⟩, out, .refl, hex, hd'⟩).elim

/-- The frame's body runs to an exit, and what it exits to diverges (in the outer frame). -/
def DivFrameAfter (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (f F : Frame) (n : Nat) (is : List Admin) : Prop :=
  ∃ (c₁ : Config H) (out : List Admin), Steps P host ⟨s, F, is⟩ c₁ ∧
    FrameExit c₁.store c₁.frame n c₁.code out ∧ Diverges P host ⟨c₁.store, f, out⟩

/-- **Splitting a divergent run of a frame.** -/
theorem diverges_frame_split {s : Store H} {f F : Frame} {n : Nat} {is : List Admin}
    (h : Diverges P host ⟨s, f, [.frame n F is]⟩) :
    Diverges P host ⟨s, F, is⟩ ∨ DivFrameAfter P host s f F n is := by
  classical
  by_cases hA : DivFrameAfter P host s f F n is
  · exact .inr hA
  left
  refine Silmaril.InfiniteTrace.coinduct
    (fun c : Config H => Diverges P host ⟨c.store, f, [.frame n c.frame c.code]⟩ ∧
      ¬ DivFrameAfter P host c.store f c.frame n c.code) ?_ (a := ⟨s, F, is⟩) ⟨h, hA⟩
  rintro ⟨s, F, is⟩ ⟨hd, hna⟩
  dsimp only at hd hna
  obtain ⟨b, hb, hd'⟩ := hd.unfold
  rcases Step.frame_inv hb with ⟨s', F', is', hin, rfl⟩ | ⟨out, hex, rfl⟩
  · refine ⟨⟨s', F', is'⟩, hin, hd', ?_⟩
    dsimp only
    rintro ⟨c₁, out, h₁, hex, hk⟩
    exact hna ⟨c₁, out, .head hin h₁, hex, hk⟩
  · exact (hna ⟨⟨s, F, is⟩, out, .refl, hex, hd'⟩).elim

end Silmaril.Proofs.Wasm.Abstract.HostCall
