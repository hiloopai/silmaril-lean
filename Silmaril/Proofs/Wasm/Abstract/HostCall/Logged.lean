module

public import Silmaril.Proofs.Wasm.Abstract.HostCall.Events
public import Silmaril.Proofs.Wasm.Abstract.HostCall.Ctx
public import Silmaril.Proofs.Wasm.Abstract.HostCall.Runs
public import Silmaril.Proofs.Wasm.Abstract.HostCall.Through

/-!
# Splitting labelled Core runs, with their host events (proofs)

The run-level lemmas of the backward simulation (`Split`, `Runs`, `Ctx`, `Through`), restated
for **labelled** runs (`EvRunN`, the counted `EvRun`), with the host-event log split as a
concatenation. The end of a run is only required to have no *host-free* step: it may sit at a
host call the host could answer.

* `hEvStep_ctx`, `hEvStep_label`, `hEvStep_frame`: a labelled step lifts through a sequence
  context, a label and a frame with the **same label**; `hEvStep_transfer`: so a step read off
  an outer labelled step by a host-generic inversion has the outer step's label
  (`hEvStep_unique`).
* `evRunN_seq_split`, `evRunN_label_seq_split`, `evRunN_frame_seq_split`: the logged splits.
  When the inner part ends at a host call, the outer run ends there too, with no events left.
* `evRunN_through`, `evRunN_through_steps` (deterministic profile): a labelled run to an end
  with no host-free step passes through every host-free step, with the same log.
* `evRunN_host_call`: at a host call the run ends, or answers it as its next event.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostCall

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Counted labelled runs -/

theorem _root_.Silmaril.Wasm.Abstract.EvRunN.evRun {n : Nat} {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRunN P host n c cs c') : EvRun P host c cs c' := by
  induction h with
  | refl => exact .refl _
  | silent hs _ ih => exact .silent hs ih
  | event hs _ ih => exact .event hs ih

theorem evRunN_of_evRun {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRun P host c cs c') : ∃ n, EvRunN P host n c cs c' := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | silent hs _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .silent hs h⟩
  | event hs _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .event hs h⟩

theorem _root_.Silmaril.Wasm.Abstract.EvRunN.zero_eq {c c' : Config H}
    {cs : List (Call (wasmHostSig H))} (h : EvRunN P host 0 c cs c') : c' = c := by
  cases h; rfl

theorem _root_.Silmaril.Wasm.Abstract.EvRunN.steps {n : Nat} {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRunN P host n c cs c') : Steps P host c c' :=
  evRun_steps h.evRun

/-- A run of `m` labelled steps from a configuration with no step at all is empty. -/
theorem _root_.Silmaril.Wasm.Abstract.EvRunN.of_stuck {m : Nat} {X c : Config H} {cs : List (Call (wasmHostSig H))}
    (hX : ∀ c', ¬ Step P host X c') (h : EvRunN P host m X cs c) : c = X ∧ cs = [] := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | silent hs _ => exact (hX _ (hEvStep_step hs)).elim
  | event hs _ => exact (hX _ (hEvStep_step hs)).elim

/-- At a host call there is no host-free step. -/
theorem noFree_of_decompose {c c' : Config H} {x : Ctx × Nat × H × List Val}
    (hd : decompose? c.store c.code = some x) : ¬ Step P Det.noHost c c' := fun h => by
  rw [decompose?_none_of_noRedex (Step.noRedex h)] at hd
  cases hd

/-! ## Labelled steps in contexts -/

/-- **A labelled step lifts through a sequence context**, with the same label. -/
theorem hEvStep_ctx {s s' : Store H} {f f' : Frame} {es es' : List Admin}
    {l : Option (Call (wasmHostSig H))} (ws : List Val) (rest : List Admin)
    (h : HEvStep P host ⟨s, f, es⟩ l ⟨s', f', es'⟩) :
    HEvStep P host ⟨s, f, vals ws ++ es ++ rest⟩ l ⟨s', f', vals ws ++ es' ++ rest⟩ := by
  cases l with
  | none =>
    rcases h with h | ⟨hc, E, a, hh, us, hd, hdiv⟩
    · exact .inl (Silmaril.Wasm.Logic.Core.Step.ctx ws rest h)
    · simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      exact .inr ⟨rfl, E.wrap ws rest, a, hh, us, decompose?_wrap ws rest hd, hdiv⟩
  | some e =>
    obtain ⟨E, a, hd, hs, hans, hc⟩ := h
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨E.wrap ws rest, a, decompose?_wrap ws rest hd, hs, hans, by simp [Ctx.fill_wrap]⟩

theorem splitVals_single {d : Admin} (hd : d.val? = none) : splitVals [d] = ([], [d]) := by
  simpa [vals] using splitVals_vals_cons (vs := []) hd []

theorem decompose?_label_some {s : Store H} {n : Nat} {cont : List Instr} {b : List Admin}
    {E : Ctx} {a : Nat} {hh : H} {us : List Val} (hd : decompose? s b = some (E, a, hh, us)) :
    decompose? s [.label n cont b] = some (.label [] n cont E [], a, hh, us) := by
  rw [decompose?_of_split (splitVals_single rfl), decompHead_label, hd]
  rfl

theorem decompose?_frame_some {s : Store H} {n : Nat} {F : Frame} {b : List Admin}
    {E : Ctx} {a : Nat} {hh : H} {us : List Val} (hd : decompose? s b = some (E, a, hh, us)) :
    decompose? s [.frame n F b] = some (.frame [] n F E [], a, hh, us) := by
  rw [decompose?_of_split (splitVals_single rfl), decompHead_frame, hd]
  rfl

/-- **A labelled step lifts through a label**, with the same label. -/
theorem hEvStep_label {s s' : Store H} {f f' : Frame} {b b' : List Admin}
    {l : Option (Call (wasmHostSig H))} (n : Nat) (cont : List Instr)
    (h : HEvStep P host ⟨s, f, b⟩ l ⟨s', f', b'⟩) :
    HEvStep P host ⟨s, f, [.label n cont b]⟩ l ⟨s', f', [.label n cont b']⟩ := by
  cases l with
  | none =>
    rcases h with h | ⟨hc, E, a, hh, us, hd, hdiv⟩
    · exact .inl (Step.ctxtLabel h)
    · simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      exact .inr ⟨rfl, _, a, hh, us, decompose?_label_some hd, hdiv⟩
  | some e =>
    obtain ⟨E, a, hd, hs, hans, hc⟩ := h
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨_, a, decompose?_label_some hd, hs, hans, by simp [Ctx.fill, vals]⟩

/-- **A labelled step lifts through a frame**, with the same label. -/
theorem hEvStep_frame {s s' : Store H} {f F F' : Frame} {b b' : List Admin}
    {l : Option (Call (wasmHostSig H))} (n : Nat)
    (h : HEvStep P host ⟨s, F, b⟩ l ⟨s', F', b'⟩) :
    HEvStep P host ⟨s, f, [.frame n F b]⟩ l ⟨s', f, [.frame n F' b']⟩ := by
  cases l with
  | none =>
    rcases h with h | ⟨hc, E, a, hh, us, hd, hdiv⟩
    · exact .inl (Step.ctxtFrame h)
    · simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      exact .inr ⟨rfl, _, a, hh, us, decompose?_frame_some hd, hdiv⟩
  | some e =>
    obtain ⟨E, a, hd, hs, hans, hc⟩ := h
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨_, a, decompose?_frame_some hd, hs, hans, by simp [Ctx.fill, vals]⟩

/-- **Label transfer**: a step `I ⟶ I'` whose labelled steps all lift to the labelled outer
step `O ⟶ O'` has the outer step's label. -/
theorem hEvStep_transfer {I I' O O' : Config H} {l : Option (Call (wasmHostSig H))}
    (hO : HEvStep P host O l O') (hI : Step P host I I')
    (hlift : ∀ l', HEvStep P host I l' I' → HEvStep P host O l' O') : HEvStep P host I l I' := by
  obtain ⟨l', h'⟩ := step_hEvStep hI
  obtain rfl := hEvStep_unique (hlift l' h') hO
  exact h'

/-! ## Head traps and exceptions -/

theorem decompose?_trap_head {s : Store H} {ws : List Val} {r : List Admin} :
    decompose? s (vals ws ++ .trap :: r) = none :=
  decompose?_vals_cons_none rfl fun _ _ => rfl

theorem decompose?_throw_head {s : Store H} {ws : List Val} {x : Nat} {r : List Admin} :
    decompose? s (vals ws ++ throwing x ++ r) = none := by
  rw [throwing_code]
  exact decompose?_vals_cons_none rfl fun _ _ => decompHead_plain rfl

/-- **A head trap only bubbles**, with no host event. -/
theorem evRunN_trap_head {m : Nat} {s : Store H} {f : Frame} {ws : List Val} {r : List Admin}
    {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host m ⟨s, f, vals ws ++ .trap :: r⟩ cs c)
    (hend : ∀ c', ¬ Step P Det.noHost c c') : c = ⟨s, f, [.trap]⟩ ∧ cs = [] := by
  suffices key : ∀ m y cs, EvRunN P host m y cs c → ∀ ws r, y = ⟨s, f, vals ws ++ .trap :: r⟩ →
      c = ⟨s, f, [.trap]⟩ ∧ cs = [] from key _ _ _ hrun ws r rfl
  clear hrun
  intro m y cs hy
  induction hy with
  | refl =>
    intro ws r hy
    subst hy
    by_cases hne : ws ≠ [] ∨ r ≠ []
    · have hst := Step.trapInstrs (P := P) (host := Det.noHost) (s := s) (f := f) hne
      exact (hend _ (by simpa using hst)).elim
    · simp only [ne_eq, not_or, Decidable.not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      exact ⟨by simp [vals], rfl⟩
  | silent hs _ ih =>
    intro ws r hy
    subst hy
    obtain ⟨ws', r', rfl, -⟩ := trap_step (hEvStep_step hs)
    exact ih hend ws' r' rfl
  | event hs _ _ =>
    intro ws r hy
    subst hy
    obtain ⟨E, a, hd, -⟩ := hs
    rw [decompose?_trap_head] at hd
    cases hd

/-- **A head exception only bubbles**, with no host event. -/
theorem evRunN_throw_head {m : Nat} {s : Store H} {f : Frame} {ws : List Val} {x : Nat}
    {r : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host m ⟨s, f, vals ws ++ throwing x ++ r⟩ cs c)
    (hend : ∀ c', ¬ Step P Det.noHost c c') : c = ⟨s, f, throwing x⟩ ∧ cs = [] := by
  suffices key : ∀ m y cs, EvRunN P host m y cs c → ∀ ws r,
      y = ⟨s, f, vals ws ++ throwing x ++ r⟩ → c = ⟨s, f, throwing x⟩ ∧ cs = [] from
    key _ _ _ hrun ws r rfl
  clear hrun
  intro m y cs hy
  induction hy with
  | refl =>
    intro ws r hy
    subst hy
    by_cases hne : ws ≠ [] ∨ r ≠ []
    · exact (hend _ (Step.throwRefInstrs hne)).elim
    · simp only [ne_eq, not_or, Decidable.not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      exact ⟨by simp [vals], rfl⟩
  | silent hs _ ih =>
    intro ws r hy
    subst hy
    obtain ⟨ws', r', rfl, -⟩ := throw_step (hEvStep_step hs)
    exact ih hend ws' r' rfl
  | event hs _ _ =>
    intro ws r hy
    subst hy
    obtain ⟨E, a, hd, -⟩ := hs
    rw [decompose?_throw_head] at hd
    cases hd

/-! ## Splitting a labelled run of a sequence -/

/-- The conclusion of `evRunN_seq_split`. -/
def SeqSplitL (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (n : Nat)
    (s : Store H) (f : Frame) (es rest : List Admin) (cs : List (Call (wasmHostSig H)))
    (c : Config H) : Prop :=
  ∃ (c₁ : Config H) (n₁ : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))), cs = cs₁ ++ cs₂ ∧
    EvRunN P host n₁ ⟨s, f, es⟩ cs₁ c₁ ∧ n₁ ≤ n ∧ (∀ c', ¬ Step P Det.noHost c₁ c') ∧
    ((∃ ws, c₁.code = vals ws ∧
        EvRunN P host (n - n₁) ⟨c₁.store, c₁.frame, vals ws ++ rest⟩ cs₂ c) ∨
      (c₁.code = [.trap] ∧ c = c₁ ∧ cs₂ = []) ∨ (∃ x, c₁.code = throwing x ∧ c = c₁ ∧ cs₂ = []) ∨
      (c = ⟨c₁.store, c₁.frame, c₁.code ++ rest⟩ ∧ cs₂ = []))

theorem seqSplitL_trap {m : Nat} {s : Store H} {f : Frame} {ws : List Val} {r rest : List Admin}
    {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host m ⟨s, f, vals ws ++ .trap :: r ++ rest⟩ cs c)
    (hend : ∀ c', ¬ Step P Det.noHost c c') :
    SeqSplitL P host m s f (vals ws ++ .trap :: r) rest cs c := by
  obtain ⟨hc, rfl⟩ := evRunN_trap_head (by simpa using hrun) hend
  subst hc
  by_cases hne : ws ≠ [] ∨ r ≠ []
  · rcases m with _ | m
    · exfalso
      have h0 := hrun.zero_eq
      have hne' : ws ≠ [] ∨ r ++ rest ≠ [] := by
        rcases hne with h | h
        · exact .inl h
        · exact .inr (by simp [h])
      have hst := Step.trapInstrs (P := P) (host := Det.noHost) (s := s) (f := f) hne'
      apply hend _
      rw [h0]
      simpa using hst
    · have hst := Step.trapInstrs (P := P) (host := Det.noHost) (s := s) (f := f) hne
      exact ⟨_, 1, [], [], rfl, .silent (Or.inl (by simpa using hst)) (.refl _), by omega,
        fun _ => trap_stuck, .inr (.inl ⟨rfl, rfl, rfl⟩)⟩
  · simp only [ne_eq, not_or, Decidable.not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    exact ⟨_, 0, [], [], rfl, .refl _, by omega, fun _ => trap_stuck, .inr (.inl ⟨rfl, rfl, rfl⟩)⟩

theorem seqSplitL_throw {m : Nat} {s : Store H} {f : Frame} {ws : List Val} {x : Nat}
    {r rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host m ⟨s, f, vals ws ++ throwing x ++ r ++ rest⟩ cs c)
    (hend : ∀ c', ¬ Step P Det.noHost c c') :
    SeqSplitL P host m s f (vals ws ++ throwing x ++ r) rest cs c := by
  obtain ⟨hc, rfl⟩ := evRunN_throw_head (r := r ++ rest) (by simpa using hrun) hend
  subst hc
  by_cases hne : ws ≠ [] ∨ r ≠ []
  · rcases m with _ | m
    · exfalso
      have h0 := hrun.zero_eq
      have hne' : ws ≠ [] ∨ r ++ rest ≠ [] := by
        rcases hne with h | h
        · exact .inl h
        · exact .inr (by simp [h])
      have hst := Step.throwRefInstrs (P := P) (host := Det.noHost) (s := s) (f := f) (a := x) hne'
      apply hend _
      rw [h0]
      simpa using hst
    · exact ⟨_, 1, [], [], rfl, .silent (Or.inl (Step.throwRefInstrs hne)) (.refl _), by omega,
        fun _ => throw_stuck, .inr (.inr (.inl ⟨x, rfl, rfl, rfl⟩))⟩
  · simp only [ne_eq, not_or, Decidable.not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    have h0 : EvRunN P host 0 ⟨s, f, vals [] ++ throwing x ++ []⟩ [] ⟨s, f, throwing x⟩ := by
      simpa [vals] using EvRunN.refl (P := P) (host := host) ⟨s, f, throwing x⟩
    exact ⟨⟨s, f, throwing x⟩, 0, [], [], rfl, h0, by omega, fun _ => throw_stuck,
      .inr (.inr (.inl ⟨x, rfl, rfl, rfl⟩))⟩

/-- A labelled step of `vals vs ++ a :: (r ++ rest)`, with `a` a non-value head that is not a
trap or an exception, is a labelled step of `vals vs ++ a :: r` followed by `rest`. -/
theorem hEvStep_seq_inv {s : Store H} {f : Frame} {vs : List Val} {a : Admin}
    {r rest : List Admin} {l : Option (Call (wasmHostSig H))} {b : Config H}
    (ha : a.val? = none) (hat : a ≠ .trap)
    (hax : ∀ ws x, ¬ (a = .plain .throwRef ∧ vs = ws ++ [.ref (.exn x)]))
    (h : HEvStep P host ⟨s, f, vals vs ++ a :: (r ++ rest)⟩ l b) :
    ∃ es', b = ⟨b.store, b.frame, es' ++ rest⟩ ∧
      HEvStep P host ⟨s, f, vals vs ++ a :: r⟩ l ⟨b.store, b.frame, es'⟩ := by
  rcases b with ⟨s', f', es'⟩
  rcases Sim.Step.split_head ha (hEvStep_step h) with ⟨ws, us, is', rfl, hst, rfl⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -, -, ws, us, x, r₁, r₂, rfl, -, -, -⟩
  · refine ⟨vals ws ++ is' ++ r, by simp, ?_⟩
    have hst' := Silmaril.Wasm.Logic.Core.Step.ctx ws r hst
    have e₁ : vals (ws ++ us) ++ a :: r = vals ws ++ (vals us ++ [a]) ++ r := by simp
    rw [e₁]
    refine hEvStep_transfer h hst' fun l' h' => ?_
    have := hEvStep_ctx (P := P) (host := host) [] rest h'
    simpa using this
  · exact absurd rfl hat
  · exact absurd ⟨rfl, by simp⟩ (hax (ws ++ us) x)

/-- **Splitting a labelled run of a sequence.** -/
theorem evRunN_seq_split {n : Nat} {s : Store H} {f : Frame} {es rest : List Admin}
    {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host n ⟨s, f, es ++ rest⟩ cs c) (hend : ∀ c', ¬ Step P Det.noHost c c') :
    SeqSplitL P host n s f es rest cs c := by
  suffices key : ∀ n y cs, EvRunN P host n y cs c → ∀ s f es, y = ⟨s, f, es ++ rest⟩ →
      SeqSplitL P host n s f es rest cs c from key _ _ _ hrun s f es rfl
  clear hrun
  intro n y cs hy
  induction hy with
  | refl =>
    intro s f es hy
    subst hy
    rcases head_cases es with ⟨ws, rfl⟩ | ⟨ws, r, rfl⟩ | ⟨ws, x, r, rfl⟩ | ⟨vs, a, r, rfl, -, -, -⟩
    · exact ⟨_, 0, [], [], rfl, .refl _, le_refl _, fun _ => Sim.Step.not_vals,
        .inl ⟨ws, rfl, .refl _⟩⟩
    · exact seqSplitL_trap (.refl _) hend
    · exact seqSplitL_throw (.refl _) hend
    · refine ⟨_, 0, [], [], rfl, .refl _, le_refl _, fun c' hc' => ?_, .inr (.inr (.inr ⟨rfl, rfl⟩))⟩
      rcases c' with ⟨s', f', es'⟩
      exact hend _ (Sim.Step.append_right hc' rest)
  | @silent m y b c₃ cs hstep hrest ih =>
    intro s f es hy
    subst hy
    rcases head_cases es with ⟨ws, rfl⟩ | ⟨ws, r, rfl⟩ | ⟨ws, x, r, rfl⟩ |
        ⟨vs, a, r, rfl, ha, hat, hax⟩
    · exact ⟨_, 0, [], cs, rfl, .refl _, by omega, fun _ => Sim.Step.not_vals,
        .inl ⟨ws, rfl, .silent hstep hrest⟩⟩
    · exact seqSplitL_trap (.silent hstep hrest) hend
    · exact seqSplitL_throw (.silent hstep hrest) hend
    obtain ⟨es', hb, hst⟩ := hEvStep_seq_inv ha hat hax (by simpa using hstep)
    rcases b with ⟨s', f', esb⟩
    obtain ⟨c₁, n₁, cs₁, cs₂, rfl, h₁, hn₁, hs₁, hk⟩ := ih hend s' f' es' hb
    refine ⟨c₁, n₁ + 1, cs₁, cs₂, rfl, .silent hst h₁, by omega, hs₁, ?_⟩
    rwa [Nat.add_sub_add_right]
  | @event m y b c₃ e cs hstep hrest ih =>
    intro s f es hy
    subst hy
    rcases head_cases es with ⟨ws, rfl⟩ | ⟨ws, r, rfl⟩ | ⟨ws, x, r, rfl⟩ |
        ⟨vs, a, r, rfl, ha, hat, hax⟩
    · exact ⟨_, 0, [], e :: cs, rfl, .refl _, by omega, fun _ => Sim.Step.not_vals,
        .inl ⟨ws, rfl, .event hstep hrest⟩⟩
    · exact seqSplitL_trap (.event hstep hrest) hend
    · exact seqSplitL_throw (.event hstep hrest) hend
    obtain ⟨es', hb, hst⟩ := hEvStep_seq_inv ha hat hax (by simpa using hstep)
    rcases b with ⟨s', f', esb⟩
    obtain ⟨c₁, n₁, cs₁, cs₂, rfl, h₁, hn₁, hs₁, hk⟩ := ih hend s' f' es' hb
    refine ⟨c₁, n₁ + 1, e :: cs₁, cs₂, rfl, .event hst h₁, by omega, hs₁, ?_⟩
    rwa [Nat.add_sub_add_right]

/-! ## Splitting a labelled run in a label or a call frame -/

/-- A label exit form is not at a host call. -/
theorem decompose?_labelExit {s : Store H} {n : Nat} {cont : List Instr} {b out : List Admin}
    (h : LabelExit n cont b out) : decompose? s b = none := by
  cases h with
  | vals vs => exact decompose?_vals_nil
  | @brZero vs' vs l rest _ _ =>
    have e : vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest =
        vals (vs' ++ vs) ++ .plain (.br l) :: rest := by simp
    rw [e]; exact decompose?_vals_cons_none rfl fun _ _ => decompHead_plain rfl
  | @brSucc vs l rest _ =>
    have e : vals vs ++ [.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by simp
    rw [e]; exact decompose?_vals_cons_none rfl fun _ _ => decompHead_plain rfl
  | @ret vs rest =>
    have e : vals vs ++ [.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by simp
    rw [e]; exact decompose?_vals_cons_none rfl fun _ _ => decompHead_plain rfl
  | @returnCall vs c' rest hc =>
    have e : vals vs ++ [c'] ++ rest = vals vs ++ c' :: rest := by simp
    rw [e]
    exact decompose?_vals_cons_none (SingleThreaded.val?_returnCallRef hc)
      fun _ _ => decompHead_returnCallRef hc
  | throw a => simpa using decompose?_throw_head (s := s) (ws := []) (x := a) (r := [])
  | trap => simpa [vals] using decompose?_trap_head (s := s) (ws := []) (r := [])

/-- The conclusion of `evRunN_label_seq_split`. -/
def LabelSeqSplitL (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (N : Nat)
    (s : Store H) (f : Frame) (ws : List Val) (n : Nat) (cont : List Instr) (b rest : List Admin)
    (cs : List (Call (wasmHostSig H))) (c : Config H) : Prop :=
  ∃ (cb : Config H) (N₁ : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))), cs = cs₁ ++ cs₂ ∧
    N₁ ≤ N ∧ EvRunN P host N₁ ⟨s, f, b⟩ cs₁ cb ∧ (∀ c', ¬ Step P Det.noHost cb c') ∧
    EvRunN P host (N - N₁) ⟨cb.store, cb.frame, vals ws ++ [.label n cont cb.code] ++ rest⟩ cs₂ c ∧
    ((decompose? cb.store cb.code).isSome →
      cs₂ = [] ∧ c = ⟨cb.store, cb.frame, vals ws ++ [.label n cont cb.code] ++ rest⟩)

/-- A run from a label whose body has no step and is at a host call is empty. -/
theorem evRunN_label_stuck {N : Nat} {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cont : List Instr} {b rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hb : ¬ ∃ c', Step P host ⟨s, f, b⟩ c') (hd : (decompose? s b).isSome)
    (h : EvRunN P host N ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ cs c) :
    cs = [] ∧ c = ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ := by
  suffices hX : ∀ c', ¬ Step P host ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ c' by
    obtain ⟨h₁, h₂⟩ := EvRunN.of_stuck hX h
    exact ⟨h₂, h₁⟩
  intro c' hc'
  obtain ⟨c₀, h₀, -⟩ := Step.ctx_in_seq (X := .label n cont b) trivial (by simpa using hc')
  rcases Step.label_inv h₀ with ⟨s', f', b', hin, -⟩ | ⟨out, hex, -⟩
  · exact hb ⟨_, hin⟩
  · rw [decompose?_labelExit hex] at hd
    cases hd

/-- **A labelled run in a label**: the body runs alone; then the label around it goes on. -/
theorem evRunN_label_seq_split {N : Nat} {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cont : List Instr} {b rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host N ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ cs c)
    (hend : ∀ c', ¬ Step P Det.noHost c c') :
    LabelSeqSplitL P host N s f ws n cont b rest cs c := by
  suffices key : ∀ N y cs, EvRunN P host N y cs c → ∀ s f b,
      y = ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ →
      LabelSeqSplitL P host N s f ws n cont b rest cs c
    from key _ _ _ hrun s f b rfl
  clear hrun
  have hstop : ∀ N s f b cs, ¬ (∃ c', Step P host ⟨s, f, b⟩ c') →
      EvRunN P host N ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ cs c →
      LabelSeqSplitL P host N s f ws n cont b rest cs c := by
    intro N s f b cs hb h
    refine ⟨⟨s, f, b⟩, 0, [], cs, rfl, by omega, .refl _,
      fun c' h' => hb ⟨c', Step.of_noHost host h'⟩, h, fun hd => ?_⟩
    exact evRunN_label_stuck hb hd h
  intro N y cs hy
  induction hy with
  | refl =>
    intro s f b hy
    subst hy
    refine ⟨⟨s, f, b⟩, 0, [], [], rfl, le_refl _, .refl _, fun c' h => ?_, .refl _,
      fun _ => ⟨rfl, rfl⟩⟩
    rcases c' with ⟨s', f', b'⟩
    exact hend _ (Silmaril.Wasm.Logic.Core.Step.ctx ws rest (Step.ctxtLabel h))
  | @silent N y z c₃ cs hstep hrest ih =>
    intro s f b hy
    subst hy
    by_cases hb : ∃ c', Step P host ⟨s, f, b⟩ c'
    · obtain ⟨c₀, h₀, hz⟩ := Step.ctx_in_seq (X := .label n cont b) trivial
        (by simpa using hEvStep_step hstep)
      rcases Step.label_inv h₀ with ⟨s', f', b', hin, rfl⟩ | ⟨out, hex, -⟩
      · have hin' : HEvStep P host ⟨s, f, b⟩ none ⟨s', f', b'⟩ :=
          hEvStep_transfer hstep hin fun l' h' => by
            simpa [hz] using hEvStep_ctx ws rest (hEvStep_label n cont h')
        obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, h₁, hs₁, hk, hx⟩ := ih hend hstop s' f' b' (by simp [hz])
        refine ⟨cb, N₁ + 1, cs₁, cs₂, rfl, by omega, .silent hin' h₁, hs₁, ?_, hx⟩
        rwa [show N + 1 - (N₁ + 1) = N - N₁ by omega]
      · obtain ⟨c', hc'⟩ := hb
        exact (labelExit_stuck (P := P) (host := host) (s := s) (f := f) hex c' hc').elim
    · exact hstop _ s f b cs hb (.silent hstep hrest)
  | @event N y z c₃ e cs hstep hrest ih =>
    intro s f b hy
    subst hy
    by_cases hb : ∃ c', Step P host ⟨s, f, b⟩ c'
    · obtain ⟨c₀, h₀, hz⟩ := Step.ctx_in_seq (X := .label n cont b) trivial
        (by simpa using hEvStep_step hstep)
      rcases Step.label_inv h₀ with ⟨s', f', b', hin, rfl⟩ | ⟨out, hex, -⟩
      · have hin' : HEvStep P host ⟨s, f, b⟩ (some e) ⟨s', f', b'⟩ :=
          hEvStep_transfer hstep hin fun l' h' => by
            simpa [hz] using hEvStep_ctx ws rest (hEvStep_label n cont h')
        obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, h₁, hs₁, hk, hx⟩ := ih hend hstop s' f' b' (by simp [hz])
        refine ⟨cb, N₁ + 1, e :: cs₁, cs₂, rfl, by omega, .event hin' h₁, hs₁, ?_, hx⟩
        rwa [show N + 1 - (N₁ + 1) = N - N₁ by omega]
      · obtain ⟨c', hc'⟩ := hb
        exact (labelExit_stuck (P := P) (host := host) (s := s) (f := f) hex c' hc').elim
    · exact hstop _ s f b _ hb (.event hstep hrest)

/-- The conclusion of `evRunN_frame_seq_split`. -/
def FrameSeqSplitL (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) (N : Nat)
    (s : Store H) (f F : Frame) (ws : List Val) (n : Nat) (b rest : List Admin)
    (cs : List (Call (wasmHostSig H))) (c : Config H) : Prop :=
  ∃ (cb : Config H) (N₁ : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))), cs = cs₁ ++ cs₂ ∧
    N₁ ≤ N ∧ EvRunN P host N₁ ⟨s, F, b⟩ cs₁ cb ∧ (∀ c', ¬ Step P Det.noHost cb c') ∧
    EvRunN P host (N - N₁)
      ⟨cb.store, f, vals ws ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩ cs₂ c ∧
    ((decompose? cb.store cb.code).isSome →
      cs₂ = [] ∧ c = ⟨cb.store, f, vals ws ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩)

/-- A run from a call frame whose body has no step and is at a host call is empty. -/
theorem evRunN_frame_stuck {N : Nat} {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {b rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hb : ¬ ∃ c', Step P host ⟨s, F, b⟩ c') (hd : (decompose? s b).isSome)
    (h : EvRunN P host N ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ cs c) :
    cs = [] ∧ c = ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ := by
  suffices hX : ∀ c', ¬ Step P host ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ c' by
    obtain ⟨h₁, h₂⟩ := EvRunN.of_stuck hX h
    exact ⟨h₂, h₁⟩
  intro c' hc'
  obtain ⟨c₀, h₀, -⟩ := Step.ctx_in_seq (X := .frame n F [.label n [] b]) trivial
    (by simpa using hc')
  rcases Step.frame_inv h₀ with ⟨s', F', is', hin, -⟩ | ⟨out, hex, -⟩
  · rcases Step.label_inv hin with ⟨s'', F'', b', hin', -⟩ | ⟨out, hex, -⟩
    · exact hb ⟨_, hin'⟩
    · rw [decompose?_labelExit hex] at hd
      cases hd
  · exact frameExit_label hex rfl

/-- **A labelled run in a call frame**: the callee body runs alone, in its frame; then the
frame and label around it go on. -/
theorem evRunN_frame_seq_split {N : Nat} {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {b rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host N ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ cs c)
    (hend : ∀ c', ¬ Step P Det.noHost c c') :
    FrameSeqSplitL P host N s f F ws n b rest cs c := by
  suffices key : ∀ N y cs, EvRunN P host N y cs c → ∀ s F b,
      y = ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ →
      FrameSeqSplitL P host N s f F ws n b rest cs c
    from key _ _ _ hrun s F b rfl
  clear hrun
  have hstop : ∀ N s F b cs, ¬ (∃ c', Step P host ⟨s, F, b⟩ c') →
      EvRunN P host N ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ cs c →
      FrameSeqSplitL P host N s f F ws n b rest cs c := by
    intro N s F b cs hb h
    refine ⟨⟨s, F, b⟩, 0, [], cs, rfl, by omega, .refl _,
      fun c' h' => hb ⟨c', Step.of_noHost host h'⟩, h, fun hd => ?_⟩
    exact evRunN_frame_stuck hb hd h
  -- an outer step with a body step is that body step, with the same label
  have hinner : ∀ (s : Store H) (F : Frame) (b : List Admin) (z : Config H)
      (l : Option (Call (wasmHostSig H))),
      (∃ c', Step P host ⟨s, F, b⟩ c') →
      HEvStep P host ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ l z →
      ∃ s' F' b', z = ⟨s', f, vals ws ++ [.frame n F' [.label n [] b']] ++ rest⟩ ∧
        HEvStep P host ⟨s, F, b⟩ l ⟨s', F', b'⟩ := by
    intro s F b z l hb hstep
    obtain ⟨c₀, h₀, hz⟩ := Step.ctx_in_seq (X := .frame n F [.label n [] b]) trivial
      (by simpa using hEvStep_step hstep)
    rcases Step.frame_inv h₀ with ⟨s', F', is', hin, rfl⟩ | ⟨out, hex, -⟩
    · rcases Step.label_inv hin with ⟨s'', F'', b', hin', he⟩ | ⟨out, hex, -⟩
      · simp only [Config.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        refine ⟨s', F', b', by simp [hz], hEvStep_transfer hstep hin' fun l' h' => ?_⟩
        simpa [hz] using hEvStep_ctx ws rest (hEvStep_frame (f := f) n (hEvStep_label n [] h'))
      · obtain ⟨c', hc'⟩ := hb
        exact (labelExit_stuck (P := P) (host := host) (s := s) (f := F) hex c' hc').elim
    · exact (frameExit_label hex rfl).elim
  intro N y cs hy
  induction hy with
  | refl =>
    intro s F b hy
    subst hy
    refine ⟨⟨s, F, b⟩, 0, [], [], rfl, le_refl _, .refl _, fun c' h => ?_, .refl _,
      fun _ => ⟨rfl, rfl⟩⟩
    rcases c' with ⟨s', F', b'⟩
    exact hend _ (Silmaril.Wasm.Logic.Core.Step.ctx ws rest
      (Step.ctxtFrame (f := f) (Step.ctxtLabel h)))
  | @silent N y z c₃ cs hstep hrest ih =>
    intro s F b hy
    subst hy
    by_cases hb : ∃ c', Step P host ⟨s, F, b⟩ c'
    · obtain ⟨s', F', b', rfl, hin'⟩ := hinner s F b z none hb hstep
      obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, h₁, hs₁, hk, hx⟩ := ih hend hstop s' F' b' rfl
      refine ⟨cb, N₁ + 1, cs₁, cs₂, rfl, by omega, .silent hin' h₁, hs₁, ?_, hx⟩
      rwa [show N + 1 - (N₁ + 1) = N - N₁ by omega]
    · exact hstop _ s F b cs hb (.silent hstep hrest)
  | @event N y z c₃ e cs hstep hrest ih =>
    intro s F b hy
    subst hy
    by_cases hb : ∃ c', Step P host ⟨s, F, b⟩ c'
    · obtain ⟨s', F', b', rfl, hin'⟩ := hinner s F b z (some e) hb hstep
      obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, h₁, hs₁, hk, hx⟩ := ih hend hstop s' F' b' rfl
      refine ⟨cb, N₁ + 1, e :: cs₁, cs₂, rfl, by omega, .event hin' h₁, hs₁, ?_, hx⟩
      rwa [show N + 1 - (N₁ + 1) = N - N₁ by omega]
    · exact hstop _ s F b _ hb (.event hstep hrest)

/-! ## Passing through host-free steps -/

section Through

variable {o : GrowOracle}

/-- **A labelled run passes through every host-free step**, with the same log. -/
theorem evRunN_through {n : Nat} {K c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN (profile o) host n K cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c') {d : Config H} (hd : Det.DStep o K d) :
    ∃ m ≤ n, EvRunN (profile o) host m d cs c := by
  have hK : decompose? K.store K.code = none := decompose?_none_of_noRedex (Step.noRedex hd)
  induction hrun generalizing d with
  | refl => exact (hend d hd).elim
  | @silent n K c₁ c cs hs hrest ih =>
    rcases hs with h₁' | ⟨-, E, a, hh, us, hdc, -⟩
    · obtain ⟨z, hz₁, hz₂⟩ := Det.DStep.join' h₁' hd
      have hK₁ : ∀ {w : Config H}, Det.DStep o c₁ w → decompose? c₁.store c₁.code = none :=
        fun hw => decompose?_none_of_noRedex (Step.noRedex hw)
      rcases hz₁ with _ | hz₁
      · rcases hz₂ with _ | hz₂
        · exact ⟨n, Nat.le_succ n, hrest⟩
        · exact ⟨n + 1, le_refl _, .silent (Or.inl hz₂) hrest⟩
      · obtain ⟨m', hm', hz⟩ := ih hend hz₁ (hK₁ hz₁)
        rcases hz₂ with _ | hz₂
        · exact ⟨m', by omega, hz⟩
        · exact ⟨m' + 1, by omega, .silent (Or.inl hz₂) hz⟩
    · rw [hK] at hdc; cases hdc
  | event hs _ _ =>
    obtain ⟨E, a, hdc, -⟩ := hs
    rw [hK] at hdc; cases hdc

/-- **A labelled run passes through every host-free run**, with the same log. -/
theorem evRunN_through_steps {n : Nat} {K T c : Config H} {cs : List (Call (wasmHostSig H))}
    (hpred : Relation.ReflTransGen (Det.DStep o) K T) (hrun : EvRunN (profile o) host n K cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c') :
    ∃ m ≤ n, EvRunN (profile o) host m T cs c := by
  induction hpred generalizing n with
  | refl => exact ⟨n, le_refl _, hrun⟩
  | tail _ hstep ih =>
    obtain ⟨m, hm, h⟩ := ih hrun
    obtain ⟨m', hm', h'⟩ := evRunN_through h hend hstep
    exact ⟨m', by omega, h'⟩

end Through

/-- A labelled run from a configuration whose only step is a host-free step to `d` goes
through `d`, one step shorter, with the same log. -/
theorem evRunN_unique {n : Nat} {K d c : Config H} {cs : List (Call (wasmHostSig H))}
    (huniq : ∀ c₁, Step P host K c₁ → c₁ = d) (hK : Step P Det.noHost K d)
    (hrun : EvRunN P host n K cs c) (hend : ∀ c', ¬ Step P Det.noHost c c') :
    ∃ m, n = m + 1 ∧ EvRunN P host m d cs c := by
  cases hrun with
  | refl => exact (hend d hK).elim
  | @silent m _ c₁ _ _ h hrest =>
    obtain rfl := huniq c₁ (hEvStep_step h)
    exact ⟨m, rfl, hrest⟩
  | @event m _ c₁ _ e _ h hrest =>
    obtain rfl := huniq c₁ (hEvStep_step h)
    have := hEvStep_unique (P := P) (host := host) h (show HEvStep P host _ none _ from Or.inl hK)
    cases this

/-! ## At a host call -/

/-- **A labelled run at a host call** under values and before a continuation: it ends there
with no event, or its next event answers the call, and the rest of the run goes on from the
answer. -/
theorem evRunN_host_call {n : Nat} {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
    {hh : H} {ps rs : Validation.Ty (.list .val)} {ws us : List Val} {rest : List Admin}
    {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (he : Validation.Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hrun : EvRunN P host n
      ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ cs c) :
    (c = ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ ∧
        cs = []) ∨
      ∃ s' r m cs', m < n ∧ cs = ⟨(hh, s, us), (s', r)⟩ :: cs' ∧
        host hh s us (.returned s' r) ∧
        EvRunN P host m ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ cs' c := by
  have hd : decompose? s (vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest) =
      some (.top ws rest, a, hh, us) := by
    have := decompose?_wrap (s := s) ws rest
      (decompose?_redex (c := .callRefType fi.type) trivial hf he hn hcode)
    simpa [Ctx.wrap] using this
  suffices key : ∀ n y cs, EvRunN P host n y cs c →
      y = ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ →
      (c = y ∧ cs = []) ∨ ∃ s' r m cs', m < n ∧ cs = ⟨(hh, s, us), (s', r)⟩ :: cs' ∧
        host hh s us (.returned s' r) ∧
        EvRunN P host m ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ cs' c by
    rcases key _ _ _ hrun rfl with ⟨h₁, h₂⟩ | h
    · exact .inl ⟨h₁, h₂⟩
    · exact .inr h
  clear hrun
  intro n y cs hy
  induction hy with
  | refl => exact fun _ => .inl ⟨rfl, rfl⟩
  | @silent m y z c₃ cs hs hrest ih =>
    intro hy
    subst hy
    rcases hs with h | ⟨rfl, -⟩
    · exact (noFree_of_decompose hd h).elim
    · rcases ih rfl with ⟨rfl, rfl⟩ | ⟨s', r, m', cs', hm', rfl, hans, hk⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨s', r, m', cs', by omega, rfl, hans, hk⟩
  | @event m y z c₃ e cs hs hrest _ =>
    intro hy
    subst hy
    obtain ⟨⟨hh', s₀, us'⟩, ⟨s', r⟩⟩ := e
    obtain ⟨E, a', hd', hs₀, hans, rfl⟩ := hs
    dsimp only at hd' hs₀ hans
    rw [hd] at hd'
    simp only [Option.some.injEq, Prod.mk.injEq] at hd'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hd'
    subst hs₀
    exact .inr ⟨s', r, m, cs, by omega, rfl, hans, by simpa [Ctx.fill] using hrest⟩

end Silmaril.Proofs.Wasm.Abstract.HostCall
