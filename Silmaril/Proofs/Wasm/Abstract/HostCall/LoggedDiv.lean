module

public import Silmaril.Proofs.Wasm.Abstract.HostCall.Logged
public import Silmaril.Proofs.Wasm.Abstract.HostCall.Div

/-!
# Splitting a logged prefix followed by host-free divergence (proofs)

`EvDiv P host n c cs`: a labelled run from `c` with the events `cs`, then host-free
divergence, cut at its last event (`HostCall.Defs`). Cut there, the prefix ends at a host call,
which has no host-free step, so the splits of labelled runs (`Logged`) apply to it, and the
divergence after the last event is split by the splits of divergent runs (`Div`).

* `evDiv_of_evRun`: a labelled run followed by host-free divergence is `EvDiv`;
* `evDiv_seq_split`, `evDiv_label_seq_split`, `evDiv_frame_seq_split`: the part in front, the
  label body or the callee body diverges with the whole log; or it runs to a stuck end with a
  prefix of the log, and the continuation goes on with the rest;
* `evDiv_through_steps` (deterministic profile): through host-free steps, with the same log;
  `evDiv_unique`: through a unique host-free step, with a smaller measure when the log is not
  empty;
* `evDiv_host_call`: at a host call the next event answers it;
* `evDiv_stuck`, `evDiv_trap`: a stuck configuration or a head trap does not diverge.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostCall

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Bookkeeping -/

/-- A configuration with an answered host call has no host-free step. -/
theorem noFree_of_event {c c' : Config H} {e : Call (wasmHostSig H)}
    (h : HEvStep P host c (some e) c') : ∀ c'', ¬ Step P Det.noHost c c'' := by
  obtain ⟨E, a, hd, -⟩ := h
  exact fun c'' => noFree_of_decompose hd

theorem evRunN_append {k k' : Nat} {c c₁ c₂ : Config H} {cs₁ cs₂ : List (Call (wasmHostSig H))}
    (h₁ : EvRunN P host k c cs₁ c₁) (h₂ : EvRunN P host k' c₁ cs₂ c₂) :
    EvRunN P host (k + k') c (cs₁ ++ cs₂) c₂ := by
  induction h₁ with
  | refl => simpa using h₂
  | silent hs _ ih =>
    have := EvRunN.silent hs (ih h₂)
    rwa [show ∀ a b : Nat, a + 1 + b = a + b + 1 from fun a b => by omega]
  | event hs _ ih =>
    have := EvRunN.event hs (ih h₂)
    rw [show ∀ a b : Nat, a + 1 + b = a + b + 1 from fun a b => by omega]
    simpa using this

/-- A host-free run is a labelled run with no event. -/
theorem evRunN_of_closed {c c' : Config H} (h : Steps P (fun _ _ _ _ => False) c c') :
    ∃ k, EvRunN P host k c [] c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head hs _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, .silent (Or.inl hs) hk⟩

/-- A run to a host call, its answer, and a host-free run after it. -/
theorem evRunN_event_closed {k : Nat} {c c₀ c₁ c₂ : Config H}
    {cs : List (Call (wasmHostSig H))} {e : Call (wasmHostSig H)}
    (h : EvRunN P host k c cs c₀) (he : HEvStep P host c₀ (some e) c₁)
    (h₂ : Steps P (fun _ _ _ _ => False) c₁ c₂) : ∃ k', EvRunN P host k' c (cs ++ [e]) c₂ := by
  obtain ⟨k₂, hk₂⟩ := evRunN_of_closed (host := host) h₂
  exact ⟨_, evRunN_append h (.event he hk₂)⟩

theorem evDiv_mono {n n' : Nat} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hn : n ≤ n') (h : EvDiv P host n c cs) : EvDiv P host n' c cs := by
  rcases h with h | ⟨k, cs₀, e, c₀, c₁, hk, h⟩
  · exact .inl h
  · exact .inr ⟨k, cs₀, e, c₀, c₁, hk.trans hn, h⟩

/-- With no event, `EvDiv` is host-free divergence. -/
theorem evDiv_nil {n : Nat} {c : Config H} (h : EvDiv P host n c []) :
    Diverges P (fun _ _ _ _ => False) c := by
  rcases h with ⟨-, hd⟩ | ⟨k, cs₀, e, c₀, c₁, -, hcs, -⟩
  · exact hd
  · simp at hcs

/-- **A labelled run followed by host-free divergence** is `EvDiv`. -/
theorem evDiv_of_evRun {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRun P host c cs c') (hd : Diverges P (fun _ _ _ _ => False) c') :
    ∃ n, EvDiv P host n c cs := by
  induction h with
  | refl => exact ⟨0, .inl ⟨rfl, hd⟩⟩
  | @silent c₁ c₂ c₃ cs hs _ ih =>
    obtain ⟨n, h | ⟨k, cs₀, e, c₀, c₄, hk, rfl, hr, he, hd'⟩⟩ := ih hd
    · obtain ⟨rfl, hd₂⟩ := h
      refine ⟨0, .inl ⟨rfl, ?_⟩⟩
      rcases hs with hs | ⟨rfl, -⟩
      · exact hd₂.fold hs
      · exact hd₂
    · exact ⟨n + 1, .inr ⟨k + 1, cs₀, e, c₀, c₄, by omega, rfl, .silent hs hr, he, hd'⟩⟩
  | @event c₁ c₂ c₃ e cs hs _ ih =>
    obtain ⟨n, h | ⟨k, cs₀, e', c₀, c₄, hk, rfl, hr, he, hd'⟩⟩ := ih hd
    · obtain ⟨rfl, hd₂⟩ := h
      exact ⟨0, .inr ⟨0, [], e, c₁, c₂, le_refl _, rfl, .refl _, hs, hd₂⟩⟩
    · exact ⟨n + 1, .inr ⟨k + 1, e :: cs₀, e', c₀, c₄, by omega, rfl, .event hs hr, he, hd'⟩⟩

/-- **A configuration with no step does not diverge**, with or without events. -/
theorem evDiv_stuck {n : Nat} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hX : ∀ c', ¬ Step P host c c') : ¬ EvDiv P host n c cs := by
  rintro (⟨-, hd⟩ | ⟨k, cs₀, e, c₀, c₁, -, -, hr, he, -⟩)
  · obtain ⟨b, hb, -⟩ := hd.unfold
    exact hX b (Step.of_noHost host hb)
  · obtain ⟨rfl, -⟩ := EvRunN.of_stuck hX hr
    exact hX _ (hEvStep_step he)

/-- **A head trap does not diverge**, with or without events. -/
theorem evDiv_trap {n : Nat} {s : Store H} {f : Frame} {ws : List Val} {r : List Admin}
    {cs : List (Call (wasmHostSig H))} : ¬ EvDiv P host n ⟨s, f, vals ws ++ .trap :: r⟩ cs := by
  rintro (⟨-, hd⟩ | ⟨k, cs₀, e, c₀, c₁, -, -, hr, he, -⟩)
  · exact trap_not_diverges hd
  · obtain ⟨rfl, -⟩ := evRunN_trap_head hr (noFree_of_event he)
    obtain ⟨E, a, hd, -⟩ := he
    have : decompose? s (vals [] ++ Admin.trap :: []) = none := decompose?_trap_head
    simp [vals] at this
    rw [this] at hd
    cases hd

/-! ## Sequences -/

/-- **Splitting a sequence**: `es` diverges with the whole log, or runs to values with a
prefix of the log and the continuation goes on with the rest. -/
theorem evDiv_seq_split {n : Nat} {s : Store H} {f : Frame} {es rest : List Admin}
    {cs : List (Call (wasmHostSig H))} (h : EvDiv P host n ⟨s, f, es ++ rest⟩ cs) :
    EvDiv P host n ⟨s, f, es⟩ cs ∨
      ∃ (c₁ : Config H) (n₁ m : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))) (ws : List Val),
        cs = cs₁ ++ cs₂ ∧ m ≤ n ∧ EvRunN P host n₁ ⟨s, f, es⟩ cs₁ c₁ ∧ c₁.code = vals ws ∧
        EvDiv P host m ⟨c₁.store, c₁.frame, vals ws ++ rest⟩ cs₂ := by
  rcases h with ⟨rfl, hd⟩ | ⟨k, cs₀, e, c₀, c₁', hk, rfl, hr, he, hd⟩
  · rcases diverges_seq_split hd with hd' | ⟨c₁, ws, hst, hw, hd₁⟩
    · exact .inl (.inl ⟨rfl, hd'⟩)
    · obtain ⟨k, hk⟩ := evRunN_of_closed (host := host) hst
      exact .inr ⟨c₁, k, n, [], [], ws, rfl, le_refl _, hk, hw, .inl ⟨rfl, hd₁⟩⟩
  obtain ⟨c₁, n₁, cs₁, cs₂, rfl, h₁, hn₁, -, hcase⟩ := evRunN_seq_split hr (noFree_of_event he)
  rcases hcase with ⟨ws, hw, hrest⟩ | ⟨htr, hc0, -⟩ | ⟨x, hth, hc0, -⟩ | ⟨rfl, rfl⟩
  · exact .inr ⟨c₁, n₁, k - n₁, cs₁, cs₂ ++ [e], ws, by simp, by omega, h₁, hw,
      .inr ⟨k - n₁, cs₂, e, c₀, c₁', le_refl _, rfl, hrest, he, hd⟩⟩
  · exfalso
    rw [hc0] at he
    obtain ⟨E, a, hdc, -⟩ := he
    have : decompose? c₁.store (vals [] ++ Admin.trap :: []) = none := decompose?_trap_head
    simp only [vals, List.map_nil, List.nil_append] at this
    rw [htr, this] at hdc
    cases hdc
  · exfalso
    rw [hc0] at he
    obtain ⟨E, a, hdc, -⟩ := he
    have : decompose? c₁.store (vals [] ++ throwing x ++ []) = none := decompose?_throw_head
    simp only [vals, List.map_nil, List.nil_append, List.append_nil] at this
    rw [hth, this] at hdc
    cases hdc
  · obtain ⟨cs₁s, cf, cc⟩ := c₁
    dsimp only at h₁ he hd ⊢
    rcases head_cases cc with ⟨ws, rfl⟩ | ⟨ws, r, rfl⟩ | ⟨ws, x, r, rfl⟩ |
        ⟨vs, a, r, rfl, ha, hat, hax⟩
    · exact .inr ⟨_, n₁, 0, cs₁, [e], ws, by simp, Nat.zero_le _, h₁, rfl,
        .inr ⟨0, [], e, _, c₁', le_refl _, rfl, .refl _, he, hd⟩⟩
    · exfalso
      obtain ⟨E, a, hdc, -⟩ := he
      rw [show vals ws ++ Admin.trap :: r ++ rest = vals ws ++ Admin.trap :: (r ++ rest) by simp,
        decompose?_trap_head] at hdc
      cases hdc
    · exfalso
      obtain ⟨E, a, hdc, -⟩ := he
      rw [show vals ws ++ throwing x ++ r ++ rest = vals ws ++ throwing x ++ (r ++ rest) by simp,
        decompose?_throw_head] at hdc
      cases hdc
    · obtain ⟨es', hb, he'⟩ := hEvStep_seq_inv ha hat hax (by simpa using he)
      rcases c₁' with ⟨s', f', esb⟩
      dsimp only at hb he'
      simp only [Config.mk.injEq, true_and] at hb
      subst hb
      rcases diverges_seq_split hd with hd' | ⟨c₂, ws, hst, hw, hd₂⟩
      · exact .inl (.inr ⟨n₁, cs₁, e, _, _, hn₁.trans hk, by simp, h₁, he', hd'⟩)
      · obtain ⟨k', hk'⟩ := evRunN_event_closed h₁ he' hst
        exact .inr ⟨c₂, k', 0, cs₁ ++ [e], [], ws, by simp, Nat.zero_le _, hk', hw,
          .inl ⟨rfl, hd₂⟩⟩

/-! ## Labels and call frames -/

/-- A label around a body stuck at a host call has no step. -/
theorem label_stuck_of_decompose {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cont : List Instr} {b rest : List Admin} {host' : HostSemantics H}
    (hb : ∀ c', ¬ Step P host' ⟨s, f, b⟩ c') (hd : (decompose? s b).isSome) :
    ∀ c', ¬ Step P host' ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ c' := by
  intro c' hc'
  obtain ⟨c₀, h₀, -⟩ := Step.ctx_in_seq (X := .label n cont b) trivial (by simpa using hc')
  rcases Step.label_inv h₀ with ⟨s', f', b', hin, -⟩ | ⟨out, hex, -⟩
  · exact hb _ hin
  · rw [decompose?_labelExit hex] at hd
    cases hd

/-- A call frame around a body stuck at a host call has no step. -/
theorem frame_stuck_of_decompose {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {b rest : List Admin} {host' : HostSemantics H}
    (hb : ∀ c', ¬ Step P host' ⟨s, F, b⟩ c') (hd : (decompose? s b).isSome) :
    ∀ c', ¬ Step P host' ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ c' := by
  intro c' hc'
  obtain ⟨c₀, h₀, -⟩ := Step.ctx_in_seq (X := .frame n F [.label n [] b]) trivial
    (by simpa using hc')
  rcases Step.frame_inv h₀ with ⟨s', F', is', hin, -⟩ | ⟨out, hex, -⟩
  · rcases Step.label_inv hin with ⟨s'', F'', b', hin', -⟩ | ⟨out, hex, -⟩
    · exact hb _ hin'
    · rw [decompose?_labelExit hex] at hd
      cases hd
  · exact frameExit_label hex rfl

/-- An answered host call inside a label is the body's answered host call. -/
theorem hEvStep_label_inv {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cont : List Instr} {b rest : List Admin} {z : Config H} {e : Call (wasmHostSig H)}
    (hd : (decompose? s b).isSome)
    (h : HEvStep P host ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ (some e) z) :
    ∃ s' f' b', z = ⟨s', f', vals ws ++ [.label n cont b'] ++ rest⟩ ∧
      HEvStep P host ⟨s, f, b⟩ (some e) ⟨s', f', b'⟩ := by
  obtain ⟨c₀, h₀, hz⟩ := Step.ctx_in_seq (X := .label n cont b) trivial
    (by simpa using hEvStep_step h)
  rcases Step.label_inv h₀ with ⟨s', f', b', hin, rfl⟩ | ⟨out, hex, -⟩
  · refine ⟨s', f', b', by simp [hz], hEvStep_transfer h hin fun l' h' => ?_⟩
    simpa [hz] using hEvStep_ctx ws rest (hEvStep_label n cont h')
  · rw [decompose?_labelExit hex] at hd
    cases hd

/-- An answered host call inside a call frame is the body's answered host call. -/
theorem hEvStep_frame_inv {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {b rest : List Admin} {z : Config H} {e : Call (wasmHostSig H)}
    (hd : (decompose? s b).isSome)
    (h : HEvStep P host ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ (some e) z) :
    ∃ s' F' b', z = ⟨s', f, vals ws ++ [.frame n F' [.label n [] b']] ++ rest⟩ ∧
      HEvStep P host ⟨s, F, b⟩ (some e) ⟨s', F', b'⟩ := by
  obtain ⟨c₀, h₀, hz⟩ := Step.ctx_in_seq (X := .frame n F [.label n [] b]) trivial
    (by simpa using hEvStep_step h)
  rcases Step.frame_inv h₀ with ⟨s', F', is', hin, rfl⟩ | ⟨out, hex, -⟩
  · rcases Step.label_inv hin with ⟨s'', F'', b', hin', he⟩ | ⟨out, hex, -⟩
    · simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨s', F', b', by simp [hz], hEvStep_transfer h hin' fun l' h' => ?_⟩
      simpa [hz] using hEvStep_ctx ws rest (hEvStep_frame (f := f) n (hEvStep_label n [] h'))
    · rw [decompose?_labelExit hex] at hd
      cases hd
  · exact (frameExit_label hex rfl).elim

/-- **Splitting a label in place**: the body diverges with the whole log, or runs to a stuck
end that is not at a host call with a prefix of the log, and the label around that end goes
on with the rest. -/
theorem evDiv_label_seq_split {N : Nat} {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cont : List Instr} {b rest : List Admin} {cs : List (Call (wasmHostSig H))}
    (h : EvDiv P host N ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ cs) :
    EvDiv P host N ⟨s, f, b⟩ cs ∨
      ∃ (cb : Config H) (N₁ m : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))),
        cs = cs₁ ++ cs₂ ∧ m ≤ N ∧ EvRunN P host N₁ ⟨s, f, b⟩ cs₁ cb ∧
        (∀ c', ¬ Step P Det.noHost cb c') ∧ decompose? cb.store cb.code = none ∧
        EvDiv P host m ⟨cb.store, cb.frame, vals ws ++ [.label n cont cb.code] ++ rest⟩ cs₂ := by
  -- a host-free run of the body to a stuck end, the label around it diverging
  have hfree : ∀ (c : Config H) (cb : Config H) (k : Nat) (cs₁ : List (Call (wasmHostSig H))),
      EvRunN P host k ⟨s, f, b⟩ cs₁ cb → (∀ c', ¬ Step P (fun _ _ _ _ => False) cb c') →
      Diverges P (fun _ _ _ _ => False)
        ⟨cb.store, cb.frame, vals ws ++ [.label n cont cb.code] ++ rest⟩ →
      decompose? cb.store cb.code = none := by
    intro _ cb k cs₁ _ hs hd
    cases hdc : decompose? cb.store cb.code with
    | none => rfl
    | some x =>
      exfalso
      obtain ⟨b', hb', -⟩ := hd.unfold
      exact label_stuck_of_decompose (P := P) (ws := ws) (n := n) (cont := cont) (rest := rest)
        (s := cb.store) (f := cb.frame) hs (by rw [hdc]; rfl) b' hb'
  rcases h with ⟨rfl, hd⟩ | ⟨k, cs₀, e, c₀, c₁, hk, rfl, hr, he, hd⟩
  · rcases diverges_label_seq_split hd with hd' | ⟨cb, hst, hs, hd₁⟩
    · exact .inl (.inl ⟨rfl, hd'⟩)
    · obtain ⟨k, hk⟩ := evRunN_of_closed (host := host) hst
      exact .inr ⟨cb, k, N, [], [], rfl, le_refl _, hk, hs, hfree cb cb k [] hk hs hd₁,
        .inl ⟨rfl, hd₁⟩⟩
  obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, hb, hsb, hk', hx⟩ :=
    evRunN_label_seq_split hr (noFree_of_event he)
  cases hdc : decompose? cb.store cb.code with
  | none =>
    exact .inr ⟨cb, N₁, k - N₁, cs₁, cs₂ ++ [e], by simp, by omega, hb, hsb, hdc,
      .inr ⟨k - N₁, cs₂, e, c₀, c₁, le_refl _, rfl, hk', he, hd⟩⟩
  | some y =>
    have hsome : (decompose? cb.store cb.code).isSome := by rw [hdc]; rfl
    obtain ⟨rfl, rfl⟩ := hx hsome
    obtain ⟨s', f', b', rfl, he'⟩ := hEvStep_label_inv hsome he
    rcases diverges_label_seq_split hd with hd' | ⟨cb', hst, hs, hd₁⟩
    · exact .inl (.inr ⟨N₁, cs₁, e, cb, _, hN₁.trans hk, by simp, hb, he', hd'⟩)
    · obtain ⟨k', hk''⟩ := evRunN_event_closed hb he' hst
      exact .inr ⟨cb', k', 0, cs₁ ++ [e], [], by simp, Nat.zero_le _, hk'', hs,
        hfree cb' cb' k' _ hk'' hs hd₁, .inl ⟨rfl, hd₁⟩⟩

/-- **Splitting a call frame in place**: the callee body diverges with the whole log, or runs
to a stuck end that is not at a host call with a prefix of the log, and the frame and label
around that end go on with the rest. -/
theorem evDiv_frame_seq_split {N : Nat} {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {b rest : List Admin} {cs : List (Call (wasmHostSig H))}
    (h : EvDiv P host N ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ cs) :
    EvDiv P host N ⟨s, F, b⟩ cs ∨
      ∃ (cb : Config H) (N₁ m : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))),
        cs = cs₁ ++ cs₂ ∧ m ≤ N ∧ EvRunN P host N₁ ⟨s, F, b⟩ cs₁ cb ∧
        (∀ c', ¬ Step P Det.noHost cb c') ∧ decompose? cb.store cb.code = none ∧
        EvDiv P host m
          ⟨cb.store, f, vals ws ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩ cs₂ := by
  have hfree : ∀ (cb : Config H), (∀ c', ¬ Step P (fun _ _ _ _ => False) cb c') →
      Diverges P (fun _ _ _ _ => False)
        ⟨cb.store, f, vals ws ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩ →
      decompose? cb.store cb.code = none := by
    intro cb hs hd
    cases hdc : decompose? cb.store cb.code with
    | none => rfl
    | some x =>
      exfalso
      obtain ⟨b', hb', -⟩ := hd.unfold
      exact frame_stuck_of_decompose (P := P) (ws := ws) (n := n) (rest := rest)
        (s := cb.store) (f := f) (F := cb.frame) hs (by rw [hdc]; rfl) b' hb'
  rcases h with ⟨rfl, hd⟩ | ⟨k, cs₀, e, c₀, c₁, hk, rfl, hr, he, hd⟩
  · rcases diverges_frame_seq_split hd with hd' | ⟨cb, hst, hs, hd₁⟩
    · exact .inl (.inl ⟨rfl, hd'⟩)
    · obtain ⟨k, hk⟩ := evRunN_of_closed (host := host) hst
      exact .inr ⟨cb, k, N, [], [], rfl, le_refl _, hk, hs, hfree cb hs hd₁, .inl ⟨rfl, hd₁⟩⟩
  obtain ⟨cb, N₁, cs₁, cs₂, rfl, hN₁, hb, hsb, hk', hx⟩ :=
    evRunN_frame_seq_split hr (noFree_of_event he)
  cases hdc : decompose? cb.store cb.code with
  | none =>
    exact .inr ⟨cb, N₁, k - N₁, cs₁, cs₂ ++ [e], by simp, by omega, hb, hsb, hdc,
      .inr ⟨k - N₁, cs₂, e, c₀, c₁, le_refl _, rfl, hk', he, hd⟩⟩
  | some y =>
    have hsome : (decompose? cb.store cb.code).isSome := by rw [hdc]; rfl
    obtain ⟨rfl, rfl⟩ := hx hsome
    obtain ⟨s', F', b', rfl, he'⟩ := hEvStep_frame_inv hsome he
    rcases diverges_frame_seq_split hd with hd' | ⟨cb', hst, hs, hd₁⟩
    · exact .inl (.inr ⟨N₁, cs₁, e, cb, _, hN₁.trans hk, by simp, hb, he', hd'⟩)
    · obtain ⟨k', hk''⟩ := evRunN_event_closed hb he' hst
      exact .inr ⟨cb', k', 0, cs₁ ++ [e], [], by simp, Nat.zero_le _, hk'', hs,
        hfree cb' hs hd₁, .inl ⟨rfl, hd₁⟩⟩

/-! ## Host-free steps and host calls -/

/-- **Through host-free steps**, with the same log (deterministic profile, typed start). -/
theorem evDiv_through_steps {o : GrowOracle} {n : Nat} {K T : Config H}
    {cs : List (Call (wasmHostSig H))}
    (hpred : Relation.ReflTransGen (Det.DStep o) K T) (ht : Sim.ContextTyped K)
    (h : EvDiv (profile o) host n K cs) : EvDiv (profile o) host n T cs := by
  rcases h with ⟨rfl, hd⟩ | ⟨k, cs₀, e, c₀, c₁, hk, rfl, hr, he, hd⟩
  · exact .inl ⟨rfl, diverges_through_steps hpred ht hd⟩
  · obtain ⟨m, hm, h⟩ := evRunN_through_steps hpred hr (noFree_of_event he)
    exact .inr ⟨m, cs₀, e, c₀, c₁, hm.trans hk, rfl, h, he, hd⟩

/-- **Through a unique host-free step**, with a smaller measure, when there are events. -/
theorem evDiv_unique {n : Nat} {K d : Config H} {cs : List (Call (wasmHostSig H))}
    (huniq : ∀ c₁, Step P host K c₁ → c₁ = d) (hK : Step P Det.noHost K d) (hcs : cs ≠ [])
    (h : EvDiv P host n K cs) : ∃ m < n, EvDiv P host m d cs := by
  rcases h with ⟨rfl, -⟩ | ⟨k, cs₀, e, c₀, c₁, hk, rfl, hr, he, hd⟩
  · exact (hcs rfl).elim
  · obtain ⟨m, rfl, h⟩ := evRunN_unique huniq hK hr (noFree_of_event he)
    exact ⟨m, by omega, .inr ⟨m, cs₀, e, c₀, c₁, le_refl _, rfl, h, he, hd⟩⟩

/-- **At a host call** the next event answers it, and the run goes on from the answer. -/
theorem evDiv_host_call {n : Nat} {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
    {hh : H} {ps rs : Validation.Ty (.list .val)} {ws us : List Val} {rest : List Admin}
    {cs : List (Call (wasmHostSig H))}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (he : Validation.Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (h : EvDiv P host n
      ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ cs) :
    ∃ s' r cs', cs = ⟨(hh, s, us), (s', r)⟩ :: cs' ∧ host hh s us (.returned s' r) ∧
      EvDiv P host n ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ cs' := by
  rcases h with ⟨rfl, hd⟩ | ⟨k, cs₀, e, c₀, c₁, hk, rfl, hr, he', hd⟩
  · exfalso
    have hd' : Diverges P (fun _ _ _ _ => False)
        ⟨s, f, vals (ws ++ us) ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ := by
      simpa using hd
    obtain ⟨-, -, -, -, -, -, -, h | ⟨-, -, h, -⟩⟩ :=
      diverges_host_call (r := .callRefType fi.type) trivial hf hcode hd'
    · exact h
    · exact h
  rcases evRunN_host_call hf hcode he hn hr with ⟨rfl, rfl⟩ |
      ⟨s', r, m, cs', hm, rfl, hans, hk'⟩
  · have hdc : decompose? s
        (vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest) =
        some (.top ws rest, a, hh, us) := by
      have := decompose?_wrap (s := s) ws rest
        (decompose?_redex (c := .callRefType fi.type) trivial hf he hn hcode)
      simpa [Ctx.wrap] using this
    obtain ⟨⟨hh', s₀, us'⟩, ⟨s', r⟩⟩ := e
    obtain ⟨E, a', hd', hs₀, hans, rfl⟩ := he'
    dsimp only at hd' hs₀ hans
    rw [hdc] at hd'
    simp only [Option.some.injEq, Prod.mk.injEq] at hd'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hd'
    subst hs₀
    exact ⟨s', r, [], rfl, hans, .inl ⟨rfl, by simpa [Ctx.fill] using hd⟩⟩
  · exact ⟨s', r, cs' ++ [e], by simp, hans,
      .inr ⟨m, cs', e, c₀, c₁, by omega, rfl, hk', he', hd⟩⟩

end Silmaril.Proofs.Wasm.Abstract.HostCall
