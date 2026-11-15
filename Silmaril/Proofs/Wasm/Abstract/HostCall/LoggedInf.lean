module

public import Silmaril.Proofs.Wasm.Abstract.HostCall.LoggedDiv
public import Silmaril.Games.Abstract.ModuleInf.Thms
public import Silmaril.Games.Abstract.HostRunInf.Defs

/-!
# Splitting a productive Core run (proofs)

The productive analogues of the splits of `EvDiv` (`LoggedDiv`), for `CoreInf`:

* `coreInf_silent`, `coreInf_cons`, `coreInf_prepend`: a finite labelled run in front of a
  productive run, its events in front of the stream (`Shape.streamAppend`);
* `coreInf_wrap_split`: the generic split. For an injective context `W`, a productive run of
  `W y₀` is a productive run of `y₀` itself, or `y₀` exits the context (as the hypothesis
  `hsplit` on finite runs says) after a prefix of the stream, and the rest of the run is
  productive. By classical choice: if it never exits, every segment of the run stays in the
  context (`hsplit` on the finite segment), and the inner configurations are determined by
  the outer ones (`W` injective), so they form one coherent inner run;
* `coreInf_seq_split`, `coreInf_label_seq_split`, `coreInf_frame_seq_split`: its instances
  for a sequence, a label and a call frame in place, from the finite splits of `Logged`;
* `coreInf_through_steps` (deterministic profile): through host-free steps;
* `coreInf_stuck`, `coreInf_trap`: a configuration with no step, or a head trap, has no
  productive run; `coreInf_host_call`: at a host call the first event answers it;
* `coreInf_not_quiet` (deterministic profile, typed): a productive run is not host-free
  divergence; `diverges_of_chain`: a chain of nonempty runs is divergence.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostCall

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded
open Shape (streamAppend)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Streams -/

theorem take_append_drop_stream {α : Type} (ω : Nat → α) (n : Nat) :
    streamTake ω n ++ω (fun k => ω (n + k)) = ω := by
  funext i
  by_cases hi : i < n
  · rw [Shape.streamAppend_lt (by simpa [streamTake] using hi)]
    simp [streamTake]
  · rw [Shape.streamAppend_ge (by simp [streamTake]; omega)]
    simp only [streamTake, List.length_ofFn]
    congr 1
    omega

theorem cons_drop_stream {α : Type} (ω : Nat → α) (n : Nat) :
    [ω n] ++ω (fun k => ω (n + 1 + k)) = fun k => ω (n + k) := by
  funext k
  rcases k with _ | k
  · rw [Shape.streamAppend_lt (by simp)]
    simp
  · rw [Shape.streamAppend_ge (by simp)]
    simp only [List.length_singleton]
    congr 1
    omega

theorem singleton_append_zero {α : Type} (e : α) (ω : Nat → α) : ([e] ++ω ω) 0 = e := by
  rw [Shape.streamAppend_lt (by simp)]
  simp

theorem singleton_append_succ {α : Type} (e : α) (ω : Nat → α) (n : Nat) :
    ([e] ++ω ω) (n + 1) = ω n := by
  rw [Shape.streamAppend_ge (by simp)]
  simp

/-! ## Silent runs -/

theorem silent_evRunN {x y : Config H}
    (h : Relation.ReflTransGen (fun a b => HEvStep P host a none b) x y) :
    ∃ k, EvRunN P host k x [] y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head hs _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, .silent hs hk⟩

theorem evRun_nil_silent {x y : Config H} (h : EvRun P host x [] y) :
    Relation.ReflTransGen (fun a b => HEvStep P host a none b) x y := by
  generalize hcs : ([] : List (Call (wasmHostSig H))) = cs at h
  induction h with
  | refl => exact .refl
  | silent hs _ ih => exact .head hs (ih hcs)
  | event _ _ _ => cases hcs

/-! ## Runs in front -/

/-- The tail of a productive run is productive. -/
theorem coreInf_tail {g : Nat → Config H} {ω : Nat → Call (wasmHostSig H)}
    (hg : ∀ n, ∃ c₁, Relation.ReflTransGen (fun a b => HEvStep P host a none b) (g n) c₁ ∧
      HEvStep P host c₁ (some (ω n)) (g (n + 1))) (n : Nat) :
    CoreInf P host (g n) (fun k => ω (n + k)) :=
  ⟨fun k => g (n + k), rfl, fun k => by simpa [Nat.add_assoc] using hg (n + k)⟩

theorem coreInf_silent {x y : Config H} {ω : Nat → Call (wasmHostSig H)}
    (hs : HEvStep P host x none y) (h : CoreInf P host y ω) : CoreInf P host x ω := by
  obtain ⟨g, hg0, hg⟩ := h
  refine ⟨fun n => match n with | 0 => x | n + 1 => g (n + 1), rfl, fun n => ?_⟩
  rcases n with _ | n
  · obtain ⟨c₁, hr, he⟩ := hg 0
    rw [hg0] at hr
    exact ⟨c₁, .head hs hr, he⟩
  · exact hg (n + 1)

theorem coreInf_cons {x y : Config H} {e : Call (wasmHostSig H)} {ω : Nat → Call (wasmHostSig H)}
    (hs : HEvStep P host x (some e) y) (h : CoreInf P host y ω) :
    CoreInf P host x ([e] ++ω ω) := by
  obtain ⟨g, hg0, hg⟩ := h
  refine ⟨fun n => match n with | 0 => x | n + 1 => g n, rfl, fun n => ?_⟩
  rcases n with _ | n
  · refine ⟨x, .refl, ?_⟩
    rw [singleton_append_zero]
    show HEvStep P host x (some e) (g 0)
    rw [hg0]; exact hs
  · rw [singleton_append_succ]
    exact hg n

/-- **A finite labelled run in front of a productive run.** -/
theorem coreInf_prepend {x y : Config H} {cs : List (Call (wasmHostSig H))}
    {ω : Nat → Call (wasmHostSig H)} (hr : EvRun P host x cs y) (h : CoreInf P host y ω) :
    CoreInf P host x (cs ++ω ω) := by
  induction hr with
  | refl => rwa [Shape.streamAppend_nil]
  | silent hs _ ih => exact coreInf_silent hs (ih h)
  | @event _ _ _ e cs hs _ ih =>
    have := coreInf_cons hs (ih h)
    rwa [← Shape.streamAppend_append] at this

/-! ## The generic split -/

/-- **Splitting a productive run of a context.** `W` is an injective context; `hsplit` says
how a finite segment of a run of `W y` ending at a host call answered by `e` splits: it stays
inside, the inner configuration answering `e`; or the inner part exits (`Exit`, after the
events so far) and the context goes on to the answer. -/
theorem coreInf_wrap_split (W : Config H → Config H) (hW : ∀ y y', W y = W y' → y = y')
    (Exit : List (Call (wasmHostSig H)) → Config H → Prop) {y₀ : Config H}
    (hsplit : ∀ (y : Config H) (cs₀ : List (Call (wasmHostSig H))) (k : Nat) (c z : Config H)
      (e : Call (wasmHostSig H)), EvRun P host y₀ cs₀ y → EvRunN P host k (W y) [] c →
      HEvStep P host c (some e) z →
      (∃ x y', EvRun P host y [] x ∧ HEvStep P host x (some e) y' ∧ z = W y') ∨
        ∃ d, Exit cs₀ d ∧ EvRun P host d [e] z)
    {ω : Nat → Call (wasmHostSig H)} (h : CoreInf P host (W y₀) ω) :
    CoreInf P host y₀ ω ∨
      ∃ (cs₁ : List (Call (wasmHostSig H))) (ω₂ : Nat → Call (wasmHostSig H)) (d : Config H),
        ω = cs₁ ++ω ω₂ ∧ Exit cs₁ d ∧ CoreInf P host d ω₂ := by
  classical
  by_cases hB : ∃ (cs₁ : List (Call (wasmHostSig H))) (ω₂ : Nat → Call (wasmHostSig H))
      (d : Config H), ω = cs₁ ++ω ω₂ ∧ Exit cs₁ d ∧ CoreInf P host d ω₂
  · exact .inr hB
  left
  obtain ⟨g, hg0, hg⟩ := h
  have step : ∀ n y, g n = W y → EvRun P host y₀ (streamTake ω n) y →
      ∃ x y', EvRun P host y [] x ∧ HEvStep P host x (some (ω n)) y' ∧ g (n + 1) = W y' := by
    intro n y hy hr
    obtain ⟨c₁, hs, he⟩ := hg n
    obtain ⟨k, hk⟩ := silent_evRunN (hy ▸ hs)
    rcases hsplit y _ k c₁ _ _ hr hk he with h | ⟨d, hx, hd⟩
    · exact h
    · refine (hB ⟨streamTake ω n, fun k => ω (n + k), d, (take_append_drop_stream ω n).symm,
        hx, ?_⟩).elim
      rw [← cons_drop_stream]
      exact coreInf_prepend hd (coreInf_tail hg (n + 1))
  have inv : ∀ n, ∃ y, g n = W y ∧ EvRun P host y₀ (streamTake ω n) y := by
    intro n
    induction n with
    | zero => exact ⟨y₀, hg0, by simpa [streamTake] using EvRun.refl (P := P) (host := host) y₀⟩
    | succ n ih =>
      obtain ⟨y, hy, hr⟩ := ih
      obtain ⟨x, y', hx, he, hy'⟩ := step n y hy hr
      refine ⟨y', hy', ?_⟩
      have := evRun_trans hr (evRun_trans hx (.event he (.refl _)))
      rwa [streamTake, List.ofFn_succ_last]
  choose g' hg' hr' using inv
  refine ⟨g', hW _ _ ((hg' 0).symm.trans hg0), fun n => ?_⟩
  obtain ⟨x, y', hx, he, hy'⟩ := step n (g' n) (hg' n) (hr' n)
  obtain rfl := hW _ _ ((hg' (n + 1)).symm.trans hy')
  exact ⟨x, evRun_nil_silent hx, he⟩

/-- An event is at a host call. -/
theorem decompose_of_event {c c' : Config H} {e : Call (wasmHostSig H)}
    (h : HEvStep P host c (some e) c') : (decompose? c.store c.code).isSome := by
  obtain ⟨E, a, hd, -⟩ := h
  rw [hd]; rfl

/-! ## Sequences, labels and call frames -/

/-- **Splitting a productive run of a sequence**: `es` runs productively itself, or first
runs to values with a prefix of the stream, and the continuation runs productively. -/
theorem coreInf_seq_split {s : Store H} {f : Frame} {es rest : List Admin}
    {ω : Nat → Call (wasmHostSig H)} (h : CoreInf P host ⟨s, f, es ++ rest⟩ ω) :
    CoreInf P host ⟨s, f, es⟩ ω ∨
      ∃ (cs₁ : List (Call (wasmHostSig H))) (ω₂ : Nat → Call (wasmHostSig H)) (c₁ : Config H)
        (n₁ : Nat) (ws : List Val), ω = cs₁ ++ω ω₂ ∧ EvRunN P host n₁ ⟨s, f, es⟩ cs₁ c₁ ∧
        c₁.code = vals ws ∧ CoreInf P host ⟨c₁.store, c₁.frame, vals ws ++ rest⟩ ω₂ := by
  have hW : ∀ y y' : Config H, (⟨y.store, y.frame, y.code ++ rest⟩ : Config H) =
      ⟨y'.store, y'.frame, y'.code ++ rest⟩ → y = y' := by
    rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
    simp only [Config.mk.injEq, List.append_cancel_right_eq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  refine (coreInf_wrap_split (P := P) (host := host)
      (fun y => ⟨y.store, y.frame, y.code ++ rest⟩) hW
      (fun cs₁ d => ∃ (c₁ : Config H) (n₁ : Nat) (ws : List Val),
        EvRunN P host n₁ ⟨s, f, es⟩ cs₁ c₁ ∧ c₁.code = vals ws ∧
          d = ⟨c₁.store, c₁.frame, vals ws ++ rest⟩) (y₀ := ⟨s, f, es⟩) ?_ h).imp id ?_
  swap
  · rintro ⟨cs₁, ω₂, d, hω, ⟨c₁, n₁, ws, h₁, hw, rfl⟩, hd⟩
    exact ⟨cs₁, ω₂, c₁, n₁, ws, hω, h₁, hw, hd⟩
  intro y cs₀ k c z e hr hk he
  have hexit : ∀ (c₁ : Config H) (ws : List Val), EvRun P host y [] c₁ → c₁.code = vals ws →
      EvRun P host ⟨c₁.store, c₁.frame, vals ws ++ rest⟩ [e] z →
      ∃ d, (∃ (c₁ : Config H) (n₁ : Nat) (ws : List Val),
        EvRunN P host n₁ ⟨s, f, es⟩ cs₀ c₁ ∧ c₁.code = vals ws ∧
          d = ⟨c₁.store, c₁.frame, vals ws ++ rest⟩) ∧ EvRun P host d [e] z := by
    intro c₁ ws h₁ hw hk
    obtain ⟨n₁, hn₁⟩ := evRunN_of_evRun (by simpa using evRun_trans hr h₁)
    exact ⟨_, ⟨c₁, n₁, ws, hn₁, hw, rfl⟩, hk⟩
  obtain ⟨c₁', n₁, cs₁, cs₂, hcs, h₁, -, -, hcase⟩ := evRunN_seq_split hk (noFree_of_event he)
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hcs.symm
  rcases hcase with ⟨ws, hw, hrest⟩ | ⟨htr, rfl, -⟩ | ⟨x, hth, rfl, -⟩ | ⟨rfl, -⟩
  · exact .inr (hexit c₁' ws h₁.evRun hw (by simpa using evRun_trans hrest.evRun (.event he (.refl _))))
  · exfalso
    have hd := decompose_of_event he
    rw [htr, show [Admin.trap] = vals [] ++ Admin.trap :: [] by simp [vals],
      decompose?_trap_head] at hd
    cases hd
  · exfalso
    have hd := decompose_of_event he
    rw [hth, show throwing x = vals [] ++ throwing x ++ [] by simp [vals],
      decompose?_throw_head] at hd
    cases hd
  · obtain ⟨cs, cf, cc⟩ := c₁'
    dsimp only at h₁ he ⊢
    rcases head_cases cc with ⟨ws, rfl⟩ | ⟨ws, r, rfl⟩ | ⟨ws, x, r, rfl⟩ |
        ⟨vs, a, r, rfl, ha, hat, hax⟩
    · exact .inr (hexit _ ws h₁.evRun rfl (.event he (.refl _)))
    · exfalso
      have hd := decompose_of_event he
      rw [show vals ws ++ Admin.trap :: r ++ rest = vals ws ++ Admin.trap :: (r ++ rest) by simp,
        decompose?_trap_head] at hd
      cases hd
    · exfalso
      have hd := decompose_of_event he
      rw [show vals ws ++ throwing x ++ r ++ rest = vals ws ++ throwing x ++ (r ++ rest) by simp,
        decompose?_throw_head] at hd
      cases hd
    · obtain ⟨es', hb, he'⟩ := hEvStep_seq_inv ha hat hax (by simpa using he)
      exact .inl ⟨_, _, h₁.evRun, he', hb⟩

/-- **Splitting a productive run of a label in place**: the body runs productively, or runs
to a stuck end that is not at a host call with a prefix of the stream, and the label around
that end runs productively. -/
theorem coreInf_label_seq_split {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cont : List Instr} {b rest : List Admin} {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ ω) :
    CoreInf P host ⟨s, f, b⟩ ω ∨
      ∃ (cs₁ : List (Call (wasmHostSig H))) (ω₂ : Nat → Call (wasmHostSig H)) (cb : Config H)
        (N₁ : Nat), ω = cs₁ ++ω ω₂ ∧ EvRunN P host N₁ ⟨s, f, b⟩ cs₁ cb ∧
        (∀ c', ¬ Step P Det.noHost cb c') ∧ decompose? cb.store cb.code = none ∧
        CoreInf P host ⟨cb.store, cb.frame, vals ws ++ [.label n cont cb.code] ++ rest⟩ ω₂ := by
  have hW : ∀ y y' : Config H,
      (⟨y.store, y.frame, vals ws ++ [.label n cont y.code] ++ rest⟩ : Config H) =
        ⟨y'.store, y'.frame, vals ws ++ [.label n cont y'.code] ++ rest⟩ → y = y' := by
    rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
    simp only [Config.mk.injEq, List.append_cancel_right_eq, List.append_cancel_left_eq,
      List.cons.injEq, Admin.label.injEq, and_true, true_and] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  refine (coreInf_wrap_split (P := P) (host := host)
      (fun y => ⟨y.store, y.frame, vals ws ++ [.label n cont y.code] ++ rest⟩) hW
      (fun cs₁ d => ∃ (cb : Config H) (N₁ : Nat), EvRunN P host N₁ ⟨s, f, b⟩ cs₁ cb ∧
        (∀ c', ¬ Step P Det.noHost cb c') ∧ decompose? cb.store cb.code = none ∧
        d = ⟨cb.store, cb.frame, vals ws ++ [.label n cont cb.code] ++ rest⟩)
      (y₀ := ⟨s, f, b⟩) ?_ h).imp id ?_
  swap
  · rintro ⟨cs₁, ω₂, d, hω, ⟨cb, N₁, h₁, hs, hdc, rfl⟩, hd⟩
    exact ⟨cs₁, ω₂, cb, N₁, hω, h₁, hs, hdc, hd⟩
  intro y cs₀ k c z e hr hk he
  obtain ⟨cb, N₁, cs₁, cs₂, hcs, -, hb, hsb, hk', hx⟩ :=
    evRunN_label_seq_split hk (noFree_of_event he)
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hcs.symm
  cases hdc : decompose? cb.store cb.code with
  | none =>
    obtain ⟨N₂, hN₂⟩ := evRunN_of_evRun (by simpa using evRun_trans hr hb.evRun)
    exact .inr ⟨_, ⟨cb, N₂, hN₂, hsb, hdc, rfl⟩,
      by simpa using evRun_trans hk'.evRun (.event he (.refl _))⟩
  | some yy =>
    have hsome : (decompose? cb.store cb.code).isSome := by rw [hdc]; rfl
    obtain ⟨-, rfl⟩ := hx hsome
    obtain ⟨s', f', b', rfl, he'⟩ := hEvStep_label_inv hsome he
    exact .inl ⟨cb, ⟨s', f', b'⟩, hb.evRun, he', rfl⟩

/-- **Splitting a productive run of a call frame in place**: the callee body runs
productively, or runs to a stuck end that is not at a host call with a prefix of the stream,
and the frame and label around that end run productively. -/
theorem coreInf_frame_seq_split {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {b rest : List Admin} {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ ω) :
    CoreInf P host ⟨s, F, b⟩ ω ∨
      ∃ (cs₁ : List (Call (wasmHostSig H))) (ω₂ : Nat → Call (wasmHostSig H)) (cb : Config H)
        (N₁ : Nat), ω = cs₁ ++ω ω₂ ∧ EvRunN P host N₁ ⟨s, F, b⟩ cs₁ cb ∧
        (∀ c', ¬ Step P Det.noHost cb c') ∧ decompose? cb.store cb.code = none ∧
        CoreInf P host
          ⟨cb.store, f, vals ws ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩ ω₂ := by
  have hW : ∀ y y' : Config H,
      (⟨y.store, f, vals ws ++ [.frame n y.frame [.label n [] y.code]] ++ rest⟩ : Config H) =
        ⟨y'.store, f, vals ws ++ [.frame n y'.frame [.label n [] y'.code]] ++ rest⟩ →
        y = y' := by
    rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
    simp only [Config.mk.injEq, List.append_cancel_right_eq, List.append_cancel_left_eq,
      List.cons.injEq, Admin.frame.injEq, Admin.label.injEq, and_true, true_and] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  refine (coreInf_wrap_split (P := P) (host := host)
      (fun y => ⟨y.store, f, vals ws ++ [.frame n y.frame [.label n [] y.code]] ++ rest⟩) hW
      (fun cs₁ d => ∃ (cb : Config H) (N₁ : Nat), EvRunN P host N₁ ⟨s, F, b⟩ cs₁ cb ∧
        (∀ c', ¬ Step P Det.noHost cb c') ∧ decompose? cb.store cb.code = none ∧
        d = ⟨cb.store, f, vals ws ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩)
      (y₀ := ⟨s, F, b⟩) ?_ h).imp id ?_
  swap
  · rintro ⟨cs₁, ω₂, d, hω, ⟨cb, N₁, h₁, hs, hdc, rfl⟩, hd⟩
    exact ⟨cs₁, ω₂, cb, N₁, hω, h₁, hs, hdc, hd⟩
  intro y cs₀ k c z e hr hk he
  obtain ⟨cb, N₁, cs₁, cs₂, hcs, -, hb, hsb, hk', hx⟩ :=
    evRunN_frame_seq_split hk (noFree_of_event he)
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hcs.symm
  cases hdc : decompose? cb.store cb.code with
  | none =>
    obtain ⟨N₂, hN₂⟩ := evRunN_of_evRun (by simpa using evRun_trans hr hb.evRun)
    exact .inr ⟨_, ⟨cb, N₂, hN₂, hsb, hdc, rfl⟩,
      by simpa using evRun_trans hk'.evRun (.event he (.refl _))⟩
  | some yy =>
    have hsome : (decompose? cb.store cb.code).isSome := by rw [hdc]; rfl
    obtain ⟨-, rfl⟩ := hx hsome
    obtain ⟨s', F', b', rfl, he'⟩ := hEvStep_frame_inv hsome he
    exact .inl ⟨cb, ⟨s', F', b'⟩, hb.evRun, he', rfl⟩

/-! ## Host-free steps, stuck ends and host calls -/

/-- **Through host-free steps** (deterministic profile). -/
theorem coreInf_through_steps {o : GrowOracle} {K T : Config H}
    {ω : Nat → Call (wasmHostSig H)} (hpred : Relation.ReflTransGen (Det.DStep o) K T)
    (h : CoreInf (profile o) host K ω) : CoreInf (profile o) host T ω := by
  obtain ⟨g, hg0, hg⟩ := h
  obtain ⟨c₁, hs, he⟩ := hg 0
  obtain ⟨k, hk⟩ := silent_evRunN (hg0 ▸ hs)
  obtain ⟨m, -, hm⟩ := evRunN_through_steps hpred hk (noFree_of_event he)
  refine ⟨fun n => match n with | 0 => T | n + 1 => g (n + 1), rfl, fun n => ?_⟩
  rcases n with _ | n
  · exact ⟨c₁, evRun_nil_silent hm.evRun, he⟩
  · exact hg (n + 1)

/-- **A configuration with no step has no productive run.** -/
theorem coreInf_stuck {c : Config H} {ω : Nat → Call (wasmHostSig H)}
    (hX : ∀ c', ¬ Step P host c c') : ¬ CoreInf P host c ω := by
  rintro ⟨g, hg0, hg⟩
  obtain ⟨c₁, hs, he⟩ := hg 0
  rw [hg0] at hs
  rcases hs.cases_head with rfl | ⟨b, hb, -⟩
  · exact hX _ (hEvStep_step he)
  · exact hX _ (hEvStep_step hb)

/-- **A head trap has no productive run.** -/
theorem coreInf_trap {s : Store H} {f : Frame} {ws : List Val} {r : List Admin}
    {ω : Nat → Call (wasmHostSig H)} : ¬ CoreInf P host ⟨s, f, vals ws ++ .trap :: r⟩ ω := by
  rintro ⟨g, hg0, hg⟩
  obtain ⟨c₁, hs, he⟩ := hg 0
  obtain ⟨k, hk⟩ := silent_evRunN (hg0 ▸ hs)
  obtain ⟨rfl, -⟩ := evRunN_trap_head hk (noFree_of_event he)
  have hd := decompose_of_event he
  rw [show [Admin.trap] = vals [] ++ Admin.trap :: [] by simp [vals], decompose?_trap_head] at hd
  cases hd

/-- **At a host call** the first event answers it, and the run goes on productively from the
answer. -/
theorem coreInf_host_call {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H} {hh : H}
    {ps rs : Validation.Ty (.list .val)} {ws us : List Val} {rest : List Admin}
    {ω : Nat → Call (wasmHostSig H)}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (he : Validation.Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (h : CoreInf P host
      ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ ω) :
    ∃ s' r, ω 0 = ⟨(hh, s, us), (s', r)⟩ ∧ host hh s us (.returned s' r) ∧
      CoreInf P host ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ (fun k => ω (1 + k)) := by
  obtain ⟨g, hg0, hg⟩ := h
  obtain ⟨c₁, hs, he'⟩ := hg 0
  obtain ⟨k, hk⟩ := silent_evRunN (hg0 ▸ hs)
  have hk' := evRunN_append hk (.event he' (.refl _))
  rcases evRunN_host_call hf hcode he hn hk' with ⟨-, hcs⟩ | ⟨s', r, m, cs', -, hcs, hans, hrest⟩
  · simp at hcs
  · simp only [List.nil_append, List.cons.injEq] at hcs
    obtain ⟨h1, rfl⟩ := hcs
    refine ⟨s', r, h1, hans, ?_⟩
    simpa [Shape.streamAppend_nil] using coreInf_prepend hrest.evRun (coreInf_tail hg 1)

/-! ## Productive runs are not host-free divergence -/

/-- A chain of nonempty runs is an infinite run. -/
theorem diverges_of_chain {R : Config H → Config H → Prop} {x : Nat → Config H}
    (h : ∀ n, Relation.TransGen R (x n) (x (n + 1))) : Silmaril.InfiniteTrace R (x 0) := by
  refine Silmaril.InfiniteTrace.coinduct (fun c => ∃ n, Relation.TransGen R c (x (n + 1)))
    ?_ ⟨0, h 0⟩
  rintro c ⟨n, hc⟩
  obtain ⟨b, hb, hb'⟩ := Relation.TransGen.head'_iff.mp hc
  rcases hb'.cases_head with rfl | ⟨c', hc', hc''⟩
  · exact ⟨_, hb, n + 1, h (n + 1)⟩
  · exact ⟨b, hb, n, Relation.TransGen.head' hc' hc''⟩

theorem silent_dsteps {o : GrowOracle} {c c₁ : Config H}
    (hs : Relation.ReflTransGen (fun a b => HEvStep (profile o) host a none b) c c₁) :
    Relation.ReflTransGen (Det.DStep o) c c₁ := by
  induction hs with
  | refl => exact .refl
  | tail _ hst ih =>
    rcases hst with hst | ⟨rfl, -⟩
    · exact ih.tail hst
    · exact ih

/-- **A productive run is not host-free divergence** (deterministic profile, typed start). -/
theorem coreInf_not_quiet {o : GrowOracle} {c : Config H} {ω : Nat → Call (wasmHostSig H)}
    (ht : Sim.ContextTyped c) (hd : Diverges (profile o) Det.noHost c)
    (h : CoreInf (profile o) host c ω) : False := by
  obtain ⟨g, hg0, hg⟩ := h
  obtain ⟨c₁, hs, he⟩ := hg 0
  rw [hg0] at hs
  obtain ⟨b, hb, -⟩ := (diverges_through_steps (silent_dsteps hs) ht hd).unfold
  exact noFree_of_event he b hb

end Silmaril.Proofs.Wasm.Abstract.HostCall
