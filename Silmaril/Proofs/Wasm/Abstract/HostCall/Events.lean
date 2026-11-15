module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Wasm.Execution.Core.Sim.ExitLift

/-!
# Host events of Core runs (proofs)

* `hEvStep_step`, `step_hEvStep`: labelled steps are exactly the Core steps;
* `hEvStep_unique`: **the label of a step is determined**: an event-free step is never an
  answered host call, and an answered host call determines its event. So no host event is
  ever dropped or invented;
* `diverges_events`: **a Core run diverges iff** it is quiescent after a finite run with
  host events `cs` (`EvRun`, `Quiet`), or productive with an infinite stream of host events
  (`CoreInf`). The witness is the run itself; no determinism is assumed. Any profile and host.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostCall

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Labelled steps -/

theorem hEvStep_step {c c' : Config H} {e : Option (Call (wasmHostSig H))}
    (h : HEvStep P host c e c') : Step P host c c' := by
  rcases c with ⟨s, f, code⟩
  cases e with
  | none =>
    rcases h with h | ⟨rfl, E, a, hh, us, hd, hdiv⟩
    · exact Step.of_noHost host h
    · obtain ⟨fi, yy, ps, rs, hf, hcode, hyy, he, hn, hc⟩ := decompose?_sound hd
      dsimp only at hc ⊢
      rw [hc]
      exact Ctx.step_fill E (fun _ => Step.callRefHostDiv hyy hf he hn hcode hdiv) f
  | some e =>
    obtain ⟨⟨hh, s₀, us⟩, ⟨s', r⟩⟩ := e
    obtain ⟨E, a, hd, -, hans, rfl⟩ := h
    obtain ⟨fi, yy, ps, rs, hf, hcode, hyy, he, hn, hc⟩ := decompose?_sound hd
    dsimp only at hc hans ⊢
    rw [hc]
    exact Ctx.step_fill E (fun _ => Step.callRefHost hyy hf he hn hcode hans) f

theorem step_hEvStep {c c' : Config H} (h : Step P host c c') :
    ∃ e, HEvStep P host c e c' := by
  rcases Step.split_host h with h | ⟨E, a, hh, args, hd, ⟨s', r, hans, rfl⟩ | ⟨hdiv, rfl⟩⟩
  · exact ⟨none, .inl h⟩
  · exact ⟨some ⟨(hh, c.store, args), (s', r)⟩, E, a, hd, rfl, hans, rfl⟩
  · exact ⟨none, .inr ⟨rfl, E, a, hh, args, hd, hdiv⟩⟩

/-- `Ctx.fill` is injective in its hole. -/
theorem Ctx.fill_inj (E : Ctx) {xs ys : List Admin} (h : E.fill xs = E.fill ys) : xs = ys := by
  induction E with
  | top pre rest =>
    simp only [Ctx.fill, List.append_assoc, List.append_cancel_left_eq] at h
    exact List.append_cancel_right h
  | label pre n cont E rest ih =>
    simp only [Ctx.fill, List.append_assoc, List.append_cancel_left_eq, List.singleton_append,
      List.cons.injEq, Admin.label.injEq] at h
    exact ih h.1.2.2
  | handler pre n cs E rest ih =>
    simp only [Ctx.fill, List.append_assoc, List.append_cancel_left_eq, List.singleton_append,
      List.cons.injEq, Admin.handler.injEq] at h
    exact ih h.1.2.2
  | frame pre n f E rest ih =>
    simp only [Ctx.fill, List.append_assoc, List.append_cancel_left_eq, List.singleton_append,
      List.cons.injEq, Admin.frame.injEq] at h
    exact ih h.1.2.2

theorem not_mem_vals {x : Admin} (hx : x.val? = none) (ws : List Val) : x ∉ vals ws := by
  intro hm
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hm
  simp at hx

/-- A host result is never the redex it answers. -/
theorem toAdmin_ne_redex (r : Result) (us : List Val) (a : Nat) {yy : Admin}
    (hyy : yy.IsCallRef) : r.toAdmin ≠ vals us ++ [.ref (.func a), yy] := by
  intro h
  have hv : yy.val? = none := Admin.val?_of_IsCallRef hyy
  cases r with
  | values ws =>
    have hm : yy ∈ vals ws := by simp only [Result.toAdmin] at h; rw [h]; simp
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hm
    simp at hv
  | trap =>
    have := congrArg List.length h
    simp [Result.toAdmin] at this
  | throw t =>
    have hl := congrArg List.length h
    simp only [Result.toAdmin, List.length_cons, List.length_nil, List.length_append, vals,
      List.length_map] at hl
    obtain rfl : us = [] := List.length_eq_zero_iff.mp (by omega)
    simp [Result.toAdmin, vals] at h

/-- **The label of a step is determined.** -/
theorem hEvStep_unique {c c' : Config H} {e e' : Option (Call (wasmHostSig H))}
    (h : HEvStep P host c e c') (h' : HEvStep P host c e' c') : e = e' := by
  -- an answered call is not event-free
  have key : ∀ {e : Call (wasmHostSig H)}, HEvStep P host c (some e) c' →
      ¬ HEvStep P host c none c' := by
    intro e hs hn
    obtain ⟨E, a, hd, -, -, rfl⟩ := hs
    rcases hn with hn | ⟨hc, -⟩
    · have := decompose?_none_of_noRedex (Step.noRedex hn)
      rw [this] at hd; cases hd
    · obtain ⟨fi, yy, ps, rs, -, -, hyy, -, -, hcode⟩ := decompose?_sound hd
      have hcc := congrArg Config.code hc
      dsimp only at hcc
      rw [hcode] at hcc
      exact toAdmin_ne_redex e.2.2 _ a hyy (Ctx.fill_inj E hcc)
  cases e with
  | none =>
    cases e' with
    | none => rfl
    | some e' => exact (key h' h).elim
  | some e =>
    cases e' with
    | none => exact (key h h').elim
    | some e' =>
      obtain ⟨⟨hh, s₀, us⟩, ⟨s', r⟩⟩ := e
      obtain ⟨⟨hh', s₀', us'⟩, ⟨s'', r'⟩⟩ := e'
      obtain ⟨E, a, hd, hs₀, -, hc⟩ := h
      obtain ⟨E', a', hd', hs₀', -, hc'⟩ := h'
      dsimp only at hd hd' hs₀ hs₀' hc hc'
      rw [hd] at hd'
      simp only [Option.some.injEq, Prod.mk.injEq] at hd'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hd'
      subst hs₀ hs₀'
      rw [hc] at hc'
      simp only [Config.mk.injEq] at hc'
      obtain ⟨rfl, -, hr⟩ := hc'
      have hr' := Ctx.fill_inj E hr
      have hT : ∀ ws : List Val, vals ws ≠ [.trap] := fun ws h =>
        not_mem_vals (x := .trap) rfl ws (by rw [h]; simp)
      have hX : ∀ (ws : List Val) (t : Nat), vals ws ≠ [.ref (.exn t), .plain .throwRef] :=
        fun ws t h => not_mem_vals (x := .plain .throwRef) rfl ws (by rw [h]; simp)
      cases r <;> cases r' <;> simp only [Result.toAdmin] at hr'
      · rw [Sim.vals_injective hr']
      · exact (hX _ _ hr').elim
      · exact (hT _ hr').elim
      · exact (hX _ _ hr'.symm).elim
      · simp only [List.cons.injEq, Admin.ref.injEq, Ref.exn.injEq] at hr'
        rw [hr'.1]
      · simp at hr'
      · exact (hT _ hr'.symm).elim
      · simp at hr'
      · rfl

/-! ## Divergence by host events -/

theorem evRun_steps {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRun P host c cs c') : Steps P host c c' := by
  induction h with
  | refl => exact .refl
  | silent hs _ ih => exact .head (hEvStep_step hs) ih
  | event hs _ ih => exact .head (hEvStep_step hs) ih

theorem evRun_of_silent {c c' c'' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : Relation.ReflTransGen (fun a b => HEvStep P host a none b) c c')
    (hk : EvRun P host c' cs c'') : EvRun P host c cs c'' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hk
  | head hs _ ih => exact .silent hs ih

theorem quiet_diverges {c : Config H} (h : Quiet P host c) : Diverges P host c :=
  Silmaril.InfiniteTrace.map (R := fun a b => HEvStep P host a none b) id
    (fun _ _ hs => hEvStep_step hs) h

theorem coreInf_diverges {c : Config H} {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host c ω) : Diverges P host c := by
  refine Silmaril.InfiniteTrace.coinduct (fun c => ∃ ω, CoreInf P host c ω) ?_ ⟨ω, h⟩
  rintro c ⟨ω, g, hg0, hg⟩
  obtain ⟨c₁, hr, he⟩ := hg 0
  rw [hg0] at hr
  rcases hr.cases_head with rfl | ⟨b, hb, hr'⟩
  · refine ⟨g 1, hEvStep_step he, fun n => ω (n + 1), fun n => g (n + 1), rfl, fun n => hg (n + 1)⟩
  · refine ⟨b, hEvStep_step hb, ω, fun n => Nat.casesOn n b fun m => g (m + 1), rfl, ?_⟩
    intro n
    cases n with
    | zero => exact ⟨c₁, hr', he⟩
    | succ m => exact hg (m + 1)

/-- One productive segment: from a divergent configuration that is never quiescent after a
finite run, event-free steps lead to a host event, after which the same holds. -/
theorem next_event {c : Config H} (hd : Diverges P host c)
    (hn : ¬ ∃ cs c', EvRun P host c cs c' ∧ Quiet P host c') :
    ∃ c₁ e c₂, Relation.ReflTransGen (fun a b => HEvStep P host a none b) c c₁ ∧
      HEvStep P host c₁ (some e) c₂ ∧ Diverges P host c₂ ∧
      ¬ ∃ cs c', EvRun P host c₂ cs c' ∧ Quiet P host c' := by
  classical
  obtain ⟨t, ht0, ht⟩ := hd
  by_cases hE : ∃ n, ∃ e, HEvStep P host (t n) (some e) (t (n + 1))
  · let n := Nat.find hE
    obtain ⟨e, he⟩ := Nat.find_spec hE
    have hsil : ∀ m < n, HEvStep P host (t m) none (t (m + 1)) := by
      intro m hm
      obtain ⟨e', he'⟩ := step_hEvStep (ht m)
      cases e' with
      | none => exact he'
      | some e' => exact absurd ⟨e', he'⟩ (Nat.find_min hE hm)
    have hrt : ∀ m ≤ n, Relation.ReflTransGen (fun a b => HEvStep P host a none b) (t 0) (t m) := by
      intro m
      induction m with
      | zero => exact fun _ => .refl
      | succ m ih => exact fun hm => (ih (by omega)).tail (hsil m (by omega))
    refine ⟨t n, e, t (n + 1), ht0 ▸ hrt n le_rfl, he, ⟨fun k => t (n + 1 + k), rfl,
      fun k => by simpa [Nat.add_assoc] using ht (n + 1 + k)⟩, ?_⟩
    rintro ⟨cs, c', hr, hq⟩
    exact hn ⟨e :: cs, c', evRun_of_silent (ht0 ▸ hrt n le_rfl) (.event he hr), hq⟩
  · refine (hn ⟨[], c, .refl c, t, ht0, fun n => ?_⟩).elim
    obtain ⟨e', he'⟩ := step_hEvStep (ht n)
    cases e' with
    | none => exact he'
    | some e' => exact (hE ⟨n, e', he'⟩).elim

/-- **Divergence by host events**: a Core run diverges iff it is quiescent after a finite
run with host events `cs`, or productive with an infinite stream of host events. -/
theorem diverges_events {c : Config H} :
    Diverges P host c ↔
      (∃ cs c', EvRun P host c cs c' ∧ Quiet P host c') ∨ ∃ ω, CoreInf P host c ω := by
  constructor
  · intro hd
    classical
    by_cases hq : ∃ cs c', EvRun P host c cs c' ∧ Quiet P host c'
    · exact .inl hq
    right
    let S := {x : Config H // Diverges P host x ∧ ¬ ∃ cs c', EvRun P host x cs c' ∧ Quiet P host c'}
    have step : ∀ x : S, ∃ (y : S) (e : Call (wasmHostSig H)) (c₁ : Config H),
        Relation.ReflTransGen (fun a b => HEvStep P host a none b) x.1 c₁ ∧
          HEvStep P host c₁ (some e) y.1 := by
      rintro ⟨x, hx, hnx⟩
      obtain ⟨c₁, e, c₂, hr, he, hd₂, hn₂⟩ := next_event hx hnx
      exact ⟨⟨c₂, hd₂, hn₂⟩, e, c₁, hr, he⟩
    choose nx ev mid hmid using step
    let G : Nat → S := fun n => Nat.rec ⟨c, hd, hq⟩ (fun _ y => nx y) n
    exact ⟨fun n => ev (G n), fun n => (G n).1, rfl, fun n => ⟨mid (G n), hmid (G n)⟩⟩
  · rintro (⟨cs, c', hr, hq⟩ | ⟨ω, h⟩)
    · exact Silmaril.InfiniteTrace.of_steps (evRun_steps hr) (quiet_diverges hq)
    · exact coreInf_diverges h

/-! ## Prefixes and consistency -/

theorem evRun_trans {c₁ c₂ c₃ : Config H} {cs cs' : List (Call (wasmHostSig H))}
    (h : EvRun P host c₁ cs c₂) (h' : EvRun P host c₂ cs' c₃) : EvRun P host c₁ (cs ++ cs') c₃ := by
  induction h with
  | refl => exact h'
  | silent hs _ ih => exact .silent hs (ih h')
  | event hs _ ih => exact .event hs (ih h')

/-- The events of an answered step are allowed by the host. -/
theorem hEvStep_consistent {c c' : Config H} {e : Call (wasmHostSig H)}
    (h : HEvStep P host c (some e) c') : coreHostRel host e.1 (.answer e.2) := by
  obtain ⟨E, a, -, hs, hans, -⟩ := h
  simpa [coreHostRel, hs] using hans

/-- **The events of a finite labelled run are allowed by the host.** -/
theorem evRun_consistent {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRun P host c cs c') : (coreHostRel host).Consistent cs := by
  induction h with
  | refl => exact fun _ h => nomatch h
  | silent _ _ ih => exact ih
  | event hs _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hEvStep_consistent hs
    · exact ih x hx

/-- **The events of a productive run are allowed by the host.** -/
theorem coreInf_consistent {c : Config H} {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host c ω) (n : Nat) : coreHostRel host (ω n).1 (.answer (ω n).2) := by
  obtain ⟨g, -, hg⟩ := h
  obtain ⟨_, -, he⟩ := hg n
  exact hEvStep_consistent he

/-- **Prefix agreement**: the first `n` events of a productive run are the events of a finite
labelled run of the same run, which continues productively with the remaining events. -/
theorem coreInf_prefix {c : Config H} {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host c ω) (n : Nat) :
    ∃ c', EvRun P host c (List.ofFn fun i : Fin n => ω i) c' ∧
      CoreInf P host c' (fun k => ω (n + k)) := by
  obtain ⟨g, hg0, hg⟩ := h
  have seg : ∀ m, EvRun P host (g m) [ω m] (g (m + 1)) := by
    intro m
    obtain ⟨c₁, hr, he⟩ := hg m
    exact evRun_of_silent hr (.event he (.refl _))
  refine ⟨g n, ?_, fun k => g (n + k), rfl, fun k => by simpa [Nat.add_assoc] using hg (n + k)⟩
  induction n with
  | zero => rw [← hg0]; exact .refl _
  | succ n ih =>
    rw [List.ofFn_succ_last]
    exact evRun_trans ih (seg n)

/-! ## Quiescent divergence -/

/-- **Quiescent divergence is host-free divergence, or a host-free run to a host call the
host diverges on.** -/
theorem quiet_split {c : Config H} (h : Quiet P host c) :
    Diverges P (fun _ _ _ _ => False) c ∨
      ∃ d : Config H, Steps P (fun _ _ _ _ => False) c d ∧
        ∃ E a hh us, decompose? d.store d.code = some (E, a, hh, us) ∧
          host hh d.store us .diverged := by
  classical
  obtain ⟨t, ht0, ht⟩ := h
  by_cases hS : ∃ n, ¬ Step P (fun _ _ _ _ => False) (t n) (t (n + 1))
  · let n := Nat.find hS
    have hpre : ∀ m < n, Step P (fun _ _ _ _ => False) (t m) (t (m + 1)) := fun m hm =>
      not_not.mp (Nat.find_min hS hm)
    have hrun : ∀ m ≤ n, Steps P (fun _ _ _ _ => False) (t 0) (t m) := by
      intro m
      induction m with
      | zero => exact fun _ => .refl
      | succ m ih => exact fun hm => (ih (by omega)).tail (hpre m (by omega))
    rcases ht n with hs | ⟨-, E, a, hh, us, hd, hdiv⟩
    · exact absurd hs (Nat.find_spec hS)
    · exact .inr ⟨t n, ht0 ▸ hrun n le_rfl, E, a, hh, us, hd, hdiv⟩
  · refine .inl ⟨t, ht0, fun n => ?_⟩
    exact not_not.mp (not_exists.mp hS n)

theorem silent_of_noHost {c d : Config H} (hr : Steps P (fun _ _ _ _ => False) c d) :
    Relation.ReflTransGen (fun a b => HEvStep P host a none b) c d := by
  induction hr with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (.inl hs)

/-- The converse: host-free divergence, or a host-free run to a diverging host call, is
quiescent. -/
theorem quiet_of_split {c : Config H}
    (h : Diverges P (fun _ _ _ _ => False) c ∨
      ∃ d : Config H, Steps P (fun _ _ _ _ => False) c d ∧
        ∃ E a hh us, decompose? d.store d.code = some (E, a, hh, us) ∧
          host hh d.store us .diverged) : Quiet P host c := by
  rcases h with hd | ⟨d, hr, E, a, hh, us, hdc, hdiv⟩
  · exact Silmaril.InfiniteTrace.map (R := Step P (fun _ _ _ _ => False)) id
      (fun _ _ hs => Or.inl hs) hd
  · refine Silmaril.InfiniteTrace.of_steps (silent_of_noHost hr) ⟨fun _ => d, rfl, fun _ => ?_⟩
    exact .inr ⟨rfl, E, a, hh, us, hdc, hdiv⟩

theorem quiet_iff {c : Config H} :
    Quiet P host c ↔ (Diverges P (fun _ _ _ _ => False) c ∨
      ∃ d : Config H, Steps P (fun _ _ _ _ => False) c d ∧
        ∃ E a hh us, decompose? d.store d.code = some (E, a, hh, us) ∧
          host hh d.store us .diverged) :=
  ⟨quiet_split, quiet_of_split⟩

end Silmaril.Proofs.Wasm.Abstract.HostCall
