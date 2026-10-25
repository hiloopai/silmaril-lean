module

public import Silmaril.Wasm.Execution.Core.Sim.Closure.Basic
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Call
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Frame
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Handler
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Label
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Struct

@[expose] public section

/-! # The generic code-relation simulation theorem

Given base relations `BI` (source) and `B` (runtime), `BaseSim` lists the
obligations a user proves **only about base pairs**, in an arbitrary value
prefix and related suffix:

* `src`: a source base pair is a runtime base pair once lowered by `expression`;
* `step`: a step of `val* x rest` is matched by `val* y rest'` in one or more
  steps, or the right side stutters while the selected rank decreases;
* `exit`: if the left reaches an exit (`br`, `return`, `return_call_ref`,
  `trap`, a thrown exception) inside `x`, the right reaches the same exit kernel
  after the same values, keeping its frame;
* `values`: if `x` is all values, `y` evaluates to the same values.

`closure_configSim` then lifts these through everything else — sequencing,
`LABEL`/`HANDLER`/`FRAME` contexts and their bubbling rules, calls into
`FuncRel`-related function bodies (`FRAME (LABEL (expression body))`), host calls
(matched as identical interactions through `HostRespects F`, the returned stores
related again), tail calls (`return_call_ref-*`), exceptions and traps — to a
`ConfigSim` on `CfgRel F (AdminsRel BI (WithCuts B))` with the selected lawful contextual rank (default `codeSize`).
The consequences `closure_behavioursOf_subset` and `closure_behavioursOf_eq`
(for configurations related by the plain closure `AdminsRel BI B`) are derived
from `Sim/Behaviour.lean`.

**Exit cuts.** The simulation relation is the closure of `B` *together with*
`ExitCut`: `val* trap x ~ val* trap y` and `val* (REF.EXN_ADDR a) THROW_REF x ~
val* (REF.EXN_ADDR a) THROW_REF y`, with arbitrary values and code on either
side. Without them the closure is not a simulation: `trap-instrs` and
`throw_ref-instrs` under `ctxt-instrs` discard an arbitrary *prefix* of the code
after the trap, which can end inside a base pair or a related suffix, and the
plain closure `AdminsRel BI B` need not relate the two remainders.
separate simulation-closure counterexamples (not included in this package) proves this (`closure_configSim_original_false`). A partial
discard after a trap or throw is unobservable, so the cut pairs are sound.

**Status.** `closure_configSim` is assembled (section *Assembly*) from per-head
helpers in namespace `Closure`. The shared interface (`BaseSim`, `ExitCut`,
`WithCuts`, `Matched`, `StepIH`) and the proved helpers (`run_vals`,
`split_active`, `exit_lift`, `cut_case`, `transport_lift`) are in
`Sim/Closure/Basic.lean`; the base-pair, sequence and terminal cases are proved
here. The open cases live in disjoint files, one per redex family, each importing
only `Sim/Closure/Basic.lean`: `struct_case` (`Sim/Closure/Struct.lean`),
`label_case` (`Label.lean`), `handler_case` (`Handler.lean`), `tail_case` and
`frame_case` (`Frame.lean`), `call_case` (`Call.lean`, with the proved
`host_case`). The proof plan: strong induction on the size of the
left code; for `ctxt-label/handler/frame` the IH under `AdminRel.label` etc.;
for a step at sequence level, decompose the `AdminsRel` derivation of the code
into a related value prefix (run the right prefix to the same values with
`BaseSim.values`, lifted by `Steps.append_right`), then either a base pair, a
cut pair, or a pointwise `AdminRel` head. A base pair is handled by `BaseSim.step`
(with suffix `[]`) when the step stays inside it, and by `BaseSim.exit` followed by
the same discard on the right (giving a cut pair) when a trap or throw inside it
discards into the suffix. A cut pair steps only by a discard, matched by a right
discard or by a stutter. A pointwise head is handled by `Step.split_head` and
`Step.transport_storeRel` (no call), `FuncRel` (Wasm call) or `HostRespects`
(host call). The bubbling rules use `BaseSim.exit` lifted to `AdminsRel` (same
decomposition). Stuttering comes from `BaseSim.step` and from discards whose
right partner already has the trap or throw at its head: a discard of code after
a trap (for example the left `[trap, nop]` against the right `[trap]` with the
base pair `([nop], [])`) is matched by a stutter. `codeSize` strictly decreases
in both cases, and `codeSize_append` makes the decrease global.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation

variable {H : Type}

variable {P : Profile} {host : HostSemantics H} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

variable {rank : List Admin → Nat} [LawfulCodeRank rank]

namespace Closure

/-- A step at a base pair: `BaseSim.step` inside it, `BaseSim.exit` plus a cut for
a trap or throw discarding into the suffix. -/
theorem base_case (hB : BaseSim P host F BI B rank) {s t s' : Store H} {f f' : Frame}
    {V : List Val} {x y L L' es' : List Admin} (hst : StoreRel F s t) (hxy : B x y)
    (hx : x.all Admin.isVal = false) (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P host ⟨s, f, vals V ++ x ++ L⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P host F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ y ++ L'⟩
      (rank (vals V ++ x ++ L)) := by
  obtain ⟨u₁, a, x₁, ha, rfl⟩ := exists_head_of_not_all hx
  have hcode : vals V ++ (vals u₁ ++ a :: x₁) ++ L = vals (V ++ u₁) ++ a :: (x₁ ++ L) := by simp
  rw [hcode] at h ⊢
  rcases Step.split_head ha h with ⟨ws, us, is', hVU, hst', rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, r, r', hVU, hxL, hne, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, xx, r, r', hVU, hxL, hne, rfl⟩
  · -- the step stays inside the base pair: `BaseSim.step`
    have hstep : Step P host ⟨s, f, vals V ++ (vals u₁ ++ a :: x₁) ++ []⟩
        ⟨s', f', vals ws ++ is' ++ x₁⟩ := by
      have := Step.append_right (Step.vals_left hst' ws) x₁
      have e : vals ws ++ (vals us ++ [a]) ++ x₁ = vals V ++ (vals u₁ ++ a :: x₁) ++ [] :=
        calc vals ws ++ (vals us ++ [a]) ++ x₁ = vals (ws ++ us) ++ a :: x₁ := by simp
          _ = vals (V ++ u₁) ++ a :: x₁ := by rw [hVU]
          _ = _ := by simp
      rw [e] at this
      exact this
    obtain ⟨t', es'', hprog, hst'', hrel⟩ := hB.step hst hxy AdminsRel.nil hstep
    have e1 : vals ws ++ is' ++ (x₁ ++ L) = vals ws ++ is' ++ x₁ ++ L := by simp
    rcases hprog with hT | ⟨rfl, rfl, rfl, hlt⟩
    · refine ⟨⟨t', f', es'' ++ L'⟩, Or.inl ?_, hst'', rfl, ?_⟩
      · exact transGen_congr (transGen_append_right hT L') (by simp) rfl
      · rw [e1]
        exact (AdminsRel.mono (fun _ _ h => Or.inl h) hrel).append hL
    · refine ⟨_, Or.inr ⟨rfl, ?_⟩, hst'', rfl, ?_⟩
      · dsimp only
        rw [e1, ← hcode]
        simp only [List.append_nil] at hlt
        exact LawfulCodeRank.append_right_lt hlt L
      · rw [e1, show vals V ++ y ++ L' = vals V ++ y ++ [] ++ L' by simp]
        exact (AdminsRel.mono (fun _ _ h => Or.inl h) hrel).append hL
  · -- a trap inside the base pair discards into the suffix: `BaseSim.exit`, then a cut
    obtain ⟨t', j', hex, hst'⟩ := hB.exit (f := f') hst hxy Exit.trap (vs := V)
      (us := V ++ u₁) (j := x₁) (by simp)
    have hlift := Steps.append_right hex L'
    dsimp only at hlift
    refine Matched.of_steps hlift ⟨_, Or.inr ⟨rfl, ?_⟩, hst', rfl,
      AdminsRel.base (Or.inr ⟨ws, V ++ u₁, [.trap], r', j' ++ L', Or.inl rfl, rfl, by simp⟩)⟩
    rw [hVU, hxL]
    have := LawfulCodeRank.discard_lt (rank := rank) ws us [.trap] r r' hne
    simpa using this
  · -- a throw inside the base pair discards into the suffix
    have heq : vals V ++ (vals u₁ ++ Admin.plain .throwRef :: x₁) =
        vals (ws ++ us) ++ throwing xx ++ x₁ :=
      calc _ = vals (V ++ u₁) ++ Admin.plain .throwRef :: x₁ := by simp
        _ = vals (ws ++ us ++ [.ref (.exn xx)]) ++ Admin.plain .throwRef :: x₁ := by rw [hVU]
        _ = _ := by simp [vals, throwing, Val.toAdmin]
    obtain ⟨t', j', hex, hst'⟩ := hB.exit (f := f') hst hxy (Exit.throw xx) heq
    have hlift := Steps.append_right hex L'
    dsimp only at hlift
    refine Matched.of_steps hlift ⟨_, Or.inr ⟨rfl, ?_⟩, hst', rfl,
      AdminsRel.base (Or.inr ⟨ws, ws ++ us, throwing xx, r', j' ++ L', Or.inr ⟨xx, rfl⟩, rfl,
        by simp⟩)⟩
    rw [hVU, hxL]
    have := LawfulCodeRank.discard_lt (rank := rank) ws us (throwing xx) r r' hne
    simpa [vals, throwing, Val.toAdmin] using this

/-- A step at a pointwise head that is neither a context nor a call: store
transport for an unchanged head, the same structured-instruction step with related
bodies, or a discard (`cut_case`). -/
theorem seq_case {s t s' : Store H} {f f' : Frame}
    {V : List Val} {a b : Admin} {L L' es' : List Admin} (hst : StoreRel F s t)
    (hab : AdminRel BI (WithCuts B) a b) (ha : a.val? = none) (hctx : ¬ a.IsCtx)
    (hcall : ¬ a.IsCallRef) (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P host ⟨s, f, vals V ++ [a] ++ L⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P host F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [b] ++ L'⟩
      (rank (vals V ++ [a] ++ L)) := by
  rw [show vals V ++ [a] ++ L = vals V ++ a :: L by simp] at h ⊢
  rcases Step.split_head ha h with ⟨ws, us, is', rfl, hst', rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, r, r', rfl, rfl, hne, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, xx, r, r', rfl, rfl, hne, rfl⟩
  · cases hab with
    | refl => exact transport_lift hst hctx hcall hL hst' _
    | plain hi => exact struct_case hst hi hcall hL hst'
    | label => exact (hctx trivial).elim
    | handler => exact (hctx trivial).elim
    | frame => exact (hctx trivial).elim
  · obtain rfl : b = .trap := hab.eq_of_flat (fun i hi => by cases hi) hctx
    exact cut_case (Or.inl rfl) hst (U := ws ++ us) (X := r ++ r') (W := ws ++ us) (Y := L')
      (by simp) rfl h
  · obtain rfl : b = .plain .throwRef :=
      hab.eq_of_flat (fun i hi i' hr => by cases hi; cases hr; rfl) hctx
    exact cut_case (Or.inr ⟨xx, rfl⟩) hst (U := ws ++ us) (X := r ++ r') (W := ws ++ us)
      (Y := L') (by simp [vals, throwing, Val.toAdmin]) (by simp [vals, throwing, Val.toAdmin]) h

omit [LawfulCodeRank rank] in
/-- A terminal left configuration: values are matched by `run_vals`, `trap` and a
thrown exception by `exit_lift` followed by the discard of the right remainder. -/
theorem terminal_case (hB : BaseFacts P host F BI B rank) {c d : Config H} {r : Result}
    (h : CfgRel F (AdminsRel BI (WithCuts B)) c d) (hc : c.code = r.toAdmin) :
    ∃ d', Steps P host d d' ∧ d'.code = r.toAdmin := by
  obtain ⟨s, f, x⟩ := c
  obtain ⟨t, g, y⟩ := d
  obtain ⟨hst, hfg, hxy⟩ := h
  dsimp only at hst hfg hxy hc ⊢
  subst g hc
  have hsegs := AdminsRel.segs (fun _ _ h => Or.inl (hB.src h)) hxy
  cases r with
  | values vs =>
    obtain ⟨t', h', -⟩ := run_vals hB hsegs (by simp [Result.toAdmin]) [] hst
    exact ⟨⟨t', f, vals vs⟩, steps_congr h' (by simp [vals_nil'])
      (by simp [vals_nil', Result.toAdmin]), rfl⟩
  | trap =>
    obtain ⟨t', us', j', h', -, -⟩ := exit_lift hB hsegs hst [] Exit.trap (us := []) (j := [])
      (by simp [Result.toAdmin, vals_nil'])
    have h'' : Steps P host ⟨t, f, y⟩ ⟨t', f, vals us' ++ [.trap] ++ j'⟩ :=
      steps_congr h' (by simp [vals_nil']) (by simp [vals_nil'])
    refine ⟨⟨t', f, [.trap]⟩, ?_, rfl⟩
    by_cases hne : us' ≠ [] ∨ j' ≠ []
    · exact h''.tail (Step.trapInstrs hne)
    · simp only [ne_eq, not_or, not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      simpa [vals_nil'] using h''
  | throw a =>
    obtain ⟨t', us', j', h', -, -⟩ := exit_lift hB hsegs hst [] (Exit.throw a) (us := [])
      (j := []) (by simp [Result.toAdmin, vals_nil', throwing])
    have h'' : Steps P host ⟨t, f, y⟩ ⟨t', f, vals us' ++ throwing a ++ j'⟩ :=
      steps_congr h' (by simp [vals_nil']) (by simp [vals_nil'])
    refine ⟨⟨t', f, throwing a⟩, ?_, rfl⟩
    by_cases hne : us' ≠ [] ∨ j' ≠ []
    · exact h''.tail (Step.throwRefInstrs hne)
    · simp only [ne_eq, not_or, not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      simpa [vals_nil'] using h''

/-- The one-step obligation, by strong induction on the size of the left code. -/
theorem step_main (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F host) (hB : BaseSim P host F BI B rank) :
    ∀ m : Nat, RankedStepIH rank P host F BI B m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro c d c' hm hcd hstep
  obtain ⟨s, f, x⟩ := c
  obtain ⟨t, g, y⟩ := d
  obtain ⟨s', f', es'⟩ := c'
  obtain ⟨hst, hfg, hxy⟩ := hcd
  dsimp only at hst hfg hxy hm hstep ⊢
  subst hfg
  have hsegs := AdminsRel.segs (fun _ _ h => Or.inl (hB.src h)) hxy
  obtain ⟨V, xs, ys, xr, yr, t₁, rfl, hseg, hact, hr, hrun, hst₁⟩ :=
    split_active hB.toBaseFacts hsegs hstep.not_all_isVal [] hst
  refine Matched.of_steps (d₁ := ⟨t₁, f, vals V ++ ys ++ yr⟩)
    (steps_congr hrun (by simp [vals_nil']) (by simp [vals_nil'])) ?_
  have hL := hr.adminsRel
  have ih : RankedStepIH rank P host F BI B (rank (vals V ++ xs ++ xr)) := ihm _ hm
  cases hseg with
  | @one a b hab =>
    have ha : a.val? = none := by simpa [Admin.isVal] using hact
    by_cases hctx : a.IsCtx
    · cases hab with
      | refl =>
        cases a
        case label n cont b =>
          exact label_case hF hhost hB ih hst₁ (InstrsRel.refl _) (AdminsRel.refl _) hL hstep
        case handler n cs b => exact handler_case hF hhost hB ih hst₁ (AdminsRel.refl _) hL hstep
        case frame n fi b => exact frame_case hF hhost hB ih hst₁ (AdminsRel.refl _) hL hstep
        all_goals exact hctx.elim
      | plain hi => exact hctx.elim
      | label n hc hb => exact label_case hF hhost hB ih hst₁ hc hb hL hstep
      | handler n cs hb => exact handler_case hF hhost hB ih hst₁ hb hL hstep
      | frame n fi hb => exact frame_case hF hhost hB ih hst₁ hb hL hstep
    · by_cases hcall : a.IsCallRef
      · exact call_case hF hhost hst₁ hab hcall hL hstep
      · exact seq_case hst₁ hab ha hctx hcall hL hstep
  | base hb =>
    rcases hb with hb | hcut
    · exact base_case hB hst₁ hb hact hL hstep
    · obtain ⟨us, ws, k, x', y', hk, rfl, rfl⟩ := hcut
      exact cut_case hk hst₁ (U := V ++ us) (X := x' ++ xr) (W := V ++ ws) (Y := y' ++ yr)
        (by simp) (by simp) hstep

end Closure

open Closure in
/-- **The generic simulation theorem.** The closure of base relations meeting
`BaseSim`, together with the exit cuts, is a stuttering simulation of Core 3.0
with itself, for any function relation `F` contained in `FuncRel BI` and any
host respecting `F`. -/
-- FLAG(statement-change): the simulation relation is `AdminsRel BI (WithCuts B)`
-- instead of `AdminsRel BI B`. The original statement is false, because partial
-- trap/throw discards leave the plain closure (`closure_configSim_original_false`,
-- separate simulation-closure counterexamples (not included in this package)).
theorem closure_configSim (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F host) (hB : BaseSim P host F BI B rank) :
    ∃ sim : ConfigSim P host (CfgRel F (AdminsRel BI (WithCuts B))),
      sim.toForwardSim.measure = fun c => rank c.code :=
  ⟨{ toForwardSim :=
      { measure := fun c => rank c.code
        step := fun hstep hcd => step_main hF hhost hB _ (Nat.lt_succ_self _) hcd hstep }
     terminal := fun hcd hc => terminal_case hB.toBaseFacts hcd hc }, rfl⟩

/-- Behaviour refinement for the closure. -/
theorem closure_behavioursOf_subset (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F host) (hB : BaseSim P host F BI B rank) {c d : Config H}
    (h : CfgRel F (AdminsRel BI B) c d) :
    behavioursOf P host c ⊆ behavioursOf P host d := by
  obtain ⟨sim, -⟩ := closure_configSim hF hhost hB
  exact sim.behavioursOf_subset (h.mono fun _ _ => AdminsRel.mono fun _ _ => Or.inl)

/-- The converse of a closure-related pair of configurations is related by the
closure of the converse relations. -/
theorem CfgRel.flip {c d : Config H} (h : CfgRel F (AdminsRel BI B) c d) :
    CfgRel (fun g f => F f g) (AdminsRel (fun a b => BI b a) (fun a b => B b a)) d c :=
  ⟨h.store.symm, h.frame.symm, h.code.flip⟩

/-- **Behavioural equivalence** for the closure, from the obligations in both
directions. -/
theorem closure_behavioursOf_eq (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hF' : ∀ fi gi, F gi fi → FuncRel (fun a b => BI b a) fi gi)
    (hhost : HostRespects F host) (hhost' : HostRespects (fun g f => F f g) host)
    (hB : BaseSim P host F BI B rank)
    {rank' : List Admin → Nat} [LawfulCodeRank rank']
    (hB' : BaseSim P host (fun g f => F f g) (fun a b => BI b a) (fun a b => B b a) rank')
    {c d : Config H} (h : CfgRel F (AdminsRel BI B) c d) :
    behavioursOf P host c = behavioursOf P host d :=
  Set.Subset.antisymm (closure_behavioursOf_subset hF hhost hB h)
    (closure_behavioursOf_subset hF' hhost' hB' h.flip)

end Silmaril.Wasm.Execution.Core.Sim
