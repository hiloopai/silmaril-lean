module

public import Silmaril.Wasm.Execution.Core.Sim.TypedStepTo
public import Silmaril.Wasm.Execution.Core.Sim.TypedKernelRuntime

@[expose] public section

/-! # Contextual simulations with kernel-prefix-aware typed facts

Both value-prefix normalization and runtime-context exits retain the target's
ambient typing witness. The active base-step relation may grow after each
source step. The earlier interfaces requiring untyped `BaseFacts` remain
available independently.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Validation Numerics SingleThreaded

variable {H : Type}
local notation "noHost" => (fun _ _ _ _ => False)
variable {P : Profile} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B B' : List Admin → List Admin → Prop}
variable {rank : List Admin → Nat} [LawfulCodeRank rank]

namespace Closure

theorem kernel_base_case_to_with_facts (hfacts : TypedKernelFacts P F BI B)
    (hbase : TypedBaseStepTo P F BI B B' rank) {s t s' : Store H} {f f' : Frame}
    {V : List Val} {x y L L' es' : List Admin} (hst : StoreRel F s t) (hxy : B x y)
    (hx : x.all Admin.isVal = false) (hL : AdminsRel BI (WithCuts B') L L')
    (htyped : ContextTyped ⟨t, f, vals V ++ y ++ L'⟩)
    (h : Step P noHost ⟨s, f, vals V ++ x ++ L⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P noHost F BI B' ⟨s', f', es'⟩ ⟨t, f, vals V ++ y ++ L'⟩
      (rank (vals V ++ x ++ L)) := by
  obtain ⟨u₁, a, x₁, ha, rfl⟩ := exists_head_of_not_all hx
  have hcode : vals V ++ (vals u₁ ++ a :: x₁) ++ L = vals (V ++ u₁) ++ a :: (x₁ ++ L) := by simp
  rw [hcode] at h ⊢
  rcases Step.split_head ha h with ⟨ws, us, is', hVU, hst', rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, r, r', hVU, hxL, hne, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, xx, r, r', hVU, hxL, hne, rfl⟩
  · -- the step stays inside the base pair: `BaseSim.step`
    have hstep : Step P noHost ⟨s, f, vals V ++ (vals u₁ ++ a :: x₁) ++ []⟩
        ⟨s', f', vals ws ++ is' ++ x₁⟩ := by
      have := Step.append_right (Step.vals_left hst' ws) x₁
      have e : vals ws ++ (vals us ++ [a]) ++ x₁ = vals V ++ (vals u₁ ++ a :: x₁) ++ [] :=
        calc vals ws ++ (vals us ++ [a]) ++ x₁ = vals (ws ++ us) ++ a :: x₁ := by simp
          _ = vals (V ++ u₁) ++ a :: x₁ := by rw [hVU]
          _ = _ := by simp
      rw [e] at this
      exact this
    obtain ⟨⟨t', g, es''⟩, hprog, hst'', hfr, hrel⟩ :=
      hbase.step hst hxy hx (by simpa using htyped.suffix) (by simpa using hstep)
    dsimp only at hst'' hfr hrel hprog
    subst g
    have e1 : vals ws ++ is' ++ (x₁ ++ L) = vals ws ++ is' ++ x₁ ++ L := by simp
    rcases hprog with hT | ⟨heq, hlt⟩
    · refine ⟨⟨t', f', es'' ++ L'⟩, Or.inl ?_, hst'', rfl, ?_⟩
      · exact transGen_congr (transGen_append_right hT L') (by simp) rfl
      · rw [e1]
        simpa only [List.append_assoc] using hrel.append hL
    · cases heq
      refine ⟨_, Or.inr ⟨rfl, ?_⟩, hst'', rfl, ?_⟩
      · dsimp only
        rw [e1, ← hcode]
        simpa only [List.append_assoc] using LawfulCodeRank.append_right_lt hlt L
      · rw [e1]
        simpa only [List.append_assoc] using hrel.append hL
  · -- a trap inside the base pair discards into the suffix: `BaseSim.exit`, then a cut
    obtain ⟨t', actual, j', hex, hst', _⟩ := hfacts.exit (f := f') hst hxy (by simpa using htyped.suffix) Exit.trap (vs := V)
      (us := V ++ u₁) (j := x₁) (by simp)
    have hlift := Steps.append_right hex L'
    dsimp only at hlift
    refine Matched.of_steps hlift ⟨_, Or.inr ⟨rfl, ?_⟩, hst', rfl,
      AdminsRel.base (Or.inr ⟨ws, actual, [.trap], r', j' ++ L', Or.inl rfl, rfl, by simp⟩)⟩
    rw [hVU, hxL]
    have := LawfulCodeRank.discard_lt (rank := rank) ws us [.trap] r r' hne
    simpa using this
  · -- a throw inside the base pair discards into the suffix
    have heq : vals V ++ (vals u₁ ++ Admin.plain .throwRef :: x₁) =
        vals (ws ++ us) ++ throwing xx ++ x₁ :=
      calc _ = vals (V ++ u₁) ++ Admin.plain .throwRef :: x₁ := by simp
        _ = vals (ws ++ us ++ [.ref (.exn xx)]) ++ Admin.plain .throwRef :: x₁ := by rw [hVU]
        _ = _ := by simp [vals, throwing, Val.toAdmin]
    obtain ⟨t', actual, j', hex, hst', _⟩ := hfacts.exit (f := f') hst hxy (by simpa using htyped.suffix) (Exit.throw xx) heq
    have hlift := Steps.append_right hex L'
    dsimp only at hlift
    refine Matched.of_steps hlift ⟨_, Or.inr ⟨rfl, ?_⟩, hst', rfl,
      AdminsRel.base (Or.inr ⟨ws, actual, throwing xx, r', j' ++ L', Or.inr ⟨xx, rfl⟩, rfl,
        by simp⟩)⟩
    rw [hVU, hxL]
    have := LawfulCodeRank.discard_lt (rank := rank) ws us (throwing xx) r r' hne
    simpa [vals, throwing, Val.toAdmin] using this

theorem kernel_step_main_to_with_facts (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F noHost)
    (hin : TypedKernelFacts P F BI B) (hout : TypedKernelFacts P F BI B')
    (hmono : ∀ x y, B x y → B' x y) (hbase : TypedBaseStepTo P F BI B B' rank) :
    ∀ m : Nat, TypedStepToIH P F BI B B' m rank := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro c d c' hm hcd htyped hstep
  obtain ⟨s, f, x⟩ := c
  obtain ⟨t, g, y⟩ := d
  obtain ⟨s', f', es'⟩ := c'
  obtain ⟨hst, hfg, hxy⟩ := hcd
  dsimp only at hst hfg hxy hm hstep htyped ⊢
  subst hfg
  have hsegs := AdminsRel.segs (fun _ _ h => Or.inl (hin.src h)) hxy
  obtain ⟨V, xs, ys, xr, yr, t₁, rfl, hseg, hact, hr, hrun, hst₁⟩ :=
    kernel_split_active hin hsegs hstep.not_all_isVal [] hst (by simpa using htyped)
  refine Matched.of_steps (d₁ := ⟨t₁, f, vals V ++ ys ++ yr⟩)
    (steps_congr hrun (by simp) (by simp)) ?_
  have htyped₁ : ContextTyped ⟨t₁, f, vals V ++ ys ++ yr⟩ :=
    htyped.steps (steps_congr hrun (by simp) (by simp))
  have hcuts : ∀ x y, WithCuts B x y → WithCuts B' x y :=
    fun x y h => h.elim (fun h => Or.inl (hmono x y h)) Or.inr
  have hL := hr.adminsRel.mono hcuts
  have ih : TypedStepToIH P F BI B B' (rank (vals V ++ xs ++ xr)) rank := ihm _ hm
  cases hseg with
  | @one a b hab =>
    have ha : a.val? = none := by simpa [Admin.isVal] using hact
    by_cases hctx : a.IsCtx
    · cases hab with
      | refl =>
        cases a
        case label n cont b =>
          exact kernel_label_case_of_body hF hhost hout (fun {c'} hs =>
            ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c') (LawfulCodeRank.label_body_lt (vals V) xr n cont b)
              ⟨hst₁, rfl, AdminsRel.refl _⟩ htyped₁.label hs)
            hst₁ (InstrsRel.refl _) (AdminsRel.refl _) hL htyped₁.label hstep
        case handler n cs b =>
          exact kernel_handler_case_of_body hF hhost hout (fun {c'} hs =>
            ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c') (LawfulCodeRank.handler_body_lt (vals V) xr n cs b)
              ⟨hst₁, rfl, AdminsRel.refl _⟩ htyped₁.handler hs)
            hst₁ (AdminsRel.refl _) hL htyped₁.handler hstep
        case frame n fi b =>
          exact kernel_frame_case_of_body hF hhost hout (fun {c'} hs =>
            ih (c := ⟨s, fi, _⟩) (d := ⟨t₁, fi, _⟩) (c' := c') (LawfulCodeRank.frame_body_lt (vals V) xr n fi b)
              ⟨hst₁, rfl, AdminsRel.refl _⟩ htyped₁.frame hs)
            hst₁ (AdminsRel.refl _) hL htyped₁.frame hstep
        all_goals exact hctx.elim
      | plain hi => exact hctx.elim
      | label n hc hb =>
        exact kernel_label_case_of_body hF hhost hout (fun {c'} hs =>
          ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c') (LawfulCodeRank.label_body_lt (vals V) xr n _ _)
            ⟨hst₁, rfl, hb⟩ htyped₁.label hs) hst₁ hc (hb.mono hcuts) hL htyped₁.label hstep
      | handler n cs hb =>
        exact kernel_handler_case_of_body hF hhost hout (fun {c'} hs =>
          ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c') (LawfulCodeRank.handler_body_lt (vals V) xr n cs _)
            ⟨hst₁, rfl, hb⟩ htyped₁.handler hs) hst₁ (hb.mono hcuts) hL htyped₁.handler hstep
      | frame n fi hb =>
        exact kernel_frame_case_of_body hF hhost hout (fun {c'} hs =>
          ih (c := ⟨s, fi, _⟩) (d := ⟨t₁, fi, _⟩) (c' := c') (LawfulCodeRank.frame_body_lt (vals V) xr n fi _)
            ⟨hst₁, rfl, hb⟩ htyped₁.frame hs) hst₁ (hb.mono hcuts) hL htyped₁.frame hstep
    · by_cases hcall : a.IsCallRef
      · exact call_case hF hhost hst₁ (hab.mono hcuts) hcall hL hstep
      · exact seq_case hst₁ (hab.mono hcuts) ha hctx hcall hL hstep
  | base hb =>
    rcases hb with hb | hcut
    · exact kernel_base_case_to_with_facts hin hbase hst₁ hb hact hL htyped₁ hstep
    · obtain ⟨us, ws, k, x', y', hk, rfl, rfl⟩ := hcut
      exact cut_case hk hst₁ (U := V ++ us) (X := x' ++ xr) (W := V ++ ws) (Y := y' ++ yr)
        (by simp) (by simp) hstep

end Closure

/-- One full contextual step can increase the runtime relation, retaining
related final stores, the exact same profile and every supported runtime context.
This is a one-step law; iteration needs a family of compatible output laws. -/
theorem kernel_closure_step_to_with_facts
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi) (hhost : HostRespects F noHost)
    (hin : TypedKernelFacts P F BI B) (hout : TypedKernelFacts P F BI B')
    (hmono : ∀ x y, B x y → B' x y) (hbase : TypedBaseStepTo P F BI B B' rank)
    {c d c' : Config H} (related : CfgRel F (AdminsRel BI (WithCuts B)) c d)
    (typed : ContextTyped d) (step : Step P noHost c c') :
    RankedMatched rank P noHost F BI B' c' d (rank c.code) :=
  Closure.kernel_step_main_to_with_facts hF hhost hin hout hmono hbase _
    (Nat.lt_succ_self _) related typed step


namespace Closure

/-- Normalize a terminal source using the typed target and retain its store. -/
theorem kernel_terminal_case_store (facts : TypedKernelFacts P F BI B)
    {c d : Config H} {r : Result} (related : CfgRel F (AdminsRel BI (WithCuts B)) c d)
    (typed : ContextTyped d) (terminal : c.code = r.toAdmin) :
    ∃ d', Steps P noHost d d' ∧ d'.code = r.toAdmin ∧ StoreRel F c.store d'.store := by
  obtain ⟨s, f, x⟩ := c
  obtain ⟨t, g, y⟩ := d
  obtain ⟨stores, frames, code⟩ := related
  dsimp only at stores frames code typed terminal ⊢
  subst g
  obtain ⟨t', run, stores'⟩ := code.kernel_result_lift facts stores typed terminal
  exact ⟨⟨t', f, r.toAdmin⟩, run, rfl, stores'⟩

end Closure

/-- Compatible enlarging runtime relations yield a genuine simulation. No
single finite relation is required to contain every later runtime phase. -/
theorem kernel_family_configSim_with_facts {Bs : Nat → List Admin → List Admin → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi) (hhost : HostRespects F noHost)
    (hfacts : ∀ n, TypedKernelFacts P F BI (Bs n))
    (hmono : ∀ n x y, Bs n x y → Bs (n + 1) x y)
    (hbase : ∀ n, TypedBaseStepTo P F BI (Bs n) (Bs (n + 1)) rank) :
    ∃ sim : ConfigSim P noHost (TypedFamilyCfgRel F BI Bs),
      sim.toForwardSim.measure = fun c => rank c.code := by
  refine ⟨⟨⟨fun c => rank c.code, ?_⟩, ?_⟩, rfl⟩
  · intro c c' d hs hrel
    obtain ⟨n, hr, ht⟩ := hrel
    obtain ⟨d', hm, hr'⟩ := kernel_closure_step_to_with_facts hF hhost
      (hfacts n) (hfacts (n + 1)) (hmono n) (hbase n) hr ht hs
    refine ⟨d', hm, n + 1, hr', ?_⟩
    rcases hm with hm | ⟨rfl, _⟩
    · exact ht.steps hm.to_reflTransGen
    · exact ht
  · intro c d r hrel hc
    obtain ⟨n, hr, ht⟩ := hrel
    obtain ⟨d', run, terminal, _⟩ := Closure.kernel_terminal_case_store (hfacts n) hr ht hc
    exact ⟨d', run, terminal⟩

/-- Completed family runs retain the final store relation, even when the
runtime relation index grows an unbounded number of times during the run. -/
theorem kernel_family_run_transport_with_facts {Bs : Nat → List Admin → List Admin → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi) (hhost : HostRespects F noHost)
    (hfacts : ∀ n, TypedKernelFacts P F BI (Bs n))
    (hmono : ∀ n x y, Bs n x y → Bs (n + 1) x y)
    (hbase : ∀ n, TypedBaseStepTo P F BI (Bs n) (Bs (n + 1)) rank)
    {n : Nat} {c d c' : Config H} {r : Result}
    (related : CfgRel F (AdminsRel BI (Bs n)) c d) (typed : ContextTyped d)
    (run : Steps P noHost c c') (terminal : c'.code = r.toAdmin) :
    ∃ d', Steps P noHost d d' ∧ d'.code = r.toAdmin ∧ StoreRel F c'.store d'.store := by
  obtain ⟨sim, _⟩ := kernel_family_configSim_with_facts hF hhost hfacts hmono hbase
  obtain ⟨d₁, hd, n', hr, ht⟩ := sim.toForwardSim.steps run
    ⟨n, related.mono (fun _ _ => AdminsRel.mono (fun _ _ => Or.inl)), typed⟩
  obtain ⟨d', hd', hc', hst⟩ := Closure.kernel_terminal_case_store (hfacts n') hr ht terminal
  exact ⟨d', hd.trans hd', hc', hst⟩

theorem kernel_family_diverges_transport_with_facts {Bs : Nat → List Admin → List Admin → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi) (hhost : HostRespects F noHost)
    (hfacts : ∀ n, TypedKernelFacts P F BI (Bs n))
    (hmono : ∀ n x y, Bs n x y → Bs (n + 1) x y)
    (hbase : ∀ n, TypedBaseStepTo P F BI (Bs n) (Bs (n + 1)) rank)
    {n : Nat} {c d : Config H} (related : CfgRel F (AdminsRel BI (Bs n)) c d)
    (typed : ContextTyped d) (diverges : Diverges P noHost c) : Diverges P noHost d := by
  obtain ⟨sim, _⟩ := kernel_family_configSim_with_facts hF hhost hfacts hmono hbase
  exact sim.toForwardSim.diverges diverges
    ⟨n, related.mono (fun _ _ => AdminsRel.mono (fun _ _ => Or.inl)), typed⟩

end Silmaril.Wasm.Execution.Core.Sim
