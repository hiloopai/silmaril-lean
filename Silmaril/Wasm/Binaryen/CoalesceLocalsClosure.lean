module

public import Silmaril.Wasm.Binaryen.CoalesceLocalsDeferred

@[expose] public section

/-! # Closing deferred local-write matches under the real Core semantics -/

namespace Silmaril.Wasm.Binaryen.CoalesceLocalsLite

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded.Det

variable {H : Type} {P : Profile} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

def DeferredStepIH (P : Profile) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop) (m : Nat) : Prop :=
  ∀ {c d c' : Config H}, aszs c.code < m → CfgRel F (AdminsRel BI (WithCuts B)) c d →
    Step P closedHost c c' → DeferredMatched (P := P) F BI B c' d (aszs c.code)

namespace DeferredClosure

theorem step_main (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F closedHost) (hB : DeferredBaseSim P F BI B) :
    ∀ m : Nat, DeferredStepIH P F BI B m := by
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
  have hsegs := AdminsRel.segs (fun _ _ h => Or.inl (hB.facts.src h)) hxy
  obtain ⟨V, xs, ys, xr, yr, t₁, rfl, hseg, hact, hr, hrun, hst₁⟩ :=
    Closure.split_active hB.facts hsegs hstep.not_all_isVal [] hst
  refine DeferredMatched.of_steps (d₁ := ⟨t₁, f, vals V ++ ys ++ yr⟩)
    (Closure.steps_congr hrun (by simp) (by simp)) ?_
  have hL := hr.adminsRel
  have ih : DeferredStepIH P F BI B (aszs (vals V ++ xs ++ xr)) := ihm _ hm
  cases hseg with
  | @one a b hab =>
    have ha : a.val? = none := by simpa [Admin.isVal] using hact
    by_cases hctx : a.IsCtx
    · cases hab with
      | refl =>
        cases a
        case label n cont b =>
          exact label_case hF hhost hB.facts (fun {c'} hs =>
            ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c')
              (LawfulCodeRank.label_body_lt (vals V) xr n cont b)
              ⟨hst₁, rfl, AdminsRel.refl _⟩ hs)
            hst₁ (InstrsRel.refl _) (AdminsRel.refl _) hL hstep
        case handler n cs b =>
          exact handler_case hF hhost hB.facts (fun {c'} hs =>
            ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c')
              (LawfulCodeRank.handler_body_lt (vals V) xr n cs b)
              ⟨hst₁, rfl, AdminsRel.refl _⟩ hs) hst₁ (AdminsRel.refl _) hL hstep
        case frame n fi b =>
          exact frame_case hF hhost hB.facts (fun {c'} hs =>
            ih (c := ⟨s, fi, _⟩) (d := ⟨t₁, fi, _⟩) (c' := c')
              (LawfulCodeRank.frame_body_lt (vals V) xr n fi b)
              ⟨hst₁, rfl, AdminsRel.refl _⟩ hs) hst₁ (AdminsRel.refl _) hL hstep
        all_goals exact hctx.elim
      | plain hi => exact hctx.elim
      | label n hc hb =>
        exact label_case hF hhost hB.facts (fun {c'} hs =>
          ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c')
            (LawfulCodeRank.label_body_lt (vals V) xr n _ _)
            ⟨hst₁, rfl, hb⟩ hs) hst₁ hc hb hL hstep
      | handler n cs hb =>
        exact handler_case hF hhost hB.facts (fun {c'} hs =>
          ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c')
            (LawfulCodeRank.handler_body_lt (vals V) xr n cs _)
            ⟨hst₁, rfl, hb⟩ hs) hst₁ hb hL hstep
      | frame n fi hb =>
        exact frame_case hF hhost hB.facts (fun {c'} hs =>
          ih (c := ⟨s, fi, _⟩) (d := ⟨t₁, fi, _⟩) (c' := c')
            (LawfulCodeRank.frame_body_lt (vals V) xr n fi _)
            ⟨hst₁, rfl, hb⟩ hs) hst₁ hb hL hstep
    · by_cases hcall : a.IsCallRef
      · exact .of_matched (Closure.call_case hF hhost hst₁ hab hcall hL hstep)
      · exact .of_matched (Closure.seq_case hst₁ hab ha hctx hcall hL hstep)
  | base hb =>
    rcases hb with hb | hcut
    · exact hB.step hst₁ hb hL hstep
    · obtain ⟨us, ws, k, x', y', hk, rfl, rfl⟩ := hcut
      exact .of_matched (Closure.cut_case hk hst₁
        (U := V ++ us) (X := x' ++ xr) (W := V ++ ws) (Y := y' ++ yr)
        (by simp) (by simp) hstep)

end DeferredClosure

/-- The source may have one forced local write pending before equal-frame synchronization. -/
def DeferredCfgRel (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop)
    (c d : Config H) : Prop :=
  ∃ c₁, Normalizes c c₁ ∧ CfgRel F (AdminsRel BI (WithCuts B)) c₁ d

theorem Normalizes.eq_of_terminal {P : Profile} {c d : Config H} {r : Result} (h : Normalizes c d)
    (hc : c.code = r.toAdmin) : d = c := by
  cases h with
  | refl => rfl
  | complete h =>
    have hs := h.step (P := P) (host := closedHost)
    obtain ⟨s, f, code⟩ := c
    dsimp only at hc
    subst code
    cases r with
    | values => exact (not_step_vals hs).elim
    | trap => exact (not_step_trap hs).elim
    | throw => exact (not_step_throwing hs).elim

/-- A genuine stuttering simulation, including the transient source frames. -/
theorem deferred_closure_configSim (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F closedHost) (hB : DeferredBaseSim P F BI B) :
    ∃ sim : ConfigSim P closedHost (DeferredCfgRel F BI B),
      sim.toForwardSim.measure = fun c => aszs c.code := by
  refine ⟨⟨⟨fun c => aszs c.code, ?_⟩, ?_⟩, rfl⟩
  · intro c c' d hs hrel
    obtain ⟨c₁, hn, hr⟩ := hrel
    cases hn with
    | refl =>
      obtain ⟨cn, d', hnorm, hm, hr'⟩ :=
        DeferredClosure.step_main hF hhost hB _ (Nat.lt_succ_self _) hr hs
      exact ⟨d', hm, cn, hnorm, hr'⟩
    | complete hn =>
      obtain rfl := hn.unique c' hs
      exact ⟨d, Or.inr ⟨rfl, hn.rank⟩, _, .refl _, hr⟩
  · intro c d r hrel hc
    obtain ⟨c₁, hn, hr⟩ := hrel
    obtain rfl := hn.eq_of_terminal (P := P) hc
    exact Closure.terminal_case hB.facts hr hc

/-- Completed runs retain final stores for subsequent invocations. -/
theorem deferred_closure_run_transport (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F closedHost) (hB : DeferredBaseSim P F BI B)
    {c d c' : Config H} {r : Result} (h : CfgRel F (AdminsRel BI B) c d)
    (hs : Steps P closedHost c c') (hc : c'.code = r.toAdmin) :
    ∃ d', Steps P closedHost d d' ∧ d'.code = r.toAdmin ∧ StoreRel F c'.store d'.store := by
  obtain ⟨sim, _⟩ := deferred_closure_configSim hF hhost hB
  obtain ⟨d₁, hd, cn, hn, hr⟩ := sim.toForwardSim.steps hs
    ⟨c, .refl _, h.mono (fun _ _ => AdminsRel.mono (fun _ _ => Or.inl))⟩
  obtain rfl := hn.eq_of_terminal (P := P) hc
  obtain ⟨d', hd', hc', hst⟩ := Closure.terminal_case_store hB.facts hr hc
  exact ⟨d', hd.trans hd', hc', hst⟩

theorem deferred_closure_diverges_transport (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F closedHost) (hB : DeferredBaseSim P F BI B)
    {c d : Config H} (h : CfgRel F (AdminsRel BI B) c d)
    (hd : Diverges P closedHost c) : Diverges P closedHost d := by
  obtain ⟨sim, _⟩ := deferred_closure_configSim hF hhost hB
  exact sim.toForwardSim.diverges hd
    ⟨c, .refl _, h.mono (fun _ _ => AdminsRel.mono (fun _ _ => Or.inl))⟩

end Silmaril.Wasm.Binaryen.CoalesceLocalsLite
