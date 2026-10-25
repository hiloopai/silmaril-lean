module

public import Silmaril.Wasm.Execution.Core.Sim.TypedClosure

@[expose] public section

/-! # A typed closure step may enlarge its runtime base relation

The input and output runtime relations may differ. Static source/exit/value
facts hold for both, while the local active base-step law maps input pairs to
output pairs. This supports finite wrapper-depth induction without pretending
that entering related callees keeps the same runtime bodies. Existing closure
and typed-closure APIs retain their definitions.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Validation Numerics SingleThreaded

variable {H : Type}

local notation "noHost" => (fun _ _ _ _ => False)

/-- The active base-step law between potentially different runtime relations.
All-value pairs are handled by the static value law; unrelated suffixes are
handled by the closure, so this callback sees only the active fragment. -/
structure TypedBaseStepTo (P : Profile) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B B' : List Admin → List Admin → Prop)
    (rank : List Admin → Nat := codeSize) : Prop where
  step : ∀ {s t s' : Store H} {f f' : Frame} {vs : List Val} {x y es' : List Admin},
    StoreRel F s t → B x y → x.all Admin.isVal = false →
    ContextTyped ⟨t, f, vals vs ++ y⟩ →
    Step P noHost ⟨s, f, vals vs ++ x⟩ ⟨s', f', es'⟩ →
    RankedMatched rank P noHost F BI B' ⟨s', f', es'⟩ ⟨t, f, vals vs ++ y⟩
      (rank (vals vs ++ x))

def TypedStepToIH (P : Profile) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B B' : List Admin → List Admin → Prop) (m : Nat)
    (rank : List Admin → Nat := codeSize) : Prop :=
  ∀ {c d c' : Config H}, rank c.code < m → CfgRel F (AdminsRel BI (WithCuts B)) c d →
    ContextTyped d → Step P noHost c c' → RankedMatched rank P noHost F BI B' c' d (rank c.code)

variable {P : Profile} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B B' : List Admin → List Admin → Prop}
  {rank : List Admin → Nat} [LawfulCodeRank rank]

namespace Closure

theorem typed_base_case_to (hfacts : BaseFacts P noHost F BI B rank)
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
    obtain ⟨t', j', hex, hst'⟩ := hfacts.exit (f := f') hst hxy Exit.trap (vs := V)
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
    obtain ⟨t', j', hex, hst'⟩ := hfacts.exit (f := f') hst hxy (Exit.throw xx) heq
    have hlift := Steps.append_right hex L'
    dsimp only at hlift
    refine Matched.of_steps hlift ⟨_, Or.inr ⟨rfl, ?_⟩, hst', rfl,
      AdminsRel.base (Or.inr ⟨ws, ws ++ us, throwing xx, r', j' ++ L', Or.inr ⟨xx, rfl⟩, rfl,
        by simp⟩)⟩
    rw [hVU, hxL]
    have := LawfulCodeRank.discard_lt (rank := rank) ws us (throwing xx) r r' hne
    simpa [vals, throwing, Val.toAdmin] using this

theorem typed_step_main_to (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F noHost)
    (hin : BaseFacts P noHost F BI B rank) (hout : BaseFacts P noHost F BI B' rank)
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
    split_active hin hsegs hstep.not_all_isVal [] hst
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
          exact label_case_of_body hF hhost hout (fun {c'} hs =>
            ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c') (LawfulCodeRank.label_body_lt (vals V) xr n cont b)
              ⟨hst₁, rfl, AdminsRel.refl _⟩ htyped₁.label hs)
            hst₁ (InstrsRel.refl _) (AdminsRel.refl _) hL hstep
        case handler n cs b =>
          exact handler_case_of_body hF hhost hout (fun {c'} hs =>
            ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c') (LawfulCodeRank.handler_body_lt (vals V) xr n cs b)
              ⟨hst₁, rfl, AdminsRel.refl _⟩ htyped₁.handler hs)
            hst₁ (AdminsRel.refl _) hL hstep
        case frame n fi b =>
          exact frame_case_of_body hF hhost hout (fun {c'} hs =>
            ih (c := ⟨s, fi, _⟩) (d := ⟨t₁, fi, _⟩) (c' := c') (LawfulCodeRank.frame_body_lt (vals V) xr n fi b)
              ⟨hst₁, rfl, AdminsRel.refl _⟩ htyped₁.frame hs)
            hst₁ (AdminsRel.refl _) hL hstep
        all_goals exact hctx.elim
      | plain hi => exact hctx.elim
      | label n hc hb =>
        exact label_case_of_body hF hhost hout (fun {c'} hs =>
          ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c') (LawfulCodeRank.label_body_lt (vals V) xr n _ _)
            ⟨hst₁, rfl, hb⟩ htyped₁.label hs) hst₁ hc (hb.mono hcuts) hL hstep
      | handler n cs hb =>
        exact handler_case_of_body hF hhost hout (fun {c'} hs =>
          ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c') (LawfulCodeRank.handler_body_lt (vals V) xr n cs _)
            ⟨hst₁, rfl, hb⟩ htyped₁.handler hs) hst₁ (hb.mono hcuts) hL hstep
      | frame n fi hb =>
        exact frame_case_of_body hF hhost hout (fun {c'} hs =>
          ih (c := ⟨s, fi, _⟩) (d := ⟨t₁, fi, _⟩) (c' := c') (LawfulCodeRank.frame_body_lt (vals V) xr n fi _)
            ⟨hst₁, rfl, hb⟩ htyped₁.frame hs) hst₁ (hb.mono hcuts) hL hstep
    · by_cases hcall : a.IsCallRef
      · exact call_case hF hhost hst₁ (hab.mono hcuts) hcall hL hstep
      · exact seq_case hst₁ (hab.mono hcuts) ha hctx hcall hL hstep
  | base hb =>
    rcases hb with hb | hcut
    · exact typed_base_case_to hin hbase hst₁ hb hact hL htyped₁ hstep
    · obtain ⟨us, ws, k, x', y', hk, rfl, rfl⟩ := hcut
      exact cut_case hk hst₁ (U := V ++ us) (X := x' ++ xr) (W := V ++ ws) (Y := y' ++ yr)
        (by simp) (by simp) hstep

end Closure

/-- One full contextual step can increase the runtime relation, retaining
related final stores, the exact same profile and every supported runtime context.
This is a one-step law; iteration needs a family of compatible output laws. -/
theorem typed_closure_step_to
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi) (hhost : HostRespects F noHost)
    (hin : BaseFacts P noHost F BI B rank) (hout : BaseFacts P noHost F BI B' rank)
    (hmono : ∀ x y, B x y → B' x y) (hbase : TypedBaseStepTo P F BI B B' rank)
    {c d c' : Config H} (related : CfgRel F (AdminsRel BI (WithCuts B)) c d)
    (typed : ContextTyped d) (step : Step P noHost c c') :
    RankedMatched rank P noHost F BI B' c' d (rank c.code) :=
  Closure.typed_step_main_to hF hhost hin hout hmono hbase _
    (Nat.lt_succ_self _) related typed step

/-- The runtime relation may move to the next member of a family after each
matched source step. The typing witness stays attached to the right side. -/
def TypedFamilyCfgRel (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : Nat → List Admin → List Admin → Prop)
    (c d : Config H) : Prop :=
  ∃ n, TypedCfgRel F BI (B n) c d

/-- Compatible enlarging runtime relations yield a genuine simulation. No
single finite relation is required to contain every later runtime phase. -/
theorem typed_family_configSim {Bs : Nat → List Admin → List Admin → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi) (hhost : HostRespects F noHost)
    (hfacts : ∀ n, BaseFacts P noHost F BI (Bs n) rank)
    (hmono : ∀ n x y, Bs n x y → Bs (n + 1) x y)
    (hbase : ∀ n, TypedBaseStepTo P F BI (Bs n) (Bs (n + 1)) rank) :
    ∃ sim : ConfigSim P noHost (TypedFamilyCfgRel F BI Bs),
      sim.toForwardSim.measure = fun c => rank c.code := by
  refine ⟨⟨⟨fun c => rank c.code, ?_⟩, ?_⟩, rfl⟩
  · intro c c' d hs hrel
    obtain ⟨n, hr, ht⟩ := hrel
    obtain ⟨d', hm, hr'⟩ := typed_closure_step_to hF hhost
      (hfacts n) (hfacts (n + 1)) (hmono n) (hbase n) hr ht hs
    refine ⟨d', hm, n + 1, hr', ?_⟩
    rcases hm with hm | ⟨rfl, _⟩
    · exact ht.steps hm.to_reflTransGen
    · exact ht
  · intro c d r hrel hc
    obtain ⟨n, hr, _⟩ := hrel
    exact Closure.terminal_case (hfacts n) hr hc

/-- Completed family runs retain the final store relation, even when the
runtime relation index grows an unbounded number of times during the run. -/
theorem typed_family_run_transport {Bs : Nat → List Admin → List Admin → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi) (hhost : HostRespects F noHost)
    (hfacts : ∀ n, BaseFacts P noHost F BI (Bs n) rank)
    (hmono : ∀ n x y, Bs n x y → Bs (n + 1) x y)
    (hbase : ∀ n, TypedBaseStepTo P F BI (Bs n) (Bs (n + 1)) rank)
    {n : Nat} {c d c' : Config H} {r : Result}
    (related : CfgRel F (AdminsRel BI (Bs n)) c d) (typed : ContextTyped d)
    (run : Steps P noHost c c') (terminal : c'.code = r.toAdmin) :
    ∃ d', Steps P noHost d d' ∧ d'.code = r.toAdmin ∧ StoreRel F c'.store d'.store := by
  obtain ⟨sim, _⟩ := typed_family_configSim hF hhost hfacts hmono hbase
  obtain ⟨d₁, hd, n', hr, _⟩ := sim.toForwardSim.steps run
    ⟨n, related.mono (fun _ _ => AdminsRel.mono (fun _ _ => Or.inl)), typed⟩
  obtain ⟨d', hd', hc', hst⟩ := Closure.terminal_case_store (hfacts n') hr terminal
  exact ⟨d', hd.trans hd', hc', hst⟩

theorem typed_family_diverges_transport {Bs : Nat → List Admin → List Admin → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi) (hhost : HostRespects F noHost)
    (hfacts : ∀ n, BaseFacts P noHost F BI (Bs n) rank)
    (hmono : ∀ n x y, Bs n x y → Bs (n + 1) x y)
    (hbase : ∀ n, TypedBaseStepTo P F BI (Bs n) (Bs (n + 1)) rank)
    {n : Nat} {c d : Config H} (related : CfgRel F (AdminsRel BI (Bs n)) c d)
    (typed : ContextTyped d) (diverges : Diverges P noHost c) : Diverges P noHost d := by
  obtain ⟨sim, _⟩ := typed_family_configSim hF hhost hfacts hmono hbase
  exact sim.toForwardSim.diverges diverges
    ⟨n, related.mono (fun _ _ => AdminsRel.mono (fun _ _ => Or.inl)), typed⟩

end Silmaril.Wasm.Execution.Core.Sim
