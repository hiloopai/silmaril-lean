module

public import Silmaril.Wasm.Execution.Core.Sim.TypedContext
public import Silmaril.Wasm.Execution.Core.Sim.Transport

@[expose] public section

/-! # Guarded closure for typed reverse simulations

The right configuration retains a typing witness in its active surrounding
context. Base steps may use that witness, while unchanged syntax and runtime
contexts reuse the ordinary closure helpers. The original untyped closure API
remains available independently.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Validation Numerics SingleThreaded

variable {H : Type}

local notation "noHost" => (fun _ _ _ _ => False)

/-- Base obligations whose step law may use typed reachability of the right
configuration. Exit and value transport do not need the guard. -/
structure TypedBaseSim (P : Profile) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop)
    (rank : List Admin → Nat := codeSize) : Prop where
  facts : BaseFacts P noHost F BI B rank
  step : ∀ {s t s' : Store H} {f f' : Frame} {vs : List Val}
    {x y rest rest' es' : List Admin},
    StoreRel F s t → B x y → AdminsRel BI B rest rest' →
    ContextTyped ⟨t, f, vals vs ++ y ++ rest'⟩ →
    Step P noHost ⟨s, f, vals vs ++ x ++ rest⟩ ⟨s', f', es'⟩ →
    ∃ (t' : Store H) (es'' : List Admin),
      (Relation.TransGen (Step P noHost) ⟨t, f, vals vs ++ y ++ rest'⟩ ⟨t', f', es''⟩ ∨
        (t' = t ∧ f' = f ∧ es'' = vals vs ++ y ++ rest' ∧
          rank es' < rank (vals vs ++ x ++ rest))) ∧
      StoreRel F s' t' ∧ AdminsRel BI B es' es''

def TypedStepIH (P : Profile) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop) (m : Nat)
    (rank : List Admin → Nat := codeSize) : Prop :=
  ∀ {c d c' : Config H}, rank c.code < m → CfgRel F (AdminsRel BI (WithCuts B)) c d →
    ContextTyped d → Step P noHost c c' → Matched P noHost F BI B c' d (rank c.code) rank

variable {P : Profile} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}
  {rank : List Admin → Nat} [LawfulCodeRank rank]

namespace Closure

theorem typed_base_case (hB : TypedBaseSim P F BI B rank) {s t s' : Store H} {f f' : Frame}
    {V : List Val} {x y L L' es' : List Admin} (hst : StoreRel F s t) (hxy : B x y)
    (hx : x.all Admin.isVal = false) (hL : AdminsRel BI (WithCuts B) L L')
    (htyped : ContextTyped ⟨t, f, vals V ++ y ++ L'⟩)
    (h : Step P noHost ⟨s, f, vals V ++ x ++ L⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P noHost F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ y ++ L'⟩
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
    obtain ⟨t', es'', hprog, hst'', hrel⟩ := hB.step hst hxy AdminsRel.nil (by simpa using htyped.suffix) hstep
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
    obtain ⟨t', j', hex, hst'⟩ := hB.facts.exit (f := f') hst hxy Exit.trap (vs := V)
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
    obtain ⟨t', j', hex, hst'⟩ := hB.facts.exit (f := f') hst hxy (Exit.throw xx) heq
    have hlift := Steps.append_right hex L'
    dsimp only at hlift
    refine Matched.of_steps hlift ⟨_, Or.inr ⟨rfl, ?_⟩, hst', rfl,
      AdminsRel.base (Or.inr ⟨ws, ws ++ us, throwing xx, r', j' ++ L', Or.inr ⟨xx, rfl⟩, rfl,
        by simp⟩)⟩
    rw [hVU, hxL]
    have := LawfulCodeRank.discard_lt (rank := rank) ws us (throwing xx) r r' hne
    simpa [vals, throwing, Val.toAdmin] using this

theorem typed_step_main (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F noHost) (hB : TypedBaseSim P F BI B rank) :
    ∀ m : Nat, TypedStepIH P F BI B m rank := by
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
  have hsegs := AdminsRel.segs (fun _ _ h => Or.inl (hB.facts.src h)) hxy
  obtain ⟨V, xs, ys, xr, yr, t₁, rfl, hseg, hact, hr, hrun, hst₁⟩ :=
    split_active hB.facts hsegs hstep.not_all_isVal [] hst
  refine Matched.of_steps (d₁ := ⟨t₁, f, vals V ++ ys ++ yr⟩)
    (steps_congr hrun (by simp) (by simp)) ?_
  have htyped₁ : ContextTyped ⟨t₁, f, vals V ++ ys ++ yr⟩ :=
    htyped.steps (steps_congr hrun (by simp) (by simp))
  have hL := hr.adminsRel
  have ih : TypedStepIH P F BI B (rank (vals V ++ xs ++ xr)) rank := ihm _ hm
  cases hseg with
  | @one a b hab =>
    have ha : a.val? = none := by simpa [Admin.isVal] using hact
    by_cases hctx : a.IsCtx
    · cases hab with
      | refl =>
        cases a
        case label n cont b =>
          exact label_case_of_body hF hhost hB.facts (fun {c'} hs =>
            ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c') (LawfulCodeRank.label_body_lt (vals V) xr n cont b)
              ⟨hst₁, rfl, AdminsRel.refl _⟩ htyped₁.label hs)
            hst₁ (InstrsRel.refl _) (AdminsRel.refl _) hL hstep
        case handler n cs b =>
          exact handler_case_of_body hF hhost hB.facts (fun {c'} hs =>
            ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c') (LawfulCodeRank.handler_body_lt (vals V) xr n cs b)
              ⟨hst₁, rfl, AdminsRel.refl _⟩ htyped₁.handler hs)
            hst₁ (AdminsRel.refl _) hL hstep
        case frame n fi b =>
          exact frame_case_of_body hF hhost hB.facts (fun {c'} hs =>
            ih (c := ⟨s, fi, _⟩) (d := ⟨t₁, fi, _⟩) (c' := c') (LawfulCodeRank.frame_body_lt (vals V) xr n fi b)
              ⟨hst₁, rfl, AdminsRel.refl _⟩ htyped₁.frame hs)
            hst₁ (AdminsRel.refl _) hL hstep
        all_goals exact hctx.elim
      | plain hi => exact hctx.elim
      | label n hc hb =>
        exact label_case_of_body hF hhost hB.facts (fun {c'} hs =>
          ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c') (LawfulCodeRank.label_body_lt (vals V) xr n _ _)
            ⟨hst₁, rfl, hb⟩ htyped₁.label hs) hst₁ hc hb hL hstep
      | handler n cs hb =>
        exact handler_case_of_body hF hhost hB.facts (fun {c'} hs =>
          ih (c := ⟨s, f, _⟩) (d := ⟨t₁, f, _⟩) (c' := c') (LawfulCodeRank.handler_body_lt (vals V) xr n cs _)
            ⟨hst₁, rfl, hb⟩ htyped₁.handler hs) hst₁ hb hL hstep
      | frame n fi hb =>
        exact frame_case_of_body hF hhost hB.facts (fun {c'} hs =>
          ih (c := ⟨s, fi, _⟩) (d := ⟨t₁, fi, _⟩) (c' := c') (LawfulCodeRank.frame_body_lt (vals V) xr n fi _)
            ⟨hst₁, rfl, hb⟩ htyped₁.frame hs) hst₁ hb hL hstep
    · by_cases hcall : a.IsCallRef
      · exact call_case hF hhost hst₁ hab hcall hL hstep
      · exact seq_case hst₁ hab ha hctx hcall hL hstep
  | base hb =>
    rcases hb with hb | hcut
    · exact typed_base_case hB hst₁ hb hact hL htyped₁ hstep
    · obtain ⟨us, ws, k, x', y', hk, rfl, rfl⟩ := hcut
      exact cut_case hk hst₁ (U := V ++ us) (X := x' ++ xr) (W := V ++ ws) (Y := y' ++ yr)
        (by simp) (by simp) hstep

end Closure

/-- A closure-related pair with a typing witness for the right configuration. -/
def TypedCfgRel (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop)
    (c d : Config H) : Prop :=
  CfgRel F (AdminsRel BI (WithCuts B)) c d ∧ ContextTyped d

/-- The guarded closure is a genuine simulation, with the right typing witness
retained after every nonempty match or stutter. -/
theorem typed_closure_configSim (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F noHost) (hB : TypedBaseSim P F BI B rank) :
    ∃ sim : ConfigSim P noHost (TypedCfgRel F BI B),
      sim.toForwardSim.measure = fun c => rank c.code := by
  refine ⟨⟨⟨fun c => rank c.code, ?_⟩, ?_⟩, rfl⟩
  · intro c c' d hs hrel
    obtain ⟨hr, ht⟩ := hrel
    obtain ⟨d', hm, hr'⟩ := Closure.typed_step_main hF hhost hB _ (Nat.lt_succ_self _) hr ht hs
    refine ⟨d', hm, hr', ?_⟩
    rcases hm with hm | ⟨rfl, _⟩
    · exact ht.steps hm.to_reflTransGen
    · exact ht
  · intro c d r hrel hc
    exact Closure.terminal_case hB.facts hrel.1 hc

/-- Completed runs retain the final store relation, as required when later
export invocations share the returned store. -/
theorem typed_closure_run_transport (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F noHost) (hB : TypedBaseSim P F BI B rank)
    {c d c' : Config H} {r : Result} (h : CfgRel F (AdminsRel BI B) c d)
    (ht : ContextTyped d) (hs : Steps P noHost c c') (hc : c'.code = r.toAdmin) :
    ∃ d', Steps P noHost d d' ∧ d'.code = r.toAdmin ∧ StoreRel F c'.store d'.store := by
  obtain ⟨sim, _⟩ := typed_closure_configSim hF hhost hB
  obtain ⟨d₁, hd, hr⟩ := sim.toForwardSim.steps hs
    ⟨h.mono (fun _ _ => AdminsRel.mono (fun _ _ => Or.inl)), ht⟩
  obtain ⟨d', hd', hc', hst⟩ := Closure.terminal_case_store hB.facts hr.1 hc
  exact ⟨d', hd.trans hd', hc', hst⟩

theorem typed_closure_diverges_transport (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F noHost) (hB : TypedBaseSim P F BI B rank)
    {c d : Config H} (h : CfgRel F (AdminsRel BI B) c d) (ht : ContextTyped d)
    (hd : Diverges P noHost c) : Diverges P noHost d := by
  obtain ⟨sim, _⟩ := typed_closure_configSim hF hhost hB
  exact sim.toForwardSim.diverges hd
    ⟨h.mono (fun _ _ => AdminsRel.mono (fun _ _ => Or.inl)), ht⟩

end Silmaril.Wasm.Execution.Core.Sim
