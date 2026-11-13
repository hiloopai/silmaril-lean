module

public import Silmaril.Proofs.Wasm.Game.LinkStartDiv.Sup

/-!
# Static links with start functions: the shared world is simulated by the composite,
divergence observed

The completed shared world `LSHc S P` (its instantiation running `S.linkedStarts`) is simulated
by the composite `CompC S P` of the completed provider and consumer link systems
**divergence-sensitively** (`LTS.DivSimulation`), for every profile (`subSim`).

Related states (`ISC`):

* before instantiation (`fresh`, `pre`), during the provider's start function (`prov`: the
  provider thread runs alone, `Split.SRel`; a `Soft` shared step is a provider step,
  `Split.prov_back_soft`; a shared result is a provider result, `Split.prov_back_end`);
* while the consumer runs its start function or an export call (`run`, `Split.CRel`), while the
  provider answers its call (`provc`, `Split.PRel`), and *doomed* (`doomed`: a provider trap
  inside a consumer call, after which the composite has already run to the consumer's trap);
* idle, dead, and the shared world's sinks.

Every shared step is matched by at least one composite step, except the steps of a doomed shared
configuration, which shrink its code (`Choice.trapped_step_lt`): the measure `itw`. The step
lemmas generalise those of `Silmaril.Proofs.Wasm.Game.Linking.Split.DivSub` from export calls to
both phases of the consumer.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.LinkStartDiv

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking
  Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril.Proofs.Wasm.Game.Linking.Split
  Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

variable {S : StartSetup} (P : Profile) (St : Static S.toSetup)

/-- The states of the shared world related to states of the composite. -/
inductive ISC : (LSHc S P).State → (CompC S P).State → Prop where
  | fresh : ISC (.inl .fresh) (.inl .fresh, .inl .fresh)
  | pre {l : List Nat} (hl : l = S.linkedStarts) :
      ISC (.inl (.inst (S.sc, .active {} [], l))) (.inl .fresh, .inl .pstart)
  | prov {σ π : Store Nat} {ts tp : Thread} {l : List Nat} (hl : l = S.consStart.toList)
      (h : SRel St σ ts π S.scs tp) (htp : ThreadOk π tp (resC startType)) :
      ISC (.inl (.inst (σ, ts, l))) (.inl (.inst (π, tp)), .inl .pwait)
  | idle {σ π κ : Store Nat} (hI : IdleT St σ π κ) :
      ISC (.inl (.ready σ)) (.inl (.ready π), .inl (.ready κ))
  | run (ph : Ph S) {σ π κ : Store Nat} {ts tc : Thread} (h : CRel St σ ts π κ tc)
      (hπ : StoreOk π) (htc : ThreadOk κ tc (resC (phF ph))) :
      ISC (.inl (shRun P ph (σ, ts))) (.inl (.ready π), .inl (cRun P ph (κ, tc)))
  | provc (ph : Ph S) {σ π κ : Store Nat} {ts tp tc : Thread} {e : S.consumerI.E.Op}
      (hco : CalloutAt κ tc e.1 e.2.1) (h : PRel St σ ts π tp κ tc e.1 e.2.1)
      (htc : ThreadOk κ tc (resC (phF ph))) (htp : ThreadOk π tp (stubT e))
      (hnr : ∀ r, ¬ ResultAt π tp r) (hlive : Live (tp.config π).code) :
      ISC (.inl (shRun P ph (σ, ts)))
        (.inl (.run e (π, tp)), .inl (cWait P ph e (S.consumerI.resumeK κ tc e)))
  | doomed (ph : Ph S) {σ π κ : Store Nat} {ts tcf : Thread} {x : (CompC S P).State}
      (E : Ctx) (F : Frame) (hts : ts.config σ = ⟨σ, F, E.fill [.trap]⟩)
      (hrun : Relation.ReflTransGen (CompC S P).Silent x
        (.inl (.ready π), .inl (cRun P ph (κ, tcf))))
      (hres : ResultAt κ tcf .trap) (hI : IdleT St σ π κ) :
      ISC (.inl (shRun P ph (σ, ts))) x
  | dead {xp : (LPc S P).State} : ISC (.inl .dead) (xp, .inl .dead)
  | sink {p : Pos _ _} {x : (CompC S P).State} : ISC (.inr p) x

/-- The size of the shared code. -/
noncomputable def itw : (LSHc S P).State → Nat
  | .inl (.inst c) => sizeOf (c.2.1.config c.1).code
  | .inl (.run _ c) => sizeOf (c.2.config c.1).code
  | _ => 0

/-- The outcome of a silent shared step. -/
def SMatched (y' y : (LSHc S P).State) (x : (CompC S P).State) : Prop :=
  (∃ x', Relation.TransGen (CompC S P).Silent x x' ∧ ISC P St y' x') ∨
    (ISC P St y' x ∧ itw P y' < itw P y)

/-- The outcome of a visible shared step. -/
def SVis (y' : (LSHc S P).State) (x : (CompC S P).State)
    (o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))) : Prop :=
  ∃ x', (CompC S P).Run x [o] x' ∧ ISC P St y' x'

variable {P St}

theorem itw_shRun (ph : Ph S) (c : Store Nat × Thread) :
    itw P (S := S) (.inl (shRun P ph c)) = sizeOf (c.2.config c.1).code := by
  cases ph <;> rfl

/-! ### Settling after a provider step -/

/-- A provider thread with a trap at its top level reaches the trap. -/
theorem prov_trap_reach {π : Store Nat} {tp : Thread} (hF : (tp.config π).frame = {})
    {W : List Val} {R : List Admin} (hdoom : (tp.config π).code = vals W ++ [.trap] ++ R) :
    ∃ tpf, Reach P (π, tp) (π, tpf) ∧ ResultAt π tpf .trap := by
  by_cases hne : W ≠ [] ∨ R ≠ []
  · have hc : tp.config π = ⟨π, {}, vals W ++ [.trap] ++ R⟩ := by
      rw [Thread.config_eta π tp, hF, hdoom]
    have hst : Step P noHost (tp.config π) ⟨π, {}, [.trap]⟩ := by
      rw [hc]
      exact .trapInstrs hne
    exact ⟨.active {} [.trap], .single ⟨{}, [.trap], rfl, hst⟩, rfl⟩
  · have hnil : W = [] ∧ R = [] := by simpa only [ne_eq, not_or, not_not] using hne
    refine ⟨tp, .refl, ?_⟩
    show (tp.config π).code = [.trap]
    rw [hdoom, hnil.1, hnil.2]
    rfl

/-- A provider trap: the composite runs to the consumer's trap, and the shared configuration is
doomed. -/
theorem isettle_trap (ph : Ph S) {σ π κ : Store Nat} {ts tp tc : Thread} {e : S.consumerI.E.Op}
    (hco : CalloutAt κ tc e.1 e.2.1) (hP : PRel St σ ts π tp κ tc e.1 e.2.1) (hκ : StoreOk κ)
    (hπ : StoreOk π) {W : List Val} {R : List Admin}
    (hdoom : (tp.config π).code = vals W ++ [.trap] ++ R) :
    ISC P St (.inl (shRun P ph (σ, ts)))
      (.inl (.run e (π, tp)), .inl (cWait P ph e (S.consumerI.resumeK κ tc e))) := by
  have hI : Idle St σ π κ := hP.world
  obtain ⟨ρp, Op, ρc, Oc, E', a', -, -, -, -, hF, -, -, hts⟩ := hP
  have hts' : ts.config σ = ⟨σ, ρc.frame (tc.config κ).frame,
      (Ctx.ext (ρc.ctx E') (W.map ρp.val) (ρp.code R)).fill [.trap]⟩ := by
    rw [hts, hdoom, ← Ctx.fill_ext]
    simp
  obtain ⟨tpf, hreach, hr⟩ := prov_trap_reach (P := P) hF hdoom
  have hp : Relation.ReflTransGen (CompC S P).Silent
      (.inl (.run e (π, tp)), .inl (cWait P ph e (S.consumerI.resumeK κ tc e)))
      (.inl (.run e (π, tpf)), .inl (cWait P ph e (S.consumerI.resumeK κ tc e))) :=
    ip_reach P hreach
  obtain ⟨E, a, hd⟩ := hco
  have hrt : S.consumerI.resumeK κ tc e .trap = (κ, .active (tc.config κ).frame (E.fill [.trap])) := by
    show (κ, resumeResult κ tc .trap) = _
    unfold resumeResult
    simp only [hd, Result.toAdmin]
  have hs : (CompC S P).Silent
      (.inl (.run e (π, tpf)), .inl (cWait P ph e (S.consumerI.resumeK κ tc e)))
      (.inl (.ready π), .inl (cRun P ph (κ, .active (tc.config κ).frame (E.fill [.trap])))) := by
    have h := isync_ret P ph (e := e) (c := (κ, tc)) (w := .trap) hr rfl
    rw [hrt] at h
    exact h
  have hc : Relation.ReflTransGen (CompC S P).Silent
      (.inl (.ready π), .inl (cRun P ph (κ, .active (tc.config κ).frame (E.fill [.trap]))))
      (.inl (.ready π), .inl (cRun P ph (κ, .active (tc.config κ).frame [.trap]))) :=
    ic_reach P ph (fill_trap_reach P κ E (tc.config κ).frame)
  exact .doomed ph _ _ hts' ((hp.tail hs).trans hc) rfl ⟨hI, hπ, hκ⟩

/-- The provider returns values: it answers and the consumer resumes. -/
theorem isettle_values (ph : Ph S) (hS : S.Scalar) {σ π κ : Store Nat} {ts tp tc : Thread}
    {e : S.consumerI.E.Op} (hco : CalloutAt κ tc e.1 e.2.1)
    (hP : PRel St σ ts π tp κ tc e.1 e.2.1) (htc : ThreadOk κ tc (resC (phF ph)))
    (htp : ThreadOk π tp (stubT e)) {vs : List Val} (hr : ResultAt π tp (.values vs)) :
    ∃ x', Relation.ReflTransGen (CompC S P).Silent
        (.inl (.run e (π, tp)), .inl (cWait P ph e (S.consumerI.resumeK κ tc e))) x' ∧
      ISC P St (.inl (shRun P ph (σ, ts))) x' := by
  have hκ : StoreOk κ := threadOk_storeOk htc
  have hπ : StoreOk π := threadOk_storeOk htp
  obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hP.world
  have hwc : S.consumerI.WellFormed κ := hS.consumer.of_funcs hκ hW.fκ
  have hv : List.Forall₂ ScalarType.HasVal (S.stubTypes.get e.1).results vs :=
    stub_results_typed htp hr
  have hw : Answer.ofResult? (S.stubTypes.get e.1) (.values vs) = some (.values ⟨vs, hv⟩) := by
    simp only [Answer.ofResult?]
    rw [dite_eq_left hv]
  obtain ⟨-, hC⟩ := hP.ret hr (fun vs' h => by cases h; exact ⟨_, hv⟩)
  have htc' : ThreadOk κ (resumeResult κ tc (.values vs)) (resC (phF ph)) :=
    resume_values_typed P hκ htc hwc hco hv
  exact ⟨_, .single (isync_ret P ph (c := (κ, tc)) hr hw), .run ph hC hπ htc'⟩

/-- **Settling after a provider step**: a provider result of values is answered and resumes
the consumer, a trapping provider makes the shared configuration doomed, a live provider keeps
running. -/
theorem isettle (ph : Ph S) (hS : S.Scalar) {σ π κ : Store Nat} {ts tp tc : Thread}
    {e : S.consumerI.E.Op} (hco : CalloutAt κ tc e.1 e.2.1)
    (hP : PRel St σ ts π tp κ tc e.1 e.2.1) (htc : ThreadOk κ tc (resC (phF ph)))
    (htp : ThreadOk π tp (stubT e)) :
    ∃ x', Relation.ReflTransGen (CompC S P).Silent
        (.inl (.run e (π, tp)), .inl (cWait P ph e (S.consumerI.resumeK κ tc e))) x' ∧
      ISC P St (.inl (shRun P ph (σ, ts))) x' := by
  have hκ : StoreOk κ := threadOk_storeOk htc
  have hπ : StoreOk π := threadOk_storeOk htp
  by_cases hres : ∃ r, ResultAt π tp r
  · obtain ⟨r, hr⟩ := hres
    cases r with
    | throw a' => exact absurd rfl ((hP.ret hr (fun _ h => by cases h)).1 a')
    | values vs => exact isettle_values ph hS hco hP htc htp hr
    | trap =>
      have hd : (tp.config π).code = vals [] ++ [.trap] ++ [] := by
        simpa [ResultAt, Result.toAdmin] using hr
      exact ⟨_, .refl, isettle_trap ph hco hP hκ hπ hd⟩
  · have hnr : ∀ r, ¬ ResultAt π tp r := fun r hr => hres ⟨r, hr⟩
    rcases doomed_or_live hnr with ⟨W, R, hdoom⟩ | hlive
    · exact ⟨_, .refl, isettle_trap ph hco hP hκ hπ hdoom⟩
    · exact ⟨_, .refl, .provc ph hco hP htc htp hnr hlive⟩

/-! ### Shared steps while the consumer runs -/

/-- A shared step while the consumer runs host-free code. -/
theorem itau_run_running (ph : Ph S) {σ π κ : Store Nat} {ts tc : Thread}
    {y : Store Nat × Thread} (hC : CRel St σ ts π κ tc) (hπ : StoreOk π)
    (htc : ThreadOk κ tc (resC (phF ph))) (hy : InternalP P (σ, ts) y)
    (hstat : statusP P κ tc = .running) :
    ∃ x', Relation.TransGen (CompC S P).Silent (.inl (.ready π), .inl (cRun P ph (κ, tc))) x' ∧
      ISC P St (.inl (shRun P ph y)) x' := by
  have hκ : StoreOk κ := threadOk_storeOk htc
  obtain ⟨⟨κ', tc'⟩, hc⟩ := statusP_running_inv hstat
  obtain ⟨σ', ts', hx', hC'⟩ := hC.step hc
  rcases next_eq_or_soft hy hx' with heq | hsoft
  · obtain ⟨-, htc', -⟩ := InternalP.preserves hκ htc hc
    exact ⟨_, .single (ic_tau P ph hc), heq ▸ .run ph hC' hπ htc'⟩
  · rcases y with ⟨σy, ty⟩
    obtain ⟨fy, cy, rfl, -⟩ := hy
    obtain ⟨X', hstep, hst', hRs⟩ := hC.soft_back hsoft
    have hy1 : σy = σ := hst'
    subst hy1
    obtain ⟨-, htcs, -⟩ := InternalP.preserves hκ htc hstep
    exact ⟨_, .single (ic_tau P ph hstep), .run ph hRs hπ htcs⟩

/-- A shared step while the consumer is at a callout: the `call_ref` into the provider. -/
theorem itau_run_callout (ph : Ph S) (hS : S.Scalar) {σ π κ : Store Nat} {ts tc : Thread}
    {y : Store Nat × Thread} (hC : CRel St σ ts π κ tc) (hπ : StoreOk π)
    (htc : ThreadOk κ tc (resC (phF ph))) (hy : InternalP P (σ, ts) y) {h : Nat}
    {args : List Val} (hstat : statusP P κ tc = .callout h args) :
    ∃ x', Relation.TransGen (CompC S P).Silent (.inl (.ready π), .inl (cRun P ph (κ, tc))) x' ∧
      ISC P St (.inl (shRun P ph y)) x' := by
  have hκ : StoreOk κ := threadOk_storeOk htc
  obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hC.world
  have hwc : S.consumerI.WellFormed κ := hS.consumer.of_funcs hκ hW.fκ
  have hwp : S.providerI.WellFormed π := hS.provider.of_funcs hπ hW.fπ
  obtain ⟨E, a, hd⟩ := statusP_callout_inv hstat
  have hco : CalloutAt κ tc h args := ⟨E, a, hd⟩
  obtain ⟨hlt, hargs⟩ := stub_args_typed (P := P) htc hwc hco
  let e : S.consumerI.E.Op := ⟨⟨h, hlt⟩, ⟨args, hargs⟩⟩
  have hop : S.consumerI.importOp? h args = some e := importOp?_stub hlt hargs
  obtain ⟨hlt', tp₀, ts₁, hp₀, hs₁, hP, -⟩ := hC.call (P := P) hco hargs
  have hy' : y = (σ, ts₁) := by
    rcases next_eq_or_soft hy hs₁ with h' | hsoft
    · exact h'
    · obtain ⟨X', hstep, -, -⟩ := hC.soft_back hsoft
      exact absurd hstep (calloutAt_no_internal hco _)
  subst hy'
  have hp₀' : InternalP P (π, S.providerI.initThread e) (π, tp₀) := hp₀
  have htp₀ : ThreadOk π tp₀ (stubT e) := (InternalP.preserves hπ (hwp.init_typed e) hp₀').2.1
  obtain ⟨x', hset, hSC⟩ := isettle ph hS (e := e) hco hP htc htp₀
  exact ⟨x', .head' (isync_call P ph (c := (κ, tc)) ⟨h, args, hco, hop⟩) (.head (ip_tau P hp₀') hset),
    hSC⟩

/-- **A shared step while the consumer runs** (its start function or an export call). -/
theorem itau_run (ph : Ph S) (hS : S.Scalar) {σ π κ : Store Nat} {ts tc : Thread}
    {y : Store Nat × Thread} (hC : CRel St σ ts π κ tc) (hπ : StoreOk π)
    (htc : ThreadOk κ tc (resC (phF ph))) (hy : InternalP P (σ, ts) y) :
    ∃ x', Relation.TransGen (CompC S P).Silent (.inl (.ready π), .inl (cRun P ph (κ, tc))) x' ∧
      ISC P St (.inl (shRun P ph y)) x' := by
  have hκ : StoreOk κ := threadOk_storeOk htc
  cases hstat : statusP P κ tc with
  | returned cr =>
    obtain ⟨r, hr⟩ := status_result hstat
    exact absurd hy (crel_no_step_of_result hC hr y)
  | stuck => exact absurd hstat (statusP_ne_stuck hκ htc)
  | running => exact itau_run_running ph hC hπ htc hy hstat
  | callout h args => exact itau_run_callout ph hS hC hπ htc hy hstat

/-- **A shared step while the provider runs** inside the consumer's call. -/
theorem itau_prov (ph : Ph S) (hS : S.Scalar) {σ π κ : Store Nat} {ts tp tc : Thread}
    {e : S.consumerI.E.Op} {y : Store Nat × Thread} (hco : CalloutAt κ tc e.1 e.2.1)
    (hP : PRel St σ ts π tp κ tc e.1 e.2.1) (htc : ThreadOk κ tc (resC (phF ph)))
    (htp : ThreadOk π tp (stubT e)) (hnr : ∀ r, ¬ ResultAt π tp r)
    (hlive : Live (tp.config π).code) (hy : InternalP P (σ, ts) y) :
    ∃ x', Relation.TransGen (CompC S P).Silent
        (.inl (.run e (π, tp)), .inl (cWait P ph e (S.consumerI.resumeK κ tc e))) x' ∧
      ISC P St (.inl (shRun P ph y)) x' := by
  have hπ : StoreOk π := threadOk_storeOk htp
  obtain ⟨⟨π', tp'⟩, hpst⟩ := prov_step (P := P) hP htp hnr
  obtain ⟨σ', ts', hx', hP'⟩ := hP.step hpst
  rcases next_eq_or_soft hy hx' with heq | hsoft
  · obtain ⟨-, htp', -⟩ := InternalP.preserves hπ htp hpst
    obtain ⟨x', hset, hSC⟩ := isettle ph hS hco hP' htc htp'
    exact ⟨x', .head' (ip_tau P hpst) hset, heq ▸ hSC⟩
  · rcases y with ⟨σy, ty⟩
    obtain ⟨fy, cy, rfl, -⟩ := hy
    obtain ⟨X', hstep, hst', hPs⟩ := hP.soft_back hlive hsoft
    have hy1 : σy = σ := hst'
    subst hy1
    obtain ⟨-, htps, -⟩ := InternalP.preserves hπ htp hstep
    obtain ⟨x', hset, hSC⟩ := isettle ph hS hco hPs htc htps
    exact ⟨x', .head' (ip_tau P hstep) hset, hSC⟩

/-- **A shared step of a doomed configuration**: no composite step, the code shrinks. -/
theorem itau_doomed (ph : Ph S) {σ π κ : Store Nat} {ts tcf : Thread} {x : (CompC S P).State}
    {E : Ctx} {F : Frame} (hts : ts.config σ = ⟨σ, F, E.fill [.trap]⟩)
    (hrun : Relation.ReflTransGen (CompC S P).Silent x
      (.inl (.ready π), .inl (cRun P ph (κ, tcf))))
    (hres : ResultAt κ tcf .trap) (hI : IdleT St σ π κ) {y : Store Nat × Thread}
    (hy : InternalP P (σ, ts) y) :
    ISC P St (.inl (shRun P ph y)) x ∧
      itw P (.inl (shRun P ph y)) < itw P (.inl (shRun P ph (σ, ts))) := by
  rcases y with ⟨σy, ty⟩
  obtain ⟨fy, cy, rfl, hstep⟩ := hy
  have hstep' : Step P noHost ⟨σ, F, E.fill [.trap]⟩ ⟨σy, fy, cy⟩ := hts ▸ hstep
  obtain ⟨hσ, hF, E', hE'⟩ := Choice.step_doomed hstep'
  have hlt : sizeOf cy < sizeOf (E.fill [.trap]) := Choice.trapped_step_lt hstep'
  have hσ' : σy = σ := hσ
  subst hσ'
  have hts' : (Thread.active fy cy).config σy = ⟨σy, F, E'.fill [.trap]⟩ := by
    have h1 : fy = F := hF
    have h2 : cy = E'.fill [.trap] := hE'
    rw [← h1, ← h2]
    rfl
  refine ⟨.doomed ph E' F hts' hrun hres hI, ?_⟩
  rw [itw_shRun, itw_shRun]
  show sizeOf cy < sizeOf (ts.config σy).code
  rw [hts]
  exact hlt

/-! ### The start functions -/

theorem toList_cons {o : Option Nat} {a : Nat} {rest : List Nat} (h : a :: rest = o.toList) :
    o = some a ∧ rest = [] := by
  cases o with
  | none => cases h
  | some b => cases h; exact ⟨rfl, rfl⟩

theorem toList_nil {o : Option Nat} (h : [] = o.toList) : o = none := by
  cases o with
  | none => rfl
  | some b => cases h

/-- The linked start sequence starts with the provider's start function, if any. -/
theorem linkedStarts_cons {a : Nat} {rest : List Nat} (h : a :: rest = S.linkedStarts) :
    (S.provStart = some a ∧ rest = S.consStart.toList) ∨
      (S.provStart = none ∧ S.consStart = some a ∧ rest = []) := by
  rcases Option.eq_none_or_eq_some S.provStart with hps | ⟨b, hps⟩
  · have h' : a :: rest = S.consStart.toList := by
      rw [h, StartSetup.linkedStarts, hps]
      rfl
    obtain ⟨hcs, hr⟩ := toList_cons h'
    exact .inr ⟨hps, hcs, hr⟩
  · have h' : a :: rest = b :: S.consStart.toList := by
      rw [h, StartSetup.linkedStarts, hps]
      rfl
    obtain ⟨rfl, hr⟩ := List.cons.inj h'
    exact .inl ⟨hps, hr⟩

theorem linkedStarts_nil (h : [] = S.linkedStarts) : S.provStart = none ∧ S.consStart = none := by
  rcases Option.eq_none_or_eq_some S.provStart with hps | ⟨b, hps⟩
  · have h' : [] = S.consStart.toList := by
      rw [h, StartSetup.linkedStarts, hps]
      rfl
    exact ⟨hps, toList_nil h'⟩
  · rw [StartSetup.linkedStarts, hps] at h
    cases h

/-- A provider step of its start function. -/
theorem ipi_tau {c c' : Store Nat × Thread} {xc : (LCc S P).State} (h : InternalP P c c') :
    (CompC S P).Silent (.inl (.inst c), xc) (.inl (.inst c'), xc) :=
  LTS.CompStep.tau₁ (CStep.base (.itau h))

/-- A provider run of its start function. -/
theorem ipi_reach {c c' : Store Nat × Thread} {xc : (LCc S P).State} (h : Reach P c c') :
    Relation.ReflTransGen (CompC S P).Silent (.inl (.inst c), xc) (.inl (.inst c'), xc) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (ipi_tau hst)

/-- The provider asked to instantiate. -/
theorem sync_askInst :
    (CompC S P).Silent (.inl .fresh, .inl .pstart)
      (.inl (.inst (S.sp, startThread S.provStart)), .inl .pwait) :=
  LTS.CompStep.sync (.ask none) (CStep.base .askInst) (CStep.base .pcall)

/-- The provider's start function returned: the consumer's begins. -/
theorem sync_ready {π : Store Nat} {tp : Thread} (hr : ResultAt π tp (.values [])) :
    (CompC S P).Silent (.inl (.inst (π, tp)), .inl .pwait)
      (.inl (.ready π), .inl (.inst (S.scs, startThread S.consStart))) :=
  LTS.CompStep.sync (.ans (m := none) .ready) (CStep.base (.iready ⟨hr, rfl⟩)) (CStep.base .pready)

/-- The provider's start function failed. -/
theorem sync_fail {π : Store Nat} {tp : Thread} {b : Behaviour Val} (hf : StartFailed (π, tp) b) :
    (CompC S P).Silent (.inl (.inst (π, tp)), .inl .pwait) (.inl .dead, .inl (.pfail b)) :=
  LTS.CompStep.sync (.ans (m := none) (.fail b)) (CStep.base (.ifail hf)) (CStep.base (.pfail b))

/-- The consumer's start function returned at once. -/
theorem vis_ready_finished (π κ : Store Nat) :
    (CompC S P).step (.inl (.ready π), .inl (.inst (κ, .active {} [])))
      (some (ansInst .ready)) (.inl (.ready π), .inl (.ready κ)) :=
  LTS.CompStep.right _ (CStep.base (.iready ⟨LinkStartDiv.resultAt_finished _, rfl⟩))

variable (hOp : St.Op = S.provOwn) (hOc : St.Oc = S.consOwn)

include hOc in
/-- The consumer's start function, invoked by the shared world, begins in the composite. -/
theorem cons_begin (hS : S.Scalar) {σ π : Store Nat} {c : Nat} (hI : Idle St σ π S.scs)
    (hπ : StoreOk π) (hcs : S.consStart = some c) :
    ISC P St (.inl (.inst (σ, .pending c [], []))) (.inl (.ready π), .inl (.inst (S.scs, .pending c []))) :=
  .run none (hI.startCons (LinkStart.StartSetup.consStart_own S St hOc c hcs)) hπ
    (start_typed hS.consumer (S.consStartTyped c hcs))

include hOc in
/-- The provider's start function has returned and the shared world invokes the consumer's. -/
theorem sprov_next (hS : S.Scalar) {σ π : Store Nat} {ts tp : Thread} {c : Nat}
    {rest : List Nat} (hl : c :: rest = S.consStart.toList) (h : SRel St σ ts π S.scs tp)
    (htp : ThreadOk π tp (resC startType)) (hres : ResultAt σ ts (.values [])) :
    ∃ x', Relation.TransGen (CompC S P).Silent (.inl (.inst (π, tp)), .inl .pwait) x' ∧
      ISC P St (.inl (.inst (σ, .pending c [], rest))) x' := by
  obtain ⟨π', tp', hreach, hr', hI⟩ := prov_back_end (P := P) hres h htp
  obtain ⟨hcs, rfl⟩ := toList_cons hl
  have hπ' : StoreOk π' := (reachableP_typed hreach (threadOk_storeOk htp) htp).1
  have e : startThread S.consStart = .pending c [] := by rw [hcs]; rfl
  have hsync := sync_ready (S := S) (P := P) hr'
  rw [e] at hsync
  exact ⟨_, Relation.TransGen.tail' (ipi_reach hreach) hsync, cons_begin hOc hS hI hπ' hcs⟩

/-- **A shared step of the provider's start function** is a provider step. -/
theorem sprov_run {σ π : Store Nat} {ts tp : Thread} {l : List Nat}
    (hl : l = S.consStart.toList) (h : SRel St σ ts π S.scs tp)
    (htp : ThreadOk π tp (resC startType)) {y : Store Nat × Thread} (hi : InternalP P (σ, ts) y) :
    ∃ x', Relation.TransGen (CompC S P).Silent (.inl (.inst (π, tp)), .inl .pwait) x' ∧
      ISC P St (.inl (.inst (y.1, y.2, l))) x' := by
  have hπ : StoreOk π := threadOk_storeOk htp
  cases hstat : statusP P π tp with
  | returned cr =>
    obtain ⟨r, hr⟩ := status_result hstat
    obtain ⟨-, ⟨ρ, hres⟩, -⟩ := h.result hr
    exact absurd hi (resultAt_no_internal hres y)
  | stuck => exact absurd hstat (statusP_ne_stuck hπ htp)
  | callout h' args => exact absurd hstat h.no_callout
  | running =>
    obtain ⟨⟨π₁, tp₁⟩, hy⟩ := statusP_running_inv hstat
    obtain ⟨σ₁, ts₁, hx₁, hR₁⟩ := h.step hy
    rcases next_eq_or_soft hi hx₁ with rfl | hsoft
    · have htp₁ : ThreadOk π₁ tp₁ (resC startType) := (InternalP.preserves hπ htp hy).2.1
      exact ⟨_, .single (ipi_tau hy), .prov hl hR₁ htp₁⟩
    · obtain ⟨X', hstep, hRs⟩ := prov_back_soft hi h hsoft
      have htps : ThreadOk π (.active (tp.config π).frame X') (resC startType) :=
        (InternalP.preserves hπ htp hstep).2.1
      exact ⟨_, .single (ipi_tau hstep), .prov hl hRs htps⟩

include hOc in
/-- Silent shared steps during the provider's start function. -/
theorem stau_prov (hS : S.Scalar) {σ π : Store Nat} {ts tp : Thread} {l : List Nat}
    (hl : l = S.consStart.toList) (h : SRel St σ ts π S.scs tp)
    (htp : ThreadOk π tp (resC startType)) {y' : (LSH S P).State}
    (hs : (LSH S P).step (.inst (σ, ts, l)) none y') :
    SMatched P St (.inl y') (.inl (.inst (σ, ts, l))) (.inl (.inst (π, tp)), .inl .pwait) := by
  cases hs with
  | itau hs' =>
    cases hs' with
    | run hi => exact .inl (sprov_run hl h htp hi)
    | next hres => exact .inl (sprov_next hOc hS hl h htp hres)

include hOp hOc in
/-- The first start function of the linked sequence is invoked. -/
theorem spre_next (hS : S.Scalar) {a : Nat} {rest : List Nat} (hl : a :: rest = S.linkedStarts) :
    ∃ x', Relation.TransGen (CompC S P).Silent (.inl .fresh, .inl .pstart) x' ∧
      ISC P St (.inl (.inst (S.sc, .pending a [], rest))) x' := by
  have hask := sync_askInst (S := S) (P := P)
  rcases linkedStarts_cons hl with ⟨hps, hrest⟩ | ⟨hps, hcs, rfl⟩
  · have e : startThread S.provStart = .pending a [] := by rw [hps]; rfl
    rw [e] at hask
    have htp : ThreadOk S.sp (.pending a []) (resC startType) :=
      start_typed hS.provider (S.provStartTyped a hps)
    exact ⟨_, .single hask,
      .prov hrest (Idle.startProv St.idle (LinkStart.StartSetup.provStart_own S St hOp a hps)) htp⟩
  · have e : startThread S.provStart = .active {} [] := by rw [hps]; rfl
    rw [e] at hask
    have hready := sync_ready (S := S) (P := P) (LinkStartDiv.resultAt_finished S.sp)
    have e' : startThread S.consStart = .pending a [] := by rw [hcs]; rfl
    rw [e'] at hready
    exact ⟨_, .tail (.single hask) hready,
      cons_begin hOc hS St.idle (ScalarInstance.WellFormed.storeOk hS.provider) hcs⟩

include hOp hOc in
/-- Silent shared steps right after the instantiation question. -/
theorem stau_pre (hS : S.Scalar) {l : List Nat} (hl : l = S.linkedStarts)
    {y' : (LSH S P).State} (hs : (LSH S P).step (.inst (S.sc, .active {} [], l)) none y') :
    SMatched P St (.inl y') (.inl (.inst (S.sc, .active {} [], l))) (.inl .fresh, .inl .pstart) := by
  cases hs with
  | itau hs' =>
    cases hs' with
    | run hi => exact absurd hi (resultAt_no_internal (LinkStartDiv.resultAt_finished _) _)
    | next _ => exact .inl (spre_next hOp hOc hS hl)

/-- A shared step in a phase, as a host-free step. -/
theorem stau_phase {ph : Ph S} {c : Store Nat × Thread} {y' : (LSH S P).State}
    (hs : (LSH S P).step (shRun P ph c) none y') :
    ∃ c', InternalP P c c' ∧ y' = shRun P ph c' :=
  sh_silent P ph hs

include hOp hOc in
/-- **Silent shared steps** are matched divergence-sensitively. -/
theorem isc_tau (hS : S.Scalar) {y y' : (LSHc S P).State} {x : (CompC S P).State}
    (hR : ISC P St y x) (h : (LSHc S P).step y none y') : SMatched P St y' y x := by
  obtain ⟨y₀, rfl⟩ : ∃ y₀, y = .inl y₀ := by
    cases hR <;> first | exact ⟨_, rfl⟩ | cases h
  obtain ⟨y₁, hs, rfl⟩ := complete_silent h
  cases hR with
  | fresh => cases hs
  | pre hl => exact stau_pre hOp hOc hS hl hs
  | prov hl hs' htp => exact stau_prov hOc hS hl hs' htp hs
  | idle _ => cases hs
  | run ph hC hπ htc =>
    obtain ⟨c', hi, rfl⟩ := stau_phase hs
    exact .inl (itau_run ph hS hC hπ htc hi)
  | provc ph hco hP htc htp hnr hlive =>
    obtain ⟨c', hi, rfl⟩ := stau_phase hs
    exact .inl (itau_prov ph hS hco hP htc htp hnr hlive hi)
  | doomed ph E F hts hrun hres hI =>
    obtain ⟨c', hi, rfl⟩ := stau_phase hs
    exact .inr (itau_doomed ph hts hrun hres hI hi)
  | dead => cases hs

/-! ### Visible steps -/

/-- A shared Opponent move into a sink, answered by the consumer's sink. -/
theorem ssink {xp : (LPc S P).State} {xc : (LC S P).State} (hc : InstSystem.cpos _ xc = .idle)
    {y : (LSH S P).State} (hy : InstSystem.pos (ShSys S.toSetup P S.linkedStarts) y = .idle)
    {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))} {p : Pos _ _}
    (ho : o.IsO) (hst : Step (InstSystem.pos (ShSys S.toSetup P S.linkedStarts) y) o p) :
    SVis P St (.inr p) (xp, .inl xc) o := by
  rw [hy] at hst
  cases o with
  | inl e => cases hst
  | inr g =>
    obtain ⟨p', ho', hst'⟩ := upper_idle (E' := S.consumerI.E.withInst (Behaviour Val)) hst
    exact ⟨_, .vis (LTS.CompStep.right g (CStep.sink ho' (hc ▸ hst'))) (.nil _), .sink⟩

/-- A consumer whose thread returned `values []` is at the result of the shared world, which
it then answers. -/
theorem cons_result (Q : Profile) (hS : S.Scalar) {ft : FnType} {σ π κ : Store Nat} {ts tc : Thread}
    {rs : Result} (hC : CRel St σ ts π κ tc) (hπ : StoreOk π) (htc : ThreadOk κ tc (resC ft))
    (final : ResultAt σ ts rs) :
    ∃ r, ResultAt κ tc r ∧ (∃ ρ : Ren, ρ.result r = rs) ∧ (∀ a, r ≠ .throw a) ∧
      IdleT St σ π κ := by
  have hκ : StoreOk κ := threadOk_storeOk htc
  have fin : ∀ r', ResultAt κ tc r' → ∃ r, ResultAt κ tc r ∧ (∃ ρ : Ren, ρ.result r = rs) ∧
      (∀ a, r ≠ .throw a) ∧ IdleT St σ π κ := fun r' hr' => by
    obtain ⟨hnt, ⟨ρ, hres⟩, hI⟩ := hC.result hr'
    exact ⟨r', hr', ⟨ρ, resultAt_unique hres final⟩, hnt, hI, hπ, hκ⟩
  cases hstat : statusP Q κ tc with
  | returned cr =>
    obtain ⟨r, hr⟩ := status_result hstat
    exact fin r hr
  | stuck => exact absurd hstat (statusP_ne_stuck hκ htc)
  | running =>
    obtain ⟨⟨κ', tc'⟩, hc⟩ := statusP_running_inv hstat
    obtain ⟨σ', ts', hx', -⟩ := hC.step hc
    exact absurd hx' (resultAt_no_internal final _)
  | callout h args =>
    obtain ⟨E, a, hd⟩ := statusP_callout_inv hstat
    have hco : CalloutAt κ tc h args := ⟨E, a, hd⟩
    obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hC.world
    have hwc : S.consumerI.WellFormed κ := hS.consumer.of_funcs hκ hW.fκ
    obtain ⟨hlt, hargs⟩ := stub_args_typed (P := Q) htc hwc hco
    obtain ⟨-, -, ts₁, -, hs₁, -⟩ := hC.call (P := Q) hco hargs
    exact absurd hs₁ (resultAt_no_internal final _)

/-- The result of a consumer's start function is not renamed. -/
theorem start_result_eq {κ : Store Nat} {tc : Thread} {r rs : Result}
    (htc : ThreadOk κ tc (resC startType)) (hr : ResultAt κ tc r) (hρ : ∃ ρ : Ren, ρ.result r = rs) :
    r = rs := by
  obtain ⟨ρ, hρ⟩ := hρ
  rw [← hρ, ren_start_result (result_of_start_typed htc hr)]

/-- The consumer's start function answers as the shared world does. -/
theorem svis_run_none (hS : S.Scalar) {σ π κ : Store Nat} {ts tc : Thread}
    (hC : CRel St σ ts π κ tc) (hπ : StoreOk π) (htc : ThreadOk κ tc (resC startType))
    {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))} {y' : (LSH S P).State}
    (hb : (LSH S P).step (.inst (σ, ts, [])) (some o) y') :
    SVis P St (.inl y') (.inl (.ready π), .inl (.inst (κ, tc))) o := by
  cases hb with
  | icall _ => exact Linking.DivShared.closed_op_elim ‹_›
  | iready hr =>
    obtain ⟨hres, -, rfl⟩ := hr
    obtain ⟨r, hr, hρ, -, hI⟩ := cons_result P hS hC hπ htc hres
    have he : r = .values [] := start_result_eq htc hr hρ
    subst he
    exact ⟨_, .vis (LTS.CompStep.right _ (CStep.base (.iready ⟨hr, rfl⟩))) (.nil _), .idle hI⟩
  | ifail hf =>
    obtain ⟨rs, hrs, -, hback⟩ := LinkStart.StartSetup.result_of_startFailed hf
    obtain ⟨r, hr, hρ, -, -⟩ := cons_result P hS hC hπ htc hrs
    have he : r = rs := start_result_eq htc hr hρ
    subst he
    exact ⟨_, .vis (LTS.CompStep.right _ (CStep.base (.ifail (hback (c' := (κ, tc)) hr)))) (.nil _),
      .dead⟩

/-- The consumer's export call answers as the shared world does. -/
theorem svis_run_some (hS : S.Scalar) {f : S.consumerI.F.Op} {σ π κ : Store Nat} {ts tc : Thread}
    (hC : CRel St σ ts π κ tc) (hπ : StoreOk π)
    (htc : ThreadOk κ tc (resC (S.consumerI.exports.get f.1)))
    {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))} {y' : (LSH S P).State}
    (hb : (LSH S P).step (.run f (σ, ts)) (some o) y') :
    SVis P St (.inl y') (.inl (.ready π), .inl (.run f (κ, tc))) o := by
  cases hb with
  | call _ => exact Linking.DivShared.closed_op_elim ‹_›
  | ret hd =>
    obtain ⟨r', hres, hans, rfl⟩ := hd
    obtain ⟨r, hr, ⟨ρ, hρ⟩, -, hI⟩ := cons_result P hS hC hπ htc hres
    have he : r = r' := result_eq_of_ren hρ hans
    subst he
    exact ⟨_, .vis (LTS.CompStep.right _ (CStep.base (.ret ⟨r, hr, hans, rfl⟩))) (.nil _), .idle hI⟩

/-- **Visible shared steps of a running consumer**. -/
theorem svis_run (hS : S.Scalar) (ph : Ph S) {σ π κ : Store Nat} {ts tc : Thread}
    (hC : CRel St σ ts π κ tc) (hπ : StoreOk π) (htc : ThreadOk κ tc (resC (phF ph)))
    {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))} {y' : (LSHc S P).State}
    (h : (LSHc S P).step (.inl (shRun P ph (σ, ts))) (some o) y') :
    SVis P St y' (.inl (.ready π), .inl (cRun P ph (κ, tc))) o := by
  cases h with
  | sink ho hst =>
    obtain ⟨q, hq⟩ := shRun_pos P ph (σ, ts)
    rw [hq] at hst
    exact (not_isO_run hst ho).elim
  | base hb =>
    cases ph with
    | none => exact svis_run_none hS hC hπ htc hb
    | some f => exact svis_run_some hS hC hπ htc hb

/-- The shared world does not answer while the provider runs inside a call. -/
theorem svis_provc (ph : Ph S) {σ π κ : Store Nat} {ts tp tc : Thread} {e : S.consumerI.E.Op}
    (hP : PRel St σ ts π tp κ tc e.1 e.2.1) (htp : ThreadOk π tp (stubT e))
    (hnr : ∀ r, ¬ ResultAt π tp r) {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))}
    {y' : (LSHc S P).State} (h : (LSHc S P).step (.inl (shRun P ph (σ, ts))) (some o) y') : False := by
  cases h with
  | sink ho hst =>
    obtain ⟨q, hq⟩ := shRun_pos P ph (σ, ts)
    rw [hq] at hst
    exact not_isO_run hst ho
  | base hb =>
    cases ph with
    | none =>
      cases hb with
      | icall _ => exact Linking.DivShared.closed_op_elim ‹_›
      | iready hr => exact no_result_prov (P := P) hP htp hnr hr.1
      | ifail hf =>
        obtain ⟨r, hr, -, -⟩ := LinkStart.StartSetup.result_of_startFailed hf
        exact no_result_prov (P := P) hP htp hnr hr
    | some f =>
      cases hb with
      | call _ => exact Linking.DivShared.closed_op_elim ‹_›
      | ret hd => obtain ⟨r, hr, -, -⟩ := hd; exact no_result_prov (P := P) hP htp hnr hr

/-- A doomed shared configuration is at no result but a trap. -/
theorem doomed_trap {σ : Store Nat} {ts : Thread} {E : Ctx} {F : Frame}
    (hts : ts.config σ = ⟨σ, F, E.fill [.trap]⟩) {r : Result} (hr : ResultAt σ ts r) :
    r = .trap := by
  have h1 : (ts.config σ).code = r.toAdmin := hr
  rw [hts] at h1
  exact Choice.fill_trap_toAdmin h1

/-- A doomed start function fails with a trap. -/
theorem svis_doomed_none {σ π κ : Store Nat} {ts tcf : Thread} {x : (CompC S P).State}
    {E : Ctx} {F : Frame} (hts : ts.config σ = ⟨σ, F, E.fill [.trap]⟩)
    (hrun : Relation.ReflTransGen (CompC S P).Silent x
      (.inl (.ready π), .inl (cRun P none (κ, tcf))))
    (hres : ResultAt κ tcf .trap)
    {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))} {y' : (LSH S P).State}
    (hb : (LSH S P).step (.inst (σ, ts, [])) (some o) y') : SVis P St (.inl y') x o := by
  cases hb with
  | icall _ => exact Linking.DivShared.closed_op_elim ‹_›
  | iready hr => exact absurd (doomed_trap hts hr.1) (by simp)
  | ifail hf =>
    obtain ⟨r, hr, -, hback⟩ := LinkStart.StartSetup.result_of_startFailed hf
    have he : r = .trap := doomed_trap hts hr
    subst he
    exact ⟨_, (run_of_rtg hrun).append
      (.vis (LTS.CompStep.right _ (CStep.base (.ifail (hback (c' := (κ, tcf)) hres)))) (.nil _)),
      .dead⟩

/-- A doomed export call answers a trap. -/
theorem svis_doomed_some {f : S.consumerI.F.Op} {σ π κ : Store Nat} {ts tcf : Thread}
    {x : (CompC S P).State} {E : Ctx} {F : Frame} (hts : ts.config σ = ⟨σ, F, E.fill [.trap]⟩)
    (hrun : Relation.ReflTransGen (CompC S P).Silent x
      (.inl (.ready π), .inl (cRun P (some f) (κ, tcf))))
    (hres : ResultAt κ tcf .trap) (hI : IdleT St σ π κ)
    {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))} {y' : (LSH S P).State}
    (hb : (LSH S P).step (.run f (σ, ts)) (some o) y') : SVis P St (.inl y') x o := by
  cases hb with
  | call _ => exact Linking.DivShared.closed_op_elim ‹_›
  | ret hd =>
    obtain ⟨r, hr, hans, rfl⟩ := hd
    have he : r = .trap := doomed_trap hts hr
    subst he
    exact ⟨_, (run_of_rtg hrun).append
      (.vis (LTS.CompStep.right _ (CStep.base (.ret ⟨.trap, hres, hans, rfl⟩))) (.nil _)),
      .idle hI⟩

/-- A doomed shared configuration answers with a trap, after the composite has run to the
consumer's trap. -/
theorem svis_doomed (ph : Ph S) {σ π κ : Store Nat} {ts tcf : Thread} {x : (CompC S P).State}
    {E : Ctx} {F : Frame} (hts : ts.config σ = ⟨σ, F, E.fill [.trap]⟩)
    (hrun : Relation.ReflTransGen (CompC S P).Silent x
      (.inl (.ready π), .inl (cRun P ph (κ, tcf))))
    (hres : ResultAt κ tcf .trap) (hI : IdleT St σ π κ)
    {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))} {y' : (LSHc S P).State}
    (h : (LSHc S P).step (.inl (shRun P ph (σ, ts))) (some o) y') : SVis P St y' x o := by
  cases h with
  | sink ho hst =>
    obtain ⟨q, hq⟩ := shRun_pos P ph (σ, ts)
    rw [hq] at hst
    exact (not_isO_run hst ho).elim
  | base hb =>
    cases ph with
    | none => exact svis_doomed_none hts hrun hres hb
    | some f => exact svis_doomed_some hts hrun hres hI hb

/-- The provider's start function returned: the report of the consumer's, which returns at
once. -/
theorem prov_ready_run {π : Store Nat} {tp : Thread} (hcs : S.consStart = none)
    (hr : ResultAt π tp (.values [])) :
    (CompC S P).Run (.inl (.inst (π, tp)), .inl .pwait) [ansInst .ready]
      (.inl (.ready π), .inl (.ready S.scs)) := by
  have e : startThread S.consStart = .active {} [] := by rw [hcs]; rfl
  have hready := sync_ready (S := S) (P := P) hr
  rw [e] at hready
  exact .tau hready (.vis (vis_ready_finished π S.scs) (.nil _))

/-- The provider's start function failed: the failure is reported. -/
theorem prov_fail_run {π : Store Nat} {tp : Thread} {b : Behaviour Val}
    (hf : StartFailed (π, tp) b) :
    (CompC S P).Run (.inl (.inst (π, tp)), .inl .pwait) [ansInst (.fail b)]
      (.inl .dead, .inl .dead) :=
  .tau (sync_fail hf) (.vis (LTS.CompStep.right _ (CStep.base (.preport b))) (.nil _))

/-- Visible shared steps before instantiation. -/
theorem svis_fresh {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))}
    {y' : (LSHc S P).State} (h : (LSHc S P).step (.inl .fresh) (some o) y') :
    SVis P St y' (.inl .fresh, .inl .fresh) o := by
  cases h with
  | sink ho hst => exact ssink rfl rfl ho hst
  | base hb =>
    cases hb
    exact ⟨_, .vis (LTS.CompStep.right _ (CStep.base .askInst)) (.nil _), .pre rfl⟩

/-- Visible shared steps when idle. -/
theorem svis_idle (hS : S.Scalar) {σ π κ : Store Nat} (hI : IdleT St σ π κ)
    {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))}
    {y' : (LSHc S P).State} (h : (LSHc S P).step (.inl (.ready σ)) (some o) y') :
    SVis P St y' (.inl (.ready π), .inl (.ready κ)) o := by
  cases h with
  | sink ho hst => exact ssink rfl rfl ho hst
  | base hb =>
    cases hb with
    | askEx st q =>
      obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hI.1
      have hwc : S.consumerI.WellFormed κ := hS.consumer.of_funcs hI.2.2 hW.fκ
      exact ⟨_, .vis (LTS.CompStep.right _ (CStep.base (InstSystem.LinkStep.askEx (S := S.consumerI.instSys P S.scs S.consStart) κ q))) (.nil _),
        .run (some q) (hI.1.start q) hI.2.1 (hwc.init_typed q)⟩

/-- Visible shared steps when dead: Opponent moves into sinks. -/
theorem svis_dead {xp : (LPc S P).State}
    {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))}
    {y' : (LSHc S P).State} (h : (LSHc S P).step (.inl .dead) (some o) y') :
    SVis P St y' (xp, .inl .dead) o := by
  cases h with
  | sink ho hst => exact ssink rfl rfl ho hst
  | base hb => cases hb

/-- The shared world is ready right after the instantiation question. -/
theorem svis_pre (hS : S.Scalar) {l : List Nat} (hl : l = S.linkedStarts)
    {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))}
    {y' : (LSHc S P).State} (h : (LSHc S P).step (.inl (.inst (S.sc, .active {} [], l))) (some o) y') :
    SVis P St y' (.inl .fresh, .inl .pstart) o := by
  cases h with
  | sink ho hst => exact (not_isO_run (show Step (.run none) o _ from hst) ho).elim
  | base hb =>
    cases hb with
    | icall _ => exact Linking.DivShared.closed_op_elim ‹_›
    | ifail hf => exact absurd hf (LinkStartDiv.rest_not_failed (LinkStartDiv.resultAt_finished _))
    | iready hr =>
      obtain ⟨-, rfl, rfl⟩ := hr
      obtain ⟨hps, hcs⟩ := linkedStarts_nil hl
      have hask := sync_askInst (S := S) (P := P)
      have e : startThread S.provStart = .active {} [] := by rw [hps]; rfl
      rw [e] at hask
      exact ⟨_, .tau hask (prov_ready_run hcs (LinkStartDiv.resultAt_finished _)),
        .idle ⟨St.idle, ScalarInstance.WellFormed.storeOk hS.provider,
          ScalarInstance.WellFormed.storeOk hS.consumer⟩⟩

/-- Visible shared steps during the provider's start function: its outcome. -/
theorem svis_prov (hS : S.Scalar) {σ π : Store Nat} {ts tp : Thread} {l : List Nat}
    (hl : l = S.consStart.toList) (h : SRel St σ ts π S.scs tp)
    (htp : ThreadOk π tp (resC startType))
    {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))}
    {y' : (LSHc S P).State} (hs : (LSHc S P).step (.inl (.inst (σ, ts, l))) (some o) y') :
    SVis P St y' (.inl (.inst (π, tp)), .inl .pwait) o := by
  cases hs with
  | sink ho hst => exact (not_isO_run (show Step (.run none) o _ from hst) ho).elim
  | base hb =>
    cases hb with
    | icall _ => exact Linking.DivShared.closed_op_elim ‹_›
    | iready hr =>
      obtain ⟨hres, rfl, rfl⟩ := hr
      obtain ⟨π', tp', hreach, hr', hI⟩ := prov_back_end (P := P) hres h htp
      have hπ' : StoreOk π' := (reachableP_typed hreach (threadOk_storeOk htp) htp).1
      exact ⟨_, (run_of_rtg (ipi_reach hreach)).append (prov_ready_run (toList_nil hl) hr'),
        .idle ⟨hI, hπ', ScalarInstance.WellFormed.storeOk hS.consumer⟩⟩
    | ifail hf =>
      obtain ⟨r, hr, -, hback⟩ := LinkStart.StartSetup.result_of_startFailed hf
      obtain ⟨π', tp', hreach, hr', -⟩ := prov_back_end (P := P) hr h htp
      exact ⟨_, (run_of_rtg (ipi_reach hreach)).append (prov_fail_run (hback (c' := (π', tp')) hr')),
        .dead⟩

/-- **Visible shared steps** are visible composite steps after silent ones. -/
theorem isc_vis (hS : S.Scalar) {y y' : (LSHc S P).State} {x : (CompC S P).State}
    {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))} (hR : ISC P St y x)
    (h : (LSHc S P).step y (some o) y') : SVis P St y' x o := by
  cases hR with
  | fresh => exact svis_fresh h
  | pre hl => exact svis_pre hS hl h
  | prov hl hs htp => exact svis_prov hS hl hs htp h
  | idle hI => exact svis_idle hS hI h
  | run ph hC hπ htc => exact svis_run hS ph hC hπ htc h
  | provc ph hco hP htc htp hnr hlive => exact (svis_provc ph hP htp hnr h).elim
  | doomed ph E F hts hrun hres hI => exact svis_doomed ph hts hrun hres hI h
  | dead => exact svis_dead h
  | sink => cases h

/-! ### The simulation -/

include hOp hOc in
/-- **The completed shared world is simulated by the composite of the completed provider and
consumer, divergence-sensitively.** -/
noncomputable def subSim (hS : S.Scalar) : LTS.DivSimulation (LSHc S P) (CompC S P) where
  R := ISC P St
  init := .fresh
  step {y y' x l} hR h := by
    cases l with
    | none =>
      rcases isc_tau hOp hOc hS hR h with ⟨x', hx', hR'⟩ | ⟨hR', -⟩
      · exact ⟨x', run_of_transGen hx', hR'⟩
      · exact ⟨x, .nil _, hR'⟩
    | some o => exact isc_vis hS hR h
  lt y' y := itw P y' < itw P y
  wf := InvImage.wf (itw P) Nat.lt_wfRel.wf
  tau hR h := isc_tau hOp hOc hS hR h

end Silmaril.Proofs.Wasm.Game.LinkStartDiv
