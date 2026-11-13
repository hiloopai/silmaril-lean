module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.DivSup
public import Silmaril.Proofs.Wasm.Game.Linking.Split.GameSub
public import Silmaril.Proofs.Wasm.Game.Machine.Doomed

/-!
# Static linking, separation: the shared world is simulated by the composite system,
divergence observed

The shared world `S.sharedI.dlts P S.sc` is simulated by the composite system of the provider
and the consumer **divergence-sensitively**, for every profile (`sharedSim`):

* a shared step from a running consumer is the forward image of a consumer step, or a `Soft`
  step, which is the image of another consumer step (`CRel.soft_back`); at a callout it is the
  `call_ref` into the provider, matched by the synchronisation and the provider's first step
  (`CRel.call`);
* a shared step from a running provider (inside the consumer's callout context) is likewise
  the image of a provider step (`PRel.step`, `PRel.soft_back` for live code);
* after a provider step the composite system *settles* (`settle`): a provider result of values
  is answered and resumes the consumer (`PRel.ret`); a trapping provider (`TRAP` at its top
  level) makes the shared configuration *doomed* (a `TRAP` under a callout context);
* a doomed shared configuration is related to the composite system that has already run to
  the consumer's trap (the provider's trap answered, the consumer's context bubbled,
  `fill_trap_reach`); doomed shared steps stay doomed in the same store (`step_doomed`) and
  are matched by no composite step, while the size of the shared code decreases
  (`Choice.trapped_step_lt`): this is the measure.

Every shared step is otherwise matched by at least one composite step. The step lemmas are
those of `GameSub`, used step by step instead of along a run to a result.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game Silmaril
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Proofs.Wasm.Game.Linking

variable {S : Setup}

/-- The states of the shared world related to states of the composite system. -/
inductive SC (St : Static S) (P : Profile) :
    S.sharedI.HState → S.providerI.HState × S.consumerI.HState → Prop where
  | idle {σ π κ : Store Nat} (h : IdleT St σ π κ) : SC St P (.idle σ) (.idle π, .idle κ)
  | run {f : S.consumerI.F.Op} {σ π κ : Store Nat} {ts tc : Thread}
      (h : CRel St σ ts π κ tc) (hπ : StoreOk π) (htc : ThreadOk κ tc (resC (S.consumerI.exports.get f.1))) :
      SC St P (.running f σ ts) (.idle π, .running f κ tc)
  | prov {f : S.consumerI.F.Op} {σ π κ : Store Nat} {ts tp tc : Thread} {e : S.consumerI.E.Op}
      (hco : CalloutAt κ tc e.1 e.2.1) (h : PRel St σ ts π tp κ tc e.1 e.2.1)
      (htc : ThreadOk κ tc (resC (S.consumerI.exports.get f.1))) (htp : ThreadOk π tp (stubT e))
      (hnr : ∀ r, ¬ ResultAt π tp r) (hlive : Live (tp.config π).code) :
      SC St P (.running f σ ts) (.running e π tp, .waiting f κ tc e)
  | doomed {f : S.consumerI.F.Op} {σ π κ : Store Nat} {ts tcf : Thread}
      {x : S.providerI.HState × S.consumerI.HState} (E : Ctx) (F : Frame)
      (hts : ts.config σ = ⟨σ, F, E.fill [.trap]⟩)
      (hrun : Relation.ReflTransGen (Comp (S := S) P).Silent x (.idle π, .running f κ tcf))
      (hres : ResultAt κ tcf .trap) (hI : IdleT St σ π κ) :
      SC St P (.running f σ ts) x

/-- The size of the shared code. -/
noncomputable def tw : S.sharedI.HState → Nat
  | .running _ σ ts => sizeOf (ts.config σ).code
  | _ => 0

/-- The measure on shared states. -/
def TwLt (y x : S.sharedI.HState) : Prop := tw y < tw x

theorem twLt_wf : WellFounded (TwLt (S := S)) := InvImage.wf tw Nat.lt_wfRel.wf

/-- The outcome of a shared step. -/
def Matched2 (St : Static S) (P : Profile) (y' y : S.sharedI.HState)
    (x : S.providerI.HState × S.consumerI.HState) : Prop :=
  (∃ x', Relation.TransGen (Comp (S := S) P).Silent x x' ∧ SC St P y' x') ∨
    (SC St P y' x ∧ TwLt y' y)

/-! ### Composite steps -/

theorem c_tau {P : Profile} {π : Store Nat} {f : S.consumerI.F.Op} {κ κ' : Store Nat}
    {tc tc' : Thread} (h : InternalP P (κ, tc) (κ', tc')) :
    (Comp (S := S) P).Silent (.idle π, .running f κ tc) (.idle π, .running f κ' tc') :=
  LTS.CompStep.tau₂ (ScalarInstance.DTrans.tau (I := S.consumerI) h)

theorem p_tau {P : Profile} {e : S.consumerI.E.Op} {π π' : Store Nat} {tp tp' : Thread}
    {xc : S.consumerI.HState} (h : InternalP P (π, tp) (π', tp')) :
    (Comp (S := S) P).Silent (.running e π tp, xc) (.running e π' tp', xc) :=
  LTS.CompStep.tau₁ (ScalarInstance.DTrans.tau (I := S.providerI) h)

/-- A consumer run is a silent composite run. -/
theorem c_reach {P : Profile} {π : Store Nat} {f : S.consumerI.F.Op} {κ κ' : Store Nat}
    {tc tc' : Thread} (h : Reach P (κ, tc) (κ', tc')) :
    Relation.ReflTransGen (Comp (S := S) P).Silent (.idle π, .running f κ tc)
      (.idle π, .running f κ' tc') := by
  generalize hx : (κ, tc) = x at h
  generalize hy : (κ', tc') = y at h
  induction h generalizing κ' tc' with
  | refl => subst hx; cases hy; exact .refl
  | @tail y₁ y₂ _ hst ih =>
    subst hy
    exact (ih (κ' := y₁.1) (tc' := y₁.2) rfl).tail (c_tau hst)

/-- The provider answers `w` and the consumer resumes. -/
theorem sync_ret {P : Profile} {e : S.consumerI.E.Op} {π : Store Nat} {tp : Thread}
    {f : S.consumerI.F.Op} {κ : Store Nat} {tc : Thread} {r : Result} {w : S.consumerI.E.Ar e}
    (hr : ResultAt π tp r) (hw : Answer.ofResult? (S.stubTypes.get e.1) r = some w) :
    (Comp (S := S) P).Silent (.running e π tp, .waiting f κ tc e)
      (.idle π, .running f κ (resumeResult κ tc (Answer.toResult (ft := S.stubTypes.get e.1) w))) :=
  LTS.CompStep.sync (.ans e w) (ScalarInstance.DTrans.oret (I := S.providerI) hr hw)
    (ScalarInstance.DTrans.uret (I := S.consumerI) w)

/-- The consumer calls the provider. -/
theorem sync_call {P : Profile} {f : S.consumerI.F.Op} {π κ : Store Nat} {tc : Thread}
    {h : Nat} {args : List Val} {e : S.consumerI.E.Op} (hco : CalloutAt κ tc h args)
    (hop : S.consumerI.importOp? h args = some e) :
    (Comp (S := S) P).Silent (.idle π, .running f κ tc)
      (.running e π (S.providerI.initThread e), .waiting f κ tc e) :=
  LTS.CompStep.sync (.ask e) (ScalarInstance.DTrans.call (I := S.providerI) π e)
    (ScalarInstance.DTrans.ucall (I := S.consumerI) hco hop)

/-! ### Settling after a provider step -/

/-- A provider trap: the composite system runs to the consumer's trap, and the shared
configuration is doomed. -/
theorem settle_trap (St : Static S) (P : Profile) {f : S.consumerI.F.Op} {σ π κ : Store Nat}
    {ts tp tc : Thread} {e : S.consumerI.E.Op} (hco : CalloutAt κ tc e.1 e.2.1)
    (hP : PRel St σ ts π tp κ tc e.1 e.2.1) (hκ : StoreOk κ) (hπ : StoreOk π)
    {W : List Val} {R : List Admin} (hdoom : (tp.config π).code = vals W ++ [.trap] ++ R) :
    SC St P (.running f σ ts) (.running e π tp, .waiting f κ tc e) := by
  have hI : Idle St σ π κ := hP.world
  obtain ⟨ρp, Op, ρc, Oc, E', a', -, -, -, -, hF, -, -, hts⟩ := hP
  have hts' : ts.config σ = ⟨σ, ρc.frame (tc.config κ).frame,
      (Ctx.ext (ρc.ctx E') (W.map ρp.val) (ρp.code R)).fill [.trap]⟩ := by
    rw [hts, hdoom, ← Ctx.fill_ext]
    simp
  have hprov : ∃ tpf, Relation.ReflTransGen (Comp (S := S) P).Silent
      (.running e π tp, .waiting f κ tc e) (.running e π tpf, .waiting f κ tc e) ∧
      ResultAt π tpf .trap := by
    by_cases hne : W ≠ [] ∨ R ≠ []
    · refine ⟨.active {} [.trap], .single (p_tau ⟨{}, [.trap], rfl, ?_⟩), rfl⟩
      have hc : tp.config π = ⟨π, {}, vals W ++ [.trap] ++ R⟩ := by
        rw [Thread.config_eta π tp, hF, hdoom]
      rw [hc]
      exact .trapInstrs hne
    · have hnil : W = [] ∧ R = [] := by simpa only [ne_eq, not_or, not_not] using hne
      refine ⟨tp, .refl, ?_⟩
      show (tp.config π).code = [.trap]
      rw [hdoom, hnil.1, hnil.2]
      rfl
  obtain ⟨tpf, hp, hr⟩ := hprov
  obtain ⟨E, a, hd⟩ := hco
  have hrt : resumeResult κ tc .trap = .active (tc.config κ).frame (E.fill [.trap]) := by
    unfold resumeResult
    simp only [hd, Result.toAdmin]
  have hs : (Comp (S := S) P).Silent (.running e π tpf, .waiting f κ tc e)
      (.idle π, .running f κ (.active (tc.config κ).frame (E.fill [.trap]))) := by
    have h : (Comp (S := S) P).Silent (.running e π tpf, .waiting f κ tc e)
        (.idle π, .running f κ (resumeResult κ tc .trap)) :=
      sync_ret (P := P) (e := e) (f := f) (κ := κ) (tc := tc) (w := .trap) hr rfl
    rw [hrt] at h
    exact h
  have hc : Relation.ReflTransGen (Comp (S := S) P).Silent
      (.idle π, .running f κ (.active (tc.config κ).frame (E.fill [.trap])))
      (.idle π, .running f κ (.active (tc.config κ).frame [.trap])) :=
    c_reach (fill_trap_reach P κ E (tc.config κ).frame)
  exact .doomed _ _ hts' ((hp.tail hs).trans hc) rfl ⟨hI, hπ, hκ⟩

/-- **Settling after a provider step**: a provider result of values is answered and resumes
the consumer, a trapping provider makes the shared configuration doomed, a live provider keeps
running. -/
theorem settle (St : Static S) (hS : S.Scalar) (P : Profile) {f : S.consumerI.F.Op}
    {σ π κ : Store Nat} {ts tp tc : Thread} {e : S.consumerI.E.Op}
    (hco : CalloutAt κ tc e.1 e.2.1) (hP : PRel St σ ts π tp κ tc e.1 e.2.1)
    (htc : ThreadOk κ tc (resC (S.consumerI.exports.get f.1))) (htp : ThreadOk π tp (stubT e)) :
    ∃ x', Relation.ReflTransGen (Comp (S := S) P).Silent (.running e π tp, .waiting f κ tc e) x' ∧
      SC St P (.running f σ ts) x' := by
  have hκ : StoreOk κ := threadOk_storeOk htc
  have hπ : StoreOk π := threadOk_storeOk htp
  by_cases hres : ∃ r, ResultAt π tp r
  · obtain ⟨r, hr⟩ := hres
    cases r with
    | throw a' => exact absurd rfl ((hP.ret hr (fun _ h => by cases h)).1 a')
    | values vs =>
      show ∃ x', _ ∧ _
      obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hP.world
      have hwc : S.consumerI.WellFormed κ := hS.consumer.of_funcs hκ hW.fκ
      have hv : List.Forall₂ ScalarType.HasVal (S.stubTypes.get e.1).results vs :=
        stub_results_typed htp hr
      have hw : Answer.ofResult? (S.stubTypes.get e.1) (.values vs) =
          some (.values ⟨vs, hv⟩) := by
        simp only [Answer.ofResult?]
        rw [dite_eq_left hv]
      obtain ⟨-, hC⟩ := hP.ret hr (fun vs' h => by cases h; exact ⟨_, hv⟩)
      have htc' : ThreadOk κ (resumeResult κ tc (.values vs)) (resC (S.consumerI.exports.get f.1)) :=
        resume_values_typed P hκ htc hwc hco hv
      exact ⟨_, .single (sync_ret (f := f) (κ := κ) (tc := tc) hr hw), .run hC hπ htc'⟩
    | trap =>
      have hd : (tp.config π).code = vals [] ++ [.trap] ++ [] := by
        simpa [ResultAt, Result.toAdmin] using hr
      exact ⟨_, .refl, settle_trap St P hco hP hκ hπ hd⟩
  · have hnr : ∀ r, ¬ ResultAt π tp r := fun r hr => hres ⟨r, hr⟩
    rcases doomed_or_live hnr with ⟨W, R, hdoom⟩ | hlive
    · exact ⟨_, .refl, settle_trap St P hco hP hκ hπ hdoom⟩
    · exact ⟨_, .refl, .prov hco hP htc htp hnr hlive⟩

/-! ### Shared steps -/

/-- A consumer at a result: the shared world is at a result too. -/
theorem crel_no_step_of_result {St : Static S} {P : Profile} {σ π κ : Store Nat}
    {ts tc : Thread} (hC : CRel St σ ts π κ tc) {r : Result} (hr : ResultAt κ tc r)
    (y : Store Nat × Thread) : ¬ InternalP P (σ, ts) y := by
  obtain ⟨-, ⟨ρ, hres⟩, -⟩ := hC.result hr
  exact resultAt_no_internal hres y

/-- **A shared step while the consumer runs.** -/
theorem tau_run (St : Static S) (hS : S.Scalar) (P : Profile) {f : S.consumerI.F.Op}
    {σ π κ : Store Nat} {ts tc : Thread} {y : Store Nat × Thread}
    (hC : CRel St σ ts π κ tc) (hπ : StoreOk π)
    (htc : ThreadOk κ tc (resC (S.consumerI.exports.get f.1))) (hy : InternalP P (σ, ts) y) :
    ∃ x', Relation.TransGen (Comp (S := S) P).Silent (.idle π, .running f κ tc) x' ∧
      SC St P (.running f y.1 y.2) x' := by
  have hκ : StoreOk κ := threadOk_storeOk htc
  obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hC.world
  have hwc : S.consumerI.WellFormed κ := hS.consumer.of_funcs hκ hW.fκ
  have hwp : S.providerI.WellFormed π := hS.provider.of_funcs hπ hW.fπ
  have hst : statusP P κ tc ≠ .stuck := statusP_ne_stuck hκ htc
  cases hstat : statusP P κ tc with
  | returned cr =>
    cases cr with
    | values vs =>
      exact absurd hy (crel_no_step_of_result (r := .values vs) hC (statusP_returned_values hstat) y)
    | trap =>
      rcases statusP_returned_trap_inv hstat with h | ⟨a, h⟩
      · exact absurd hy (crel_no_step_of_result (r := .trap) hC h y)
      · exact absurd hy (crel_no_step_of_result (r := .throw a) hC h y)
  | stuck => exact absurd hstat hst
  | running =>
    show ∃ x', _ ∧ _
    obtain ⟨⟨κ', tc'⟩, hc⟩ := statusP_running_inv hstat
    obtain ⟨σ', ts', hx', hC'⟩ := hC.step hc
    rcases next_eq_or_soft hy hx' with heq | hsoft
    · obtain ⟨-, htc', -⟩ := InternalP.preserves hκ htc hc
      exact ⟨_, .single (c_tau hc), heq ▸ .run hC' hπ htc'⟩
    · rcases y with ⟨σy, ty⟩
      obtain ⟨fy, cy, rfl, -⟩ := hy
      obtain ⟨X', hstep, hst', hRs⟩ := hC.soft_back hsoft
      have hy1 : σy = σ := hst'
      subst hy1
      obtain ⟨-, htcs, -⟩ := InternalP.preserves hκ htc hstep
      exact ⟨_, .single (c_tau hstep), .run hRs hπ htcs⟩
  | callout h args =>
    show ∃ x', _ ∧ _
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
    obtain ⟨x', hset, hSC⟩ := settle St hS P (f := f) (e := e) hco hP htc htp₀
    exact ⟨x', .head' (sync_call hco hop) (.head (p_tau hp₀') hset), hSC⟩

/-- A running provider in a related state has a host-free step. -/
theorem prov_step {St : Static S} {P : Profile} {σ π κ : Store Nat} {ts tp tc : Thread}
    {e : S.consumerI.E.Op} (hP : PRel St σ ts π tp κ tc e.1 e.2.1)
    (htp : ThreadOk π tp (stubT e)) (hnr : ∀ r, ¬ ResultAt π tp r) :
    ∃ y, InternalP P (π, tp) y := by
  have hπ : StoreOk π := threadOk_storeOk htp
  have hst : statusP P π tp ≠ .stuck := statusP_ne_stuck hπ htp
  cases hstat : statusP P π tp with
  | returned cr =>
    cases cr with
    | values vs => exact absurd (statusP_returned_values hstat) (hnr (.values vs))
    | trap =>
      rcases statusP_returned_trap_inv hstat with h | ⟨a, h⟩
      · exact absurd h (hnr .trap)
      · exact absurd h (hnr (.throw a))
  | stuck => exact absurd hstat hst
  | callout h' args' => exact absurd hstat (p_no_callout hP)
  | running => exact statusP_running_inv hstat

/-- **A shared step while the provider runs.** -/
theorem tau_prov (St : Static S) (hS : S.Scalar) (P : Profile) {f : S.consumerI.F.Op}
    {σ π κ : Store Nat} {ts tp tc : Thread} {e : S.consumerI.E.Op} {y : Store Nat × Thread}
    (hco : CalloutAt κ tc e.1 e.2.1) (hP : PRel St σ ts π tp κ tc e.1 e.2.1)
    (htc : ThreadOk κ tc (resC (S.consumerI.exports.get f.1))) (htp : ThreadOk π tp (stubT e))
    (hnr : ∀ r, ¬ ResultAt π tp r) (hlive : Live (tp.config π).code)
    (hy : InternalP P (σ, ts) y) :
    ∃ x', Relation.TransGen (Comp (S := S) P).Silent (.running e π tp, .waiting f κ tc e) x' ∧
      SC St P (.running f y.1 y.2) x' := by
  have hπ : StoreOk π := threadOk_storeOk htp
  obtain ⟨⟨π', tp'⟩, hpst⟩ := prov_step (P := P) hP htp hnr
  obtain ⟨σ', ts', hx', hP'⟩ := hP.step hpst
  rcases next_eq_or_soft hy hx' with heq | hsoft
  · obtain ⟨-, htp', -⟩ := InternalP.preserves hπ htp hpst
    obtain ⟨x', hset, hSC⟩ := settle St hS P (f := f) hco hP' htc htp'
    exact ⟨x', .head' (p_tau hpst) hset, heq ▸ hSC⟩
  · rcases y with ⟨σy, ty⟩
    obtain ⟨fy, cy, rfl, -⟩ := hy
    obtain ⟨X', hstep, hst', hPs⟩ := hP.soft_back hlive hsoft
    have hy1 : σy = σ := hst'
    subst hy1
    obtain ⟨-, htps, -⟩ := InternalP.preserves hπ htp hstep
    obtain ⟨x', hset, hSC⟩ := settle St hS P (f := f) hco hPs htc htps
    exact ⟨x', .head' (p_tau hstep) hset, hSC⟩

/-- **A shared step of a doomed configuration**: no composite step, the code shrinks. -/
theorem tau_doomed {St : Static S} {P : Profile} {f : S.consumerI.F.Op} {σ π κ : Store Nat}
    {ts tcf : Thread} {x : S.providerI.HState × S.consumerI.HState} {E : Ctx} {F : Frame}
    (hts : ts.config σ = ⟨σ, F, E.fill [.trap]⟩)
    (hrun : Relation.ReflTransGen (Comp (S := S) P).Silent x (.idle π, .running f κ tcf))
    (hres : ResultAt κ tcf .trap) (hI : IdleT St σ π κ) {y : Store Nat × Thread}
    (hy : InternalP P (σ, ts) y) :
    SC St P (.running f y.1 y.2) x ∧ TwLt (S := S) (.running f y.1 y.2) (.running f σ ts) := by
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
  refine ⟨.doomed E' F hts' hrun hres hI, ?_⟩
  show sizeOf cy < sizeOf (ts.config σy).code
  rw [hts]
  exact hlt

/-- A silent composite run as a run without visible moves. -/
theorem run_of_rtg {E F : Sig.{0}} {L : LTS E F} {x y : L.State}
    (h : Relation.ReflTransGen L.Silent x y) : L.Run x [] y := by
  induction h with
  | refl => exact .nil _
  | tail _ hs ih => exact ih.append (.tau hs (.nil _))

/-- **Silent shared steps** are matched divergence-sensitively. -/
theorem shared_tau (St : Static S) (hS : S.Scalar) (P : Profile) {y y' : S.sharedI.HState}
    {x : S.providerI.HState × S.consumerI.HState} (hR : SC St P y x)
    (h : S.sharedI.DTrans P y none y') : Matched2 St P y' y x := by
  cases h with
  | @tau f σ σ' ts ts' hi =>
    cases hR with
    | run hC hπ htc => exact .inl (tau_run St hS P hC hπ htc hi)
    | prov hco hP htc htp hnr hlive => exact .inl (tau_prov St hS P hco hP htc htp hnr hlive hi)
    | doomed E F hts hrun hres hI => exact .inr (tau_doomed hts hrun hres hI hi)

/-- An answer of the shared world while the consumer runs is an answer of the consumer. -/
theorem oret_run (St : Static S) (hS : S.Scalar) (P : Profile) {f : S.consumerI.F.Op} {σ π κ : Store Nat}
    {ts tc : Thread} {r : Result} {v : S.consumerI.F.Ar f} (hC : CRel St σ ts π κ tc)
    (hπ : StoreOk π) (htc : ThreadOk κ tc (resC (S.consumerI.exports.get f.1)))
    (final : ResultAt σ ts r) (answer : Answer.ofResult? (S.consumerI.exports.get f.1) r = some v) :
    ResultAt κ tc r ∧ IdleT St σ π κ := by
  have hκ : StoreOk κ := threadOk_storeOk htc
  have hst : statusP P κ tc ≠ .stuck := statusP_ne_stuck hκ htc
  have fin : ∀ r', ResultAt κ tc r' → ResultAt κ tc r ∧ IdleT St σ π κ := by
    intro r' hr'
    obtain ⟨-, ⟨ρ, hres⟩, hI⟩ := hC.result hr'
    have he : ρ.result r' = r := resultAt_unique hres final
    have hrr : r' = r := result_eq_of_ren he answer
    exact ⟨hrr ▸ hr', hI, hπ, hκ⟩
  cases hstat : statusP P κ tc with
  | returned cr =>
    cases cr with
    | values vs => exact fin (.values vs) (statusP_returned_values hstat)
    | trap =>
      rcases statusP_returned_trap_inv hstat with h | ⟨a, h⟩
      · exact fin .trap h
      · exact fin (.throw a) h
  | stuck => exact absurd hstat hst
  | running =>
    obtain ⟨⟨κ', tc'⟩, hc⟩ := statusP_running_inv hstat
    obtain ⟨σ', ts', hx', -⟩ := hC.step hc
    exact absurd hx' (resultAt_no_internal final _)
  | callout h args =>
    obtain ⟨E, a, hd⟩ := statusP_callout_inv hstat
    have hco : CalloutAt κ tc h args := ⟨E, a, hd⟩
    obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hC.world
    have hwc : S.consumerI.WellFormed κ := hS.consumer.of_funcs hκ hW.fκ
    obtain ⟨hlt, hargs⟩ := stub_args_typed (P := P) htc hwc hco
    obtain ⟨-, -, ts₁, -, hs₁, -⟩ := hC.call (P := P) hco hargs
    exact absurd hs₁ (resultAt_no_internal final _)

/-- The shared world does not answer while the provider runs. -/
theorem no_result_prov {St : Static S} {P : Profile} {σ π κ : Store Nat} {ts tp tc : Thread}
    {e : S.consumerI.E.Op} (hP : PRel St σ ts π tp κ tc e.1 e.2.1)
    (htp : ThreadOk π tp (stubT e)) (hnr : ∀ r, ¬ ResultAt π tp r) {r : Result}
    (final : ResultAt σ ts r) : False := by
  obtain ⟨⟨π', tp'⟩, hpst⟩ := prov_step (P := P) hP htp hnr
  obtain ⟨σ', ts', hx', -⟩ := hP.step hpst
  exact resultAt_no_internal final _ hx'

/-- **Visible shared steps** are visible composite steps after silent ones. -/
theorem shared_vis (St : Static S) (hS : S.Scalar) (P : Profile) {y y' : S.sharedI.HState}
    {x : S.providerI.HState × S.consumerI.HState} {o : Move S.sharedI.E S.sharedI.F}
    (hR : SC St P y x) (h : S.sharedI.DTrans P y (some o) y') :
    ∃ x', (Comp (S := S) P).Run x [o] x' ∧ SC St P y' x' := by
  cases h with
  | call σ f =>
    cases hR with
    | @idle _ π κ hI =>
      obtain ⟨⟨ρp, Op, ρc, Oc, hW⟩, hπ, hκ⟩ := hI
      have hwc : S.consumerI.WellFormed κ := hS.consumer.of_funcs hκ hW.fκ
      exact ⟨_, .vis (LTS.CompStep.right (.ask f) (ScalarInstance.DTrans.call (I := S.consumerI) κ f))
        (.nil _), .run (Idle.start ⟨ρp, Op, ρc, Oc, hW⟩ f) hπ (hwc.init_typed f)⟩
  | ucall _ _ => exact DivShared.closed_op_elim (by assumption)
  | uret _ => cases hR
  | @oret f σ ts r v final answer =>
    cases hR with
    | run hC hπ htc =>
      obtain ⟨hr, hI⟩ := oret_run St hS P hC hπ htc final answer
      exact ⟨_, .vis (LTS.CompStep.right (.ans f v)
        (ScalarInstance.DTrans.oret (I := S.consumerI) hr answer)) (.nil _), .idle hI⟩
    | prov hco hP htc htp hnr hlive => exact (no_result_prov (P := P) hP htp hnr final).elim
    | doomed E F hts hrun hres hI =>
      have hc : E.fill [.trap] = r.toAdmin := by
        have h1 : (ts.config σ).code = r.toAdmin := final
        rw [hts] at h1
        exact h1
      have hr : r = .trap := Choice.fill_trap_toAdmin hc
      subst hr
      exact ⟨_, (run_of_rtg hrun).append (.vis (LTS.CompStep.right (.ans f v)
        (ScalarInstance.DTrans.oret (I := S.consumerI) hres answer)) (.nil _)), .idle hI⟩

/-- **The shared world is simulated by the composite system, divergence-sensitively.** -/
noncomputable def sharedSim (St : Static S) (hS : S.Scalar) (P : Profile) :
    LTS.DivSimulation (S.sharedI.dlts P S.sc) (Comp (S := S) P) where
  R := SC St P
  init := .idle ⟨St.idle, ScalarInstance.WellFormed.storeOk hS.provider,
    ScalarInstance.WellFormed.storeOk hS.consumer⟩
  step {y y' x l} hR h := by
    cases l with
    | none =>
      rcases shared_tau St hS P hR h with ⟨x', hx', hR'⟩ | ⟨hR', -⟩
      · exact ⟨x', run_of_transGen hx', hR'⟩
      · exact ⟨x, .nil _, hR'⟩
    | some o => exact shared_vis St hS P hR h
  lt := TwLt
  wf := twLt_wf
  tau hR h := shared_tau St hS P hR h

/-- **Divergence-aware `⊆` of step (B)**: the divergence-observing strategy of the shared world
refines that of the composite system (plays, divergences, infinite plays). -/
theorem shared_le_comp (hS : S.Scalar) (P : Profile) :
    S.sharedI.dstrategy P S.sc ≤ DStrategy.ofLTS (Comp (S := S) P) :=
  (static_nonempty S hS).elim fun St => (sharedSim St hS P).ofLTS_le

/-- **Step (B), divergence observed, every profile**: the shared world and the composite system
have the same divergence-observing strategies. -/
theorem shared_eq_comp (hS : S.Scalar) (P : Profile) :
    S.sharedI.dstrategy P S.sc = DStrategy.ofLTS (Comp (S := S) P) :=
  le_antisymm (shared_le_comp hS P) (comp_le_shared hS P)

end Silmaril.Proofs.Wasm.Game.Linking.Split
