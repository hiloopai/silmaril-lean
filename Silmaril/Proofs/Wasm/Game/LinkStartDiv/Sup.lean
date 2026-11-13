module

public import Silmaril.Proofs.Wasm.Game.LinkStartDiv.Base

/-!
# Static links with start functions: the composite is simulated by the shared world,
divergence observed

The composite `CompC S P` of the completed provider and consumer link systems is simulated by the
completed shared world `LSHc S P` (its instantiation running `S.linkedStarts`)
**divergence-sensitively** (`LTS.DivSimulation`), for every profile (`supSim`).

Related states (`ICS`), following the link:

* before instantiation, after the instantiation question (`pre`), during the provider's start
  function (`prov`, the provider thread running alone, `Split.SRel`), after a provider failure
  (`pfail`);
* while the consumer runs its start function or an export call (`run`, `Split.CRel`), at its
  import call into the provider (`call`), while the provider answers it (`provc`,
  `Split.PRel`), once its start function has returned (`cdone`), and idle (`idle`);
* dead after a failure (`dead`), and the stuck states that the completions add (`junk`).

The hidden synchronisations of the link (the instantiation question and answer of the provider,
the consumer's import calls and their answers) take no shared step, except when the next start
function is invoked; they decrease the measure `irank`.

New proofs (the export-phase steps follow `Silmaril.Proofs.Wasm.Game.Linking.Split.DivSup`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.LinkStartDiv

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking
  Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril.Proofs.Wasm.Game.Linking.Split
  Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

variable {S : StartSetup} (P : Profile) (St : Static S.toSetup)

/-- The states of the composite related to states of the shared world. -/
inductive ICS : (CompC S P).State → (LSHc S P).State → Prop where
  | fresh : ICS (.inl .fresh, .inl .fresh) (.inl .fresh)
  | pre : ICS (.inl .fresh, .inl .pstart) (.inl (.inst (S.sc, .active {} [], S.linkedStarts)))
  | prov {σ π : Store Nat} {ts tp : Thread} (h : SRel St σ ts π S.scs tp) :
      ICS (.inl (.inst (π, tp)), .inl .pwait) (.inl (.inst (σ, ts, S.consStart.toList)))
  | pfail {σ : Store Nat} {ts : Thread} {rest : List Nat} {b : Behaviour Val}
      (h : StartFailed (σ, ts) b) :
      ICS (.inl .dead, .inl (.pfail b)) (.inl (.inst (σ, ts, rest)))
  | cdone {σ π κ : Store Nat} {ts tc : Thread} (hI : Idle St σ π κ)
      (hs : ResultAt σ ts (.values [])) (hc : ResultAt κ tc (.values [])) :
      ICS (.inl (.ready π), .inl (.inst (κ, tc))) (.inl (.inst (σ, ts, [])))
  | idle {σ π κ : Store Nat} (hI : Idle St σ π κ) :
      ICS (.inl (.ready π), .inl (.ready κ)) (.inl (.ready σ))
  | run (ph : Ph S) {σ π κ : Store Nat} {ts tc : Thread} (h : CRel St σ ts π κ tc) :
      ICS (.inl (.ready π), .inl (cRun P ph (κ, tc))) (.inl (shRun P ph (σ, ts)))
  | call (ph : Ph S) {σ π κ : Store Nat} {ts tc : Thread} {e : S.consumerI.E.Op}
      (h : CRel St σ ts π κ tc) (hco : CalloutAt κ tc e.1 e.2.1) :
      ICS (.inl (.run e (π, S.providerI.initThread e)),
          .inl (cWait P ph e (S.consumerI.resumeK κ tc e)))
        (.inl (shRun P ph (σ, ts)))
  | provc (ph : Ph S) {σ π κ : Store Nat} {ts tp tc : Thread} {e : S.consumerI.E.Op}
      (h : PRel St σ ts π tp κ tc e.1 e.2.1) (hnp : NotPending tp) :
      ICS (.inl (.run e (π, tp)), .inl (cWait P ph e (S.consumerI.resumeK κ tc e)))
        (.inl (shRun P ph (σ, ts)))
  | dead {xp : (LP S P).State} (hxp : PIdle P xp) : ICS (.inl xp, .inl .dead) (.inl .dead)
  | junk {x : (CompC S P).State} {y : (LSHc S P).State} (h : Stuck P x) : ICS x y

/-- The measure of the hidden synchronisations. -/
def irank : (CompC S P).State → Nat
  | (.inl .fresh, .inl .pstart) => 5
  | (.inl (.inst _), .inl .pwait) => 4
  | (.inl (.run _ (_, .active _ _)), .inl _) => 2
  | (.inl (.ready _), .inl (.inst _)) => 1
  | (.inl (.ready _), .inl (.run _ _)) => 1
  | _ => 0

/-- The outcome of a silent composite step. -/
def IMatched (x' x : (CompC S P).State) (y : (LSHc S P).State) : Prop :=
  (∃ y', Relation.TransGen (LSHc S P).Silent y y' ∧ ICS P St x' y') ∨
    (ICS P St x' y ∧ irank P x' < irank P x)

/-! ### Facts -/

variable {P St}

theorem cstep {x x' : (CompC S P).State} {l : Option (Move S.providerI.E
    (S.consumerI.F.withInst (Behaviour Val)))} (h : (CompC S P).step x l x') :
    LTS.CompStep (LPc S P) (LCc S P) x l x' := h

theorem lt_of_rank {x' x : (CompC S P).State} {a b : Nat} (ha : irank P x' = a)
    (hb : irank P x = b) (hab : a < b) : irank P x' < irank P x := ha ▸ hb ▸ hab

theorem irank_inr (xp : (LPc S P).State) (p : Pos _ _) : irank P (S := S) (xp, .inr p) = 0 := by
  cases xp with
  | inr _ => rfl
  | inl y =>
    cases y with
    | run q c => obtain ⟨σ, t⟩ := c; cases t <;> rfl
    | _ => rfl

theorem irank_run (ph : Ph S) (π : Store Nat) (c : Store Nat × Thread) :
    irank P (S := S) (.inl (.ready π), .inl (cRun P ph c)) = 1 := by
  cases ph <;> rfl

theorem irank_prov {e : S.providerI.F.Op} {π : Store Nat} {tp : Thread} (hnp : NotPending tp)
    {xc : (LC S P).State} : irank P (S := S) (.inl (.run e (π, tp)), .inl xc) = 2 := by
  cases tp with
  | pending a args => exact absurd rfl (hnp a args)
  | active f c => rfl

/-- The provider's finished start thread runs alone. -/
theorem srel_finished {σ π κ : Store Nat} (hI : Idle St σ π κ) :
    SRel St σ (.active {} []) π κ (.active {} []) := by
  obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hI
  refine ⟨ρp, Op, ρc, Oc, hW, Op.frameGood_empty, Op.codeGood_nil, ?_⟩
  show (⟨σ, {}, []⟩ : Config Nat) = ⟨σ, ρp.frame {}, ρp.code []⟩
  rw [(Ren.code_eq_nil_iff ρp).2 rfl]
  rfl

theorem cWait_pos (ph : Ph S) (e : S.consumerI.E.Op) (k : S.consumerI.E.Ar e → Store Nat × Thread) :
    ∃ q m, InstSystem.cpos (S.consumerI.instSys P S.scs S.consStart) (cWait P ph e k) = .wait q m := by
  cases ph with
  | none => exact ⟨none, some e, rfl⟩
  | some f => exact ⟨some f, some e, rfl⟩

/-- No upper move is legal while waiting. -/
theorem not_upper_wait {E F : Sig.{0}} {q : F.Op} {m : E.Op} {g : Ev F} {p : Pos E F}
    (h : Step (.wait q m) (.inr g) p) : False := by
  cases h

/-- No lower Opponent move is legal when idle or running. -/
theorem not_lower_O {E F : Sig.{0}} {x : Pos E F} (hx : x = .idle ∨ ∃ q, x = .run q)
    {f : Ev E} {p : Pos E F} (h : Step x (.inl f) p) (ho : Move.IsO (Sum.inl f : Move E F)) : False := by
  rcases hx with rfl | ⟨q, rfl⟩
  · cases h
  · exact not_isO_run h ho

theorem lc_run_lower (ph : Ph S) {c : Store Nat × Thread}
    {f : Ev (S.consumerI.E.withInst (Behaviour Val))} {y : (LC S P).State}
    (h : (LC S P).step (cRun P ph c) (some (.inl f)) y) :
    ∃ e, f = .ask (some e) ∧ S.consumerI.CallsOut c e ∧
      y = cWait P ph e (S.consumerI.resumeK c.1 c.2 e) := by
  cases f with
  | ask m =>
    obtain ⟨e, rfl, hc, rfl⟩ := lc_ask P ph h
    exact ⟨e, rfl, hc, rfl⟩
  | ans m n =>
    cases ph with
    | none => cases h
    | some g => cases h

/-- The consumer's answer of a stub call resumes it. -/
theorem lc_wait_resume (ph : Ph S) {e : S.consumerI.E.Op}
    {k : S.consumerI.E.Ar e → Store Nat × Thread} {v : S.consumerI.E.Ar e} {y : (LC S P).State}
    (h : (LC S P).step (cWait P ph e k) (some (.inl (.ans (m := some e) v))) y) :
    y = cRun P ph (k v) := by
  cases ph with
  | none => cases h; rfl
  | some f => cases h; rfl

theorem calloutAt_of_callsOut {c : Store Nat × Thread} {e : S.consumerI.E.Op}
    (h : S.consumerI.CallsOut c e) : CalloutAt c.1 c.2 e.1 e.2.1 := by
  obtain ⟨h', args, callout, op⟩ := h
  obtain ⟨h1, h2⟩ := ifaceOp?_eq op
  rw [h1, h2]
  exact callout

/-! ### Shared steps used by the simulation -/

theorem sh_next {σ : Store Nat} {t : Thread} {a : Nat} {rest l : List Nat} (hl : l = a :: rest)
    (hres : ResultAt σ t (.values [])) :
    (LSH S P).step (.inst (σ, t, l)) none (.inst (σ, .pending a [], rest)) := by
  subst hl
  exact .itau (SeqStep.next hres)

theorem sh_iready {σ : Store Nat} {t : Thread} {l : List Nat} (hl : l = [])
    (hres : ResultAt σ t (.values [])) :
    (LSH S P).step (.inst (σ, t, l)) (some (ansInst .ready)) (.ready σ) :=
  .iready ⟨hres, hl, rfl⟩

theorem sh_ifail {σ : Store Nat} {t : Thread} {l : List Nat} {b : Behaviour Val}
    (h : StartFailed (σ, t) b) :
    (LSH S P).step (.inst (σ, t, l)) (some (ansInst (.fail b))) .dead :=
  .ifail h

/-- The silent step of the shared world, completed. -/
theorem shc_silent {y y' : (LSH S P).State} (h : (LSH S P).step y none y') :
    Relation.TransGen (LSHc S P).Silent (.inl y) (.inl y') :=
  .single (CStep.base h)

theorem ics_prov_of {σ π : Store Nat} {ts tp : Thread} {l : List Nat}
    (hl : l = S.consStart.toList) (h : SRel St σ ts π S.scs tp) :
    ICS P St (.inl (.inst (π, tp)), .inl .pwait) (.inl (.inst (σ, ts, l))) := by
  subst hl
  exact .prov h

theorem ics_cdone_of {σ π κ : Store Nat} {ts tc : Thread} {l : List Nat} (hl : l = [])
    (hI : Idle St σ π κ) (hs : ResultAt σ ts (.values [])) (hc : ResultAt κ tc (.values [])) :
    ICS P St (.inl (.ready π), .inl (.inst (κ, tc))) (.inl (.inst (σ, ts, l))) := by
  subst hl
  exact .cdone hI hs hc

/-! ### Silent steps, case by case -/

/-- No silent step from states waiting for an outside question. -/
theorem quiet_idle {xp : (LP S P).State} {xc : (LC S P).State} (hp : PIdle P xp)
    (hc : xc = .fresh ∨ (∃ κ, xc = .ready κ) ∨ xc = .dead) {x' : (CompC S P).State}
    (h : (CompC S P).step (.inl xp, .inl xc) none x') : False := by
  cases cstep h with
  | tau₁ h₁ => obtain ⟨y, hy, -⟩ := complete_silent h₁; exact pIdle_quiet P hp hy
  | tau₂ h₂ =>
    obtain ⟨y, hy, -⟩ := complete_silent h₂
    rcases hc with rfl | ⟨κ, rfl⟩ | rfl <;> cases hy
  | sync f _ hc' =>
    cases hc' with
    | base hb => rcases hc with rfl | ⟨κ, rfl⟩ | rfl <;> cases hb
    | sink ho hst =>
      rcases hc with rfl | ⟨κ, rfl⟩ | rfl <;> exact not_lower_O (.inl rfl) hst ho

variable (hOp : St.Op = S.provOwn) (hOc : St.Oc = S.consOwn)
include hOp in
/-- The provider asked to instantiate: its start thread, and the shared world's. -/
theorem tau_pre_ask :
    IMatched P St (.inl (.inst (S.sp, startThread S.provStart)), .inl .pwait)
      (.inl .fresh, .inl .pstart) (.inl (.inst (S.sc, .active {} [], S.linkedStarts))) := by
  rcases Option.eq_none_or_eq_some S.provStart with hps | ⟨a, hps⟩
  · have hl : S.linkedStarts = S.consStart.toList := by simp [StartSetup.linkedStarts, hps]
    have e : startThread S.provStart = .active {} [] := by rw [hps]; rfl
    rw [e]
    exact .inr ⟨ics_prov_of hl (srel_finished St.idle), lt_of_rank rfl rfl (by decide : 4 < 5)⟩
  · have hl : S.linkedStarts = a :: S.consStart.toList := by simp [StartSetup.linkedStarts, hps]
    have e : startThread S.provStart = .pending a [] := by rw [hps]; rfl
    rw [e]
    have hstep := sh_next (S := S) (P := P) (σ := S.sc) (t := .active {} []) hl
      (LinkStartDiv.resultAt_finished _)
    exact .inl ⟨_, shc_silent hstep,
      .prov (Idle.startProv St.idle (LinkStart.StartSetup.provStart_own S St hOp a hps))⟩

include hOp in
/-- After the instantiation question, the provider is asked to instantiate. -/
theorem tau_pre {x' : (CompC S P).State} (h : (CompC S P).step (.inl .fresh, .inl .pstart) none x') :
    IMatched P St x' (.inl .fresh, .inl .pstart) (.inl (.inst (S.sc, .active {} [], S.linkedStarts))) := by
  cases cstep h with
  | tau₁ h₁ => obtain ⟨y, hy, -⟩ := complete_silent h₁; cases hy
  | tau₂ h₂ => obtain ⟨y, hy, -⟩ := complete_silent h₂; cases hy
  | sync f hp hc =>
    cases hc with
    | sink ho hst =>
      exact (not_lower_O (x := InstSystem.cpos _ InstSystem.St.pstart) (.inr ⟨none, rfl⟩) hst ho).elim
    | base hb =>
      cases hb
      cases hp with
      | sink _ _ => exact .inr ⟨.junk (stuck_cWait P (.inl rfl) _), lt_of_rank rfl rfl (by decide : 0 < 5)⟩
      | base hb' =>
        cases hb'
        exact tau_pre_ask hOp

omit hOp in
include hOc in
/-- The provider's start function has returned: the consumer's start function begins. -/
theorem tau_prov_ready {σ π : Store Nat} {ts tp : Thread} (h : SRel St σ ts π S.scs tp)
    (hr : ResultAt π tp (.values [])) :
    IMatched P St (.inl (.ready π), .inl (.inst (S.scs, startThread S.consStart)))
      (.inl (.inst (π, tp)), .inl .pwait) (.inl (.inst (σ, ts, S.consStart.toList))) := by
  obtain ⟨-, ⟨ρ, hres⟩, hI⟩ := h.result hr
  have e₀ : ρ.result (.values []) = .values [] := ren_start_result (.inl rfl)
  have hs : ResultAt σ ts (.values []) := e₀ ▸ hres
  rcases Option.eq_none_or_eq_some S.consStart with hcs | ⟨c, hcs⟩
  · have hl : S.consStart.toList = [] := by rw [hcs]; rfl
    have e : startThread S.consStart = .active {} [] := by rw [hcs]; rfl
    rw [e]
    exact .inr ⟨ics_cdone_of hl hI hs (LinkStartDiv.resultAt_finished _),
      lt_of_rank rfl rfl (by decide : 1 < 4)⟩
  · have hl : S.consStart.toList = [c] := by rw [hcs]; rfl
    have e : startThread S.consStart = .pending c [] := by rw [hcs]; rfl
    rw [e]
    have hstep := sh_next (S := S) (P := P) (σ := σ) (t := ts) hl hs
    exact .inl ⟨_, shc_silent hstep,
      .run none (hI.startCons (LinkStart.StartSetup.consStart_own S St hOc c hcs))⟩

omit hOp in
/-- The provider's start function has failed: the failure is reported. -/
theorem tau_prov_fail {σ π : Store Nat} {ts tp : Thread} {b : Behaviour Val}
    (h : SRel St σ ts π S.scs tp) (hf : StartFailed (π, tp) b) :
    IMatched P St (.inl .dead, .inl (.pfail b)) (.inl (.inst (π, tp)), .inl .pwait)
      (.inl (.inst (σ, ts, S.consStart.toList))) := by
  obtain ⟨r, hr, hrr, hback⟩ := LinkStart.StartSetup.result_of_startFailed hf
  obtain ⟨-, ⟨ρ, hres⟩, -⟩ := h.result hr
  have e : ρ.result r = r := ren_start_result hrr
  exact .inr ⟨.pfail (hback (c' := (σ, ts)) (e ▸ hres)), lt_of_rank rfl rfl (by decide : 0 < 4)⟩

omit hOp in
include hOc in
/-- The provider answers the instantiation question. -/
theorem tau_prov_sync {σ π : Store Nat} {ts tp : Thread} (h : SRel St σ ts π S.scs tp)
    {f : Ev (S.providerI.F.withInst (Behaviour Val))} {xp' : (LPc S P).State}
    {xc' : (LCc S P).State} (hp : (LPc S P).step (.inl (.inst (π, tp))) (some (.inr f)) xp')
    (hc : (LCc S P).step (.inl .pwait) (some (.inl f)) xc') :
    IMatched P St (xp', xc') (.inl (.inst (π, tp)), .inl .pwait)
      (.inl (.inst (σ, ts, S.consStart.toList))) := by
  have hjunk : ∀ {xp : (LP S P).State} (hxp : PIdle P xp) (p : Pos _ _),
      IMatched P St (.inl xp, .inr p) (.inl (.inst (π, tp)), .inl .pwait)
        (.inl (.inst (σ, ts, S.consStart.toList))) := fun hxp p =>
    .inr ⟨.junk (stuck_pIdle P hxp p), lt_of_rank (irank_inr _ _) rfl (by decide : 0 < 4)⟩
  cases hp with
  | sink ho hst => exact (not_isO_run hst ho).elim
  | base hb' =>
    cases hb' with
    | iready hr =>
      obtain ⟨hr, rfl⟩ := hr
      cases hc with
      | sink _ _ => exact hjunk (.inr (.inl ⟨_, rfl⟩)) _
      | base hb => cases hb; exact tau_prov_ready hOc h hr
    | ifail hf =>
      cases hc with
      | sink _ _ => exact hjunk (.inr (.inr rfl)) _
      | base hb => cases hb; exact tau_prov_fail h hf

omit hOp in
include hOc in
/-- **The provider's start function runs alone**, then answers the instantiation question. -/
theorem tau_prov {σ π : Store Nat} {ts tp : Thread} (h : SRel St σ ts π S.scs tp)
    {x' : (CompC S P).State} (hs : (CompC S P).step (.inl (.inst (π, tp)), .inl .pwait) none x') :
    IMatched P St x' (.inl (.inst (π, tp)), .inl .pwait) (.inl (.inst (σ, ts, S.consStart.toList))) := by
  cases cstep hs with
  | tau₁ h₁ =>
    obtain ⟨y, hy, rfl⟩ := complete_silent h₁
    cases hy with
    | itau hi =>
      obtain ⟨σ', ts', hi', h'⟩ := h.step hi
      exact .inl ⟨_, shc_silent (.itau (SeqStep.run hi')), .prov h'⟩
  | tau₂ h₂ => obtain ⟨y, hy, -⟩ := complete_silent h₂; cases hy
  | sync f hp hc => exact tau_prov_sync hOc h hp hc

omit hOp in
/-- A reported provider failure has no silent step. -/
theorem tau_pfail {b : Behaviour Val} {x' : (CompC S P).State}
    (h : (CompC S P).step (.inl .dead, .inl (.pfail b)) none x') : False := by
  cases cstep h with
  | tau₁ h₁ => obtain ⟨y, hy, -⟩ := complete_silent h₁; cases hy
  | tau₂ h₂ => obtain ⟨y, hy, -⟩ := complete_silent h₂; cases hy
  | sync f hp hc =>
    cases hc with
    | base hb => cases hb
    | sink ho hst =>
      exact not_lower_O (x := InstSystem.cpos _ (InstSystem.St.pfail b)) (.inr ⟨none, rfl⟩) hst ho

omit hOp in
/-- A consumer whose start function has returned has no silent step. -/
theorem tau_cdone {π κ : Store Nat} {tc : Thread} (hc : ResultAt κ tc (.values []))
    {x' : (CompC S P).State} (h : (CompC S P).step (.inl (.ready π), .inl (.inst (κ, tc))) none x') :
    False := by
  cases cstep h with
  | tau₁ h₁ => obtain ⟨y, hy, -⟩ := complete_silent h₁; cases hy
  | tau₂ h₂ =>
    obtain ⟨y, hy, -⟩ := complete_silent h₂
    cases hy with
    | itau hi => exact resultAt_no_internal hc _ hi
  | sync f hp hc' =>
    cases hc' with
    | base hb =>
      obtain ⟨e, -, hco, -⟩ := lc_run_lower (c := (κ, tc)) none hb
      exact resultAt_not_calloutAt hc (calloutAt_of_callsOut hco)
    | sink ho hst =>
      exact not_lower_O (x := InstSystem.cpos _ (InstSystem.St.inst (S := S.consumerI.instSys P S.scs S.consStart) (κ, tc))) (.inr ⟨none, rfl⟩) hst ho

omit hOp in
/-- The consumer calls the provider. -/
theorem tau_run_sync (ph : Ph S) {σ π κ : Store Nat} {ts tc : Thread} (h : CRel St σ ts π κ tc)
    {f : Ev (S.providerI.F.withInst (Behaviour Val))} {xp' : (LPc S P).State}
    {xc' : (LCc S P).State} (hp : (LPc S P).step (.inl (.ready π)) (some (.inr f)) xp')
    (hc : (LCc S P).step (.inl (cRun P ph (κ, tc))) (some (.inl f)) xc') :
    IMatched P St (xp', xc') (.inl (.ready π), .inl (cRun P ph (κ, tc)))
      (.inl (shRun P ph (σ, ts))) := by
  cases hc with
  | sink ho hst =>
    obtain ⟨q, hq⟩ := cRun_pos P ph (κ, tc)
    rw [hq] at hst
    exact (not_isO_run hst ho).elim
  | base hb =>
    obtain ⟨e, rfl, hco, rfl⟩ := lc_run_lower ph hb
    have hlt : 0 < irank P (S := S) (.inl (.ready π), .inl (cRun P ph (κ, tc))) := by
      rw [irank_run]
      exact Nat.one_pos
    cases hp with
    | sink _ _ => exact .inr ⟨.junk (stuck_cWait P (.inr ⟨ph, e, _, rfl⟩) _), hlt⟩
    | base hb' =>
      cases hb'
      exact .inr ⟨.call ph h (calloutAt_of_callsOut hco), hlt⟩

omit hOp in
/-- **The consumer runs** (its start function or an export call). -/
theorem tau_run (ph : Ph S) {σ π κ : Store Nat} {ts tc : Thread} (h : CRel St σ ts π κ tc)
    {x' : (CompC S P).State}
    (hs : (CompC S P).step (.inl (.ready π), .inl (cRun P ph (κ, tc))) none x') :
    IMatched P St x' (.inl (.ready π), .inl (cRun P ph (κ, tc))) (.inl (shRun P ph (σ, ts))) := by
  cases cstep hs with
  | tau₁ h₁ => obtain ⟨y, hy, -⟩ := complete_silent h₁; cases hy
  | tau₂ h₂ =>
    obtain ⟨y, hy, rfl⟩ := complete_silent h₂
    obtain ⟨⟨κ', tc'⟩, hi, rfl⟩ := lc_silent P ph hy
    obtain ⟨σ', ts', hi', h'⟩ := h.step hi
    exact .inl ⟨_, shc_silent (sh_tau P ph hi'), .run ph h'⟩
  | sync f hp hc => exact tau_run_sync ph h hp hc

omit hOp in
/-- **The provider accepts the consumer's call**: its first step is the shared `call_ref`. -/
theorem tau_call (ph : Ph S) {σ π κ : Store Nat} {ts tc : Thread} {e : S.consumerI.E.Op}
    (h : CRel St σ ts π κ tc) (hco : CalloutAt κ tc e.1 e.2.1) {x' : (CompC S P).State}
    (hs : (CompC S P).step (.inl (.run e (π, S.providerI.initThread e)),
      .inl (cWait P ph e (S.consumerI.resumeK κ tc e))) none x') :
    IMatched P St x' (.inl (.run e (π, S.providerI.initThread e)),
      .inl (cWait P ph e (S.consumerI.resumeK κ tc e))) (.inl (shRun P ph (σ, ts))) := by
  obtain ⟨hlt, tp₀, ts₁, hp₀, hs₁, hP, -⟩ := h.call (P := P) hco e.2.2
  have hp₀' : InternalP P (π, S.providerI.initThread e) (π, tp₀) := hp₀
  cases cstep hs with
  | tau₁ h₁ =>
    obtain ⟨y, hy, rfl⟩ := complete_silent h₁
    cases hy with
    | @tau _ _ c' hi =>
      have he : c' = (π, tp₀) := InternalP.pending_unique hi hp₀'
      subst he
      exact .inl ⟨_, shc_silent (sh_tau P ph hs₁), .provc ph hP (notPending_of_internal hp₀')⟩
  | tau₂ h₂ =>
    obtain ⟨y, hy, -⟩ := complete_silent h₂
    obtain ⟨g, hg⟩ := lc_wait_quiet P ph hy
    cases hg
  | sync f hp hc =>
    cases hp with
    | sink ho hst => exact (not_isO_run hst ho).elim
    | base hb =>
      cases hb with
      | ret hd =>
        obtain ⟨r, hr, -, -⟩ := hd
        exact (resultAt_no_internal hr _ hp₀').elim

omit hOp in
/-- The provider's answer to the consumer's call resumes the consumer. -/
theorem tau_provc_ret (ph : Ph S) {σ π κ : Store Nat} {ts tp tc : Thread} {e : S.consumerI.E.Op}
    (h : PRel St σ ts π tp κ tc e.1 e.2.1) (hnp : NotPending tp) {r : Result}
    {v : S.consumerI.E.Ar e} (hr : ResultAt π tp r)
    (hans : Answer.ofResult? (S.stubTypes.get e.1) r = some v) {xc' : (LCc S P).State}
    (hc : (LCc S P).step (.inl (cWait P ph e (S.consumerI.resumeK κ tc e)))
      (some (.inl (.ans (m := some e) v))) xc') :
    IMatched P St (.inl (.ready π), xc') (.inl (.run e (π, tp)),
      .inl (cWait P ph e (S.consumerI.resumeK κ tc e))) (.inl (shRun P ph (σ, ts))) := by
  cases hc with
  | sink _ _ =>
    exact .inr ⟨.junk (stuck_pIdle P (.inr (.inl ⟨π, rfl⟩)) _),
      lt_of_rank rfl (irank_prov hnp) (by decide : 0 < 2)⟩
  | base hc' =>
    have hy := lc_wait_resume ph hc'
    subst hy
    obtain ⟨-, hC⟩ := h.ret hr (fun vs hvs => ⟨_, ofResult?_values (hvs ▸ hans)⟩)
    have hC' : CRel St σ ts π κ
        (resumeResult κ tc (Answer.toResult (ft := S.consumerI.imports.get e.1) v)) :=
      (ofResult?_toResult' hans).symm ▸ hC
    exact .inr ⟨.run ph hC', lt_of_rank (irank_run ph π _) (irank_prov hnp) (by decide : 1 < 2)⟩

omit hOp in
/-- **The provider runs inside the consumer's call**, then answers it. -/
theorem tau_provc (ph : Ph S) {σ π κ : Store Nat} {ts tp tc : Thread} {e : S.consumerI.E.Op}
    (h : PRel St σ ts π tp κ tc e.1 e.2.1) (hnp : NotPending tp) {x' : (CompC S P).State}
    (hs : (CompC S P).step (.inl (.run e (π, tp)),
      .inl (cWait P ph e (S.consumerI.resumeK κ tc e))) none x') :
    IMatched P St x' (.inl (.run e (π, tp)), .inl (cWait P ph e (S.consumerI.resumeK κ tc e)))
      (.inl (shRun P ph (σ, ts))) := by
  cases cstep hs with
  | tau₁ h₁ =>
    obtain ⟨y, hy, rfl⟩ := complete_silent h₁
    cases hy with
    | tau hi =>
      obtain ⟨σ', ts', hi', h'⟩ := h.step hi
      exact .inl ⟨_, shc_silent (sh_tau P ph hi'), .provc ph h' (notPending_of_internal hi)⟩
  | tau₂ h₂ =>
    obtain ⟨y, hy, -⟩ := complete_silent h₂
    obtain ⟨g, hg⟩ := lc_wait_quiet P ph hy
    cases hg
  | sync f hp hc =>
    cases hp with
    | sink ho hst => exact (not_isO_run hst ho).elim
    | base hb =>
      cases hb with
      | ret hd =>
        obtain ⟨r, hr, hans, rfl⟩ := hd
        exact tau_provc_ret ph h hnp hr hans hc

include hOp hOc in
/-- **Silent composite steps** are matched divergence-sensitively. -/
theorem ics_tau {x x' : (CompC S P).State} {y : (LSHc S P).State} (hR : ICS P St x y)
    (h : (CompC S P).step x none x') : IMatched P St x' x y := by
  cases hR with
  | fresh => exact (quiet_idle (.inl rfl) (.inl rfl) h).elim
  | pre => exact tau_pre hOp h
  | prov hs => exact tau_prov hOc hs h
  | pfail hf => exact (tau_pfail h).elim
  | cdone hI hs hc => exact (tau_cdone hc h).elim
  | idle hI => exact (quiet_idle (.inr (.inl ⟨_, rfl⟩)) (.inr (.inl ⟨_, rfl⟩)) h).elim
  | run ph hC => exact tau_run ph hC h
  | call ph hC hco => exact tau_call ph hC hco h
  | provc ph hP hnp => exact tau_provc ph hP hnp h
  | dead hxp => exact (quiet_idle hxp (.inr (.inr rfl)) h).elim
  | junk hst => exact (hst _ _ h).elim

/-! ### Visible steps -/

variable (P St) in
/-- The outcome of a visible composite step: the same visible shared step. -/
def IVis (x' : (CompC S P).State) (y : (LSHc S P).State)
    (o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))) : Prop :=
  ∃ y', (LSHc S P).step y (some o) y' ∧ ICS P St x' y'

/-- An upper Opponent move from the idle position is legal in any game with the same upper
interface. -/
theorem upper_idle {E F E' : Sig.{0}} {g : Ev F} {p : Pos E F}
    (h : Step (.idle : Pos E F) (.inr g) p) :
    ∃ p' : Pos E' F, Move.IsO (Sum.inr g : Move E' F) ∧ Step (.idle : Pos E' F) (.inr g) p' := by
  cases h with
  | ask q => exact ⟨.run q, trivial, .ask q⟩

omit hOp in
/-- A consumer Opponent move into a sink, answered by the shared world's sink. -/
theorem vis_sink {xp : (LP S P).State} (hp : PIdle P xp) {xc : (LC S P).State}
    {y : (LSH S P).State} (hc : InstSystem.cpos _ xc = .idle)
    (hy : InstSystem.pos (ShSys S.toSetup P S.linkedStarts) y = .idle)
    {g : Ev (S.consumerI.F.withInst (Behaviour Val))} {p : Pos _ _}
    (hst : Step (InstSystem.cpos _ xc) (.inr g) p) :
    IVis P St (.inl xp, .inr p) (.inl y) (.inr g) := by
  rw [hc] at hst
  obtain ⟨p', ho', hst'⟩ := upper_idle (E' := S.sharedI.E) hst
  exact ⟨.inr p', CStep.sink ho' (hy ▸ hst'), .junk (stuck_pIdle P hp p)⟩

omit hOp in
/-- Visible steps of the consumer in a phase answer from a running position only. -/
theorem vis_run_none {σ π κ : Store Nat} {ts tc : Thread} (h : CRel St σ ts π κ tc)
    {g : Ev (S.consumerI.F.withInst (Behaviour Val))} {y : (LC S P).State}
    (hb : (LC S P).step (.inst (κ, tc)) (some (.inr g)) y) :
    IVis P St (.inl (.ready π), .inl y) (.inl (shRun P none (σ, ts))) (.inr g) := by
  cases hb with
  | iready hr =>
    obtain ⟨hr, rfl⟩ := hr
    obtain ⟨-, ⟨ρ, hres⟩, hI⟩ := h.result hr
    have e : ρ.result (.values []) = .values [] := ren_start_result (.inl rfl)
    exact ⟨_, CStep.base (sh_iready rfl (e ▸ hres)), .idle hI⟩
  | ifail hf =>
    obtain ⟨r, hr, hrr, hback⟩ := LinkStart.StartSetup.result_of_startFailed hf
    obtain ⟨-, ⟨ρ, hres⟩, -⟩ := h.result hr
    have e : ρ.result r = r := ren_start_result hrr
    exact ⟨_, CStep.base (sh_ifail (hback (c' := (σ, ts)) (e ▸ hres))),
      .dead (.inr (.inl ⟨π, rfl⟩))⟩

omit hOp in
theorem vis_run_some {f : S.consumerI.F.Op} {σ π κ : Store Nat} {ts tc : Thread}
    (h : CRel St σ ts π κ tc) {g : Ev (S.consumerI.F.withInst (Behaviour Val))}
    {y : (LC S P).State} (hb : (LC S P).step (.run f (κ, tc)) (some (.inr g)) y) :
    IVis P St (.inl (.ready π), .inl y) (.inl (shRun P (some f) (σ, ts))) (.inr g) := by
  cases hb with
  | ret hd =>
    obtain ⟨r, hr, hans, rfl⟩ := hd
    obtain ⟨-, ⟨ρ, hres⟩, hI⟩ := h.result hr
    have hres' : ResultAt σ ts r := by simpa only [ren_result_of_ofResult? hans ρ] using hres
    exact ⟨_, CStep.base (.ret ⟨r, hres', hans, rfl⟩), .idle hI⟩

omit hOp in
/-- **Visible composite steps of a running consumer**. -/
theorem vis_run (ph : Ph S) {σ π κ : Store Nat} {ts tc : Thread} (h : CRel St σ ts π κ tc)
    {g : Ev (S.consumerI.F.withInst (Behaviour Val))} {xc' : (LCc S P).State}
    (hc : (LCc S P).step (.inl (cRun P ph (κ, tc))) (some (.inr g)) xc') :
    IVis P St (.inl (.ready π), xc') (.inl (shRun P ph (σ, ts))) (.inr g) := by
  cases hc with
  | sink ho hst =>
    obtain ⟨q, hq⟩ := cRun_pos P ph (κ, tc)
    rw [hq] at hst
    exact (not_isO_run hst ho).elim
  | base hb =>
    cases ph with
    | none => exact vis_run_none h hb
    | some f => exact vis_run_some h hb

omit hOp in
/-- A waiting consumer makes no visible move. -/
theorem vis_wait (ph : Ph S) {e : S.consumerI.E.Op} {k : S.consumerI.E.Ar e → Store Nat × Thread}
    {g : Ev (S.consumerI.F.withInst (Behaviour Val))} {xc' : (LCc S P).State}
    (hc : (LCc S P).step (.inl (cWait P ph e k)) (some (.inr g)) xc') : False := by
  cases hc with
  | sink _ hst =>
    obtain ⟨q, m, hq⟩ := cWait_pos ph e k
    rw [hq] at hst
    exact not_upper_wait hst
  | base hb =>
    obtain ⟨g', hg⟩ := lc_wait_quiet P ph hb
    cases hg

omit hOp in
/-- Visible steps from the idle states. -/
theorem vis_idle {σ π κ : Store Nat} (hI : Idle St σ π κ)
    {g : Ev (S.consumerI.F.withInst (Behaviour Val))} {xc' : (LCc S P).State}
    (hc : (LCc S P).step (.inl (.ready κ)) (some (.inr g)) xc') :
    IVis P St (.inl (.ready π), xc') (.inl (.ready σ)) (.inr g) := by
  cases hc with
  | sink ho hst => exact vis_sink (.inr (.inl ⟨π, rfl⟩)) rfl rfl hst
  | base hb =>
    cases hb with
    | askEx st q => exact ⟨_, CStep.base (InstSystem.Step.askEx (S := ShSys S.toSetup P S.linkedStarts) σ q),
      .run (some q) (hI.start q)⟩

omit hOp in
/-- Visible steps of a consumer whose start function has returned. -/
theorem vis_cdone {σ π κ : Store Nat} {ts tc : Thread} (hI : Idle St σ π κ)
    (hs : ResultAt σ ts (.values [])) (hc₀ : ResultAt κ tc (.values []))
    {g : Ev (S.consumerI.F.withInst (Behaviour Val))} {xc' : (LCc S P).State}
    (hc : (LCc S P).step (.inl (.inst (κ, tc))) (some (.inr g)) xc') :
    IVis P St (.inl (.ready π), xc') (.inl (.inst (σ, ts, []))) (.inr g) := by
  cases hc with
  | sink ho hst => exact (not_isO_run hst ho).elim
  | base hb =>
    cases hb with
    | iready hr => obtain ⟨-, rfl⟩ := hr; exact ⟨_, CStep.base (sh_iready rfl hs), .idle hI⟩
    | ifail hf => exact absurd hf (LinkStartDiv.rest_not_failed hc₀)

omit hOp in
/-- Visible steps before instantiation. -/
theorem vis_fresh {g : Ev (S.consumerI.F.withInst (Behaviour Val))} {xc' : (LCc S P).State}
    (hc : (LCc S P).step (.inl .fresh) (some (.inr g)) xc') :
    IVis P St (.inl .fresh, xc') (.inl .fresh) (.inr g) := by
  cases hc with
  | sink _ hst => exact vis_sink (.inl rfl) rfl rfl hst
  | base hb => cases hb; exact ⟨_, CStep.base .askInst, .pre⟩

omit hOp in
/-- The provider's failure is reported. -/
theorem vis_pfail {σ : Store Nat} {ts : Thread} {rest : List Nat} {b : Behaviour Val}
    (hf : StartFailed (σ, ts) b) {g : Ev (S.consumerI.F.withInst (Behaviour Val))}
    {xc' : (LCc S P).State} (hc : (LCc S P).step (.inl (.pfail b)) (some (.inr g)) xc') :
    IVis P St (.inl .dead, xc') (.inl (.inst (σ, ts, rest))) (.inr g) := by
  cases hc with
  | sink ho hst => exact (not_isO_run hst ho).elim
  | base hb => cases hb; exact ⟨_, CStep.base (sh_ifail hf), .dead (.inr (.inr rfl))⟩

omit hOp in
/-- No visible step while the consumer asks the provider to instantiate or waits for it. -/
theorem vis_pstart {g : Ev (S.consumerI.F.withInst (Behaviour Val))} {xc' : (LCc S P).State}
    (hc : (LCc S P).step (.inl .pstart) (some (.inr g)) xc') : False := by
  cases hc with
  | sink ho hst => exact not_isO_run hst ho
  | base hb => cases hb

omit hOp in
theorem vis_pwait {g : Ev (S.consumerI.F.withInst (Behaviour Val))} {xc' : (LCc S P).State}
    (hc : (LCc S P).step (.inl .pwait) (some (.inr g)) xc') : False := by
  cases hc with
  | sink _ hst => exact not_upper_wait hst
  | base hb => cases hb

omit hOp in
/-- Visible steps after a failure: Opponent moves into sinks. -/
theorem vis_dead {xp : (LP S P).State} (hxp : PIdle P xp)
    {g : Ev (S.consumerI.F.withInst (Behaviour Val))} {xc' : (LCc S P).State}
    (hc : (LCc S P).step (.inl .dead) (some (.inr g)) xc') :
    IVis P St (.inl xp, xc') (.inl .dead) (.inr g) := by
  cases hc with
  | sink _ hst => exact vis_sink hxp rfl rfl hst
  | base hb => cases hb

omit hOp in
/-- **Visible upper steps of the consumer** are visible shared steps. -/
theorem ics_vis_right {xp : (LPc S P).State} {xc : (LCc S P).State} {y : (LSHc S P).State}
    {g : Ev (S.consumerI.F.withInst (Behaviour Val))} {xc' : (LCc S P).State}
    (hR : ICS P St (xp, xc) y) (hc : (LCc S P).step xc (some (.inr g)) xc') :
    IVis P St (xp, xc') y (.inr g) := by
  cases hR with
  | fresh => exact vis_fresh hc
  | pre => exact (vis_pstart hc).elim
  | prov _ => exact (vis_pwait hc).elim
  | pfail hf => exact vis_pfail hf hc
  | cdone hI hs hc₀ => exact vis_cdone hI hs hc₀ hc
  | idle hI => exact vis_idle hI hc
  | run ph hC => exact vis_run ph hC hc
  | call ph _ _ => exact (vis_wait ph hc).elim
  | provc ph _ _ => exact (vis_wait ph hc).elim
  | dead hxp => exact vis_dead hxp hc
  | junk hst => exact (hst _ _ (LTS.CompStep.right g hc)).elim

omit hOp in
/-- **Visible composite steps** are visible shared steps. -/
theorem ics_vis {x x' : (CompC S P).State} {y : (LSHc S P).State}
    {o : Move S.providerI.E (S.consumerI.F.withInst (Behaviour Val))} (hR : ICS P St x y)
    (h : (CompC S P).step x (some o) x') : IVis P St x' y o := by
  cases cstep h with
  | left e _ => exact prov_ev_elim e
  | right g hc => exact ics_vis_right hR hc

/-! ### The simulation -/

include hOp hOc in
/-- **The composite of the completed provider and consumer is simulated by the completed shared
world, divergence-sensitively.** -/
noncomputable def supSim : LTS.DivSimulation (CompC S P) (LSHc S P) where
  R := ICS P St
  init := .fresh
  step {x x' y l} hR h := by
    cases l with
    | none =>
      rcases ics_tau hOp hOc hR h with ⟨y', hy', hR'⟩ | ⟨hR', -⟩
      · exact ⟨y', run_of_transGen hy', hR'⟩
      · exact ⟨y, .nil _, hR'⟩
    | some o =>
      obtain ⟨y', hy', hR'⟩ := ics_vis hR h
      exact ⟨y', .vis hy' (.nil _), hR'⟩
  lt x' x := irank P x' < irank P x
  wf := InvImage.wf (irank P) Nat.lt_wfRel.wf
  tau hR h := ics_tau hOp hOc hR h

end Silmaril.Proofs.Wasm.Game.LinkStartDiv
