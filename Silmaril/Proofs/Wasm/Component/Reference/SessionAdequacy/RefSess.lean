module

public import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.CallTrap
public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.Transfer
public import Silmaril.Wasm.Component.Reference.SessionAdequacy.Defs

/-!
# Resumable reference sessions are specification sessions

The specification of a resumable session (`SessSpec`, `SessionAdequacy.Defs`): a chain of
calls threading the instance's Core store, each a returned call (`RetAt`) or a trapped call
(`TrapAt`), the next call starting at the store the trap left.

* `sess_specToRef`: every specification session is a reference session (`sessObs`);
* `sess_refToSpec`: every reference session is a specification session.

Per call, between calls (`ReadyAt`): `call_forward_trap` builds the trapping machine run from a
trapped call of the specification, and `call_trap_inv` reads a trapping machine run back; the
core store of the trapped configuration is the store the trapped call left, so the resumed
configuration (`resumeCfg`) is again between calls (`resume_ready`). Resolved calls are #669's
(`call_forward_ret`, `seq_step`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower)
open Silmaril.Wasm.Execution.Core (Store Config Steps invoke vals throwing Result)
open Silmaril.Wasm.SingleThreaded (ofFlat toFlat?)
open Silmaril.Wasm.Game (InternalP Reach ResultAt statusP)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

theorem refOuts_inj : ∀ {o o' : List (Option (List IVal))}, refOuts o = refOuts o' → o = o'
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: o, a' :: o', h => by
    simp only [refOuts, List.map_cons, List.cons.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    rw [refOuts_inj (o := o) (o' := o') h₂]
    cases a with
    | none => cases a' with
      | none => rfl
      | some _ => cases h₁
    | some ws => cases a' with
      | none => cases h₁
      | some ws' =>
        simp only [Option.map_some, Option.some.injEq] at h₁
        rw [map_toRefVal_inj h₁]

variable {P : Profile} {prof : ProfileKind}

/-- **A trapped call keeps the store well formed.** -/
theorem _root_.Silmaril.Wasm.Component.Reference.TrapAt.wellFormed {c : Simple}
    {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : c.mod.IsInst I) {x : SimpleExport}
    (hcore : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat)) {vs : List IVal}
    {s s' : Store Nat} (hw : I.WellFormed s) (h : TrapAt P c I x vs s s') : I.WellFormed s' := by
  obtain ⟨nm, hc⟩ := hcore
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hc
  obtain ⟨t', res, run, final, -⟩ := h.run
  have hxs : (lowerArgs x.ty.params vs).map (·.type) = c.mod.exports[x.core].2.params := by
    rw [hget]
    exact lowerList_types _ _ h.typed
  have steps : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s (I.addrs.getD x.core 0)
      ((lowerArgs x.ty.params vs).map ofFlat)) (t'.config s') :=
    internalP_steps (H := Nat) run
  obtain ⟨w, hw'⟩ := answer_at hI hw hk hxs steps (r := res) final
  have hpath : I.Activation P s [.inr (.ask (opAt hI hk hxs)),
      .inr (.ans (opAt hI hk hxs) w)] s' :=
    .cons (.call s _) (.cons (.oret run final hw') (.nil _))
  refine (Silmaril.Wasm.Game.ScalarInstance.WellFormed.activation hw ?_ hpath).1
  intro e v hm
  simp at hm

/-! ## Configurations between calls -/

theorem fresh_succ {G : Garb P} {k : Nat} (h : G.Fresh k) : G.Fresh (k + 1) :=
  ⟨fun x hx => Nat.lt_succ_of_lt (h.pending x hx), fun x hx => Nat.lt_succ_of_lt (h.results x hx)⟩

/-- Resuming between calls is between calls, at the core store of the trapped
configuration. -/
theorem resumeCfg_ready (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P) (m' : Machine.Config (E3 P) Unit) :
    resumeCfg (readyCfg cs ι fs G) m' = readyCfg m'.core ι fs G := rfl

variable {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
  {cs : (core3P P).Store (CanonHost (core3P P))} {x : SimpleExport}
  {vs : List IVal} {ι : InstState} {fs : List (CFuncInst (core3P P))}
  {G : Garb P} {k j : Nat}

/-- The resumed configuration after a trapped call is between calls. -/
theorem resume_ready (C : CallCtxAt P c I cs x vs) (R : ReadyAt I cs ι G k)
    {cs' : (core3P P).Store (CanonHost (core3P P))}
    (h : TrapAt P c I x vs (Store.mapH (fun _ => 0) cs) (Store.mapH (fun _ => 0) cs')) :
    ReadyAt I cs' ι G (k + 1) :=
  ⟨h.wellFormed C.inst C.core R.wf, R.threads, fresh_succ R.fresh⟩

/-! ## One trapped call -/

/-- The static data of a call, with the store of a lift trap. -/
structure CallRunT (prof : ProfileKind) (P : Profile)
    (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P) (k j : Nat) (x : SimpleExport)
    (vs : List IVal) (I : Silmaril.Wasm.Game.ScalarInstance) : Prop where
  run : ∃ M₀ th K segs rest tr₁, LRun prof (refHost P).hr (D P)
      (invokedAt cs ι fs G k j (vs.map toRefVal)) tr₁ M₀ ∧
    CallAtKT prof P cs (enterInst ι ⟨G.threads.length⟩) fs G k j x (I.addrs.getD x.core 0) vs
      M₀ th K segs rest

theorem callRunT (C : CallCtxAt P c I cs x vs) (R : ReadyAt I cs ι G k)
    (hff : floatFreeList x.ty.params = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true)
    (hf : fs[j]? = some (.lifted (I.addrs.getD x.core 0) (liftedFt x) {} ⟨0⟩)) :
    CallRunT prof P cs ι fs G k j x vs I :=
  ⟨call_at_kT prof cs ι _ fs G k j _ x vs hff C.typed hmax hres hmaxr hffr
    (addThread?_ok R.threads _) (removeThread?_enter _ _) hf⟩

/-- **A trapped call of the specification is a trapping call of the machine**, whose trapped
configuration holds the store the call left. -/
theorem call_forward_trap (C : CallCtxAt P c I cs x vs) (R : ReadyAt I cs ι G k)
    (CR : CallRunT prof P cs ι fs G k j x vs I) {s' : Store Nat}
    (h : TrapAt P c I x vs (Store.mapH (fun _ => 0) cs) s') :
    ∃ m', Calls prof (refHost P).hr (D P) (readyCfg cs ι fs G) ⟨k⟩ ⟨j⟩ (vs.map toRefVal) m'
      .trap ∧ m'.core = Store.mapH (someHost P) s' := by
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := CR.run
  obtain ⟨t', res, run, final', hres⟩ := h.run
  obtain ⟨tr₂, htr₂, r₂⟩ := core_to_result (prof := prof) C hat.toCallAtK.ctl hat.toCallAtK.core run
  obtain ⟨nm, hcore⟩ := C.core
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  have hxs : (lowerArgs x.ty.params vs).map (·.type) = c.mod.exports[x.core].2.params := by
    rw [hget]
    exact C.lowered
  have steps : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (invoke (Store.mapH (fun _ => 0) cs) (I.addrs.getD x.core 0)
        ((lowerArgs x.ty.params vs).map ofFlat)) (t'.config s') :=
    internalP_steps (H := Nat) run
  have hlive : Live M₀ := ⟨by rw [hat.toCallAtK.ctl]; exact List.cons_ne_nil _ _,
    hat.toCallAtK.lock⟩
  have hcode : (t'.config (Store.mapH (someHost P) s')).code = res.toAdmin :=
    (config_code_mapH' _ _ _).trans final'
  have hinv : Machine.Steps prof (refHost P).hr (D P) (readyCfg cs ι fs G)
      (.host (.invoke ⟨k⟩ ⟨j⟩ (vs.map toRefVal)) :: (tr₁ ++ tr₂))
      (coreCfg M₀ th K segs rest (Store.mapH (someHost P) s', t')) :=
    .cons (invoke_step R _) (steps_append hpre.steps r₂)
  have hnh : ∀ ev, Label.host ev ∉ tr₁ ++ tr₂ := by
    intro ev hm
    rcases List.mem_append.mp hm with hm | hm
    · exact LRun.no_host hpre ev hm
    · exact not_host_of_core htr₂ ev hm
  have hnt : ∀ r, Label.trap r ∉ tr₁ ++ tr₂ := by
    intro r hm
    rcases List.mem_append.mp hm with hm | hm
    · exact LRun.no_trap hpre hlive r hm
    · exact not_trap_of_core htr₂ r hm
  -- a trap of the core activation
  have trapCase : (E3 P).status (Store.mapH (someHost P) s') t' = .returned .trap →
      ∃ m', Calls prof (refHost P).hr (D P) (readyCfg cs ι fs G) ⟨k⟩ ⟨j⟩ (vs.map toRefVal)
        m' .trap ∧ m'.core = Store.mapH (someHost P) s' := by
    intro hst
    have s₃ : Step prof (refHost P).hr (D P)
        (coreCfg M₀ th K segs rest (Store.mapH (someHost P) s', t')) (.trap .coreTrap)
        (trapCfg (coreCfg M₀ th K segs rest (Store.mapH (someHost P) s', t'))) :=
      Step.coreTrap rfl hst
    refine ⟨trapCfg (coreCfg M₀ th K segs rest (Store.mapH (someHost P) s', t')),
      ⟨(tr₁ ++ tr₂) ++ [.trap .coreTrap], ?_, ?_, ?_, ?_⟩, rfl⟩
    · simpa only [List.cons_append] using steps_append hinv (.cons s₃ (.refl _))
    · intro ev hm
      rcases List.mem_append.mp hm with hm | hm
      · exact absurd hm (hnh ev)
      · simp at hm
    · intro _ msg hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hnt _ hm
      · simp at hm
    · exact trapCfg_lockdown _
  cases res with
  | trap =>
    exact trapCase (by
      show flatStatus (statusP P _ _) = _
      rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_trap hcode]
      rfl)
  | throw a =>
    exact trapCase (by
      show flatStatus (statusP P _ _) = _
      rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_throwing hcode]
      rfl)
  | values cvs =>
    obtain ⟨w, hw⟩ := answer_at C.inst C.wf hk hxs steps final'
    have htyped : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal
        (I.exports.get (opAt C.inst hk hxs).1).results cvs := by
      unfold Silmaril.Wasm.Game.Answer.ofResult? at hw
      dsimp only at hw
      split_ifs at hw with ht
      exact ht
    rw [opAt_type] at htyped
    obtain ⟨ys, hys⟩ : ∃ ys, cvs.mapM toFlat? = some ys :=
      Silmaril.Proofs.Wasm.Component.Core3G.toFlat?_isSome htyped
    have hty : ys.map (·.type) = ValTy.flatList x.ty.results := by
      have ht := run_typed_at C.inst C.wf hk hxs steps final' hys
      rw [hget] at ht
      exact ht
    have hst : (E3 P).status (Store.mapH (someHost P) s') t' = .returned (.values ys) := by
      show flatStatus (statusP P _ _) = _
      rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_values hcode]
      simp only [flatStatus, hys]
    have s₃ : Step prof (refHost P).hr (D P)
        (coreCfg M₀ th K segs rest (Store.mapH (someHost P) s', t')) .tau
        (retCfg M₀ th K segs rest (Store.mapH (someHost P) s', t') ys) :=
      Step.coreReturned rfl hst
    have hpre' : Machine.Steps prof (refHost P).hr (D P) (readyCfg cs ι fs G)
        (.host (.invoke ⟨k⟩ ⟨j⟩ (vs.map toRefVal)) :: ((tr₁ ++ tr₂) ++ [.tau]))
        (retCfg M₀ th K segs rest (Store.mapH (someHost P) s', t') ys) := by
      simpa only [List.cons_append] using steps_append hinv (.cons s₃ (.refl _))
    have hl : liftArgs x.ty.results ys = none := by
      cases hl : liftArgs x.ty.results ys with
      | none => rfl
      | some ws => simp [coreRes, hys, liftOutcome, hl] at hres
    obtain ⟨mT, rT, hrT, hl₁, hsT, hlive₁, hu⟩ := hat.trapT _ ys hty hl
    have hmT : Machine.Steps prof (refHost P).hr (D P) (readyCfg cs ι fs G)
        (.host (.invoke ⟨k⟩ ⟨j⟩ (vs.map toRefVal)) ::
          ((((tr₁ ++ tr₂) ++ [.tau]) ++ [.tau]) ++ [.trap rT])) (trapCfg mT) := by
      simpa only [List.cons_append] using
        steps_append (steps_append hpre' hl₁.steps) (.cons hu.1 (.refl _))
    refine ⟨trapCfg mT, ⟨_, hmT, ?_, ?_, trapCfg_lockdown _⟩, ?_⟩
    · intro ev hm
      exfalso
      rcases List.mem_append.mp hm with hm | hm
      · rcases List.mem_append.mp hm with hm | hm
        · rcases List.mem_append.mp hm with hm | hm
          · exact hnh ev hm
          · simp at hm
        · simp at hm
      · simp at hm
    · intro _ msg hm
      rcases List.mem_append.mp hm with hm | hm
      · rcases List.mem_append.mp hm with hm | hm
        · rcases List.mem_append.mp hm with hm | hm
          · exact hnt _ hm
          · simp at hm
        · simp at hm
      · simp only [List.mem_singleton, Label.trap.injEq] at hm
        exact hrT msg hm.symm
    · show mT.core = _
      rw [hsT.2]
      rfl

/-- After a lift trap keeping the store, the call traps at that store. -/
theorem trapsNextT_inv {m₁ m' : Machine.Config (E3 P) Unit} {k : Nat}
    {tr : List (Label (E3 P) Unit)} {out : CallOutcome} (hT : TrapsNextT prof P m₁)
    (hs : Machine.Steps prof (refHost P).hr (D P) m₁ tr m')
    (ho : out.Holds (refHost P).hr ⟨k⟩ m') :
    ∃ mT, (mT.store = m₁.store ∧ mT.core = m₁.core) ∧ m' = trapCfg mT := by
  obtain ⟨mT, r, -, hlr, hst, hlive, hu⟩ := hT
  rcases hlr.inv hs with hl | ⟨tr₄, -, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  cases r' with
  | refl => exact absurd ho (hlive.not_holds _ _)
  | cons s r'' =>
    obtain ⟨rfl, rfl⟩ := hu.2 _ _ s
    exact ⟨mT, hst, steps_of_locked rfl rfl r''⟩

/-- **A trapping call of the machine is a trapped call of the specification**, ending at the
core store of the trapped configuration. -/
theorem call_trap_inv (C : CallCtxAt P c I cs x vs) (R : ReadyAt I cs ι G k)
    (hff : floatFreeList x.ty.params = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true)
    (hf : fs[j]? = some (.lifted (I.addrs.getD x.core 0) (liftedFt x) {} ⟨0⟩))
    {m' : Machine.Config (E3 P) Unit}
    (hcalls : Calls prof (refHost P).hr (D P) (readyCfg cs ι fs G) ⟨k⟩ ⟨j⟩ (vs.map toRefVal) m'
      .trap) :
    TrapAt P c I x vs (Store.mapH (fun _ => 0) cs) (Store.mapH (fun _ => 0) m'.core) := by
  obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
  obtain ⟨m₂, s, r⟩ := Machine.Steps.cons_iff.mp hs
  have r₁ : Machine.Steps prof (refHost P).hr (D P) (invokedAt cs ι fs G k j (vs.map toRefVal))
      tr m' := invoke_inv_k s ▸ r
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_at_kT prof cs ι _ fs G k j _ x vs hff
    C.typed hmax hres hmaxr hffr (addThread?_ok R.threads _) (removeThread?_enter _ _) hf
  rcases hpre.inv r₁ with hl | ⟨tr'', e, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  rcases coreCfg_steps_inv (core_run_k hat.ctl hat.core r') with
    ⟨y, -, hm, -⟩ | ⟨y, pre, l, m₁, tr₂, hy, -, e', hx, r''⟩
  · have hl : Live (coreCfg M₀ th K segs rest y) := ⟨List.cons_ne_nil _ _, hat.lock⟩
    exact absurd (hm ▸ ho) (hl.not_holds _ _)
  have hev' : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨k⟩ ev := fun ev hm =>
    hev ev (by rw [e, e']; exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_cons_of_mem _ hm)))
  have hreach : Reach P (Store.mapH (fun _ => 0) cs,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs))
      (Store.mapH (fun _ => 0) y.1, y.2) :=
    reach_mapH (fun _ => 0) (coreSteps_internal hy)
  rcases hx with ⟨ys, hst, -, hm⟩ | ⟨hst, -, hm⟩ | ⟨h, args, hst⟩
  · obtain ⟨-, hty, -⟩ := C.values hy hst
    obtain ⟨cvs, hc, hmm⟩ := status_values hst
    cases hl : liftArgs x.ty.results ys with
    | some ws =>
      have hres' := result?_next R.fresh x j (I.addrs.getD x.core 0) (vs.map toRefVal)
        (ws.map toRefVal) y.1 (InstState.removeThread 1 (enterInst ι ⟨G.threads.length⟩)) fs
      obtain ⟨he, -⟩ := out_of_resolvesK (hat.ret y ys ws hty hl) hres' (hm ▸ r'') hev' ho
      cases he
    | none =>
      obtain ⟨mT, hsT, rfl⟩ := trapsNextT_inv (hat.trapT y ys hty hl) (hm ▸ r'') ho
      have hcore' : (trapCfg mT).core = y.1 := by
        show mT.core = _
        rw [hsT.2]
        rfl
      rw [hcore']
      exact ⟨C.typed, y.2, .values cvs, hreach, (config_code_mapH _ _ _).trans hc,
        by simp only [coreRes, hmm, liftOutcome, hl]⟩
  · have hm' : m' = trapCfg (coreCfg M₀ th K segs rest y) := steps_of_locked rfl rfl (hm ▸ r'')
    subst hm'
    rcases status_trap hst with hc | ⟨a, hc⟩
    · exact ⟨C.typed, y.2, .trap, hreach, (config_code_mapH _ _ _).trans hc, rfl⟩
    · exact ⟨C.typed, y.2, .throw a, hreach, (config_code_mapH _ _ _).trans hc, rfl⟩
  · exact (C.no_callout hy hst).elim

/-! ## Sessions -/

variable {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}

/-- **Specification sessions are reference sessions**, between calls. -/
theorem sessCalls_forward (hc : c.Good) (hf : c.FloatFree) (ha : c.Arity) (hI : c.mod.IsInst I) :
    ∀ (calls : List (Fin c.exports.length × List IVal)) (outs : List (Option (List IVal)))
      (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState) (G : Garb P) (k : Nat)
      (s' : Store Nat), ReadyAt I cs ι G k → TypedCalls c calls →
      SessSpec P c I (Store.mapH (fun _ => 0) cs) (specCalls c calls) outs s' →
      SessCalls prof (refHost P)
        (readyCfg cs ι (liftedFuncs P (fun k => I.addrs.getD k 0) c) G) k (callArgs c calls)
        (refOuts outs)
  | [], outs, cs, ι, G, k, s', _, _, h => by
    cases h
    exact .nil _ _
  | (j, vs) :: calls, outs, cs, ι, G, k, s', R, ht, h => by
    have h' : SessSpec P c I (Store.mapH (fun _ => 0) cs)
        ((c.exports[j], vs) :: specCalls c calls) outs s' := h
    have hvs : ValTy.checkList c.exports[j].ty.params vs = true := ht _ List.mem_cons_self
    have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
    have C : CallCtxAt P c I cs c.exports[j] vs := ⟨hI, R.wf, hc.core _ hx, hvs⟩
    obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
    obtain ⟨hff, hffr⟩ := hf _ hx
    have hget := liftedFuncs_get? (P := P) c (fun k => I.addrs.getD k 0) j.isLt
    have ht' : TypedCalls c calls := fun q hq => ht q (List.mem_cons_of_mem _ hq)
    cases h' with
    | @ret _ s₁ _ _ _ ws _ outs' hret hseq =>
      have CR := callRun (prof := prof) C R hff hmax hres hmaxr hffr hget
      obtain ⟨cs₁, hcs₁, hcall⟩ := call_forward_ret C R CR hret
      have R₁ : ReadyAt I cs₁ (InstState.removeThread 1 (enterInst ι ⟨G.threads.length⟩))
          (nextGarb G c.exports[j] k j (I.addrs.getD c.exports[j].core 0) (vs.map toRefVal)
            (ws.map toRefVal)) (k + 1) :=
        ⟨hcs₁ ▸ hret.wellFormed hI (hc.core _ hx) R.wf, threadsOk_after _ _,
          fresh_next R.fresh _ _ _ _ _⟩
      exact .ret hcall (sessCalls_forward hc hf ha hI calls outs' cs₁ _ _ (k + 1) s' R₁ ht'
        (hcs₁ ▸ hseq))
    | @trap _ s₁ _ _ _ _ outs' htrap hseq =>
      have CR := callRunT (prof := prof) C R hff hmax hres hmaxr hffr hget
      obtain ⟨m', hcall, hcore'⟩ := call_forward_trap C R CR htrap
      have hwf : I.WellFormed s₁ := htrap.wellFormed hI (hc.core _ hx) R.wf
      have hs₁ : Store.mapH (fun _ => (0 : Nat)) m'.core = s₁ := by
        rw [hcore']
        exact mapH_mapH_of_noHostFns _ _ (noHostFns_of_wf hI.2.1 hwf)
      have R₁ : ReadyAt I m'.core ι G (k + 1) :=
        resume_ready C R (hs₁ ▸ htrap)
      refine .trap hcall ?_
      rw [resumeCfg_ready]
      exact sessCalls_forward hc hf ha hI calls outs' m'.core ι G (k + 1) s' R₁ ht'
        (hs₁ ▸ hseq)

/-- **Reference sessions are specification sessions**, between calls. -/
theorem sess_inv (hc : c.Good) (hf : c.FloatFree) (ha : c.Arity) (hI : c.mod.IsInst I) :
    ∀ (calls : List (Fin c.exports.length × List IVal))
      (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState) (G : Garb P) (k : Nat)
      (outs : List (Option (List RVal))), ReadyAt I cs ι G k → TypedCalls c calls →
      SessCalls prof (refHost P)
        (readyCfg cs ι (liftedFuncs P (fun k => I.addrs.getD k 0) c) G) k (callArgs c calls)
        outs →
      ∃ outs' s', SessSpec P c I (Store.mapH (fun _ => 0) cs) (specCalls c calls) outs' s' ∧
        outs = refOuts outs'
  | [], cs, ι, G, k, outs, _, _, hS => by
    cases hS
    exact ⟨[], _, .nil _, rfl⟩
  | (j, vs) :: calls, cs, ι, G, k, outs, R, ht, hS => by
    have hvs : ValTy.checkList c.exports[j].ty.params vs = true := ht _ List.mem_cons_self
    have ht' : TypedCalls c calls := fun q hq => ht q (List.mem_cons_of_mem _ hq)
    cases hS with
    | ret hcall hS' =>
      obtain ⟨cs₁, ι₁, G₁, ws, rfl, hret, rfl, R₁⟩ := seq_step hc hf ha hI R j hvs hcall
      obtain ⟨outs', s', hseq, rfl⟩ := sess_inv hc hf ha hI calls cs₁ ι₁ G₁ (k + 1) _ R₁ ht' hS'
      exact ⟨some ws :: outs', s', .ret hret hseq, rfl⟩
    | @trap _ m₁ _ _ _ _ _ hcall hS' =>
      have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
      have C : CallCtxAt P c I cs c.exports[j] vs := ⟨hI, R.wf, hc.core _ hx, hvs⟩
      obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
      obtain ⟨hff, hffr⟩ := hf _ hx
      have htrap := call_trap_inv C R hff hmax hres hmaxr hffr
        (liftedFuncs_get? (P := P) c (fun k => I.addrs.getD k 0) j.isLt) hcall
      rw [resumeCfg_ready] at hS'
      obtain ⟨outs', s', hseq, rfl⟩ := sess_inv hc hf ha hI calls m₁.core ι G (k + 1) _
        (resume_ready C R htrap) ht' hS'
      exact ⟨none :: outs', s', .trap htrap hseq, rfl⟩

/-- **Specification sessions are reference sessions** (every profile and component choice
profile). -/
theorem sess_specToRef (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I)
    (calls : List (Fin c.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (s : Store Nat) (ht : TypedCalls c calls)
    (h : SessSpec P c I I.store (specCalls c calls) outs s) :
    refOuts outs ∈ sessObs P prof c calls := by
  obtain ⟨I', cs, hI', hcs, hinst⟩ := inst_forward P prof hc.good hc.inst
  obtain rfl := NumModule.IsInst.unique hI' hI
  have hS := sessCalls_forward (prof := prof) hc.good hc.floatFree hc.arity hI' calls outs cs {}
    ⟨[], [], [], [], [], [], []⟩ 0 s (ready_afterInst hI' hcs) ht (hcs ▸ h)
  refine ⟨afterInst P cs (liftedFuncs P (fun k => I'.addrs.getD k 0) c), ⟨0⟩, exportMap c,
    calls.map fun q => (⟨q.1⟩ : FuncId), hinst, mapM_lookup hc.good calls, ?_⟩
  rw [zip_callArgs]
  exact hS

/-- **Reference sessions are specification sessions** (every profile and component choice
profile). -/
theorem sess_refToSpec (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    (calls : List (Fin c.exports.length × List IVal)) (ht : TypedCalls c calls)
    {o : List (Option (List RVal))} (ho : o ∈ sessObs P prof c calls) :
    ∃ (I : Silmaril.Wasm.Game.ScalarInstance) (outs : List (Option (List IVal))) (s : Store Nat),
      c.mod.IsInst I ∧ SessSpec P c I I.store (specCalls c calls) outs s ∧ o = refOuts outs := by
  obtain ⟨I, cs, hI, hcs, hinst⟩ := instPhase P prof c hc.good hc.inst
  obtain ⟨m₀, inst, es, fs, hr, hfs, hS⟩ := ho
  have he : m₀ = afterInst P cs (liftedFuncs P (fun k => I.addrs.getD k 0) c) ∧
      inst = ⟨0⟩ ∧ es = exportMap c := by
    simpa only [InstResult.instance.injEq] using hinst _ hr
  have hfs' : fs = calls.map fun q => (⟨q.1⟩ : FuncId) :=
    Option.some.inj (hfs.symm.trans (he.2.2 ▸ mapM_lookup hc.good calls))
  have hS₁ : SessCalls prof (refHost P) (readyCfg cs {}
      (liftedFuncs P (fun k => I.addrs.getD k 0) c) ⟨[], [], [], [], [], [], []⟩) 0
      (callArgs c calls) o := by
    have hS₀ : SessCalls prof (refHost P) (afterInst P cs (liftedFuncs P
        (fun k => I.addrs.getD k 0) c)) 0 (fs.zip ((calls.map fun q =>
          (c.exports[q.1].name, q.2.map toRefVal)).map Prod.snd)) o := he.1 ▸ hS
    rw [← zip_callArgs, ← hfs']
    exact hS₀
  obtain ⟨outs, s, hseq, rfl⟩ := sess_inv hc.good hc.floatFree hc.arity hI calls cs {} _ 0 o
    (ready_afterInst hI hcs) ht hS₁
  exact ⟨I, outs, s, hI, hcs ▸ hseq, rfl⟩

end Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
