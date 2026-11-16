module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.Round

/-!
# Forward runs of a linked call: one call

`linkCall_fwd`: from a configuration between linked calls (`ReadyL` at the importer's store `u`
and the exporter's `π`), a well-formed specification round (`SessRound.Ok`) whose instance play
runs from `u` to `u₁` and whose component import calls are an `ExpRunT` segment of the exporter
from `π` to `π₁` is a call of the reference machine (`Calls`, top-level call `k` of the linked
component's export `j`):

* a round answering results `ws` is a resolved call ending at the next configuration between
  calls, with `ReadyL` at `u₁`, `π₁`;
* a round answering a trap is a trapped call (with a specification trap), and `LReady` holds at
  the core store of the trapped configuration, `u₁` and `π₁`; `resumeCfg` resumes from there.

The machine run is the host's invocation, the deterministic prefix of `call_atLKTS`, the
segmented run of the importer's core activation (`rounds_fwd`, `lseg_run`), and its end: a
return (`CallAtLKTS.ret`, or `CallAtLKTS.trap` where the lift fails), a trap of the importer's
core activation (`coreTrap_end`), or a trapping nested call (`nest_trapCore`, `nest_trapLift`,
`nest_trapArgs`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## The host's invocation -/

/-- The host's invocation of call `k` from a configuration between linked calls. -/
theorem invoke_stepL {cs : (core3P P).Store (CanonHost (core3P P))} {ιe ιi : InstState}
    {fs : List (CFuncInst (core3P P))} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k : Nat}
    (hG : G.Fresh k) (j : Nat) (args : List Silmaril.Wasm.Component.Reference.Val) :
    Step prof (fun _ _ => false) (DI P impl) (readyCfgL cs ιe ιi fs G ST h₀)
      (.host (.invoke ⟨k⟩ ⟨j⟩ args)) (invokedAtL cs ιe ιi fs G ST h₀ k j args) := by
  refine Step.hostInvoke ⟨rfl, rfl, rfl⟩ fun y hy e => ?_
  have hlt := hG.pending y hy
  rw [e] at hlt
  exact Nat.lt_irrefl _ hlt

/-- **A trapped end after the invocation is a trapped call.** -/
theorem calls_of_trapEnd {cs : (core3P P).Store (CanonHost (core3P P))} {ιe ιi : InstState}
    {fs : List (CFuncInst (core3P P))} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k j : Nat}
    (hG : G.Fresh k) {args : List Silmaril.Wasm.Component.Reference.Val}
    {c : (E3 P).Store (CanonHost (E3 P))}
    (h : TrapEnd prof P impl (invokedAtL cs ιe ιi fs G ST h₀ k j args) c) :
    ∃ m', Calls prof (fun _ _ => false) (DI P impl) (readyCfgL cs ιe ιi fs G ST h₀) ⟨k⟩ ⟨j⟩ args
      m' .trap ∧ m'.core = c := by
  obtain ⟨tr, m', r, hh, hi, hl, hc⟩ := h
  exact ⟨m', ⟨tr, .cons (invoke_stepL hG j args) r, fun ev hm => absurd hm (hh ev),
    fun _ msg => hi msg, hl⟩, hc⟩

/-! ## One call -/

section Call

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

/-- What a forward linked call shows for the outcome `o` of a round: results `ws` are a resolved
call ending between calls with `ReadyL` at `u₁`, `π₁`; a trap is a trapped call with `LReady` at
the core store of the trapped configuration. -/
def FwdOut (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ) (l : Linked2)
    (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (s₀ u₀ : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (fs : List (CFuncInst (core3P P)))
    (m : Machine.Config (E3 P) σ) (h₀ : σ) (k j : Nat)
    (args : List Silmaril.Wasm.Component.Reference.Val) (u₁ π₁ : Store Nat) :
    Option (List Silmaril.Wasm.Component.Val) → Prop
  | some ws => ∃ (cs' : (core3P P).Store (CanonHost (core3P P))) (ιe' ιi' : InstState)
      (G' : Garb P σ) (ST' : List Subtask),
      Calls prof (fun _ _ => false) (DI P impl) m ⟨k⟩ ⟨j⟩ args
        (readyCfgL cs' ιe' ιi' fs G' ST' h₀) (.resolved (some (ws.map toRefVal))) ∧
      ReadyL P l Ie Ii s₀ u₀ F₀ cs' ιe' ιi' G' u₁ π₁ (k + 1)
  | none => ∃ m', Calls prof (fun _ _ => false) (DI P impl) m ⟨k⟩ ⟨j⟩ args m' .trap ∧
      LReady P l Ie Ii s₀ u₀ F₀ m'.core u₁ π₁

/-- **A specification round is a call of the reference machine** (`FwdOut`). -/
theorem linkCall_fwd (S₀ : LStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOk l Ii s₀ fs) {cs : (core3P P).Store (CanonHost (core3P P))}
    {ιe ιi : InstState} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k : Nat} {u π : Store Nat}
    (R : ReadyL P l Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k) (d : Linked2.SessRound l Ii) (hok : d.Ok)
    {u₁ π₁ : Store Nat} (hpath : Ii.Path P (.idle u) d.instMoves (.idle u₁))
    (hexp : Linked2.ExpRunT P l Ie π d.dss.flatten π₁)
    {o : Option (List Silmaril.Wasm.Component.Val)} (hans : d.ans = o.map .vals) :
    FwdOut prof P impl l Ie Ii s₀ u₀ F₀ fs (readyCfgL cs ιe ιi fs G ST h₀) h₀ k
      (l.exp.exports.length + d.j) (d.vs.map toRefVal) u₁ π₁ o := by
  obtain ⟨xs, hck, hf₁, hf₂, hrel⟩ := hok
  have hvs : ValTy.checkList l.imp.exports[d.j].ty.params d.vs = true := by
    unfold checkLower at hck
    split_ifs at hck with h
    exact h
  have hxs : xs = lowerArgs l.imp.exports[d.j].ty.params d.vs := by
    simp only [checkLower, hvs, ↓reduceIte, Option.some.injEq] at hck
    exact hck.symm
  subst hxs
  have hx : l.imp.exports[d.j] ∈ l.imp.exports := List.getElem_mem d.j.isLt
  obtain ⟨nm, hcore⟩ := S₀.impGood.core _ hx
  have hflat : l.imp.mod.exports[l.imp.exports[d.j].core]? =
      some (nm, l.imp.exports[d.j].ty.flat) := hcore
  have hft' : Ii.exports.get d.f.1 = fnOf l.imp.exports[d.j].ty.flat := by
    have hlt : d.f.1.val < l.imp.mod.exports.length := by
      rw [hf₁]
      exact (List.getElem?_eq_some_iff.mp hflat).1
    have e₁ : Ii.exports.get d.f.1 = fnOf (l.imp.mod.exports[d.f.1.val]'hlt).2 := by
      simp only [List.get_eq_getElem, S₀.impInst.2.2, List.getElem_map]
    rw [e₁]
    have e₂ : l.imp.mod.exports[d.f.1.val]'hlt = (nm, l.imp.exports[d.j].ty.flat) := by
      have := (List.getElem?_eq_some_iff.mp hflat).2
      simp only [← hf₁] at this
      exact this
    rw [e₂]
  obtain ⟨hmax, hmaxr, hres⟩ := S₀.arity.1 _ hx
  obtain ⟨hpf, hrf⟩ := S₀.floats.1 _ hx
  have ha : Ii.addrs.getD l.imp.exports[d.j].core 0 = Ii.addr d.f.1 := by
    rw [← hf₁]
    rfl
  have hfj : fs[l.exp.exports.length + d.j]? = some (.lifted (s₀.funcs.length + Ii.addr d.f.1)
      (liftedFt l.imp.exports[d.j]) {} ⟨2⟩) := ha ▸ hfs d.j
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atLKTS (impl := impl) prof cs ιe ιi fs G
    ST h₀ k (l.exp.exports.length + d.j) _ l.imp.exports[d.j] d.vs hpf hvs hmax hres hmaxr hrf
    R.thI R.leave hfj
  have S : LStat P l Ie Ii u F₀ M₀ (ownOf s₀) := S₀.move R.inv.wfI (hat.funcs.trans hB₀.symm)
  have hI₀ : LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) d.f
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr d.f.1)
        (lowerArgs l.imp.exports[d.j].ty.params d.vs)) (u, Ii.initThread d.f) π :=
    linv_ready R.inv hf₂ rfl
  -- the instance's play
  have hpath' : Ii.Path P (.running d.f u (Ii.initThread d.f))
      (callMoves d.cs ++ [.inr (.ans d.f d.w)]) (.idle u₁) := by
    have h : Ii.Path P (.idle u) (.inr (.ask d.f) :: (callMoves d.cs ++ [.inr (.ans d.f d.w)]))
        (.idle u₁) := hpath
    cases h with
    | cons h₁ h₂ =>
      cases h₁
      exact h₂
  obtain ⟨recs, yc, hseg, hend⟩ := rounds_fwd S R.inv d.cs d.dss _ (u, Ii.initThread d.f) π π₁
    u₁ hI₀ hrel hexp hpath'
  -- the machine run to the end of the importer's segmented run
  have hlive₀ : Live M₀ := by
    rw [hat.start]
    exact coreCfg_extN_live _ _ _ _ _ _ _ _ _
  obtain ⟨ιe', N', C', tr₂, hte', hq₂, r₂⟩ := lseg_run (prof := prof) (impl := impl) (K := K)
    (segs := segs) (rest := rest) hat.frame hseg ιe [] M₀.conts R.thE (LInv.linkOk S hI₀)
  have r₁₂ : Steps prof (fun _ _ => false) (DI P impl)
      (invokedAtL cs ιe ιi fs G ST h₀ k (l.exp.exports.length + d.j) (d.vs.map toRefVal))
      (tr₁ ++ tr₂) (coreCfg (extN M₀ ιe' N' C') th K segs rest yc) := by
    refine Adequacy.steps_append hpre.steps ?_
    rw [← hat.start] at r₂
    exact r₂
  have hq₁₂ : Quiet (tr₁ ++ tr₂) := (Quiet.of_lrun hpre hlive₀).append hq₂
  -- a trapped end
  have hfr : ∀ c, TrapEnd prof P impl (coreCfg (extN M₀ ιe' N' C') th K segs rest yc) c →
      LReady P l Ie Ii s₀ u₀ F₀ c u₁ π₁ → d.ans = none →
      FwdOut prof P impl l Ie Ii s₀ u₀ F₀ fs (readyCfgL cs ιe ιi fs G ST h₀) h₀ k
        (l.exp.exports.length + d.j) (d.vs.map toRefVal) u₁ π₁ o := by
    intro c hT hRc hn
    have ho : o = none := by
      cases o with
      | none => rfl
      | some ws =>
        rw [hn] at hans
        cases hans
    subst ho
    obtain ⟨m', hc, hcore⟩ := calls_of_trapEnd R.fresh (TrapEnd.steps r₁₂ hq₁₂ hT)
    exact ⟨m', hc, hcore ▸ hRc⟩
  rcases hend with ⟨t', r, hIc, final, hw⟩ | ⟨c, hN, hRc, hw⟩
  · -- the importer's part finished
    obtain ⟨ρp, Op, ρc, Oc, hLc, -⟩ := hIc.rel
    cases r with
    | throw b => exact (not_result_throw hLc final).elim
    | trap =>
      exact hfr _ (coreTrap_end (status_of_trap (gL P l) hLc final)) (lready_after R.inv hIc)
        (lifted_trap (x := l.imp.exports[d.j]) (fun _ h => by cases h) hw)
    | values cvs =>
      have htyped : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal
          (Ii.exports.get d.f.1).results cvs := by
        unfold Silmaril.Wasm.Game.Answer.ofResult? at hw
        dsimp only at hw
        split_ifs at hw with ht
        exact ht
      rw [hft'] at htyped
      obtain ⟨zs, hm⟩ := Silmaril.Proofs.Wasm.Component.Core3G.toFlat?_isSome htyped
      have hst := status_of_values (gL P l) hLc final hm
      have hty : zs.map (·.type) = ValTy.flatList l.imp.exports[d.j].ty.results :=
        results_typed hft' hw hm
      have hR' : d.ans = (liftArgs l.imp.exports[d.j].ty.results zs).map .vals :=
        lifted_answer hw hm
      have s₃ : Step prof (fun _ _ => false) (DI P impl)
          (coreCfg (extN M₀ ιe' N' C') th K segs rest yc) .tau
          (retCfg (extN M₀ ιe' N' C') th K segs rest yc zs) := Step.coreReturned rfl hst
      cases hl : liftArgs l.imp.exports[d.j].ty.results zs with
      | none =>
        rw [hl] at hR'
        exact hfr _ (TrapEnd.steps (.cons s₃ (.refl _)) Quiet.tau
          (hat.trap ιe' N' C' yc zs hty hl).trapEnd) (lready_after R.inv hIc) hR'
      | some ws =>
        rw [hl] at hR'
        have ho : o = some ws := by
          cases o with
          | none =>
            rw [hans] at hR'
            cases hR'
          | some ws' =>
            rw [hans] at hR'
            simp only [Option.map_some, Option.some.injEq, Payload.vals.injEq] at hR'
            rw [hR']
        subst ho
        obtain ⟨C'', tr₃, mE, hlr, rfl⟩ := hat.ret ιe' N' C' yc zs ws hty hl
        refine ⟨_, _, _, _, _, ⟨(tr₁ ++ tr₂) ++ (.tau :: tr₃), .cons (invoke_stepL R.fresh _ _)
          (Adequacy.steps_append r₁₂ (.cons s₃ hlr.steps)), ?_, (fun h => by cases h),
          ⟨rfl, rfl, result?_nextL R.fresh _ _ _ _ _ _ _ _ _ _ _ _⟩⟩,
          ⟨lready_after R.inv hIc, hte', threadsOk_after _ _,
            (removeThread_enter_mayLeave _ _).trans R.leave, fresh_nextL R.fresh _ _ _ _ _ _⟩⟩
        intro ev hm
        exfalso
        rcases List.mem_append.mp hm with hm | hm
        · exact hq₁₂.1 ev hm
        · rcases List.mem_cons.mp hm with hm | hm
          · cases hm
          · exact Adequacy.LRun.no_host hlr ev hm
  · -- a nested call trapped
    obtain ⟨fid, a, p, ys, hst, hf, hr, hcase⟩ := hN
    have hS := LInv.linkOk S hI₀ recs yc _ ys hseg hst
    have hT : TrapEnd prof P impl (coreCfg (extN M₀ ιe' N' C') th K segs rest yc) c := by
      rcases hcase with ⟨hws, rfl⟩ | ⟨ws, e, hws, he, hend', rfl⟩
      · exact nest_trapArgs hat.frame hte' hst hf hr hS hws
      · rcases hend' with h | ⟨zs, h, hn⟩
        · exact nest_trapCore hat.frame hte' hst hf hr hS hws he h
        · exact nest_trapLift hat.frame hte' hst hf hr hS hws he h hn
    exact hfr c hT hRc (lifted_trap (x := l.imp.exports[d.j]) (fun _ h => by cases h) hw)

end Call

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
