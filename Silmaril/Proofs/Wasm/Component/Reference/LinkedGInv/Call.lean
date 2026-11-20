module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv.Phase

/-!
# One linked call, read back

`linkCallK`/`linkCallT` of `Linked2` for `LinkedG` with an exporter given by reference data `d`
(R1, R3 as `BwdF`, R5, R6): from a configuration between calls (`ReadyB` of `LinkedGRound`,
with no waiting thread), every top-level call of the importer's export `j` on typed arguments
that terminates (`Calls`, any outcome) is a `LinkedG.SessSpec` round (`linkCall_invB`): a
well-formed round (`SessRound.Ok`) whose instance play runs from the importer's store `u` to
`u₁` and whose component import calls are an `ExpRun` of the exporter from `s` to `s₁`; a
resolved call answers the round's results and ends between calls (`ReadyB` at `s₁`, `u₁` and the
next call id); a trapped call answers a trap and `ReadyB` holds at its `resumeCfg`. A cancelled
or deadlocked outcome does not occur.

The read-back follows the forward round of `linkCall_fwdB`: the host's invocation and the
importer's `canon lift` (`call_atG`, a live run), the first stop of the rest of the run
(`first_stop`, before any host event), the importer's core activation (`phase_backB`), and its
exit: the return (`CallAtG.ret`, a live run to the resolution, after which only ticks happen:
`quiet` with `tick_back`), results of the importer that do not lift (`CallAtG.trap`), a trap of
the importer's core activation, or a trapped end of the round.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload checkLower sigN)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-- **The read-back of a specification trap**, without the host state (`trapsAtSH_back`). -/
theorem trapsAtS_back {M m' : Machine.Config (E3 P) σ} {c : (E3 P).Store (CanonHost (E3 P))}
    {tr : List (Label (E3 P) σ)} (H : TrapsAtS prof P impl M c)
    (r : Machine.Steps prof (fun _ _ => false) (DI P impl) M tr m') :
    Live m' ∨ ∃ mT : Machine.Config (E3 P) σ, m' = trapCfg mT ∧ mT.core = c := by
  obtain ⟨tr₁, mT, rT, hr, hrun, hlive, hu, hc⟩ := H
  rcases trapsAtSH_back (h := mT.host) ⟨tr₁, mT, rT, hr, hrun, hlive, hu, hc, rfl⟩ r with h |
    ⟨mT', -, -, h₁, h₂, -⟩
  · exact .inl h
  · exact .inr ⟨mT', h₁, h₂⟩

/-- The outcome of a call holding at a locked-down configuration is a trap. -/
theorem out_trap_of_locked {m : Machine.Config (E3 P) σ} {c : CallId} {out : CallOutcome}
    (ho : out.Holds (fun _ _ => false) c m) (hl : m.store.lockdown = true) : out = .trap := by
  cases out with
  | resolved r => exact absurd (ho.2.1.symm.trans hl) (by decide)
  | trap => rfl
  | deadlock => exact absurd (ho.1.2.1.symm.trans hl) (by decide)

/-- What a read-back round shows for its outcome `o`: results `ws` are the resolution of the
call, ending between calls (no new waiting thread); a trap is a trapped call, `resumeCfg` of
which is between calls. -/
def BackOutB {e : ExpSpec} (d : e.RefData P) (pl : d.Pl) (ii : Nat) (Ii : SInst)
    (s₀ ui : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P)))) (g : CanonHost (E3 P) → Nat)
    (Oc₀ : Own) (fs : List (CFuncInst (core3P P))) (m m' : Machine.Config (E3 P) σ) (k : Nat)
    (s₁ : e.St) (u₁ : Store Nat) (out : CallOutcome) : Option (List IVal) → Prop
  | some ws => out = .resolved (some (ws.map toRefVal)) ∧
      ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m' s₁ u₁ (k + 1) ∧ m'.store.waiting = m.store.waiting
  | none => out = .trap ∧ ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs (resumeCfg m m') s₁ u₁ (k + 1)

section Round

variable {lg : LinkedG} {d : lg.exp.RefData P} {pl : d.Pl} {ii : Nat} {Ii : SInst}
  {s₀ ui : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
  {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {fs : List (CFuncInst (core3P P))}
  {jf : Nat → Nat}

/-- `ReadyB` at `resumeCfg` of a trapped call, from the parts at the trapped core store. -/
theorem ready_trapB (hRes : d.Resume) {m m' : Machine.Config (E3 P) σ} {s s₁ : lg.exp.St}
    {u u₁ : Store Nat} {k : Nat} (R : ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m s u k) {f : Ii.F.Op}
    (hTA : TrapAtG d pl Ii s₀ u F₀ g Oc₀ f m.store s₁ m'.core u₁) :
    ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs (resumeCfg m m') s₁ u₁ (k + 1) :=
  ⟨R.ctl, R.lock, R.nest, R.funcs, R.imp, R.exp,
    fun x hx => Nat.lt_succ_of_lt (R.pending x hx), fun x hx => Nat.lt_succ_of_lt (R.results x hx),
    lready_trapG hRes R.inv hTA⟩

/-- **A terminating linked call between calls is a specification round** (`BackOutB`). -/
theorem linkCall_invB (ST : StatB P lg d pl ii Ii s₀ ui F₀ g tr Oc₀ fs jf) (hFr : d.Frame)
    (hBw : d.BwdF) (hRes : d.Resume) (hB : d.Bounded) {m : Machine.Config (E3 P) σ}
    {s : lg.exp.St} {u : Store Nat} {k : Nat}
    (R : ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m s u k) (hwt : m.store.waiting = [])
    (j : Fin lg.imp.exports.length) {vs : List IVal}
    (hvs : ValTy.checkList lg.imp.exports[j].ty.params vs = true)
    {m' : Machine.Config (E3 P) σ} {out : CallOutcome}
    (hcalls : Calls prof (fun _ _ => false) (DI P impl) m ⟨k⟩ ⟨jf j⟩ (vs.map toRefVal) m' out) :
    ∃ (dr : LinkedG.SessRound lg Ii) (u₁ : Store Nat) (s₁ : lg.exp.St)
      (o : Option (List IVal)),
      dr.j = j ∧ dr.vs = vs ∧ dr.Ok ∧ Ii.Path P (.idle u) dr.instMoves (.idle u₁) ∧
      LinkedG.ExpRun P lg s dr.dss.flatten s₁ ∧ dr.ans = o.map .vals ∧
      BackOutB d pl ii Ii s₀ ui F₀ g Oc₀ fs m m' k s₁ u₁ out o := by
  have SI := ST.imp
  have hx : lg.imp.exports[j] ∈ lg.imp.exports := List.getElem_mem j.isLt
  obtain ⟨nm, hcore⟩ := SI.good.core _ hx
  have hk : lg.imp.exports[j].core < lg.imp.mod.exports.length :=
    (List.getElem?_eq_some_iff.mp hcore).1
  have hflat : lg.imp.mod.exports[lg.imp.exports[j].core] = (nm, lg.imp.exports[j].ty.flat) :=
    (List.getElem?_eq_some_iff.mp hcore).2
  have hxs : (lowerArgs lg.imp.exports[j].ty.params vs).map (·.type) =
      lg.imp.mod.exports[lg.imp.exports[j].core].2.params := by
    rw [hflat]
    exact lowerList_types _ _ hvs
  obtain ⟨f, hf₁, hf₂, hft⟩ := typedCallI SI.inst hk hxs
  have hft' : Ii.exports.get f.1 = fnOf lg.imp.exports[j].ty.flat := by rw [hft, hflat]
  obtain ⟨hmax, hmaxr, hres⟩ := ST.wire.arity.1 _ hx
  obtain ⟨hpf, hrf⟩ := ST.wire.floats.1 _ hx
  have ha : Ii.addrs.getD lg.imp.exports[j].core 0 = Ii.addr f.1 := by
    rw [← hf₁]
    rfl
  have hfj : m.store.funcs[jf j]? = some (.lifted (s₀.funcs.length + Ii.addr f.1)
      (liftedFt lg.imp.exports[j]) {} ⟨ii⟩) := by
    rw [R.funcs, ← ha]
    exact ST.lifted j
  have hck : checkLower lg.imp.exports[j].ty.params vs =
      some (lowerArgs lg.imp.exports[j].ty.params vs) := by
    simp only [checkLower, hvs, ↓reduceIte]
  obtain ⟨ιi, hii, hth, hleave⟩ := R.imp
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atG (impl := impl) prof m R.lock k
    (jf j) _ ii lg.imp.exports[j] vs hpf hvs hmax hres hmaxr hrf hii hth hfj
  -- the invariants at the start of the importer's core activation
  have hR₀ : LReadyG d pl Ii s₀ ui F₀ g Oc₀ M₀.ref s u := by
    refine lready_frame hFr R.inv hat.core (by show M₀.store.funcs = _; rw [hat.store]; rfl) ?_
    intro i hi
    show M₀.store.insts[i]? = _
    rw [hat.store]
    exact List.getElem?_set_ne (fun h => ST.out (by rw [h]; exact hi))
  obtain ⟨F, hI₀⟩ := linv_readyG hR₀ ST.own (f := f) hf₂
  have SIu : ImpStatG P lg.imp Ii u F₀ g tr := ⟨SI.good, SI.inst, R.inv.wfI, SI.tramp, SI.inv⟩
  obtain ⟨F₁, -, -, -, -, -, -, hH₀⟩ := R.inv.rel
  have hFG₀ : FrameG d pl ii th M₀.store := by
    refine ⟨by rw [hat.store]; exact R.lock, ?_, ?_, ST.out, ?_⟩
    · rw [hat.store, hat.thread]
      have h₁ : ArenaField.threads.get? (storeG₃ m.store lg.imp.exports[j] ii
          (enterInst ιi ⟨m.store.threads.length⟩) k (vs.map toRefVal))
          ⟨m.store.threads.length⟩ = some ((thread₁ m.store.tasks).withIndex 1) :=
        threads_get_last rfl
      have h₂ : ArenaField.tasks.get? (storeG₃ m.store lg.imp.exports[j] ii
          (enterInst ιi ⟨m.store.threads.length⟩) k (vs.map toRefVal))
          ((thread₁ m.store.tasks).withIndex 1).task =
          some ((taskG₁ lg.imp.exports[j] ii m.store.callers
            ⟨m.store.threads.length⟩).withState .started) :=
        tasks_get_last rfl
      simp only [instOfThread?, h₁, h₂, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rfl
    · rw [hat.store]
      exact ⟨enterInst ιi ⟨m.store.threads.length⟩, List.getElem?_set_self (lt_of_getElem? hii),
        hleave⟩
    · intro w hw
      obtain ⟨xe, hxe⟩ := hw
      obtain ⟨-, hblk⟩ := hFr.lifted pl s m.ref F₁ w xe hH₀ hxe
      rw [hat.store]
      show ∃ ι, (List.set m.store.insts ii (enterInst ιi ⟨m.store.threads.length⟩))[d.inst pl w]? =
        some ι ∧ _
      have hne : ii ≠ d.inst pl w := fun h => ST.out (by rw [h]; exact hblk)
      rw [List.getElem?_set_ne hne]
      exact R.exp w ⟨xe, hxe⟩
  have hM₀ : M₀ = coreCfg M₀ th K segs rest (M₀.ref.core,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr f.1)
        (lowerArgs lg.imp.exports[j].ty.params vs)) := eq_coreCfg hat.ctl
  have hS₀f : M₀.ref.funcs = m.store.funcs := by
    rw [Machine.Config.ref_toCStore, hat.store]; rfl
  -- the run
  obtain ⟨trc, hs, hev, hnoint, ho⟩ := hcalls
  obtain ⟨m₂, st, r₁⟩ := Machine.Steps.cons_iff.mp hs
  have hm₂ : m₂ = invokedG m k (jf j) (vs.map toRefVal) := by
    cases st
    rfl
  subst hm₂
  rcases hpre.inv r₁ with hl | ⟨tr'', etr, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  have hm'l : ¬ Live m' := fun hl => hl.not_holds _ _ ho
  obtain ⟨trA, trB, EE, etrAB, rA, hEE, hhA, rB⟩ := first_stop r' hm'l
  have hevB : ∀ ev, Label.host ev ∈ trB → CallHostEvent ⟨k⟩ ev :=
    fun ev hm => hev ev (etr ▸ List.mem_append_right _ (etrAB ▸ List.mem_append_right _ hm))
  -- at a locked-down stop the call trapped
  have hlocked : EE.store.lockdown = true → EE.ctl = [] → m' = EE ∧ out = .trap := by
    intro hlk hct
    have e₁ := steps_of_locked hct hlk rB
    subst e₁
    exact ⟨rfl, out_trap_of_locked ho hlk⟩
  have hni : EE.store.lockdown = true → EE.ctl = [] →
      ∀ msg, Label.trap (.internal msg) ∉ trA := by
    intro hlk hct msg hm
    obtain ⟨-, hout⟩ := hlocked hlk hct
    exact hnoint hout msg (etr ▸ List.mem_append_right _ (etrAB ▸ List.mem_append_left _ hm))
  rw [hM₀] at rA
  obtain ⟨rs, dss, s₁, x', hrel, hexp, hend⟩ := phase_backB (prof := prof) (impl := impl) SIu
    ST.wire hFr hBw hB th K segs rest trA.length M₀ s F _ _ trA EE le_rfl hI₀ hFG₀ rA hhA hEE hni
  have hok : ∀ w : Ii.F.Ar f, (⟨j, vs, f, rs, w, dss⟩ : LinkedG.SessRound lg Ii).Ok :=
    fun _ => ⟨_, hck, hf₁, hf₂, hrel⟩
  rcases hend with ⟨tr₂, C', S'', F', yc, l, m₁, hh₂, hnco, hx', r₂, hIc, hFGc, hXc, hpath⟩ |
    ⟨hlk, hct, hTA, hpath⟩
  · -- the importer's core activation exited
    have hS₀ : S''.funcs = m.store.funcs := by rw [callExt_funcs hXc, hS₀f]
    have hTA₀ : TrapAtG d pl Ii s₀ u F₀ g Oc₀ f m.store s₁ yc.1 x'.1 :=
      trapAt_of_linv hIc hS₀
    obtain ⟨ρc, Oc, hL, -⟩ := hIc.rel
    obtain ⟨ts, hst', htt⟩ := linvG_typed SIu hIc
    rcases hx' with ⟨zs, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h', ys', hc'⟩
    · -- the importer returned values
      obtain ⟨cvs, hcode, hm⟩ := status_values hst
      have hc : (yc.2.config (Store.mapH g yc.1)).code = Silmaril.Wasm.Execution.Core.vals cvs :=
        (config_code_mapH g yc.1 yc.2).trans hcode
      obtain ⟨vs', hv, hvm⟩ := values_back P hL hst' htt hc
      have hm' : (vs'.map (linkMap s₀ ρc).val).mapM Silmaril.Wasm.SingleThreaded.toFlat? =
          some zs := by
        rw [hvm]
        exact hm
      have hvs' : vs' = cvs := (map_val_of_mapM _ hm').symm.trans hvm
      have hr : Silmaril.Wasm.Game.ResultAt x'.1 x'.2 (.values cvs) := hvs' ▸ hv
      obtain ⟨w, hw, -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run SIu.wf
        (valEnv_throwsBelow Ii _) hIc.run hr
      have hP : Ii.Path P (.idle u)
          (LinkedG.SessRound.instMoves ⟨j, vs, f, rs, w, dss⟩) (.idle x'.1) :=
        .cons (.call u f) (hpath [.inr (.ans f w)] (.idle x'.1)
          (fun _ _ hr' => .cons (.oret hr' hr hw) (.nil _)))
      have hty : zs.map (·.type) = ValTy.flatList lg.imp.exports[j].ty.results :=
        results_typed hft' hw hm
      have hR' : (LinkedG.SessRound.ans ⟨j, vs, f, rs, w, dss⟩ : Option Payload) =
          (liftArgs lg.imp.exports[j].ty.results zs).map .vals :=
        lifted_answer hw hm
      have hlS'' : S''.lockdown = false := hFGc.lock
      cases hl : liftArgs lg.imp.exports[j].ty.results zs with
      | none =>
        rw [hl] at hR'
        rcases trapsAtS_back (hat.trap S'' C' yc zs hlS'' hty hl) r₂ with hl' | ⟨mT, rfl, hcT⟩
        · exact absurd hl' hEE
        obtain ⟨rfl, rfl⟩ := hlocked rfl rfl
        refine ⟨⟨j, vs, f, rs, w, dss⟩, x'.1, s₁, none, rfl, rfl, hok w, hP, hexp, hR', rfl,
          ready_trapB (f := f) hRes R ?_⟩
        show TrapAtG d pl Ii s₀ u F₀ g Oc₀ f m.store s₁ mT.core x'.1
        rw [hcT]
        exact hTA₀
      | some ws =>
        rw [hl] at hR'
        -- the call's records in the store at the return
        have hM₀s : M₀.ref.toCStore = _ := hat.store
        obtain ⟨RT, hRT⟩ := prefix_concat_split (hM₀s ▸ hXc.tasks)
        obtain ⟨RH, hRH⟩ := prefix_concat_split (hM₀s ▸ hXc.threads)
        obtain ⟨CL, hCL⟩ := prefix_concat_split (hM₀s ▸ hXc.callers)
        have hIi : S''.insts[ii]? = some (enterInst ιi ⟨m.store.threads.length⟩) := by
          rw [hXc.insts_out ii ST.out, hM₀s]
          exact List.getElem?_set_self (lt_of_getElem? hii)
        obtain ⟨tr₃, mE, hlr, hmE⟩ := hat.ret S'' C' RT RH CL yc zs ws hRT hRH hCL hIi hlS''
          hty hl
        rcases hlr.inv r₂ with hl' | ⟨tr₄, etr₄, r₄⟩
        · exact absurd hl' hEE
        have hmEc : mE.ctl = [] := by rw [hmE]
        have e₄ : EE = mE := steps_nil_of_ctl hmEc r₄
          (fun ev hm => hh₂ ev (etr₄ ▸ List.mem_append_right _ hm))
        subst e₄
        have hwE : EE.store.waiting = m.store.waiting := by
          rw [hmE]
          show S''.waiting = m.store.waiting
          rw [hXc.eq, hM₀s]
          rfl
        have hlE : EE.store.lockdown = false := by rw [hmE]; exact hlS''
        have hresE : EE.result? ⟨k⟩ = some (some (ws.map toRefVal)) := by
          rw [hmE]
          unfold Machine.Config.result?
          show ((M₀.results ++ [((⟨k⟩ : CallId), some (ws.map toRefVal))]).find?
            (fun p => p.1 == (⟨k⟩ : CallId))).map Prod.snd = _
          rw [hat.results, List.find?_append, find?_freshG R.results]
          simp
        have htick : ∀ m₃, Machine.Step prof (fun _ _ => false) (DI P impl) EE (.host .tick) m₃ →
            ∃ trT, LRun prof (fun _ _ => false) (DI P impl) m₃ trT EE :=
          fun m₃ hs₃ => tick_back hlE (hwE.trans hwt) hs₃
        rcases quiet (c := ⟨k⟩) hmEc (by rw [hresE]; simp) htick _ trB m' le_rfl rB hevB with
          rfl | hl'
        swap
        · exact absurd ho (hl'.not_holds _ _)
        have hout : out = .resolved (some (ws.map toRefVal)) := by
          cases out with
          | resolved r => exact congrArg _ (Option.some.inj (ho.2.2.symm.trans hresE))
          | trap => exact absurd (ho.symm.trans hlE) (by decide)
          | deadlock => exact absurd (ho.2.symm.trans hresE) (by simp)
        have hnest : S''.nestingDepth = 1 := by
          rw [callExt_nest hXc, hM₀s]
          show m.store.nestingDepth + 1 = 1
          rw [R.nest]
        refine ⟨⟨j, vs, f, rs, w, dss⟩, x'.1, s₁, some ws, rfl, rfl, hok w, hP, hexp, hR', hout,
          ?_, hwE⟩
        -- between calls again
        have hR₁ := lready_afterG R.inv hIc
        rw [hmE]
        refine ⟨rfl, hlS'', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show S''.nestingDepth - 1 = 0
          rw [hnest]
        · show S''.funcs = fs
          rw [hS₀, R.funcs]
        · exact ⟨_, List.getElem?_set_self (lt_of_getElem? hIi),
            threadsOk_after ιi ⟨m.store.threads.length⟩,
            (removeThread_enter_mayLeave _ _).trans hleave⟩
        · intro w' hw'
          obtain ⟨xe, hxe⟩ := hw'
          obtain ⟨-, hblk⟩ := hFr.lifted pl s m.ref F₁ w' xe hH₀ hxe
          show ∃ ι, (List.set S''.insts ii _)[d.inst pl w']? = some ι ∧ _
          have hne : ii ≠ d.inst pl w' := fun h => ST.out (by rw [h]; exact hblk)
          rw [List.getElem?_set_ne hne]
          exact hFGc.exp w' ⟨xe, hxe⟩
        · intro x hx
          have hx' : x ∈ M₀.pending := hx
          rw [hat.pending] at hx'
          rcases List.mem_append.mp hx' with hx' | hx'
          · exact Nat.lt_succ_of_lt (R.pending x hx')
          · rw [List.mem_singleton.mp hx']
            exact Nat.lt_succ_self k
        · intro x hx
          have hx' : x ∈ M₀.results ++ [((⟨k⟩ : CallId), some (ws.map toRefVal))] := hx
          rw [hat.results] at hx'
          rcases List.mem_append.mp hx' with hx' | hx'
          · exact Nat.lt_succ_of_lt (R.results x hx')
          · rw [List.mem_singleton.mp hx']
            exact Nat.lt_succ_self k
        · refine lready_frame hFr hR₁ hIc.core.symm rfl ?_
          intro i hi
          show (S''.insts.set ii _)[i]? = _
          exact List.getElem?_set_ne (fun h => ST.out (by rw [h]; exact hi))
    · -- the importer's core activation trapped
      have e₂ := steps_of_locked rfl rfl r₂
      subst e₂
      obtain ⟨rfl, rfl⟩ := hlocked rfl rfl
      have hr : Silmaril.Wasm.Game.ResultAt x'.1 x'.2 .trap := by
        rcases status_trap hst with hc | ⟨a, hc⟩
        · exact trap_back P hL hst' htt ((config_code_mapH g yc.1 yc.2).trans hc)
        · exact (throwing_back P hL hst' htt ((config_code_mapH g yc.1 yc.2).trans hc)).elim
      obtain ⟨w, hw, -⟩ := Silmaril.Wasm.Game.ScalarInstance.sanswer_of_run SIu.wf
        (valEnv_throwsBelow Ii _) hIc.run hr
      refine ⟨⟨j, vs, f, rs, w, dss⟩, x'.1, s₁, none, rfl, rfl, hok w,
        .cons (.call u f) (hpath [.inr (.ans f w)] (.idle x'.1)
          (fun _ _ hr' => .cons (.oret hr' hr hw) (.nil _))), hexp,
        lifted_trap (x := lg.imp.exports[j]) (fun _ h => by cases h) hw, rfl,
        ready_trapB hRes R hTA₀⟩
    · exact absurd hc' (hnco h' ys')
  · -- a trapped end of the round
    obtain ⟨rfl, rfl⟩ := hlocked hlk hct
    exact ⟨⟨j, vs, f, rs, .trap, dss⟩, x'.1, s₁, none, rfl, rfl, hok _, .cons (.call u f) hpath,
      hexp, rfl, rfl, ready_trapB hRes R (hTA.funcs_congr hS₀f)⟩

end Round

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv
