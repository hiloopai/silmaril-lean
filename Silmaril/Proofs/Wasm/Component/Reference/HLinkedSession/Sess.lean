module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Call
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.SilentCall

/-!
# Sessions of `HLinked2.toRef`, specification to reference

* `sessH_fwd`: a specification session (`HLinked2.SessSpec`) from the stores of `ReadyL` (at
  `l.toW`), whose host calls are answered as `g` prescribes (`HostRun g` on all of them), is a
  resumable session of the reference machine (`SessRun`) under any host that handles the host
  callouts as `g` (`Handles`), from the configuration between calls in host state `h₀` to one in
  the host state at the end of `HostRun`, with the reference images of the outcomes; `ReadyL`
  holds at the end (`linkCall_fwdG` for each round, `resumeCfg` after a trap);
* `hlinked2_sess_specToRef`: under `HLinked2.Adequate` and a typed host (`HLinked2.HostTyped`),
  the specification sessions from the instances' stores are session observations of `l.toRef`
  under the logging host `answerHostS P (logG g)`, with the final host state and log of the
  `HostRun` of `logG g`;
* `handles_silent`: the host that never answers handles the host callouts as `silentG` (each
  one blocks the importer's thread and the synchronous lift loop traps `cannotBlockSync`);
  `hlinked2_silent_specToRef`: the specification sessions whose host calls are all answered by a
  trap are session observations of `l.toRef` under `silentHost`;
* `hlinked2_silent_cannotBlock_sess`: after such a session, a call whose round makes a host call
  traps `cannotBlockSync` under `silentHost` (`silent_call`); `hlinked2_silent_session_sess`: the
  session extended by that call answers a trap for it.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)

local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}
  {g : σ → HostFuncId → List RVal → Option (List RVal × σ)}

/-! ## Calls of a session -/

/-- The reference calls of a session: the importer's export `j` is component function
`host.length + exp.exports.length + j`. -/
def callArgsH (l : HLinked2)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)) :
    List (FuncId × List RVal) :=
  calls.map fun q => (⟨l.host.length + l.exp.exports.length + q.1⟩, q.2.map toRefVal)

theorem mapM_lookupH {l : HLinked2} (hIg : l.imp.Good) :
    ∀ (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)),
      (l.refCalls calls).mapM (fun q => l.exportMap.lookup q.1) =
        some (calls.map fun q => (⟨l.host.length + l.exp.exports.length + q.1⟩ : FuncId))
  | [] => rfl
  | q :: calls => by
    have ih := mapM_lookupH hIg calls
    show ((l.imp.exports[q.1].name, q.2.map toRefVal) :: l.refCalls calls).mapM _ = _
    rw [List.mapM_cons, ih]
    simp only [exportMapH_lookup hIg q.1]
    rfl

theorem zip_callArgsH {l : HLinked2}
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)) :
    (calls.map fun q => (⟨l.host.length + l.exp.exports.length + q.1⟩ : FuncId)).zip
        ((l.refCalls calls).map Prod.snd) = callArgsH l calls := by
  induction calls with
  | nil => rfl
  | cons q calls ih =>
    simp only [HLinked2.refCalls, List.map_cons, List.zip_cons_cons, callArgsH] at ih ⊢
    rw [ih]

/-- A logging host is typed when its answering function is. -/
theorem HostTyped.logG {l : HLinked2} (hT : l.HostTyped g) : l.HostTyped (HLinked2.logG g) := by
  intro s i hi ws rs s' h
  simp only [HLinked2.logG, Option.map_eq_some_iff] at h
  obtain ⟨⟨rs', t⟩, hg, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, -⟩ := he
  exact hT s.1 i hi ws rs' t hg

/-- `silentG` is typed: it never answers. -/
theorem HostTyped.silentG (l : HLinked2) : l.HostTyped (HLinked2.silentG (σ := σ)) := by
  intro s i hi ws rs s' h
  cases h

/-! ## Sessions between calls -/

section Sess

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

/-- **Specification sessions with host calls answered are resumable sessions of the machine
between calls**, ending between calls in the final host state of the `HostRun`. -/
theorem sessH_fwd (hHd : Handles prof P impl g l) (hT : l.HostTyped g)
    (S₀ : HStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOkH l Ii s₀ fs)
    {calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)}
    {outs : List (Option (List Silmaril.Wasm.Component.Val))}
    {hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))} {u π u' π' : Store Nat}
    (hspec : HLinked2.SessSpec P l Ie Ii u π calls outs hs u' π') :
    ∀ (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState) (G : Garb P σ)
      (ST : List Subtask) (h₀ : σ) (k : Nat) (s' : σ),
      ReadyL P l.toW Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k → HostRun g h₀ hs.flatten s' →
      ∃ (cs' : (core3P P).Store (CanonHost (core3P P))) (ιe' ιi' : InstState) (G' : Garb P σ)
        (ST' : List Subtask),
        LinkedSession.SessRun prof (linkHost impl) (readyCfgL cs ιe ιi fs G ST h₀) k
          (callArgsH l calls) (refOuts outs) (readyCfgL cs' ιe' ιi' fs G' ST' s') ∧
        ReadyL P l.toW Ie Ii s₀ u₀ F₀ cs' ιe' ιi' G' u' π' (k + calls.length) := by
  induction hspec with
  | nil =>
    intro cs ιe ιi G ST h₀ k s' R hr
    obtain rfl := hostRun_nil hr
    exact ⟨cs, ιe, ιi, G, ST, .nil _ _, R⟩
  | @round u π u₁ π₁ u' π' cs outs hs o d hok hpath hexp hans _ ih =>
    intro cs₀ ιe ιi G ST h₀ k s' R hr
    rw [List.flatten_cons] at hr
    obtain ⟨s₁, hr₁, hr₂⟩ := hostRun_split hr
    have hlen : k + 1 + cs.length = k + (cs.length + 1) := by omega
    cases o with
    | some ws =>
      obtain ⟨cs', ιe', ιi', G', ST', hc, R'⟩ := linkCall_fwdG (prof := prof) (impl := impl)
        (ST := ST) hHd hT S₀ hB₀ hfs R d hok hpath hexp hr₁ hans
      obtain ⟨cs'', ιe'', ιi'', G'', ST'', hS, R''⟩ := ih _ _ _ _ _ _ _ _ R' hr₂
      refine ⟨cs'', ιe'', ιi'', G'', ST'', .ret hc hS, ?_⟩
      simpa only [List.length_cons, hlen] using R''
    | none =>
      obtain ⟨m', hc, hR', hhost⟩ := linkCall_fwdG (prof := prof) (impl := impl)
        (ST := ST) hHd hT S₀ hB₀ hfs R d hok hpath hexp hr₁ hans
      have R₁ : ReadyL P l.toW Ie Ii s₀ u₀ F₀ m'.core ιe ιi G u₁ π₁ (k + 1) :=
        ⟨hR', R.thE, R.thI, R.leave, fresh_succL R.fresh⟩
      obtain ⟨cs'', ιe'', ιi'', G'', ST'', hS, R''⟩ := ih _ _ _ _ _ _ _ _ R₁ hr₂
      refine ⟨cs'', ιe'', ιi'', G'', ST'', .trap hc ?_, ?_⟩
      · rw [resumeCfg_readyL, hhost]
        exact hS
      · simpa only [List.length_cons, hlen] using R''

end Sess

/-! ## Assembly -/

/-- The static facts and the invariant after instantiation, and the instantiation itself, under
any host `H` from host state `h₀`. -/
theorem init_facts (P : Profile) (prof : ProfileKind) {l : HLinked2} (hl : l.Adequate)
    {σ : Type} (H : Host (core3P P) σ) (h₀ : σ) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii) :
    ∃ (m : Machine.Config (core3P P) σ) (F₀ : List (FuncInst (CanonHost (E3 P))))
      (cs : (core3P P).Store (CanonHost (core3P P))) (fs : List (CFuncInst (core3P P))),
      InstResult.instance m ⟨0⟩ l.exportMap ∈ instBehaviours prof H
        (LinkedSession.hostConfig l.host h₀) l.toRef (importArgs l.host) ∧
      m = readyCfgL cs {} {} fs Garb.empty [] h₀ ∧
      HStat P l Ie Ii Ii.store F₀ (readyCfgL (σ := σ) cs {} {} fs Garb.empty [] h₀)
        (ownOf Ie.store) ∧
      LiftedOkH l Ii Ie.store fs ∧
      ReadyL P l.toW Ie Ii Ie.store Ii.store F₀ cs {} {} (Garb.empty : Garb P σ) Ii.store
        Ie.store 0 := by
  obtain ⟨hEg, hEi, hIg, hIi', har, hff, hW, hN, hn, hS⟩ := hl
  obtain ⟨Ie₀, cse, cie, hFe⟩ := coreFacts (Pf := P) hEg hEi
  obtain rfl : Ie = Ie₀ := NumModule.IsInst.unique hIe hFe.isInst
  obtain ⟨r, cii, hrs, hh', hFi⟩ := coreFactsH_of_inst (Pf := P) hIg hIi'
    ⟨hS.imp.data, hS.imp.elems⟩ hIi cse
  have hmem := instH_mem hEg hFe hIg har hIi'.importNames hW hN hFi prof H h₀
  exact ⟨_, _, _, _, hmem, rfl, hstat_init hEg hIg hW hn har hff hFe hIi hh' _ rfl,
    liftedOkH_afterLink hIi hIg hFe, readyH_init (σ := σ) hS hn hW hFe hIi hrs hh'⟩

/-- **Specification sessions of an `HLinked2` with a typed host are reference sessions**, with
the host state and log: the reference images of the outcomes of every `HLinked2.SessSpec`
session from the instances' stores, whose host calls are answered by the logging host of `g`
from `(s₀, [])` to `st'` (`HostRun (logG g)`), are a session observation of `l.toRef` with the
final host state and log `st'`. -/
theorem hlinked2_sess_specToRef (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    (hT : l.HostTyped g) (s₀ : σ) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)}
    {outs : List (Option (List Silmaril.Wasm.Component.Val))}
    {hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))} {u' π' : Store Nat}
    (h : HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u' π')
    {st' : σ × List HLinked2.HostEvent} (hr : HostRun (HLinked2.logG g) (s₀, []) hs.flatten st') :
    (refOuts outs, st') ∈ HLinked2.sessObs P prof l g s₀ calls := by
  obtain ⟨m, F₀, cs, fs, hmem, rfl, S₀, hfs, R₀⟩ :=
    init_facts P prof hl (answerHostS P (HLinked2.logG g)) (s₀, []) hIe hIi
  obtain ⟨cs', ιe', ιi', G', ST', hsr, -⟩ := sessH_fwd (prof := prof)
    (impl := answerImplS (HLinked2.logG g)) (handles_answer hl.impArity hl.impFloatFree hl.wireTy)
    (HostTyped.logG hT) S₀ rfl hfs h _ _ _ _ [] (s₀, []) 0 st' R₀ hr
  refine ⟨_, ⟨0⟩, l.exportMap,
    calls.map fun q => (⟨l.host.length + l.exp.exports.length + q.1⟩ : FuncId),
    readyCfgL cs' ιe' ιi' fs G' ST' st', hmem, mapM_lookupH hl.impGood calls, ?_, rfl⟩
  rw [zip_callArgsH]
  exact hsr

/-! ## A host that never answers -/

/-- **The host that never answers handles the host callouts as `silentG`**: a callout whose
arguments do not lift traps; any other blocks the importer's thread on the unresolved subtask,
and the synchronous lift loop of the call traps `cannotBlockSync`. -/
theorem handles_silent {l : HLinked2} (har : l.imp.Arity) (hff : l.imp.FloatFree)
    (hW : l.WireTy) : Handles prof P (HLinked2.silentImpl (σ := σ)) HLinked2.silentG l := by
  intro cs ιe₀ ιi fs G ST h₀ k j x a vs M₀ th K segs rest hat hfn ιe SL CL TL HL C h y i hi ys
    hst hys
  have hF := gframe_of hat
  have hmem := host_mem hW hi
  obtain ⟨hmaxp, -, -⟩ := har.2 _ hmem
  obtain ⟨hpf, -⟩ := hff.2 _ hmem
  obtain ⟨ι₂, hι₂, hleave⟩ := hF.inst2 ιe SL CL TL HL C h
  have hf : ArenaField.funcs.get? (extG M₀ ιe SL CL TL HL C h).store ⟨i⟩ =
      some (.host (witFt l.host[i].2) ⟨i⟩) := (funcs_extG _ _ _ _ _ _ _ _ _).trans (hfn i hi)
  have hentry := hF.entry ⟨i⟩ (witFt l.host[i].2) ιe SL CL TL HL C h
  refine ⟨fun hws => hostCall_noLiftG (fun _ => ⟨_, rfl⟩) rfl hst hentry hι₂ hleave hf hpf hys
    hmaxp hws, fun ws hws => ⟨fun _ => ?_, fun us s' hg => by cases hg⟩⟩
  have hth := hat.thread
  subst hth
  let M₁ := coreCfg (extG M₀ ιe SL CL TL HL C h) (some ⟨G.threads.length⟩) K segs rest y
  have s₃ : Step prof (fun _ _ => false) (DI P HLinked2.silentImpl) M₁ .tau
      { M₁ with ctl := ⟨some ⟨G.threads.length⟩,
        .prog (DI P HLinked2.silentImpl
          (.hostCallout (.lowered ⟨i⟩ (witFt l.host[i].2) {} ⟨2⟩) ys)),
        .core y.2 K :: segs⟩ :: rest } :=
    Step.coreCallout rfl hst
  obtain ⟨pos, trB, hB⟩ := blocks_callout_silent (t := ⟨G.threads.length⟩) (m := M₁) hentry hι₂
    hleave hf hpf hys hmaxp hws
  obtain ⟨kB, segsB, rB⟩ := hB.lrun (prof := prof) (hr := fun _ _ => false) rfl Prog.pure
    (.core y.2 K :: segs) rest
  rw [Prog.bind_eq, Prog.bind_pure] at rB
  let mB : Machine.Config (E3 P) σ :=
    { M₁ with store := silentSt M₁.store ⟨2⟩ ys l.host[i].2 pos ⟨G.threads.length⟩ }
  have hlB : Live ({ mB with ctl := ⟨some ⟨G.threads.length⟩,
      .prog (.op (S := Eff (E3 P) σ) (.block none) kB), segsB⟩ :: rest } :
        Machine.Config (E3 P) σ) :=
    ⟨List.cons_ne_nil _ _, rfl⟩
  let M₂ : Machine.Config (E3 P) σ :=
    { (mB.setCont ⟨G.threads.length⟩ (some (blockedAct ⟨G.threads.length⟩ kB segsB))) with
      store := threadStatusSt ⟨G.threads.length⟩ .blocked mB.store, ctl := rest }
  have s₄ : Step prof (fun _ _ => false) (DI P HLinked2.silentImpl)
      { mB with ctl := ⟨some ⟨G.threads.length⟩,
        .prog (.op (S := Eff (E3 P) σ) (.block none) kB), segsB⟩ :: rest } .tau M₂ :=
    Step.block rfl
  have hready : M₂.store.threadReady (fun _ => false) ⟨G.threads.length⟩ = false :=
    threadReady_blocked _ _ _ _ (silent_unresolved M₁.store ⟨2⟩ ys l.host[i].2 pos)
  have hinst : M₂.store.inst? ⟨2⟩ = some (enterInst ιi ⟨G.threads.length⟩) := by
    show (extG M₀ ιe SL CL TL HL C h).store.insts[2]? = _
    simp [extG, hat.insts]
    rfl
  have htasks : M₂.store.tasks = G.tasks ++
      [(taskK₁ x G.callers ⟨G.threads.length⟩).withState .started] ++ TL := by
    show M₀.store.tasks ++ TL = _
    rw [hat.tasks]
  have hT := TrapsAtRH.trapEndH (fun _ h => by cases h) (hat.blockH M₂ _ _ rfl rfl htasks (by
    intro h
    cases h) (instCandidates_enter hinst hready))
  have hc : M₂.core = y.1 := rfl
  have hh : M₂.host = h := rfl
  rw [hc, hh] at hT
  exact TrapEndH.steps (.cons s₃ (Adequacy.steps_append rB.steps (.cons s₄ (.refl _))))
    (Quiet.tau.append ((Quiet.of_lrun rB hlB).append Quiet.tau)) hT

/-- **Specification sessions whose host calls are all answered by a trap are sessions of
`l.toRef` under the host that never answers** (`silentObs`), the host state unchanged. -/
theorem hlinked2_silent_specToRef (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (h₀ : σ) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)}
    {outs : List (Option (List Silmaril.Wasm.Component.Val))}
    {hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))} {u' π' : Store Nat}
    (h : HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u' π')
    (hr : HostRun HLinked2.silentG h₀ hs.flatten h₀) :
    (refOuts outs, h₀) ∈ HLinked2.silentObs P prof l h₀ calls := by
  obtain ⟨m, F₀, cs, fs, hmem, rfl, S₀, hfs, R₀⟩ :=
    init_facts P prof hl (HLinked2.silentHost P) h₀ hIe hIi
  obtain ⟨cs', ιe', ιi', G', ST', hsr, -⟩ := sessH_fwd (prof := prof)
    (impl := HLinked2.silentImpl) (handles_silent hl.impArity hl.impFloatFree hl.wireTy)
    (HostTyped.silentG l) S₀ rfl hfs h _ _ _ _ [] h₀ 0 h₀ R₀ hr
  refine ⟨_, ⟨0⟩, l.exportMap,
    calls.map fun q => (⟨l.host.length + l.exp.exports.length + q.1⟩ : FuncId),
    readyCfgL cs' ιe' ιi' fs G' ST' h₀, hmem, mapM_lookupH hl.impGood calls, ?_, rfl⟩
  rw [zip_callArgsH]
  exact hsr

/-- **A host that never answers, any call of a session**: after a specification session from
the instances' stores whose host calls are all answered by a trap (`silentObs` of its calls), a
typed call whose round from the stores reached makes a host call traps `cannotBlockSync`, with
no host event and no other trap after its invocation. -/
theorem hlinked2_silent_cannotBlock_sess (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (h₀ : σ) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)}
    {outs : List (Option (List Silmaril.Wasm.Component.Val))}
    {hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))} {u π : Store Nat}
    (h : HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u π)
    (hr : HostRun HLinked2.silentG h₀ hs.flatten h₀) (d : Linked2.SessRound l.toL2 Ii)
    (hok : d.Ok) {u₁ π₁ : Store Nat} (hpath : Ii.Path P (.idle u) d.instMoves (.idle u₁))
    (hexp : HLinked2.ExpRunH P l Ie π d.dss.flatten π₁)
    (hh : l.hostCalls d.dss.flatten ≠ []) :
    ∃ m : Machine.Config (core3P P) σ,
      InstResult.instance m ⟨0⟩ l.exportMap ∈ instBehaviours prof (HLinked2.silentHost P)
        (LinkedSession.hostConfig l.host h₀) l.toRef (importArgs l.host) ∧
      ∃ m₁ : Machine.Config (core3P P) σ,
        LinkedSession.SessRun prof (HLinked2.silentHost P) m 0 (callArgsH l calls) (refOuts outs)
          m₁ ∧ m₁.host = h₀ ∧
        ∃ (tr : List (Label (core3P P) σ)) (m' : Machine.Config (core3P P) σ),
          Steps prof (HLinked2.silentHost P).hr (HLinked2.silentHost P).dispatch m₁
            (.host (.invoke ⟨calls.length⟩ ⟨l.host.length + l.exp.exports.length + d.j⟩
              (d.vs.map toRefVal)) :: (tr ++ [.trap .cannotBlockSync])) m' ∧
          (∀ ev, Label.host ev ∉ tr) ∧ (∀ r, Label.trap r ∉ tr) ∧ m'.store.lockdown = true := by
  obtain ⟨m, F₀, cs, fs, hmem, rfl, S₀, hfs, R₀⟩ :=
    init_facts P prof hl (HLinked2.silentHost P) h₀ hIe hIi
  obtain ⟨cs', ιe', ιi', G', ST', hsr, R'⟩ := sessH_fwd (prof := prof)
    (impl := HLinked2.silentImpl) (handles_silent hl.impArity hl.impFloatFree hl.wireTy)
    (HostTyped.silentG l) S₀ rfl hfs h _ _ _ _ [] h₀ 0 h₀ R₀ hr
  rw [Nat.zero_add] at R'
  obtain ⟨tr, m', hsteps, hq₁, hq₂, hlock⟩ := silent_call (prof := prof) (ST := ST') (h₀ := h₀)
    S₀ rfl hfs R' d hok hpath hexp hh
  exact ⟨_, hmem, _, hsr, rfl, tr, m', .cons (invoke_stepL (impl := HLinked2.silentImpl)
    R'.fresh _ _) hsteps, hq₁, hq₂, hlock⟩

/-- Resumable sessions compose. -/
theorem sessRun_append {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {H : Host E σ}
    {m m₁ m₂ : Machine.Config E σ} {k : Nat} {cs cs' : List (FuncId × List RVal)}
    {outs outs' : List (Option (List RVal))}
    (h₁ : LinkedSession.SessRun prof H m k cs outs m₁)
    (h₂ : LinkedSession.SessRun prof H m₁ (k + cs.length) cs' outs' m₂) :
    LinkedSession.SessRun prof H m k (cs ++ cs') (outs ++ outs') m₂ := by
  induction h₁ with
  | nil => simpa using h₂
  | ret hc _ ih =>
    refine .ret hc (ih ?_)
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using h₂
  | trap hc _ ih =>
    refine .trap hc (ih ?_)
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using h₂

/-- **The session extended by such a call answers a trap for it** (`silentObs`). -/
theorem hlinked2_silent_session_sess (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (h₀ : σ) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)}
    {outs : List (Option (List Silmaril.Wasm.Component.Val))}
    {hs : List (List (Σ _ : (sigN l.host.length).Op, Option Payload))} {u π : Store Nat}
    (h : HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs hs u π)
    (hr : HostRun HLinked2.silentG h₀ hs.flatten h₀) (d : Linked2.SessRound l.toL2 Ii)
    (hok : d.Ok) {u₁ π₁ : Store Nat} (hpath : Ii.Path P (.idle u) d.instMoves (.idle u₁))
    (hexp : HLinked2.ExpRunH P l Ie π d.dss.flatten π₁)
    (hh : l.hostCalls d.dss.flatten ≠ []) :
    ∃ s : σ, (refOuts outs ++ [none], s) ∈
      HLinked2.silentObs P prof l h₀ (calls ++ [(d.j, d.vs)]) := by
  obtain ⟨m, hmem, m₁, hsr, -, tr, m', hsteps, hq₁, hq₂, hlock⟩ :=
    hlinked2_silent_cannotBlock_sess P prof hl h₀ hIe hIi h hr d hok hpath hexp hh
  have hc : Calls prof (HLinked2.silentHost P).hr (HLinked2.silentHost P).dispatch m₁
      ⟨calls.length⟩ ⟨l.host.length + l.exp.exports.length + d.j⟩ (d.vs.map toRefVal) m'
      .trap := by
    refine ⟨tr ++ [.trap .cannotBlockSync], hsteps, ?_, ?_, hlock⟩
    · intro ev hm
      rcases List.mem_append.mp hm with hm | hm
      · exact absurd hm (hq₁ ev)
      · simp at hm
    · intro _ msg hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hq₂ _ hm
      · simp at hm
  have hlen : (callArgsH l calls).length = calls.length := by simp [callArgsH]
  refine ⟨(resumeCfg m₁ m').host, m, ⟨0⟩, l.exportMap,
    (calls ++ [(d.j, d.vs)]).map fun q => (⟨l.host.length + l.exp.exports.length + q.1⟩ : FuncId),
    resumeCfg m₁ m', hmem, mapM_lookupH hl.impGood _, ?_, rfl⟩
  rw [zip_callArgsH]
  have e : callArgsH l (calls ++ [(d.j, d.vs)]) = callArgsH l calls ++
      [((⟨l.host.length + l.exp.exports.length + d.j⟩ : FuncId), d.vs.map toRefVal)] := by
    simp [callArgsH]
  rw [e]
  refine sessRun_append hsr ?_
  rw [Nat.zero_add, hlen]
  exact .trap hc (.nil _ _)

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
