module

public import Silmaril.Proofs.Wasm.Component.Reference.MultiPath
public import Silmaril.Proofs.Wasm.Component.Reference.MultiSpec
public import Silmaril.Proofs.Wasm.Component.Reference.CallRun

/-!
# The call phase between other calls

`callK`: from a configuration `readyCfg` between calls (`ReadyAt`: the core store is well
formed for the instance, the instance's thread table is empty or has one freed slot, earlier
calls have smaller ids), every behaviour of top-level call `k` of export `j` is an outcome of
`specAt` at the current Core store; a resolved call is a returned call (`RetAt`) and ends in
the next configuration between calls.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower)

variable {P : Profile} {prof : ProfileKind}

/-! ## The instance's thread table -/

/-- The instance with the implicit thread `t` of a call registered. -/
def enterInst (ι : InstState) (t : ThreadId) : InstState :=
  { ι with threads := ⟨#[none, some t], []⟩ }

theorem addThread?_ok {ι : InstState} (h : ThreadsOk ι) (t : ThreadId) :
    ι.addThread? t = some (1, enterInst ι t) := by
  rcases h with h | h
  · unfold InstState.addThread? Table.add?
    rw [h]
    rfl
  · unfold InstState.addThread? Table.add?
    rw [h]
    rfl

theorem removeThread?_enter (ι : InstState) (t : ThreadId) :
    (enterInst ι t).removeThread? 1 = some (t, InstState.removeThread 1 (enterInst ι t)) := rfl

theorem threadsOk_after (ι : InstState) (t : ThreadId) :
    ThreadsOk (InstState.removeThread 1 (enterInst ι t)) := .inr rfl

/-! ## Configurations between calls -/

/-- **The invariant between calls**: the core store is well formed for the instance, the
thread table is reusable and the earlier calls have smaller ids than `k`. -/
structure ReadyAt (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState) (G : Garb P) (k : Nat) :
    Prop where
  wf : I.WellFormed (Store.mapH (fun _ => 0) cs)
  threads : ThreadsOk ι
  fresh : G.Fresh k

/-- The host invocation from a configuration between calls. -/
theorem invoke_inv_k {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState}
    {fs : List (CFuncInst (core3P P))} {G : Garb P} {k j : Nat} {args : List Val}
    {m : Machine.Config (E3 P) Unit}
    (h : Step prof (refHost P).hr (D P) (readyCfg cs ι fs G) (.host (.invoke ⟨k⟩ ⟨j⟩ args)) m) :
    m = invokedAt cs ι fs G k j args := by
  cases h
  rfl

/-- A tick between calls returns to the same configuration. -/
theorem ready_tick (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P) (m₁ : Machine.Config (E3 P) Unit)
    (hs : Step prof (refHost P).hr (D P) (readyCfg cs ι fs G) (.host .tick) m₁) :
    ∃ trT, LRun prof (refHost P).hr (D P) m₁ trT (readyCfg cs ι fs G) := by
  cases hs
  apply Exists.intro
  repeat mstep
  exact .refl _

theorem find?_fresh {σ : Type} {G : Garb P σ} {k : Nat} (h : G.Fresh k) :
    G.results.find? (·.1 == (⟨k⟩ : CallId)) = none := by
  rw [List.find?_eq_none]
  intro x hx e
  have hlt := h.results x hx
  have hx' : x.1 = ⟨k⟩ := by simpa using e
  rw [hx'] at hlt
  exact absurd hlt (Nat.lt_irrefl _)

theorem result?_next {G : Garb P} {k : Nat} (h : G.Fresh k) (x : SimpleExport) (j : Nat)
    (a : (E3 P).FuncAddr) (args rs : List Val) (cs : (core3P P).Store (CanonHost (core3P P)))
    (ι : InstState) (fs : List (CFuncInst (core3P P))) :
    (readyCfg cs ι fs (nextGarb G x k j a args rs)).result? ⟨k⟩ = some (some rs) := by
  unfold Machine.Config.result?
  show ((G.results ++ [((⟨k⟩ : CallId), some rs)]).find? (fun p => p.1 == (⟨k⟩ : CallId))).map
    Prod.snd = _
  rw [List.find?_append, find?_fresh h]
  simp

theorem fresh_next {G : Garb P} {k : Nat} (h : G.Fresh k) (x : SimpleExport) (j : Nat)
    (a : (E3 P).FuncAddr) (args rs : List Val) : (nextGarb G x k j a args rs).Fresh (k + 1) where
  pending := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact Nat.lt_succ_of_lt (h.pending y hy)
    · rw [List.mem_singleton.mp hy]
      exact Nat.lt_succ_self k
  results := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact Nat.lt_succ_of_lt (h.results y hy)
    · rw [List.mem_singleton.mp hy]
      exact Nat.lt_succ_self k

/-! ## Outcomes of call `k` -/

/-- After a resolving suffix, the only outcome of call `k` is the resolution, at the next
configuration between calls. -/
theorem out_of_resolvesK {m₁ m' : Machine.Config (E3 P) Unit}
    {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState}
    {fs : List (CFuncInst (core3P P))} {G : Garb P} {k : Nat} {rs : List Val}
    (hR : ResolvesAt prof P m₁ (readyCfg cs ι fs G)) (hres : (readyCfg cs ι fs G).result? ⟨k⟩ =
      some (some rs)) {tr : List (Label (E3 P) Unit)} {out : CallOutcome}
    (hs : Steps prof (refHost P).hr (D P) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨k⟩ ev)
    (ho : out.Holds (refHost P).hr ⟨k⟩ m') :
    out = .resolved (some rs) ∧ m' = readyCfg cs ι fs G := by
  obtain ⟨tr₃, mE, hlr, rfl⟩ := hR
  rcases hlr.inv hs with hl | ⟨tr₄, e, r⟩
  · exact absurd ho (hl.not_holds _ _)
  have hev' : ∀ ev, Label.host ev ∈ tr₄ → CallHostEvent ⟨k⟩ ev :=
    fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
  have hq := quiet (c := ⟨k⟩) rfl (by rw [hres]; simp) (ready_tick cs ι fs G) _ tr₄ m' le_rfl r
    hev'
  rcases hq with rfl | hl
  · refine ⟨?_, rfl⟩
    cases out with
    | resolved r => exact congrArg _ (Option.some.inj (ho.2.2.symm.trans hres))
    | trap => exact absurd ho (fun h => Bool.false_ne_true h)
    | deadlock => exact absurd (ho.2.symm.trans hres) (by simp)
  · exact absurd ho (hl.not_holds _ _)

/-- After a trapping suffix, the only outcome of call `k` is the trap. -/
theorem out_of_trapsNextK {m₁ m' : Machine.Config (E3 P) Unit} {k : Nat}
    {tr : List (Label (E3 P) Unit)} {out : CallOutcome} (hT : TrapsNext prof P m₁)
    (hs : Steps prof (refHost P).hr (D P) m₁ tr m')
    (ho : out.Holds (refHost P).hr ⟨k⟩ m') : out = .trap := by
  obtain ⟨mT, r, hlr, hlive, hu⟩ := hT
  rcases hlr.inv hs with hl | ⟨tr₄, -, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  cases r' with
  | refl => exact absurd ho (hlive.not_holds _ _)
  | cons s r'' =>
    obtain ⟨rfl, rfl⟩ := hu.2 _ _ s
    rw [steps_of_locked rfl rfl r''] at ho
    cases out with
    | resolved r => exact absurd ho.2.1 (by simp)
    | trap => rfl
    | deadlock => exact absurd ho.1.2.1 (by simp)

/-! ## The core activation at a later store -/

variable {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
  {cs : (core3P P).Store (CanonHost (core3P P))} {x : SimpleExport}
  {vs : List Silmaril.Wasm.Component.Val}

/-- The static facts of call `k` of export `x` on `vs` at core store `cs`. -/
structure CallCtxAt (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3P P).Store (CanonHost (core3P P))) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) : Prop where
  inst : c.mod.IsInst I
  wf : I.WellFormed (Store.mapH (fun _ => 0) cs)
  core : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat)
  typed : ValTy.checkList x.ty.params vs = true

theorem CallCtxAt.lowered (C : CallCtxAt P c I cs x vs) :
    (lowerArgs x.ty.params vs).map (·.type) = ValTy.flatList x.ty.params :=
  lowerList_types _ _ C.typed

theorem CallCtxAt.lowerOk (C : CallCtxAt P c I cs x vs) :
    checkLower x.ty.params vs = some (lowerArgs x.ty.params vs) := by
  unfold checkLower
  rw [ite_eq_left_iff.mpr (fun h => absurd C.typed h)]

theorem CallCtxAt.spec (C : CallCtxAt P c I cs x vs) {b : Silmaril.Wasm.Component.Reference.Outcome}
    (h : ∃ r ∈ coreAt P I x.core (lowerArgs x.ty.params vs) (Store.mapH (fun _ => 0) cs),
      b = liftOutcome x.ty r) :
    b ∈ specAt P c I x vs (Store.mapH (fun _ => 0) cs) := by
  unfold specAt
  rw [C.lowerOk]
  exact .inl h

theorem CallCtxAt.spec_diverges (C : CallCtxAt P c I cs x vs)
    (h : Silmaril.Wasm.Execution.Core.Diverges P Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke (Store.mapH (fun _ => 0) cs) (I.addrs.getD x.core 0)
        ((lowerArgs x.ty.params vs).map Silmaril.Wasm.SingleThreaded.ofFlat))) :
    .diverges ∈ specAt P c I x vs (Store.mapH (fun _ => 0) cs) := by
  unfold specAt
  rw [C.lowerOk]
  exact .inr ⟨rfl, h⟩

/-- The run of the core activation, renamed. -/
theorem CallCtxAt.run (_C : CallCtxAt P c I cs x vs) {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) y) :
    Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke (Store.mapH (fun _ => 0) cs) (I.addrs.getD x.core 0)
        ((lowerArgs x.ty.params vs).map Silmaril.Wasm.SingleThreaded.ofFlat))
      (Config.mapH (fun _ => 0) (y.2.config y.1)) :=
  coreSteps_run hy

theorem CallCtxAt.no_callout (C : CallCtxAt P c I cs x vs) {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) y)
    {h : CanonHost (E3 P)} {args : List FlatValue} (hs : (E3 P).status y.1 y.2 = .callout h args) :
    False := by
  obtain ⟨nm, hcore⟩ := C.core
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  obtain ⟨E, a', h', args', hd⟩ := status_callout hs
  obtain ⟨E', hd'⟩ := decompose?_mapH (fun _ => 0) hd
  have hxs : (lowerArgs x.ty.params vs).map (·.type) = c.mod.exports[x.core].2.params := by
    rw [hget]
    exact C.lowered
  have hn := run_no_callout_at C.inst C.wf hk hxs (C.run hy)
  have hstore : (Config.mapH (fun _ => (0 : Nat)) (y.2.config y.1)).store =
      Store.mapH (fun _ => 0) y.1 :=
    congrArg (Store.mapH _) (Silmaril.Wasm.SingleThreaded.Thread.config_store _ _)
  rw [hstore] at hn
  exact absurd (hd'.symm.trans hn) (by simp)

theorem config_code_mapH (g : CanonHost (E3 P) → Nat)
    (s : Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P)))
    (t : Silmaril.Wasm.SingleThreaded.Thread) :
    (t.config (Store.mapH g s)).code = (t.config s).code := by
  cases t with
  | pending a args => exact congrArg Silmaril.Wasm.Execution.Core.Config.code (invoke_mapH g _ _ _).symm
  | active f code => rfl

/-- A returned core activation: an outcome of `coreAt`, with values of the flat result types,
and a returned call whenever the IR lift succeeds. -/
theorem CallCtxAt.values (C : CallCtxAt P c I cs x vs) {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) y)
    {ys : List FlatValue} (hs : (E3 P).status y.1 y.2 = .returned (.values ys)) :
    some ys ∈ coreAt P I x.core (lowerArgs x.ty.params vs) (Store.mapH (fun _ => 0) cs) ∧
      ys.map (·.type) = ValTy.flatList x.ty.results ∧
      ∀ ws, liftArgs x.ty.results ys = some ws →
        RetAt P c I x vs (Store.mapH (fun _ => 0) cs) ws (Store.mapH (fun _ => 0) y.1) := by
  obtain ⟨nm, hcore⟩ := C.core
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcore
  obtain ⟨cvs, hc, hm⟩ := status_values hs
  have hxs : (lowerArgs x.ty.params vs).map (·.type) = c.mod.exports[x.core].2.params := by
    rw [hget]
    exact C.lowered
  have ht := run_typed_at C.inst C.wf hk hxs (C.run hy) hc hm
  rw [hget] at ht
  refine ⟨⟨_, .values cvs, C.run hy, hc, hm.symm⟩, ht, fun ws hws => ⟨C.typed, ?_⟩⟩
  refine ⟨y.2, cvs, ys, reach_mapH (fun _ => 0) (coreSteps_internal hy), ?_, hm, hws⟩
  exact (config_code_mapH _ _ _).trans hc

theorem CallCtxAt.trap (_C : CallCtxAt P c I cs x vs) {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) y)
    (hs : (E3 P).status y.1 y.2 = .returned .trap) :
    none ∈ coreAt P I x.core (lowerArgs x.ty.params vs) (Store.mapH (fun _ => 0) cs) := by
  obtain ⟨c', res, run, hc, hr⟩ := coreRun_trap (fun _ => (0 : Nat)) (coreSteps_internal hy) hs
  exact ⟨c', res, run, hc, hr.symm⟩

/-! ## Call `k` -/

variable {ι : InstState} {fs : List (CFuncInst (core3P P))} {G : Garb P} {k j : Nat}

/-- The configuration between calls after call `k` of function `j` resolved with `rs`. -/
def nextCfg (cs' : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P) (x : SimpleExport) (k j : Nat)
    (a : (E3 P).FuncAddr) (args rs : List Val) : Machine.Config (E3 P) Unit :=
  readyCfg cs' (InstState.removeThread 1 (enterInst ι ⟨G.threads.length⟩)) fs
    (nextGarb G x k j a args rs)

/-- What a call outcome says about call `k`: an outcome of the specification at the current
store, and for a resolution a returned call ending between calls. -/
def CallFacts (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P) (x : SimpleExport) (k j : Nat)
    (vs : List Silmaril.Wasm.Component.Val) (m' : Machine.Config (E3 P) Unit) (out : CallOutcome) :
    Prop :=
  Outcome.ofCall out ∈ specAt P c I x vs (Store.mapH (fun _ => 0) cs) ∧
    ∀ rs, out = .resolved (some rs) → ∃ cs' ws, rs = ws.map toRefVal ∧
      RetAt P c I x vs (Store.mapH (fun _ => 0) cs) ws (Store.mapH (fun _ => 0) cs') ∧
      m' = nextCfg cs' ι fs G x k j (I.addrs.getD x.core 0) (vs.map toRefVal) rs

/-- Call `k` after a returned core activation. -/
theorem values_facts (C : CallCtxAt P c I cs x vs) (R : ReadyAt I cs ι G k)
    {M₀ : Machine.Config (E3 P) Unit} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)}
    (hat : CallAtK prof P cs (enterInst ι ⟨G.threads.length⟩) fs G k j x
      (I.addrs.getD x.core 0) vs M₀ th K segs rest) {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) y)
    {ys : List FlatValue} (hst : (E3 P).status y.1 y.2 = .returned (.values ys))
    {tr : List (Label (E3 P) Unit)} {m' : Machine.Config (E3 P) Unit} {out : CallOutcome}
    (hs : Steps prof (refHost P).hr (D P) (retCfg M₀ th K segs rest y ys) tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨k⟩ ev)
    (ho : out.Holds (refHost P).hr ⟨k⟩ m') : CallFacts P c I cs ι fs G x k j vs m' out := by
  obtain ⟨hout, hty, hret⟩ := C.values hy hst
  cases hl : liftArgs x.ty.results ys with
  | some ws =>
    have hres := result?_next R.fresh x j (I.addrs.getD x.core 0) (vs.map toRefVal)
      (ws.map toRefVal) y.1 (InstState.removeThread 1 (enterInst ι ⟨G.threads.length⟩)) fs
    obtain ⟨rfl, hm⟩ := out_of_resolvesK (hat.ret y ys ws hty hl) hres hs hev ho
    refine ⟨C.spec ⟨_, hout, by simp only [Outcome.ofCall, liftOutcome, hl]⟩, ?_⟩
    intro rs hrs
    have hrs' : rs = ws.map toRefVal := (Option.some.inj (CallOutcome.resolved.inj hrs)).symm
    exact ⟨y.1, ws, hrs', hret ws hl, hrs' ▸ hm⟩
  | none =>
    obtain rfl := out_of_trapsNextK (hat.trap y ys hty hl) hs ho
    exact ⟨C.spec ⟨_, hout, by simp only [Outcome.ofCall, liftOutcome, hl]⟩,
      fun _ h => nomatch h⟩

/-- A trapped core activation: the only outcome of call `k` is the trap. -/
theorem trap_facts (C : CallCtxAt P c I cs x vs) {M₀ : Machine.Config (E3 P) Unit}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)} {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) y)
    (hst : (E3 P).status y.1 y.2 = .returned .trap) {tr : List (Label (E3 P) Unit)}
    {m' : Machine.Config (E3 P) Unit} {out : CallOutcome}
    (hs : Steps prof (refHost P).hr (D P) (trapCfg (coreCfg M₀ th K segs rest y)) tr m')
    (ho : out.Holds (refHost P).hr ⟨k⟩ m') : CallFacts P c I cs ι fs G x k j vs m' out := by
  have hm : m' = trapCfg (coreCfg M₀ th K segs rest y) := steps_of_locked rfl rfl hs
  have hout : out = .trap := by
    cases out with
    | resolved r => exact absurd (hm ▸ ho).2.1 (by simp)
    | trap => rfl
    | deadlock => exact absurd (hm ▸ ho).1.2.1 (by simp)
  exact hout ▸ ⟨C.spec ⟨_, C.trap hy hst, rfl⟩, fun _ h => nomatch h⟩

/-- **Calls after the core activation left it.** -/
theorem exit_facts (C : CallCtxAt P c I cs x vs) (R : ReadyAt I cs ι G k)
    {M₀ : Machine.Config (E3 P) Unit} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)}
    (hat : CallAtK prof P cs (enterInst ι ⟨G.threads.length⟩) fs G k j x
      (I.addrs.getD x.core 0) vs M₀ th K segs rest) {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) y)
    {l : Label (E3 P) Unit} {m₁ m' : Machine.Config (E3 P) Unit} {tr : List (Label (E3 P) Unit)}
    {out : CallOutcome} (hx : CoreExit M₀ th K segs rest y l m₁)
    (hs : Steps prof (refHost P).hr (D P) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨k⟩ ev)
    (ho : out.Holds (refHost P).hr ⟨k⟩ m') : CallFacts P c I cs ι fs G x k j vs m' out := by
  rcases hx with ⟨ys, hst, -, hm⟩ | ⟨hst, -, hm⟩ | ⟨h, args, hst⟩
  · exact values_facts C R hat hy hst (hm ▸ hs) hev ho
  · exact trap_facts C hy hst (hm ▸ hs) ho
  · exact (C.no_callout hy hst).elim

/-- The configuration running the core activation is a core configuration. -/
theorem eq_core_k {M₀ : Machine.Config (E3 P) Unit} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)} {a : Nat} {xs : List FlatValue}
    (hctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) K, segs⟩ ::
      rest) (hcore : M₀.store.core = cs) :
    M₀ = coreCfg M₀ th K segs rest (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) := by
  rw [← hcore]
  exact eq_coreCfg hctl

/-- The run of call `k` after the host's invocation, from the core configuration. -/
theorem core_run_k {M₀ m' : Machine.Config (E3 P) Unit} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)} {tr : List (Label (E3 P) Unit)} {a : Nat}
    {xs : List FlatValue}
    (hctl : M₀.ctl = ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) K, segs⟩ ::
      rest) (hcore : M₀.store.core = cs) (hs : Steps prof (refHost P).hr (D P) M₀ tr m') :
    Steps prof (refHost P).hr (D P)
      (coreCfg M₀ th K segs rest (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs)) tr m' := by
  exact eq_core_k hctl hcore ▸ hs

/-- **Terminating calls between calls** follow the specification at the current store. -/
theorem calls_facts (C : CallCtxAt P c I cs x vs) (R : ReadyAt I cs ι G k)
    (hff : floatFreeList x.ty.params = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true)
    (hf : fs[j]? = some (.lifted (I.addrs.getD x.core 0) (liftedFt x) {} ⟨0⟩))
    {m' : Machine.Config (E3 P) Unit} {out : CallOutcome}
    (hcalls : Calls prof (refHost P).hr (D P) (readyCfg cs ι fs G) ⟨k⟩ ⟨j⟩ (vs.map toRefVal) m'
      out) : CallFacts P c I cs ι fs G x k j vs m' out := by
  obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
  obtain ⟨m₂, s, r⟩ := Steps.cons_iff.mp hs
  have r₁ : Steps prof (refHost P).hr (D P) (invokedAt cs ι fs G k j (vs.map toRefVal)) tr m' :=
    invoke_inv_k s ▸ r
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_at_k prof cs ι _ fs G k j _ x vs hff
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
  exact exit_facts C R hat hy hx r'' hev' ho

/-- After the core activation left it, call `k` does not diverge. -/
theorem exit_not_diverges_k (C : CallCtxAt P c I cs x vs) {M₀ : Machine.Config (E3 P) Unit}
    {th : Option ThreadId} {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    (hat : CallAtK prof P cs (enterInst ι ⟨G.threads.length⟩) fs G k j x
      (I.addrs.getD x.core 0) vs M₀ th K segs rest) {y : CoreSt (E3 P)}
    (hy : Relation.ReflTransGen (CoreStep (E3 P))
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) y)
    {l : Label (E3 P) Unit} {m₁ : Machine.Config (E3 P) Unit}
    (hx : CoreExit M₀ th K segs rest y l m₁) : ¬ Diverges prof (refHost P).hr (D P) m₁ := by
  rcases hx with ⟨ys, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h, args, hst⟩
  · obtain ⟨-, hty, -⟩ := C.values hy hst
    cases hl : liftArgs x.ty.results ys with
    | some ws =>
      obtain ⟨tr₃, mE, hlr, rfl⟩ := hat.ret y ys ws hty hl
      exact fun hd => not_diverges_of_ctl_nil rfl (hlr.diverges hd)
    | none => exact trapsNext_not_diverges (hat.trap y ys hty hl)
  · exact not_diverges_trapCfg _
  · exact (C.no_callout hy hst).elim

/-- **Divergent calls between calls** follow the specification at the current store. -/
theorem diverges_facts (C : CallCtxAt P c I cs x vs) (R : ReadyAt I cs ι G k)
    (hff : floatFreeList x.ty.params = true) (hmax : (ValTy.flatList x.ty.params).length ≤ 16)
    (hres : x.ty.results.length ≤ 1) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hffr : floatFreeList x.ty.results = true)
    (hf : fs[j]? = some (.lifted (I.addrs.getD x.core 0) (liftedFt x) {} ⟨0⟩))
    (hd : CallDiverges prof (refHost P).hr (D P) (readyCfg cs ι fs G) ⟨k⟩ ⟨j⟩ (vs.map toRefVal)) :
    .diverges ∈ specAt P c I x vs (Store.mapH (fun _ => 0) cs) := by
  obtain ⟨m₂, s, hd⟩ := hd
  have hd₁ : Diverges prof (refHost P).hr (D P) (invokedAt cs ι fs G k j (vs.map toRefVal)) :=
    invoke_inv_k s ▸ hd
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_at_k prof cs ι _ fs G k j _ x vs hff
    C.typed hmax hres hmaxr hffr (addThread?_ok R.threads _) (removeThread?_enter _ _) hf
  have hd₀ : Diverges prof (refHost P).hr (D P) (coreCfg M₀ th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs))) :=
    eq_core_k hat.ctl hat.core ▸ hpre.diverges hd₁
  rcases coreCfg_diverges_inv hd₀ with hi | ⟨y, l, m₁, hy, hx, hd'⟩
  · exact C.spec_diverges (coreRun_diverges (P := P) (fun _ => (0 : Nat))
      (Silmaril.InfiniteTrace.map id (fun _ _ h => h.2) hi))
  · exact (exit_not_diverges_k C hat hy hx hd').elim

end Silmaril.Proofs.Wasm.Component.Reference
