module

public import Silmaril.Proofs.Wasm.Component.Reference.CallKI
public import Silmaril.Proofs.Wasm.Component.Reference.CallPhaseI
public import Silmaril.Proofs.Wasm.Component.Reference.MultiCall
public import Silmaril.Proofs.Wasm.Component.Reference.SeqIRI

/-!
# The call phase with imports between other calls

`calls_factsKI`: from a configuration between calls (`readyCfgI`, `ReadyAtI`: the core store
renames under `trampIdx` to a well-formed store of the instance, its host functions are the
trampolines of the imports, the instance's thread table is reusable, the instance may leave, and
earlier calls have smaller ids), every terminating outcome of top-level call `k` of export `j`,
over `core3P P` with `answerHostS P g` (a stateful host; `answerHost P g` is its stateless instance), is a play of the core instance from the current store
(`CallStartAt`, `path_returnedAt`, `path_callout_trapAt`) whose IR round (`IRRoundI`) makes import
calls answered by `g` and answers as the outcome prescribes (`ObsAns`). A resolved call ends at
the next configuration between calls, the instance idle at the store reached: Core runs never
allocate functions (`aseg_funcs`), so the trampoline invariant persists; the play's import
answers throw nothing, so the store stays well formed (`WellFormed.activation`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN)

variable {P : Profile} {σ : Type} {g : σ → HostFuncId → List Val → Option (List Val × σ)}
  {prof : ProfileKind} {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance}

/-! ## Configurations between calls -/

/-- **The invariant between calls with imports.** -/
structure ReadyAtI (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState) (G : Garb P σ) (k : Nat) :
    Prop where
  wf : I.WellFormed (Store.mapH trampIdx cs)
  tramp : c.TrampOk cs
  threads : ThreadsOk ι
  leave : ι.mayLeave = true
  fresh : G.Fresh k

theorem invoke_inv_kA {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState}
    {fs : List (CFuncInst (core3P P))} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k j : Nat}
    {args : List Val} {m : Machine.Config (E3 P) σ}
    (h : Step prof (answerHostS P g).hr (DA P g) (readyCfgI cs ι fs G ST h₀)
      (.host (.invoke ⟨k⟩ ⟨j⟩ args)) m) :
    m = invokedAtI cs ι fs G ST h₀ k j args := by
  cases h
  rfl

theorem ready_tickA (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (G : Garb P σ) (ST : List Subtask) (h₀ : σ)
    (m₁ : Machine.Config (E3 P) σ)
    (hs : Step prof (answerHostS P g).hr (DA P g) (readyCfgI cs ι fs G ST h₀) (.host .tick) m₁) :
    ∃ trT, LRun prof (answerHostS P g).hr (DA P g) m₁ trT (readyCfgI cs ι fs G ST h₀) := by
  cases hs
  apply Exists.intro
  repeat mstep
  exact .refl _

theorem result?_nextA {G : Garb P σ} {k : Nat} (h : G.Fresh k) (x : SimpleExport) (j : Nat)
    (a : (E3 P).FuncAddr) (args rs : List Val) (CL : List (Caller (E3 P)))
    (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState)
    (fs : List (CFuncInst (core3P P))) (ST : List Subtask) (h₀ : σ) :
    (readyCfgI cs ι fs (nextGarbA P g G x k j a args rs CL) ST h₀).result? ⟨k⟩ =
      some (some rs) := by
  unfold Machine.Config.result?
  show ((G.results ++ [((⟨k⟩ : CallId), some rs)]).find? (fun p => p.1 == (⟨k⟩ : CallId))).map
    Prod.snd = _
  rw [List.find?_append, find?_fresh h]
  simp

theorem fresh_nextA {G : Garb P σ} {k : Nat} (h : G.Fresh k) (x : SimpleExport) (j : Nat)
    (a : (E3 P).FuncAddr) (args rs : List Val) (CL : List (Caller (E3 P))) :
    (nextGarbA P g G x k j a args rs CL).Fresh (k + 1) where
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

/-- After a resolving suffix, the only outcome of call `k` is the resolution, at the next
configuration between calls. -/
theorem out_of_resolvesKA {m₁ m' : Machine.Config (E3 P) σ}
    {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState}
    {fs : List (CFuncInst (core3P P))} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k : Nat}
    {rs : List Val}
    (hR : ResolvesAtA prof P g m₁ (readyCfgI cs ι fs G ST h₀))
    (hres : (readyCfgI cs ι fs G ST h₀).result? ⟨k⟩ = some (some rs))
    {tr : List (Label (E3 P) σ)} {out : CallOutcome}
    (hs : Steps prof (answerHostS P g).hr (DA P g) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨k⟩ ev)
    (ho : out.Holds (answerHostS P g).hr ⟨k⟩ m') :
    out = .resolved (some rs) ∧ m' = readyCfgI cs ι fs G ST h₀ := by
  obtain ⟨tr₃, mE, hlr, rfl⟩ := hR
  rcases hlr.inv hs with hl | ⟨tr₄, e, r⟩
  · exact absurd ho (hl.not_holds _ _)
  have hev' : ∀ ev, Label.host ev ∈ tr₄ → CallHostEvent ⟨k⟩ ev :=
    fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
  have hq := quiet (c := ⟨k⟩) rfl (by rw [hres]; simp) (ready_tickA cs ι fs G ST h₀) _ tr₄ m'
    le_rfl r hev'
  rcases hq with rfl | hl
  · refine ⟨?_, rfl⟩
    cases out with
    | resolved r => exact congrArg _ (Option.some.inj (ho.2.2.symm.trans hres))
    | trap => exact absurd ho (fun h => Bool.false_ne_true h)
    | deadlock => exact absurd (ho.2.symm.trans hres) (by simp)
  · exact absurd ho (hl.not_holds _ _)

/-- After a trapping suffix, the only outcome of call `k` is the trap. -/
theorem out_of_trapsNextKA {m₁ m' : Machine.Config (E3 P) σ} {k : Nat}
    {tr : List (Label (E3 P) σ)} {out : CallOutcome} (hT : TrapsNextA prof P g m₁)
    (hs : Steps prof (answerHostS P g).hr (DA P g) m₁ tr m')
    (ho : out.Holds (answerHostS P g).hr ⟨k⟩ m') : out = .trap := by
  obtain ⟨mT, r, hlr, hlive, hu⟩ := hT
  rcases hlr.inv hs with hl | ⟨tr₄, -, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  cases r' with
  | refl => exact absurd ho (hlive.not_holds _ _)
  | cons s r'' =>
    obtain ⟨rfl, rfl⟩ := hu.2 _ _ s
    rw [steps_of_locked rfl rfl r''] at ho
    exact holds_trapCfg' ho

/-! ## Plays at a later store -/

/-- The static facts of call `k` of export `j` with imports at the core store `cs`. -/
structure CallCtxKI (P : Profile) (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3P P).Store (CanonHost (core3P P))) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (f : I.F.Op) (a : Nat) : Prop where
  start : CallStartAt c I (Store.mapH trampIdx cs) cs f a (lowerArgs c.exports[j].ty.params vs)
  typed : ValTy.checkList c.exports[j].ty.params vs = true
  core : f.1.val = c.exports[j].core
  ty : I.exports.get f.1 = fnOf c.exports[j].ty.flat

theorem CallCtxKI.lowered {cs : (core3P P).Store (CanonHost (core3P P))}
    {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val} {f : I.F.Op} {a : Nat}
    (C : CallCtxKI P c I cs j vs f a) :
    checkLower c.exports[j].ty.params vs = some (lowerArgs c.exports[j].ty.params vs) := by
  simp only [checkLower, C.typed, ↓reduceIte]

/-- The IR round of an instance round whose import calls are related to component import calls
answered by `g` from host state `s` to `s'`. -/
theorem irRound_of {cs : (core3P P).Store (CanonHost (core3P P))} {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {f : I.F.Op} {a : Nat} (C : CallCtxKI P c I cs j vs f a)
    {rounds : List (Round I.E)} (w : I.F.Ar f) {s s' : σ}
    {dss : List (List (Round (sigN c.imports.length)))}
    (hrel : List.Forall₂ (ImpRel c I) rounds dss) (hrun : HostRun g s dss.flatten s') :
    ∃ u : CRound (sigN c.imports.length) (sigN c.toComp.exports.length),
      IRRoundI c I j vs ⟨f, rounds, w⟩ u ∧ HostRun g s u.cs s' ∧
      u.a = (answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift c.exports[j].ty)) :=
  ⟨_, ⟨_, dss, C.lowered, C.core, C.start.args, hrel, rfl⟩, hrun, rfl⟩

theorem mem_callMoves_ans {E F : Silmaril.Games.Sig.{0}} {e : E.Op} {v : E.Ar e} :
    ∀ {l : List (Round E)}, (.inl (.ans e v) : Move E F) ∈ callMoves l → (⟨e, v⟩ : Round E) ∈ l
  | [], h => nomatch h
  | ⟨m, n⟩ :: l, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_callMoves_ans h)

/-- The callout rounds of a segmented run are answered by `g`. -/
theorem resp_of_rounds {calls : List (σ × CallRec × σ)} {rounds : List (Round I.E)}
    (h : List.Forall₂ (RoundOf c I g) calls rounds) :
    ∀ r ∈ rounds, ∃ s s', RespG c I g s r.1 r.2 s' := by
  induction h with
  | nil => exact fun r hr => nomatch hr
  | cons hcl _ ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨_, _, hcl.2.2⟩
    · exact ih r hr

/-- **A returned call keeps the store well formed**: the import answers of its play throw
nothing. -/
theorem wf_after {s s' : Silmaril.Wasm.Execution.Core.Store Nat} (hw : I.WellFormed s)
    {f : I.F.Op} {rounds : List (Round I.E)} {w : I.F.Ar f}
    (hresp : ∀ r ∈ rounds, ∃ q q', RespG c I g q r.1 r.2 q')
    (hpath : I.Path P (.idle s) (cplay [⟨f, rounds, w⟩]) (.idle s')) : I.WellFormed s' := by
  refine (Silmaril.Wasm.Game.ScalarInstance.WellFormed.activation hw ?_ hpath).1
  intro e v hm
  have hm' : (.inl (.ans e v) : Move I.E I.F) ∈ callMoves rounds := by
    rcases List.mem_cons.mp hm with h | h
    · cases h
    rcases List.mem_append.mp h with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · cases h
      · exact nomatch h
  obtain ⟨q, q', hq⟩ := hresp _ (mem_callMoves_ans hm')
  have hr : Silmaril.Wasm.Game.Answer.toResult v = _ := hq.choose_spec.choose_spec.choose_spec.2.2.2.2
  cases v with
  | values _ => trivial
  | trap => cases hr
  | throw _ => cases hr

/-- Segmented runs keep the trampoline invariant. -/
theorem trampOk_after {B : CStore (E3 P)} {th : Option ThreadId} {x y : CoreSt (E3 P)}
    {calls : List (σ × CallRec × σ)} {s s' : σ}
    (h : ASeg g (SiteI c) B th s x calls s' y) (ht : c.TrampOk x.1) : c.TrampOk y.1 := by
  intro a fi hh hfi hcode
  have hf : (x.1 : Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P))).funcs[a]? = some fi := by
    rw [← aseg_funcs h]
    exact hfi
  exact ht a fi hh hf hcode

/-! ## Call `k` -/

/-- **What call `k` with imports shows**, from host state `s`: a play of the instance from the
current store, its IR round with import calls answered by `g` from `s` to some `s'`, and the IR
answer of the outcome; a resolution ends, with the instance idle, at the next configuration
between calls, in host state `s'`. -/
def CallFactsKI (P : Profile) (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (g : σ → HostFuncId → List Val → Option (List Val × σ))
    (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (k : Nat) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (s : σ) (m' : Machine.Config (E3 P) σ)
    (out : CallOutcome) : Prop :=
  ∃ (r : CRound I.E I.F) (u : CRound (sigN c.imports.length) (sigN c.toComp.exports.length))
    (q : I.HState) (s' : σ), IRRoundI c I j vs r u ∧ HostRun g s u.cs s' ∧
    I.Path P (.idle (Store.mapH trampIdx cs)) (cplay [r]) q ∧ ObsAns (Outcome.ofCall out) u.a ∧
    ∀ rs, out = .resolved (some rs) → ∃ cs' ι' G' ST', q = .idle (Store.mapH trampIdx cs') ∧
      m' = readyCfgI cs' ι' fs G' ST' s' ∧ ReadyAtI c I cs' ι' G' (k + 1)

variable {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState}
  {fs : List (CFuncInst (core3P P))} {G : Garb P σ} {ST₀ : List Subtask} {k : Nat}
  {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val} {f : I.F.Op}

/-- A returned core activation whose results lift: the call resolves at the next configuration
between calls. -/
theorem facts_resolved (R : ReadyAtI c I cs ι G k)
    (C : CallCtxKI P c I cs j vs f (I.addrs.getD c.exports[j].core 0))
    {calls : List (σ × CallRec × σ)} {y : CoreSt (E3 P)} {B : CStore (E3 P)}
    {th : Option ThreadId} {s s' : σ}
    (hs : ASeg g (SiteI c) B th s (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (I.addrs.getD c.exports[j].core 0) (lowerArgs c.exports[j].ty.params vs)) calls s' y)
    {rounds : List (Round I.E)} {w : I.F.Ar f} (hrs : List.Forall₂ (RoundOf c I g) calls rounds)
    (hpath : I.Path P (.idle (Store.mapH trampIdx cs)) (cplay [⟨f, rounds, w⟩])
      (.idle (Store.mapH trampIdx y.1)))
    {ws : List Silmaril.Wasm.Component.Val}
    (hR : (answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift c.exports[j].ty)) =
      some (.vals ws))
    {m' : Machine.Config (E3 P) σ} {ι' : InstState} {G' : Garb P σ} {ST : List Subtask}
    (hι : ι' = InstState.removeThread 1 (enterInst ι ⟨G.threads.length⟩)) (hG : G'.Fresh (k + 1))
    (hm : m' = readyCfgI y.1 ι' fs G' ST s') :
    CallFactsKI P c I g cs fs k j vs s m' (.resolved (some (ws.map toRefVal))) := by
  obtain ⟨dss, hrel, hrun⟩ := rounds_dss hrs hs.chain
  obtain ⟨u, hu, hds, hua⟩ := irRound_of C w hrel hrun
  have hready : ReadyAtI c I y.1 ι' G' (k + 1) :=
    { wf := wf_after C.start.wf (resp_of_rounds hrs) hpath
      tramp := trampOk_after hs R.tramp
      threads := hι ▸ threadsOk_after _ _
      leave := hι ▸ R.leave
      fresh := hG }
  refine ⟨⟨f, rounds, w⟩, u, _, s', hu, hds, hpath, ⟨ws, rfl, hua.trans hR⟩, ?_⟩
  intro rs _
  exact ⟨y.1, ι', G', ST, rfl, hm, hready⟩

/-- A trapping outcome with its play. -/
theorem facts_trap (C : CallCtxKI P c I cs j vs f (I.addrs.getD c.exports[j].core 0))
    {rounds : List (Round I.E)} {w : I.F.Ar f} {s s' : σ}
    {dss : List (List (Round (sigN c.imports.length)))}
    (hrel : List.Forall₂ (ImpRel c I) rounds dss) (hrun : HostRun g s dss.flatten s')
    {q : I.HState}
    (hpath : I.Path P (.idle (Store.mapH trampIdx cs)) (cplay [⟨f, rounds, w⟩]) q)
    (hR : (answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift c.exports[j].ty)) = none)
    {m' : Machine.Config (E3 P) σ} :
    CallFactsKI P c I g cs fs k j vs s m' .trap := by
  obtain ⟨u, hu, hds, hua⟩ := irRound_of C w hrel hrun
  exact ⟨⟨f, rounds, w⟩, u, q, s', hu, hds, hpath, hua.trans hR, fun _ h => nomatch h⟩

/-- A returned core activation of call `k`: the call resolves at the next configuration between
calls, or traps where the IR lift fails. -/
theorem facts_values (R : ReadyAtI c I cs ι G k)
    (C : CallCtxKI P c I cs j vs f (I.addrs.getD c.exports[j].core 0))
    {M₀ : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {jf : Nat}
    (hat : CallAtKA prof P g cs (enterInst ι ⟨G.threads.length⟩) fs G ST₀ k jf c.exports[j]
      (I.addrs.getD c.exports[j].core 0) vs M₀ th K segs rest)
    {calls : List (σ × CallRec × σ)} {y : CoreSt (E3 P)} {s s' : σ}
    (hs : ASeg g (SiteI c) M₀.store th s (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (I.addrs.getD c.exports[j].core 0) (lowerArgs c.exports[j].ty.params vs)) calls s' y)
    {ys : List Flat} (hst : (E3 P).status y.1 y.2 = .returned (.values ys)) {ST : List Subtask}
    {CL : List (Caller (E3 P))} {tr₂ : List (Label (E3 P) σ)} {m' : Machine.Config (E3 P) σ}
    {out : CallOutcome}
    (r₂ : Steps prof (answerHostS P g).hr (DA P g)
      (retCfg (extSC (withH M₀ s') ST CL) th K segs rest y ys) tr₂ m')
    (hev : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨k⟩ ev)
    (ho : out.Holds (answerHostS P g).hr ⟨k⟩ m') : CallFactsKI P c I g cs fs k j vs s m' out := by
  obtain ⟨cvs, hcode, hm⟩ := status_values hst
  obtain ⟨rounds, w, hrs, hpath, hw⟩ := path_returnedAt C.start hs (.values cvs) hcode
  have hty : ys.map (·.type) = ValTy.flatList c.exports[j].ty.results := results_typed C.ty hw hm
  have hR : (answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift c.exports[j].ty)) =
      (liftArgs c.exports[j].ty.results ys).map .vals := lifted_answer hw hm
  cases hl : liftArgs c.exports[j].ty.results ys with
  | some ws =>
    show CallFactsKI P c I g cs fs k j vs s m' out
    have hres : (readyCfgI y.1 (InstState.removeThread 1 (enterInst ι ⟨G.threads.length⟩)) fs
        (nextGarbA P g G c.exports[j] k jf (I.addrs.getD c.exports[j].core 0) (vs.map toRefVal)
          (ws.map toRefVal) CL) (ST₀ ++ ST) s').result? ⟨k⟩ = some (some (ws.map toRefVal)) :=
      result?_nextA R.fresh _ _ _ _ _ _ _ _ _ _ _
    have hout : out = .resolved (some (ws.map toRefVal)) ∧ m' = readyCfgI y.1
        (InstState.removeThread 1 (enterInst ι ⟨G.threads.length⟩)) fs
        (nextGarbA P g G c.exports[j] k jf (I.addrs.getD c.exports[j].core 0) (vs.map toRefVal)
          (ws.map toRefVal) CL) (ST₀ ++ ST) s' :=
      out_of_resolvesKA (hat.ret s' ST CL y ys ws hty hl) hres r₂ hev ho
    rw [hout.1]
    exact facts_resolved R C hs hrs hpath (hR.trans (by rw [hl]; rfl)) rfl
      (fresh_nextA R.fresh _ _ _ _ _ _) hout.2
  | none =>
    have hout : out = .trap := out_of_trapsNextKA (hat.trap s' ST CL y ys hty hl) r₂ ho
    rw [hout]
    obtain ⟨dss, hrel, hrun⟩ := rounds_dss hrs hs.chain
    exact facts_trap C hrel hrun hpath (hR.trans (by rw [hl]; rfl))

/-- A trapped core activation of call `k`. -/
theorem facts_coreTrap (C : CallCtxKI P c I cs j vs f (I.addrs.getD c.exports[j].core 0))
    {B : CStore (E3 P)} {th : Option ThreadId}
    {calls : List (σ × CallRec × σ)} {y : CoreSt (E3 P)} {s s' : σ}
    (hs : ASeg g (SiteI c) B th s (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (I.addrs.getD c.exports[j].core 0) (lowerArgs c.exports[j].ty.params vs)) calls s' y)
    (hst : (E3 P).status y.1 y.2 = .returned .trap) {m' : Machine.Config (E3 P) σ} :
    CallFactsKI P c I g cs fs k j vs s m' .trap := by
  have hr : ∃ r : Silmaril.Wasm.Execution.Core.Result, (∀ vs, r ≠ .values vs) ∧
      (y.2.config y.1).code = r.toAdmin := by
    rcases status_trap hst with hc' | ⟨e, hc'⟩
    · exact ⟨.trap, (fun _ h => by cases h), hc'⟩
    · exact ⟨.throw e, (fun _ h => by cases h), hc'⟩
  obtain ⟨r, hrv, hcode⟩ := hr
  obtain ⟨rounds, w, hrs, hpath, hw⟩ := path_returnedAt C.start hs r hcode
  obtain ⟨dss, hrel, hrun⟩ := rounds_dss hrs hs.chain
  exact facts_trap C hrel hrun hpath (lifted_trap (x := c.exports[j]) hrv hw)

/-- The flat arguments of a callout redex. -/
theorem filterMap_callout {y : CoreSt (E3 P)} {h : CanonHost (E3 P)} {ys : List Flat}
    {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hst : (E3 P).status y.1 y.2 = .callout h ys)
    (hd : Silmaril.Wasm.SingleThreaded.decompose? y.1 (y.2.config y.1).code = some (E, a, h, args)) :
    args.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys := by
  obtain ⟨E', a', args', hd', hm⟩ := status_callout_redex hst
  have hargs : args' = args := by
    have e' := hd'.symm.trans hd
    simp only [Option.some.injEq, Prod.mk.injEq] at e'
    exact e'.2.2.2
  exact hargs ▸ filterMap_of_mapM hm

/-- A failing callout of call `k`: the call traps. -/
theorem facts_fail (C : CallCtxKI P c I cs j vs f (I.addrs.getD c.exports[j].core 0))
    {B : CStore (E3 P)} {th : Option ThreadId}
    {calls : List (σ × CallRec × σ)} {y : CoreSt (E3 P)} {s s' : σ}
    (hs : ASeg g (SiteI c) B th s (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (I.addrs.getD c.exports[j].core 0) (lowerArgs c.exports[j].ty.params vs)) calls s' y)
    {L : LowerSite P} {ys : List Flat} {E : Silmaril.Wasm.SingleThreaded.Ctx} {a' : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val} (hst : (E3 P).status y.1 y.2 = .callout L.host ys)
    (hq : SiteI c L) (hf : L.Fails g s' ys)
    (hd : Silmaril.Wasm.SingleThreaded.decompose? y.1 (y.2.config y.1).code =
      some (E, a', L.host, args)) {m' : Machine.Config (E3 P) σ} :
    CallFactsKI P c I g cs fs k j vs s m' .trap := by
  obtain ⟨rounds, e, q, hrs, he, hpath⟩ := path_callout_trapAt C.start hs (decompose_mapped hd)
  have hek : e.1.val = L.f.idx ∧ e.2.1 = args := ifaceOp?_some he
  have hys : e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys :=
    hek.2 ▸ filterMap_callout hst hd
  obtain ⟨ds, hds, hrun₁⟩ := impRel_fail (I := I) (e := e) hq hek.1 hys hf
  obtain ⟨dss, hrel, hrun⟩ := rounds_dss hrs hs.chain
  have hrel' : List.Forall₂ (ImpRel c I) (rounds ++ [⟨e, .trap⟩]) (dss ++ [ds]) :=
    List.rel_append hrel (.cons hds .nil)
  have hrun' : HostRun g s (dss ++ [ds]).flatten s' := by
    rw [List.flatten_append, List.flatten_singleton]
    exact hrun.append hrun₁
  exact facts_trap (w := .trap) C hrel' hrun' hpath rfl

/-- **The reference outcome of an ending core phase of call `k`.** -/
theorem facts_of_end (R : ReadyAtI c I cs ι G k)
    (C : CallCtxKI P c I cs j vs f (I.addrs.getD c.exports[j].core 0))
    {M₀ : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)} {jf : Nat} {s : σ}
    (hat : CallAtKA prof P g cs (enterInst ι ⟨G.threads.length⟩) fs G ST₀ k jf c.exports[j]
      (I.addrs.getD c.exports[j].core 0) vs M₀ th K segs rest)
    {tr : List (Label (E3 P) σ)} {m' : Machine.Config (E3 P) σ} {out : CallOutcome}
    (hend : CoreEnd (prof := prof) g (SiteI c) M₀ s th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD c.exports[j].core 0)
        (lowerArgs c.exports[j].ty.params vs)) tr m' out)
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨k⟩ ev)
    (ho : out.Holds (answerHostS P g).hr ⟨k⟩ m') :
    CallFactsKI P c I g cs fs k j vs s m' out := by
  obtain ⟨calls, s', y, hs, hexit | hfail⟩ := hend
  · obtain ⟨ST, CL, pre, l, m₁, tr₂, htr, hco, hx, r₂⟩ := hexit
    have hev' : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨k⟩ ev :=
      fun ev hm => hev ev (htr ▸ List.mem_append_right _ hm)
    rcases hx with ⟨ys, hst, -, hm₁⟩ | ⟨hst, -, hm₁⟩ | ⟨h, ys, hst⟩
    · exact facts_values R C hat hs hst (hm₁ ▸ r₂) hev' ho
    · have hout : out = .trap := holds_trapCfg' (steps_of_locked rfl rfl (hm₁ ▸ r₂) ▸ ho)
      exact hout ▸ facts_coreTrap C hs hst
    · exact absurd hst (hco h ys)
  · obtain ⟨L, ys, E, a', args, hst, hq, -, hf, hd, hout⟩ := hfail
    exact hout ▸ facts_fail C hs hst hq hf hd

/-- The configuration of call `k` running its core activation, with no callout records yet. -/
theorem coreCfg_startK {x : SimpleExport} {a : Nat} {ι' : InstState} {jf : Nat}
    {M₀ : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)}
    (hat : CallAtKA prof P g cs ι' fs G ST₀ k jf x a vs M₀ th K segs rest) :
    M₀ = coreCfg (extSC (withH M₀ M₀.host) [] []) th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a (lowerArgs x.ty.params vs)) := by
  rw [withH_self, extSC_nil, ← hat.core]
  exact eq_coreCfg hat.ctl

/-- **Terminating calls with imports between calls**, from host state `s`. -/
theorem calls_factsKI (hc : c.Good) (hff : c.FloatFree) (har : c.Arity) (hI : c.mod.IsInst I)
    (hg : c.HostOkS g) (R : ReadyAtI c I cs ι G k) (j : Fin c.exports.length)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) {s : σ}
    {m' : Machine.Config (E3 P) σ} {out : CallOutcome}
    (hcalls : Calls prof (answerHostS P g).hr (DA P g)
      (readyCfgI cs ι (SimpleI.afterFuncs P (fun k => I.addrs.getD k 0) c) G ST₀ s) ⟨k⟩
      ⟨c.imports.length + j⟩ (vs.map toRefVal) m' out) :
    CallFactsKI P c I g cs (SimpleI.afterFuncs P (fun k => I.addrs.getD k 0) c) k j vs s m'
      out := by
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
  obtain ⟨nm, hcore⟩ := hc.core _ hx
  have hk : c.exports[j].core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcore).1
  have hflat : c.mod.exports[c.exports[j].core] = (nm, c.exports[j].ty.flat) :=
    (List.getElem?_eq_some_iff.mp hcore).2
  have hxs : (lowerArgs c.exports[j].ty.params vs).map (·.type) =
      c.mod.exports[c.exports[j].core].2.params := by
    rw [hflat]
    exact lowerList_types _ _ hvs
  obtain ⟨f, hf₁, hf₂, hft⟩ := typedCallI hI hk hxs
  have C : CallCtxKI P c I cs j vs f (I.addrs.getD c.exports[j].core 0) :=
    { start := ⟨hc, hI, rfl, R.wf, by rw [← hf₁]; rfl, hf₂⟩, typed := hvs, core := hf₁
      ty := by rw [hft, hflat] }
  obtain ⟨hmax, hmaxr, hres⟩ := har.1 _ hx
  obtain ⟨hpf, hrf⟩ := hff.1 _ hx
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat, hhost⟩ := call_at_kA (g := g) prof cs ι _
    (SimpleI.afterFuncs P (fun k => I.addrs.getD k 0) c) G ST₀ s k (c.imports.length + j) _
    c.exports[j] vs hpf hvs hmax hres hmaxr hrf (addThread?_ok R.threads _)
    (removeThread?_enter _ _) (afterFuncs_lifted _ j.isLt)
  have hok : CalloutsOk g (SiteI c) M₀.store th M₀.host
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
        (I.addrs.getD c.exports[j].core 0) (lowerArgs c.exports[j].ty.params vs)) :=
    calloutsOk_ofAt C.start hff har R.tramp hg ⟨hat.funcs, hat.entry, ⟨_, hat.inst, R.leave⟩⟩
  obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
  obtain ⟨m₂, st, r⟩ := Steps.cons_iff.mp hs
  have r₀ : Steps prof (answerHostS P g).hr (DA P g) (invokedAtI cs ι
      (SimpleI.afterFuncs P (fun k => I.addrs.getD k 0) c) G ST₀ s k (c.imports.length + j)
      (vs.map toRefVal)) tr m' := invoke_inv_kA st ▸ r
  rcases hpre.inv r₀ with hl | ⟨tr'', e, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  have r'' : Steps prof (answerHostS P g).hr (DA P g) (coreCfg (extSC (withH M₀ M₀.host) [] [])
      th K segs rest (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
        (I.addrs.getD c.exports[j].core 0) (lowerArgs c.exports[j].ty.params vs))) tr'' m' :=
    coreCfg_startK hat ▸ r'
  have hend : CoreEnd (prof := prof) g (SiteI c) M₀ M₀.host th K segs rest
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD c.exports[j].core 0)
        (lowerArgs c.exports[j].ty.params vs)) tr'' m' out :=
    segs_inv hat.lock tr''.length _ _ [] [] tr'' m' out le_rfl hok r'' ho
  have hev' : ∀ ev, Label.host ev ∈ tr'' → CallHostEvent ⟨k⟩ ev :=
    fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
  rw [← hhost]
  exact facts_of_end R C hat hend hev' ho

end Silmaril.Proofs.Wasm.Component.Reference
