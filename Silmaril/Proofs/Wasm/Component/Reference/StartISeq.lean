module

public import Silmaril.Proofs.Wasm.Component.Reference.SoundSeqI

/-!
# Calls with imports between calls, for any component functions

`calls_factsKI` and the sequence lemmas of `SoundSeqI` are stated for the component functions
`SimpleI.afterFuncs` of a component without a start function. With a start function the lifted
start function sits between the host functions of the imports and the lifted exports
(`fsS`). The lemmas here take any component functions `fs` with the host functions of the
imports first (`HostPre`) and export `j` lifted at `o + j` (`LiftsAt`):

* `calloutsOk_ofAtP` (`FrameOkP`: only the import prefix of the functions is used);
* `calls_factsKIP`, `seqI_stepP`, `seqI_invP`, `last_callIP`.

The proofs are those of `CallPhaseI`, `CallPhaseKI` and `SoundSeqI`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN)

variable {P : Profile} {σ : Type} {g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ)}
  {prof : ProfileKind}
  {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance}

/-- The component functions `fs` begin with the host functions of the imports. -/
def HostPre (c : SimpleI) (fs : List (CFuncInst (core3P P))) : Prop :=
  ∀ k (hk : k < c.imports.length), fs[k]? = some (.host (witFt c.imports[k].2) ⟨k⟩)

/-- Export `j` of `c` is lifted at function `o + j` of `fs`. -/
def LiftsAt (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance) (fs : List (CFuncInst (core3P P)))
    (o : Nat) : Prop :=
  ∀ j : Fin c.exports.length,
    fs[o + j]? = some (.lifted (I.addrs.getD c.exports[j].core 0) (liftedFt c.exports[j]) {} ⟨0⟩)

/-- Calls of exports (by index) on IR values, as reference function values at offset `o`. -/
def callArgsIO (c : SimpleI) (o : Nat)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)) :
    List (FuncId × List Silmaril.Wasm.Component.Reference.Val) :=
  calls.map fun q => (⟨o + q.1⟩, q.2.map toRefVal)

/-- The facts about the frame (any component functions with the host functions of the imports
first) of the core activation that the callouts use. -/
structure FrameOkP (c : SimpleI) (B : CStore (E3 P)) (th : Option ThreadId) : Prop where
  funcs : ∀ k (hk : k < c.imports.length), B.funcs[k]? = some (.host (witFt c.imports[k].2) ⟨k⟩)
  entry : ∀ f ft opts, calloutEntry B th (.lowered f ft opts ⟨0⟩) = none
  inst : ∃ st, ArenaField.insts.get? B ⟨0⟩ = some st ∧ st.mayLeave = true

/-- **The callouts of the core activation are the trampolines of the imports** (at a later store), at the types
of the imports, typed and answered by `g` as the IR prescribes. -/
theorem calloutsOk_ofAtP {s : Silmaril.Wasm.Execution.Core.Store Nat} {cs : (core3P P).Store (CanonHost (core3P P))} {f : I.F.Op} {a : Nat}
    {xs : List Flat} (C : CallStartAt c I s cs f a xs) (hff : c.FloatFree) (har : c.Arity)
    (htr : c.TrampOk cs) (hg : c.HostOkS g) {B : CStore (E3 P)} {th : Option ThreadId}
    (hB : FrameOkP c B th) {s₀ : σ} :
    CalloutsOk g (SiteI c) B th s₀ (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) := by
  intro calls s' y h ys hs hst
  obtain ⟨-, -, post⟩ := aseg_rounds C.good C.inst C.wf (f := f) hs (C.pre s₀)
  obtain ⟨E, a', args, hd, hm⟩ := status_callout_redex hst
  obtain ⟨fi, -, -, -, hfi, hcode, -⟩ := Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  have hfi' : (cs : Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P))).funcs[a']? = some fi := by
    rw [← aseg_funcs hs]
    exact hfi
  obtain ⟨k, hk, rfl⟩ := htr a' fi h hfi' hcode
  obtain ⟨e, he⟩ := callout_typed C.wf post (decompose_mapped hd)
  have hek := ifaceOp?_some he
  have htyped : ys.map (·.type) = ValTy.flatList c.imports[k].2.params := by
    have ht : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal
        ((ValTy.flatList c.imports[k].2.params).map .num) args := by
      have h₀ : (I.imports.get e.1).params = (ValTy.flatList c.imports[k].2.params).map .num := by
        rw [imports_get C.good C.inst e k hk hek.1]
        rfl
      have h₁ : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (I.imports.get e.1).params args :=
        hek.2 ▸ e.2.2
      exact h₀ ▸ h₁
    exact toFlat?_types _ _ _ ht hm
  obtain ⟨st, hst', hleave⟩ := hB.inst
  have hmem : c.imports[k] ∈ c.imports := List.getElem_mem hk
  let L : LowerSite P := ⟨⟨k⟩, ⟨0⟩, st, witFt c.imports[k].2, ⟨k⟩, c.imports[k].2⟩
  refine ⟨L, ⟨k, hk, rfl, rfl, rfl⟩, rfl, ?_⟩
  exact { entry := hB.entry _ _ _, inst := hst', leave := hleave
          func := by
            show (B.funcs)[k]? = _
            exact hB.funcs k hk
          pff := (hff.2 _ hmem).1, rff := (hff.2 _ hmem).2, typed := htyped
          maxp := (har.2 _ hmem).1, res := (har.2 _ hmem).2.2, maxr := (har.2 _ hmem).2.1
          answers := fun s ws rs s' h => hg s k hk ws rs s' h }


section Calls

variable {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState}
  {G : Garb P σ} {ST₀ : List Subtask} {k : Nat}
  {vs : List Silmaril.Wasm.Component.Val}

/-- **Terminating calls with imports between calls**, for any component functions with the host
functions of the imports first and the called export's lift at `jf`, from host state `s`. -/
theorem calls_factsKIP (hc : c.Good) (hff : c.FloatFree) (har : c.Arity) (hI : c.mod.IsInst I)
    (hg : c.HostOkS g) {fs : List (CFuncInst (core3P P))} {jf : Nat}
    (hfh : ∀ k (hk : k < c.imports.length), fs[k]? = some (.host (witFt c.imports[k].2) ⟨k⟩))
    (R : ReadyAtI c I cs ι G k) (j : Fin c.exports.length)
    (hfl : fs[jf]? = some (.lifted (I.addrs.getD c.exports[j].core 0) (liftedFt c.exports[j]) {} ⟨0⟩))
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) {s : σ}
    {m' : Machine.Config (E3 P) σ} {out : CallOutcome}
    (hcalls : Calls prof (answerHostS P g).hr (DA P g)
      (readyCfgI cs ι fs G ST₀ s) ⟨k⟩
      ⟨jf⟩ (vs.map toRefVal) m' out) :
    CallFactsKI P c I g cs fs k j vs s m'
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
    fs G ST₀ s k jf _
    c.exports[j] vs hpf hvs hmax hres hmaxr hrf (addThread?_ok R.threads _)
    (removeThread?_enter _ _) hfl
  have hok : CalloutsOk g (SiteI c) M₀.store th M₀.host
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
        (I.addrs.getD c.exports[j].core 0) (lowerArgs c.exports[j].ty.params vs)) :=
    calloutsOk_ofAtP C.start hff har R.tramp hg
      ⟨fun k hk => hat.funcs ▸ hfh k hk, hat.entry, ⟨_, hat.inst, R.leave⟩⟩
  obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
  obtain ⟨m₂, st, r⟩ := Steps.cons_iff.mp hs
  have r₀ : Steps prof (answerHostS P g).hr (DA P g) (invokedAtI cs ι
      fs G ST₀ s k jf
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


end Calls

/-- One resolved call between calls, from host state `s`. -/
theorem seqI_stepP (hc : c.Good) (hff : c.FloatFree) (har : c.Arity) (hI : c.mod.IsInst I)
    (hg : c.HostOkS g) {fs : List (CFuncInst (core3P P))} {o : Nat} (hfh : HostPre c fs)
    (hfo : LiftsAt c I fs o) {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState}
    {G : Garb P σ} {ST : List Subtask} {k : Nat} {s : σ} (R : ReadyAtI c I cs ι G k)
    (j : Fin c.exports.length)
    {vs : List Silmaril.Wasm.Component.Val} (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {m₁ : Machine.Config (E3 P) σ} {rs : List Silmaril.Wasm.Component.Reference.Val}
    (hcall : Calls prof (answerHostS P g).hr (DA P g) (readyCfgI cs ι fs G ST s) ⟨k⟩
      ⟨o + j⟩ (vs.map toRefVal) m₁ (.resolved (some rs))) :
    ∃ (r : CRound I.E I.F) (ds : List (Round (sigN c.imports.length)))
      (ws : List Silmaril.Wasm.Component.Val) (cs' : (core3P P).Store (CanonHost (core3P P)))
      (ι' : InstState) (G' : Garb P σ) (ST' : List Subtask) (s' : σ),
      IRRoundI c I j vs r ⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), ds, some (.vals ws)⟩ ∧
      HostRun g s ds s' ∧ rs = ws.map toRefVal ∧
      I.Activation P (Store.mapH trampIdx cs) (cplay [r]) (Store.mapH trampIdx cs') ∧
      m₁ = readyCfgI cs' ι' fs G' ST' s' ∧ ReadyAtI c I cs' ι' G' (k + 1) := by
  obtain ⟨r, u, q, s', hu, hds, hpath, hobs, hnext⟩ := calls_factsKIP hc hff har hI hg hfh R j (hfo j) hvs hcall
  obtain ⟨ws, hrs, hua⟩ : ∃ ws : List Silmaril.Wasm.Component.Val, rs = ws.map toRefVal ∧
      u.a = some (.vals ws) := hobs
  obtain ⟨cs', ι', G', ST', rfl, hm, R'⟩ := hnext rs rfl
  have hu' : u = ⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), u.cs, some (.vals ws)⟩ := hu.eq hua
  exact ⟨r, u.cs, ws, cs', ι', G', ST', s', hu' ▸ hu, hds, hrs, hpath, hm, R'⟩

/-- What a sequence of resolved calls with imports between calls shows, from host state `s`. -/
def SeqFactsIP (P : Profile) (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance)
    (fs : List (CFuncInst (core3P P)))
    (g : σ → HostFuncId → List Silmaril.Wasm.Component.Reference.Val → Option (List Silmaril.Wasm.Component.Reference.Val × σ))
    (cs : (core3P P).Store (CanonHost (core3P P))) (k : Nat) (s : σ)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (rss : List (List Silmaril.Wasm.Component.Reference.Val)) (mₙ : Machine.Config (E3 P) σ) : Prop :=
  ∃ (lr : List (CRound I.E I.F)) (dss : List (List (Round (sigN c.imports.length))))
    (wss : List (List Silmaril.Wasm.Component.Val)) (cs' : (core3P P).Store (CanonHost (core3P P)))
    (ι' : InstState) (G' : Garb P σ) (ST' : List Subtask) (s' : σ),
    I.Activation P (Store.mapH trampIdx cs) (cplay lr) (Store.mapH trampIdx cs') ∧
    List.Forall₂ (fun r u => ∃ j vs, IRRoundI c I j vs r u) lr (seqRoundsI c calls dss wss) ∧
    HostRun g s dss.flatten s' ∧ rss = wss.map (·.map toRefVal) ∧
    calls.length = dss.length ∧ calls.length = wss.length ∧
    mₙ = readyCfgI cs' ι' fs G' ST' s' ∧ ReadyAtI c I cs' ι' G' (k + calls.length)

/-- Sequences of resolved calls from one configuration between calls. -/
theorem seqFactsI_consP {fs : List (CFuncInst (core3P P))} {cs cs₁ : (core3P P).Store (CanonHost (core3P P))} {k : Nat} {s s₁ : σ}
    {j : Fin c.exports.length} {vs : List Silmaril.Wasm.Component.Val}
    {calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val)} {r : CRound I.E I.F}
    {ds : List (Round (sigN c.imports.length))} {ws : List Silmaril.Wasm.Component.Val}
    {rss : List (List Silmaril.Wasm.Component.Reference.Val)} {mₙ : Machine.Config (E3 P) σ}
    (hu : IRRoundI c I j vs r ⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), ds, some (.vals ws)⟩)
    (hds : HostRun g s ds s₁)
    (hact : I.Activation P (Store.mapH trampIdx cs) (cplay [r]) (Store.mapH trampIdx cs₁))
    (h : SeqFactsIP P c I fs g cs₁ (k + 1) s₁ calls rss mₙ) :
    SeqFactsIP P c I fs g cs k s ((j, vs) :: calls) ((ws.map toRefVal) :: rss) mₙ := by
  obtain ⟨lr, dss, wss, cs', ι', G', ST', s', hact', hrel, hdss, rfl, hl₁, hl₂, hm, R'⟩ := h
  have hk : k + 1 + calls.length = k + ((j, vs) :: calls).length := by
    simp only [List.length_cons]
    omega
  refine ⟨r :: lr, ds :: dss, ws :: wss, cs', ι', G', ST', s', ?_, .cons ⟨j, vs, hu⟩ hrel, ?_,
    rfl, by rw [List.length_cons, hl₁, List.length_cons],
    by rw [List.length_cons, hl₂, List.length_cons], hm, hk ▸ R'⟩
  · show I.Activation P _ (cplay ([r] ++ lr)) _
    rw [cplay_append]
    exact path_append hact hact'
  · rw [List.flatten_cons]
    exact hds.append hdss

/-- **Sequences of resolved calls with imports** are activations of the instance from store to
store, with IR rounds, the host state threaded through their import calls. -/
theorem seqI_invP (hc : c.Good) (hff : c.FloatFree) (har : c.Arity) (hI : c.mod.IsInst I)
    (hg : c.HostOkS g) {fs : List (CFuncInst (core3P P))} {o : Nat} (hfh : HostPre c fs)
    (hfo : LiftsAt c I fs o) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState) (G : Garb P σ)
      (ST : List Subtask) (s : σ) (k : Nat) (rss : List (List Silmaril.Wasm.Component.Reference.Val))
      (mₙ : Machine.Config (E3 P) σ),
      ReadyAtI c I cs ι G k → c.TypedCalls calls →
      SeqCalls prof (answerHostS P g) (readyCfgI cs ι fs G ST s) k (callArgsIO c o calls)
        rss mₙ →
      SeqFactsIP P c I fs g cs k s calls rss mₙ
  | [], cs, ι, G, ST, s, k, rss, mₙ, R, _, hS => by
    cases hS
    exact ⟨[], [], [], cs, ι, G, ST, s, .nil _, .nil, .nil _, rfl, rfl, rfl, rfl, R⟩
  | (j, vs) :: calls, cs, ι, G, ST, s, k, rss, mₙ, R, ht, hS => by
    cases hS with
    | cons hcall hS' =>
      have hvs : ValTy.checkList c.exports[j].ty.params vs = true := ht _ List.mem_cons_self
      obtain ⟨r, ds, ws, cs₁, ι₁, G₁, ST₁, s₁, hu, hds, rfl, hact, rfl, R₁⟩ :=
        seqI_stepP hc hff har hI hg hfh hfo R j hvs hcall
      exact seqFactsI_consP hu hds hact (seqI_invP hc hff har hI hg hfh hfo calls cs₁ ι₁ G₁ ST₁ s₁ (k + 1)
        _ _ R₁ (fun q hq => ht q (List.mem_cons_of_mem _ hq)) hS')

/-- The last call of a sequence with imports, from host state `s`. -/
theorem last_callIP (hc : c.Good) (hff : c.FloatFree) (har : c.Arity) (hI : c.mod.IsInst I)
    (hg : c.HostOkS g) {fs : List (CFuncInst (core3P P))} {o : Nat} (hfh : HostPre c fs)
    (hfo : LiftsAt c I fs o) {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState}
    {G : Garb P σ} {ST : List Subtask} {n : Nat} {s : σ} (R : ReadyAtI c I cs ι G n)
    (j : Fin c.exports.length)
    {vs : List Silmaril.Wasm.Component.Val} (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {b : Silmaril.Wasm.Component.Reference.Outcome}
    (hb : b ∈ callBehaviours prof (answerHostS P g) (readyCfgI cs ι fs G ST s) ⟨n⟩
      ⟨o + j⟩ (vs.map toRefVal)) :
    b = .diverges ∨ ∃ (r : CRound I.E I.F)
      (u : CRound (sigN c.imports.length) (sigN c.toComp.exports.length)) (q : I.HState)
      (s' : σ), IRRoundI c I j vs r u ∧ HostRun g s u.cs s' ∧
      I.Path P (.idle (Store.mapH trampIdx cs)) (cplay [r]) q ∧ ObsAns b u.a := by
  rcases hb with ⟨m', out, hcalls, rfl⟩ | ⟨rfl, -⟩
  · obtain ⟨r, u, q, s', hu, hds, hpath, hobs, -⟩ := calls_factsKIP hc hff har hI hg hfh R j (hfo j) hvs hcalls
    exact .inr ⟨r, u, q, s', hu, hds, hpath, hobs⟩
  · exact .inl rfl


end Silmaril.Proofs.Wasm.Component.Reference
