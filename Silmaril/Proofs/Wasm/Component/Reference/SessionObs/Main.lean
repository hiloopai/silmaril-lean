module

public import Silmaril.Wasm.Component.Reference.SessionObs.Defs
public import Silmaril.Wasm.Game.Termination.Thms
public import Silmaril.Proofs.Wasm.Component.Reference.SessionDiv.Main
public import Silmaril.Proofs.Wasm.Component.Reference.SessionStrat.Main
public import Silmaril.Proofs.Wasm.Component.Reference.MultiSpec
public import Silmaril.Wasm.SingleThreaded.Exec.StatusComplete
public import Silmaril.Wasm.SingleThreaded.Determinism

/-!
# Reference session observations of infinite behaviour

* `SessExec.prefix`, `refSessProd_prefix`: a coherent productive execution gives every finite
  prefix as a resumable session (`SessCalls`, `sessObs`);
* `refSessProd_of_prefix`: conversely, for a store-deterministic session triple (the
  deterministic profiles, `storeDet_compTripleS`), if every finite prefix is a session
  behaviour, the specification stores cohere (`infRounds_of_prefix`, through
  `infRounds_of_rounds`) and a coherent stream of reference configurations is built forward,
  one call at a time (`step_forward`, as in #676's `sessCalls_forward`), by dependent choice
  (`exists_stream`);
* `quiet_not_terminates`: at the deterministic profiles, a call that diverges after a session
  does not also return or trap after the same session (Core termination excludes divergence,
  `Silmaril.Wasm.Game.reach_normal_not_infinite`, from the header `Wasm.Game.Termination`);
* `sess_no_callout`: the lowered call of a session never reaches a host call redex;
* `refSessEquivFull_iff`: at the deterministic profiles the full equivalence is `RefSessEquivD`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.SessionObs

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

/-! ## Generic facts -/

section Generic

/-- **Dependent choice along `ℕ`**: a step relation that can always continue an invariant has an
infinite stream of steps. -/
theorem exists_stream {α : Type _} (Q : ℕ → α → Prop) (R : ℕ → α → α → Prop) {x₀ : α}
    (h0 : Q 0 x₀) (h : ∀ k x, Q k x → ∃ y, R k x y ∧ Q (k + 1) y) :
    ∃ f : ℕ → α, f 0 = x₀ ∧ ∀ k, R k (f k) (f (k + 1)) := by
  let g : (k : ℕ) → {x // Q k x} := fun k =>
    Nat.rec (motive := fun k => {x // Q k x}) ⟨x₀, h0⟩
      (fun k x => ⟨Classical.choose (h k x.1 x.2), (Classical.choose_spec (h k x.1 x.2)).2⟩) k
  exact ⟨fun k => (g k).1, rfl, fun k => (Classical.choose_spec (h k (g k).1 (g k).2)).1⟩

theorem zip_ofFn {β γ : Type _} : ∀ {n : ℕ} (f : Fin n → β) (g : Fin n → γ),
    (List.ofFn f).zip (List.ofFn g) = List.ofFn fun i => (f i, g i)
  | 0, _, _ => rfl
  | _ + 1, f, g => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.zip_cons_cons, zip_ofFn]

theorem mapM_ofFn_some {β γ : Type} {g : β → Option γ} :
    ∀ {n : ℕ} {f : Fin n → β} {r : Fin n → γ},
      (∀ i, g (f i) = some (r i)) → (List.ofFn f).mapM g = some (List.ofFn r)
  | 0, _, _, _ => rfl
  | _ + 1, f, r, h => by
    simp [List.ofFn_succ, List.mapM_cons, h 0, mapM_ofFn_some (fun i => h i.succ)]

end Generic

/-! ## Sessions on the machine -/

section Machine

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type} {prof : ProfileKind}
  {h : Host E σ}

theorem SessStep.cons {m m' : Machine.Config E σ} {k : Nat} {f : FuncId} {args : List RVal}
    {o : Option (List RVal)} {cs : List (FuncId × List RVal)} {outs : List (Option (List RVal))}
    (hs : SessStep prof h m k f args o m') (hr : SessCalls prof h m' (k + 1) cs outs) :
    SessCalls prof h m k ((f, args) :: cs) (o :: outs) := by
  cases hs with
  | ret hc => exact .ret hc hr
  | trap hc => exact .trap hc hr

theorem SessExec.take {m₀ : Machine.Config E σ} {a : ℕ → FuncId × List RVal}
    {out : ℕ → Option (List RVal)} {m : ℕ → Machine.Config E σ}
    (hx : SessExec prof h m₀ a out m) : ∀ (n i : ℕ),
      SessCalls prof h (m i) i (List.ofFn fun t : Fin n => a (i + t))
        (List.ofFn fun t : Fin n => out (i + t))
  | 0, i => .nil _ _
  | n + 1, i => by
    rw [List.ofFn_succ, List.ofFn_succ]
    have ea : (fun t : Fin n => a (i + (t.succ : ℕ))) = fun t : Fin n => a (i + 1 + (t : ℕ)) :=
      funext fun t => congrArg a (by simp only [Fin.val_succ]; omega)
    have eo : (fun t : Fin n => out (i + (t.succ : ℕ))) = fun t : Fin n => out (i + 1 + (t : ℕ)) :=
      funext fun t => congrArg out (by simp only [Fin.val_succ]; omega)
    rw [ea, eo]
    simp only [Fin.val_zero, Nat.add_zero]
    exact SessStep.cons (hx.step i) (SessExec.take hx n (i + 1))

/-- **Prefix closure on the machine.** -/
theorem SessExec.prefix {m₀ : Machine.Config E σ} {a : ℕ → FuncId × List RVal}
    {out : ℕ → Option (List RVal)} {m : ℕ → Machine.Config E σ}
    (hx : SessExec prof h m₀ a out m) (n : ℕ) :
    SessCalls prof h m₀ 0 (Silmaril.Games.Abstract.streamTake a n)
      (Silmaril.Games.Abstract.streamTake out n) := by
  have ht := SessExec.take hx n 0
  simp only [Nat.zero_add] at ht
  rw [hx.zero] at ht
  exact ht

end Machine

/-! ## Simple components -/

open Silmaril.Games.Abstract (streamTake End)
open Silmaril.Games.Abstract.StratThread (Rounds StoreDet InfRounds)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionStrat
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {P : Profile} {prof : ProfileKind} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}

theorem refSessQuiet_iff {calls : List (Fin c.exports.length × List IVal)}
    {outs : List (Option (List IVal))} {j : Fin c.exports.length} {vs : List IVal} :
    RefSessQuiet P prof c calls outs j vs ↔ outs ∈ refDivs P prof c calls j vs := by
  simp only [RefSessQuiet, refDivs, sessDivBehaviours, Set.mem_ofPred_eq, List.map_map]
  rfl

theorem typed_streamTake {a : ℕ → Fin c.exports.length × List IVal}
    (ht : ∀ k, ValTy.checkList c.exports[(a k).1].ty.params (a k).2 = true) (n : ℕ) :
    TypedCalls c (streamTake a n) := fun q hq => by
  simp only [streamTake, List.mem_ofFn] at hq
  obtain ⟨i, rfl⟩ := hq
  exact ht i

/-- **Prefix closure**: a productive execution gives every finite prefix as a session. -/
theorem refSessProd_prefix {a : ℕ → Fin c.exports.length × List IVal}
    {out : ℕ → Option (List IVal)} (h : RefSessProd P prof c a out) (n : ℕ) :
    refOuts (streamTake out n) ∈ sessObs P prof c (streamTake a n) := by
  obtain ⟨m₀, inst, es, fs, hinst, hlk, m, hx⟩ := h
  refine ⟨m₀, inst, es, streamTake fs n, hinst, ?_, ?_⟩
  · simp only [streamTake, List.map_ofFn]
    exact mapM_ofFn_some fun i => hlk i
  · have e₁ : (streamTake fs n).zip (((streamTake a n).map fun q =>
        (c.exports[q.1].name, q.2.map toRefVal)).map Prod.snd) =
        streamTake (fun k => (fs k, (a k).2.map toRefVal)) n := by
      simp only [streamTake, List.map_ofFn]
      exact zip_ofFn _ _
    have e₂ : refOuts (streamTake out n) =
        streamTake (fun k => (out k).map (List.map toRefVal)) n := by
      simp only [refOuts, streamTake, List.map_ofFn]
      rfl
    rw [e₁, e₂]
    exact SessExec.prefix hx n

theorem sessQ_of_typed {q : Fin c.exports.length × List IVal}
    (ht : ValTy.checkList c.exports[q.1].ty.params q.2 = true) :
    c.sessQ ((q.1 : Nat), Payload.vals q.2) = some q := by
  rw [sessQ_eq]
  exact typedQ_typed q.1.isLt ht

/-- A round of the triple on a typed call is a returned or a trapped call. -/
theorem spec_step {s s' : Store Nat} {j : Fin c.exports.length} {vs : List IVal}
    {o : Option (List IVal)}
    (hm : (([] : List (Silmaril.Games.Abstract.Call (sigN 0))), End.ret (outAns o) s') ∈
      compFin P c I s ((j : Nat), Payload.vals vs))
    (hq : c.sessQ ((j : Nat), Payload.vals vs) = some (j, vs)) :
    (∃ ws, o = some ws ∧ RetAt P c I c.exports[j] vs s ws s') ∨
      (o = none ∧ TrapAt P c I c.exports[j] vs s s') := by
  obtain ⟨-, ⟨ws, s₁, hret, he⟩ | ⟨s₁, htrap, he⟩ | ⟨-, he⟩⟩ := (mem_compFin_some hq).mp hm
  · simp only [End.ret.injEq] at he
    obtain ⟨ho, rfl⟩ := he
    cases o with
    | none => cases ho
    | some ws' =>
      simp only [outAns, Sum.inl.injEq, Payload.vals.injEq] at ho
      subst ho
      exact .inl ⟨_, rfl, hret⟩
  · simp only [End.ret.injEq] at he
    obtain ⟨ho, rfl⟩ := he
    cases o with
    | none => exact .inr ⟨rfl, htrap⟩
    | some _ => cases ho
  · cases he

/-- **Coherent specification stores**: for a store-deterministic triple, typed calls whose every
finite prefix is a session behaviour are a coherent infinite sequence of rounds. -/
theorem infRounds_of_prefix (prof : ProfileKind) (hc : c.Adequate) (hI : c.mod.IsInst I)
    (hdet : StoreDet (compTripleS P c I))
    (a : ℕ → Fin c.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList c.exports[(a k).1].ty.params (a k).2 = true)
    (h : ∀ k, refOuts (streamTake out k) ∈ sessObs P prof c (streamTake a k)) :
    ∃ s, InfRounds (compTripleS P c I) I.store
      (fun k => (((a k).1 : Nat), Payload.vals (a k).2)) (fun k => ([], outAns (out k))) s := by
  have hr : ∀ k, ∃ s, Rounds (compTripleS P c I) I.store
      (streamTake (fun i => ((((a i).1 : Nat), Payload.vals (a i).2),
        (([] : List (Silmaril.Games.Abstract.Call (sigN 0))), outAns (out i)))) k) s := by
    intro k
    obtain ⟨I'', outs, s, hI'', hspec, heq⟩ :=
      sess_refToSpec _ prof c hc _ (typed_streamTake ht k) (h k)
    obtain rfl := refOuts_inj heq
    obtain rfl := isInst_unique hI'' hI
    obtain ⟨hR, -, -⟩ := rounds_of_sessSpec hspec (typed_streamTake ht k)
    rw [← map_toRound_streamTake, map_ofRound_toRound] at hR
    exact ⟨s, hR⟩
  exact infRounds_of_rounds hdet hr

/-- **One session call between calls, forward**: a returned or trapped call of the
specification is a step of the reference session, ending between calls again. -/
theorem step_forward (hc : c.Good) (hf : c.FloatFree) (ha : c.Arity) (hI : c.mod.IsInst I)
    {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState} {G : Garb P} {k : Nat}
    (R : ReadyAt I cs ι G k) (j : Fin c.exports.length) {vs : List IVal}
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) {o : Option (List IVal)}
    {s' : Store Nat}
    (h : (∃ ws, o = some ws ∧ RetAt P c I c.exports[j] vs (Store.mapH (fun _ => 0) cs) ws s') ∨
      (o = none ∧ TrapAt P c I c.exports[j] vs (Store.mapH (fun _ => 0) cs) s')) :
    ∃ cs' ι' G', SessStep prof (refHost P)
        (readyCfg cs ι (liftedFuncs P (fun k => I.addrs.getD k 0) c) G) k ⟨j⟩
        (vs.map toRefVal) (o.map (List.map toRefVal))
        (readyCfg cs' ι' (liftedFuncs P (fun k => I.addrs.getD k 0) c) G') ∧
      ReadyAt I cs' ι' G' (k + 1) ∧ Store.mapH (fun _ => (0 : Nat)) cs' = s' := by
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
  have C : CallCtxAt P c I cs c.exports[j] vs := ⟨hI, R.wf, hc.core _ hx, hvs⟩
  obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
  obtain ⟨hff, hffr⟩ := hf _ hx
  have hget := liftedFuncs_get? (P := P) c (fun k => I.addrs.getD k 0) j.isLt
  rcases h with ⟨ws, rfl, hret⟩ | ⟨rfl, htrap⟩
  · have CR := callRun (prof := prof) C R hff hmax hres hmaxr hffr hget
    obtain ⟨cs₁, hcs₁, hcall⟩ := call_forward_ret C R CR hret
    have R₁ : ReadyAt I cs₁ (InstState.removeThread 1 (enterInst ι ⟨G.threads.length⟩))
        (nextGarb G c.exports[j] k j (I.addrs.getD c.exports[j].core 0) (vs.map toRefVal)
          (ws.map toRefVal)) (k + 1) :=
      ⟨hcs₁ ▸ hret.wellFormed hI (hc.core _ hx) R.wf, threadsOk_after _ _,
        fresh_next R.fresh _ _ _ _ _⟩
    exact ⟨cs₁, _, _, .ret hcall, R₁, hcs₁⟩
  · have CR := callRunT (prof := prof) C R hff hmax hres hmaxr hffr hget
    obtain ⟨m', hcall, hcore'⟩ := call_forward_trap C R CR htrap
    have hwf : I.WellFormed s' := htrap.wellFormed hI (hc.core _ hx) R.wf
    have hs₁ : Store.mapH (fun _ => (0 : Nat)) m'.core = s' := by
      rw [hcore']
      exact mapH_mapH_of_noHostFns _ _ (noHostFns_of_wf hI.2.1 hwf)
    have hst : SessStep prof (refHost P)
        (readyCfg cs ι (liftedFuncs P (fun k => I.addrs.getD k 0) c) G) k ⟨j⟩
        (vs.map toRefVal) none
        (resumeCfg (readyCfg cs ι (liftedFuncs P (fun k => I.addrs.getD k 0) c) G) m') :=
      .trap hcall
    rw [resumeCfg_ready] at hst
    exact ⟨m'.core, ι, G, hst, resume_ready C R (hs₁ ▸ htrap), hs₁⟩

/-- **The converse of prefix closure** for a store-deterministic session triple: if every finite
prefix of the typed calls `a` with the outcomes `out` is a session behaviour, there is a coherent
productive execution. -/
theorem refSessProd_of_prefix (prof : ProfileKind) (hc : c.Adequate)
    (hdet : ∀ I, c.mod.IsInst I → StoreDet (compTripleS P c I))
    (a : ℕ → Fin c.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList c.exports[(a k).1].ty.params (a k).2 = true)
    (h : ∀ k, refOuts (streamTake out k) ∈ sessObs P prof c (streamTake a k)) :
    RefSessProd P prof c a out := by
  obtain ⟨I, cs₀, hI, hcs, hinst⟩ := inst_forward P prof hc.good hc.inst
  obtain ⟨s, hs⟩ := infRounds_of_prefix prof hc hI (hdet I hI) a out ht h
  have hstep : ∀ k, (∃ ws, out k = some ws ∧
        RetAt P c I c.exports[(a k).1] (a k).2 (s k) ws (s (k + 1))) ∨
      (out k = none ∧ TrapAt P c I c.exports[(a k).1] (a k).2 (s k) (s (k + 1))) :=
    fun k => spec_step (hs.step k) (sessQ_of_typed (ht k))
  obtain ⟨m, h0, hm⟩ := exists_stream
    (fun k m => ∃ cs ι G, m = readyCfg cs ι (liftedFuncs P (fun k => I.addrs.getD k 0) c) G ∧
      ReadyAt I cs ι G k ∧ Store.mapH (fun _ => (0 : Nat)) cs = s k)
    (fun k m m' => SessStep prof (refHost P) m k ⟨(a k).1⟩ ((a k).2.map toRefVal)
      ((out k).map (List.map toRefVal)) m')
    (x₀ := readyCfg cs₀ {} (liftedFuncs P (fun k => I.addrs.getD k 0) c)
      ⟨[], [], [], [], [], [], []⟩)
    ⟨cs₀, {}, _, rfl, ready_afterInst hI hcs, hcs.trans hs.zero.symm⟩
    (by
      rintro k _ ⟨cs, ι, G, rfl, R, hcs'⟩
      have hk := hstep k
      rw [← hcs'] at hk
      obtain ⟨cs', ι', G', hS, R', hs'⟩ :=
        step_forward (prof := prof) hc.good hc.floatFree hc.arity hI R (a k).1 (ht k) hk
      exact ⟨_, hS, cs', ι', G', rfl, R', hs'⟩)
  exact ⟨_, ⟨0⟩, exportMap c, fun k => ⟨(a k).1⟩, hinst,
    fun k => exportMap_lookup hc.good _ (a k).1.isLt, m, h0, hm⟩

/-! ## Quiescent divergence and termination -/

theorem divAt_not_result {o : GrowOracle} {x : SimpleExport} {vs : List IVal} {s s' : Store Nat}
    {t' : Silmaril.Wasm.SingleThreaded.Thread} {r : Silmaril.Wasm.Execution.Core.Result}
    (hd : DivAt (profile o) I x vs s)
    (run : Silmaril.Wasm.Game.Reach (profile o)
      (s, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) (s', t'))
    (final : Silmaril.Wasm.Game.ResultAt s' t' r) : False := by
  obtain ⟨-, g, h0, hg⟩ := hd
  exact Silmaril.Wasm.Game.reach_normal_not_infinite run
    (Silmaril.Wasm.Game.resultAt_no_internal final) ⟨g, h0, hg⟩

theorem divAt_not_retAt {o : GrowOracle} {x : SimpleExport} {vs ws : List IVal}
    {s s' : Store Nat} (hd : DivAt (profile o) I x vs s) (h : RetAt (profile o) c I x vs s ws s') :
    False := by
  obtain ⟨t', cvs, ys, run, final, -, -⟩ := h.run
  exact divAt_not_result hd run final

theorem divAt_not_trapAt {o : GrowOracle} {x : SimpleExport} {vs : List IVal}
    {s s' : Store Nat} (hd : DivAt (profile o) I x vs s) (h : TrapAt (profile o) c I x vs s s') :
    False := by
  obtain ⟨t', res, run, final, -⟩ := h.run
  exact divAt_not_result hd run final

theorem sessSpec_append : ∀ {s s₂ : Store Nat} {l₁ l₂ : List (SimpleExport × List IVal)}
    {o₁ o₂ : List (Option (List IVal))}, l₁.length = o₁.length →
    SessSpec P c I s (l₁ ++ l₂) (o₁ ++ o₂) s₂ →
    ∃ s₁, SessSpec P c I s l₁ o₁ s₁ ∧ SessSpec P c I s₁ l₂ o₂ s₂
  | s, _, [], _, [], _, _, h => ⟨s, .nil s, h⟩
  | _, _, [], _, _ :: _, _, hl, _ => absurd hl (by simp)
  | _, _, _ :: _, _, [], _, hl, _ => absurd hl (by simp)
  | _, _, (_, _) :: _, _, _ :: _, _, hl, h => by
    rcases sessSpec_cons_inv h with ⟨ws, s₁, rfl, hr, h'⟩ | ⟨s₁, rfl, hr, h'⟩
    · obtain ⟨s₃, h₁, h₂⟩ := sessSpec_append (by simpa using hl) h'
      exact ⟨s₃, .ret hr h₁, h₂⟩
    · obtain ⟨s₃, h₁, h₂⟩ := sessSpec_append (by simpa using hl) h'
      exact ⟨s₃, .trap hr h₁, h₂⟩

/-- **Quiescent divergence excludes termination of the same call** (deterministic profiles). -/
theorem quiet_not_terminates (o : GrowOracle) (prof : ProfileKind) (hc : c.Adequate)
    {calls : List (Fin c.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {j : Fin c.exports.length} {vs : List IVal} (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (hq : RefSessQuiet (profile o) prof c calls outs j vs) (r : Option (List RVal)) :
    refOuts outs ++ [r] ∉ sessObs (profile o) prof c (calls ++ [(j, vs)]) := by
  intro hm
  have hq' : outs ∈ sessDivs (profile o) c calls j vs := by
    rw [SessionDiv.sessDivs_eq_refDivs _ prof c hc calls j vs ht hvs]
    exact refSessQuiet_iff.mp hq
  obtain ⟨I, s, hI, hseq, hd⟩ := hq'
  have ht' : TypedCalls c (calls ++ [(j, vs)]) := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ht q hq
    · rw [List.mem_singleton.mp hq]
      exact hvs
  obtain ⟨I', outs', s₂, hI', hspec, he⟩ := sess_refToSpec _ prof c hc _ ht' hm
  obtain rfl := isInst_unique hI' hI
  have hlen := sessSpec_length hspec
  obtain ⟨outs₁, o₁, rfl⟩ : ∃ l x, outs' = l ++ [x] := by
    rcases List.eq_nil_or_concat outs' with h | ⟨l, x, h⟩
    · subst h
      simp [specCalls] at hlen
    · exact ⟨l, x, h.trans (List.concat_eq_append ..)⟩
  have hl₁ : (specCalls c calls).length = outs₁.length := by
    simp [specCalls] at hlen ⊢
    omega
  have e : specCalls c (calls ++ [(j, vs)]) = specCalls c calls ++ [(c.exports[j], vs)] := by
    simp [specCalls]
  rw [e] at hspec
  obtain ⟨s₁, h₁, h₂⟩ := sessSpec_append hl₁ hspec
  have he₁ : outs = outs₁ := by
    refine refOuts_inj ?_
    simp only [refOuts, List.map_append] at he
    exact (List.append_inj' he rfl).1
  subst he₁
  obtain rfl := rounds_functional (storeDet_compTripleS o) (rounds_of_sessSpec hseq ht).1
    (rounds_of_sessSpec h₁ ht).1
  rcases sessSpec_cons_inv h₂ with ⟨ws, s₃, -, hr, -⟩ | ⟨s₃, -, hr, -⟩
  · exact divAt_not_retAt hd hr
  · exact divAt_not_trapAt hd hr

/-! ## No host callout -/

theorem sess_wellFormed (hc : c.Good) (hI : c.mod.IsInst I) :
    ∀ {s s' : Store Nat} {l : List (SimpleExport × List IVal)} {outs : List (Option (List IVal))},
      (∀ q ∈ l, q.1 ∈ c.exports) → I.WellFormed s → SessSpec P c I s l outs s' →
      I.WellFormed s'
  | _, _, _, _, _, hw, .nil _ => hw
  | _, _, _, _, hl, hw, .ret hr h =>
    sess_wellFormed hc hI (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      (hr.wellFormed hI (hc.core _ (hl _ List.mem_cons_self)) hw) h
  | _, _, _, _, hl, hw, .trap hr h =>
    sess_wellFormed hc hI (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      (hr.wellFormed hI (hc.core _ (hl _ List.mem_cons_self)) hw) h

/-- **No host callout in a session call**: after a specification session from the instance's
store, the lowered call of a typed export never reaches a host call redex. -/
theorem sess_no_callout (hc : c.Adequate) (hI : c.mod.IsInst I)
    {calls : List (Fin c.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {s : Store Nat} (hs : SessSpec P c I I.store (specCalls c calls) outs s)
    (j : Fin c.exports.length) {vs : List IVal}
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {s' : Store Nat} {t' : Silmaril.Wasm.SingleThreaded.Thread}
    (run : Silmaril.Wasm.Game.Reach P
      (s, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (I.addrs.getD c.exports[j].core 0)
        (lowerArgs c.exports[j].ty.params vs)) (s', t'))
    (hh : Nat) (args : List Silmaril.Wasm.Execution.Core.Val) :
    ¬ Silmaril.Wasm.Game.CalloutAt s' t' hh args := by
  rintro ⟨E, a, hd⟩
  have hw : I.WellFormed s := sess_wellFormed hc.good hI (fun q hq => by
      simp only [specCalls, List.mem_map] at hq
      obtain ⟨q', -, rfl⟩ := hq
      exact List.getElem_mem q'.1.isLt) hI.1.choose_spec.ok hs
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
  obtain ⟨nm, hcx⟩ := hc.good.core _ hx
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hcx
  have hxs : (lowerArgs c.exports[j].ty.params vs).map (·.type) =
      c.mod.exports[c.exports[j].core].2.params := by
    rw [hget]
    exact lowerList_types _ _ hvs
  have steps : Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke s (I.addrs.getD c.exports[j].core 0)
        ((lowerArgs c.exports[j].ty.params vs).map Silmaril.Wasm.SingleThreaded.ofFlat))
      (t'.config s') :=
    internalP_steps (H := Nat) run
  have hn := run_no_callout_at hI hw hk hxs steps
  rw [Silmaril.Wasm.SingleThreaded.Thread.config_store] at hn
  rw [hn] at hd
  cases hd

/-! ## The full equivalence -/

theorem castCalls_streamTake {c c' : Simple} (len : c.exports.length = c'.exports.length)
    (a : ℕ → Fin c.exports.length × List IVal) (n : ℕ) :
    castCalls len (streamTake a n) = streamTake (castStream len a) n := by
  simp only [castCalls, castStream, streamTake, List.map_ofFn]
  rfl

/-- **The full equivalence is `RefSessEquivD`** at the deterministic profiles. -/
theorem refSessEquivFull_iff (o : GrowOracle) (prof : ProfileKind) {c c' : Simple}
    (hc : c.Adequate) (hc' : c'.Adequate) :
    RefSessEquivFull (profile o) prof c c' ↔ RefSessEquivD (profile o) prof c c' := by
  rw [SessionDiv.refSessEquivD_iff hc hc']
  constructor
  · intro h
    exact ⟨h.toRefSessEquiv, fun calls j vs ht hvs => Set.ext fun outs => by
      simpa only [refSessQuiet_iff] using h.quiet calls outs j vs ht hvs⟩
  · rintro ⟨h, hd⟩
    refine ⟨h, fun calls outs j vs ht hvs => ?_, fun a out ht => ?_⟩
    · rw [refSessQuiet_iff, refSessQuiet_iff, hd calls j vs ht hvs]
    · have ht' : ∀ k, ValTy.checkList c'.exports[(castStream h.len a k).1].ty.params
          (castStream h.len a k).2 = true := fun k => by
        show ValTy.checkList c'.exports[Fin.cast h.len (a k).1].ty.params (a k).2 = true
        rw [h.ty]
        exact ht k
      rw [Iff.intro refSessProd_prefix
          (refSessProd_of_prefix prof hc (fun _ _ => storeDet_compTripleS o) a out ht),
        Iff.intro refSessProd_prefix
          (refSessProd_of_prefix prof hc' (fun _ _ => storeDet_compTripleS o) _ out ht')]
      refine forall_congr' fun n => ?_
      rw [h.obs _ (typed_streamTake ht n), castCalls_streamTake]

end Silmaril.Proofs.Wasm.Component.Reference.SessionObs
