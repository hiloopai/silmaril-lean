module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs.Inj
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.Sess
public import Silmaril.Proofs.Wasm.Component.Reference.SessionObs.Main

/-!
# Productive executions of linked components on the reference machine

* `refSessProd_prefixL`: a coherent productive execution gives every finite prefix as a resumable
  session behaviour (`SessionObs.SessExec.prefix`, every engine);
* `refSessProd_of_prefixL`: conversely, for store-deterministic linked triples (the deterministic
  profiles, `storeDet_compTripleS`), if every finite prefix is a session behaviour, the
  specification stores cohere (`infRounds_of_prefixL`) and a coherent stream of reference
  configurations is built forward, one linked call at a time (#712's `linkCall_fwd`, `ReadyL`
  between calls, `resumeCfg` after a trap), by dependent choice (`SessionObs.exists_stream`);
* `refSessEquivFull_iffL`: at the deterministic profiles the full equivalence is
  `Linked2.RefSessEquivD`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs

open Silmaril.Games
open Silmaril.Games.Abstract (streamTake End Call)
open Silmaril.Games.Abstract.StratThread (Rounds StoreDet InfRounds)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy (refOuts_inj)
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

variable {P : Profile} {prof : ProfileKind}

/-! ## Prefix closure -/

theorem refSessProd_prefixL {l : Linked2} {σ : Type} {impl : HostImpl (core3P P) σ} {h₀ : σ}
    {a : ℕ → Fin l.imp.exports.length × List IVal} {out : ℕ → Option (List IVal)}
    (h : Linked2.RefSessProd P prof l impl h₀ a out) (n : ℕ) :
    refOuts (streamTake out n) ∈ Linked2.sessObs prof l impl h₀ (streamTake a n) := by
  obtain ⟨m₀, inst, es, fs, hinst, hlk, m, hx⟩ := h
  refine ⟨m₀, inst, es, streamTake fs n, hinst, ?_, ?_⟩
  · simp only [streamTake, List.map_ofFn]
    exact SessionObs.mapM_ofFn_some fun i => hlk i
  · have e₁ : (streamTake fs n).zip (((streamTake a n).map fun q =>
        (l.imp.exports[q.1].name, q.2.map toRefVal)).map Prod.snd) =
        streamTake (fun k => (fs k, (a k).2.map toRefVal)) n := by
      simp only [streamTake, List.map_ofFn]
      exact SessionObs.zip_ofFn _ _
    have e₂ : refOuts (streamTake out n) =
        streamTake (fun k => (out k).map (List.map toRefVal)) n := by
      simp only [refOuts, streamTake, List.map_ofFn]
      rfl
    rw [e₁, e₂]
    exact SessionObs.SessExec.prefix hx n

/-! ## The converse -/

theorem outAns_inj {o o' : Option (List IVal)} (h : outAns o = outAns o') : o = o' := by
  cases o <;> cases o' <;> simp_all [outAns]

/-- A round of the triple on a typed call is a specification round. -/
theorem spec_stepL {l : Linked2} {Ie Ii : SInst} {s s' : Store Nat × Store Nat}
    {j : Fin l.imp.exports.length} {vs : List IVal} {o : Option (List IVal)}
    (hm : (([] : List (Call (sigN 0))), End.ret (outAns o) s') ∈
      Linked2.compFin P l Ie Ii s ((j : Nat), Payload.vals vs))
    (hq : l.typedQ ((j : Nat), Payload.vals vs) = some (j, vs)) :
    Linked2.SessSpec P l Ie Ii s.2 s.1 [(j, vs)] [o] s'.2 s'.1 := by
  obtain ⟨-, ⟨o', π', u', h₁, he⟩ | ⟨-, he⟩⟩ := (mem_compFin_some hq).mp hm
  · simp only [End.ret.injEq] at he
    obtain ⟨ho, rfl⟩ := he
    obtain rfl := outAns_inj ho
    exact h₁
  · cases he

/-- **The converse of prefix closure** for store-deterministic linked triples: if every finite
prefix of the typed calls `a` with the outcomes `out` is a session behaviour, there is a coherent
productive execution. -/
theorem refSessProd_of_prefixL (prof : ProfileKind) {l : Linked2} (hl : l.Adequate)
    (hdet : ∀ Ie Ii, l.exp.mod.IsInst Ie → l.imp.mod.IsInst Ii →
      StoreDet (Linked2.compTripleS P l Ie Ii))
    (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (h : ∀ k, refOuts (streamTake out k) ∈ Linked2.sessObs prof l impl h₀ (streamTake a k)) :
    Linked2.RefSessProd P prof l impl h₀ a out := by
  obtain ⟨hEg, hEi, hIg, hIi', har, hff, hW, hN, hn, hS⟩ := id hl
  obtain ⟨Ie, cse, cie, hFe⟩ := coreFacts (Pf := P) hEg hEi
  obtain ⟨Ii, hIi⟩ := hIi'.inst
  obtain ⟨s, hs⟩ := infRounds_of_prefixL prof hl hFe.isInst hIi (hdet _ _ hFe.isInst hIi) a out
    ht impl h₀ h
  obtain ⟨r, cii, hrs, hh, hFi⟩ := coreFactsL_of_inst (Pf := P) hIg hIi'
    ⟨hS.imp.data, hS.imp.elems⟩ hIi cse ⟨2⟩ l.wireFid
  obtain ⟨trD, ho, d⟩ := instL_lrun (prof := prof) (hr := (linkHost impl).hr)
    (D := (linkHost impl).dispatch) (fun _ _ => rfl) hEg hFe hIg har hIi'.importNames hW hN hFi h₀
  have S₀ : LStat P l Ie Ii Ii.store
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs
      (readyCfgL (σ := σ) (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)) {} {}
        (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
          liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) Garb.empty [] h₀)
      (ownOf Ie.store) :=
    lstat_init hEg hIg hW hn har hff hFe hIi hh _ rfl
  have hg₀ : StoreGood Ie.store := storeGood_inst hS.exp hFe.isInst.1.choose_spec
  have hgu : StoreGood Ii.store := storeGood_inst hS.imp hIi.1.choose_spec
  have R₀ : ReadyL P l Ie Ii Ie.store Ii.store
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)) {} {}
      (Garb.empty : Garb P σ) Ii.store Ie.store 0 :=
    { inv := lready_init hg₀ hgu (linkStore_mapH hn hW hFe hrs hh) rfl
        hFe.isInst.1.choose_spec.ok hIi.1.choose_spec.ok
      thE := threadsOk_empty
      thI := threadsOk_empty
      leave := rfl
      fresh := { pending := (fun _ h => nomatch h), results := (fun _ h => nomatch h) } }
  have hok : LiftedOk l Ii Ie.store (liftedList (Pf := P) (fun k => Ie.addrs.getD k 0) ⟨1⟩
      l.exp.exports ++ liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) :=
    liftedOk_afterLink hIi hIg hFe
  have hstep : ∀ k, Linked2.SessSpec P l Ie Ii (s k).2 (s k).1 [(a k)] [out k] (s (k + 1)).2
      (s (k + 1)).1 := fun k =>
    spec_stepL (hs.step k) (typedQ_typed (ht k))
  have R₀' : ReadyL P l Ie Ii Ie.store Ii.store
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)) {} {}
      (Garb.empty : Garb P σ) (s 0).2 (s 0).1 0 := by
    rw [hs.zero]
    exact R₀
  obtain ⟨m, h0, hm⟩ := SessionObs.exists_stream
    (fun k (m : Machine.Config (E3 P) σ) => ∃ (cs : (core3P P).Store (CanonHost (core3P P)))
      (ιe ιi : InstState) (G : Garb P σ) (ST : List Subtask) (hh : σ),
      m = readyCfgL cs ιe ιi (liftedList (Pf := P) (fun k => Ie.addrs.getD k 0) ⟨1⟩
          l.exp.exports ++ liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports)
        G ST hh ∧
      ReadyL P l Ie Ii Ie.store Ii.store
        (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs cs ιe ιi G
        (s k).2 (s k).1 k)
    (fun k m m' => SessStep prof (linkHost impl) m k ⟨l.exp.exports.length + (a k).1⟩
      ((a k).2.map toRefVal) ((out k).map (List.map toRefVal)) m')
    (x₀ := readyCfgL (σ := σ) (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r))
      {} {} (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
        liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) Garb.empty [] h₀)
    ⟨_, _, _, _, _, _, rfl, R₀'⟩
    (by
      rintro k _ ⟨cs, ιe, ιi, G, ST, hh, rfl, R⟩
      obtain ⟨dr, hj, hv, hokr, hp, he, hans⟩ := sessSpec_single (hstep k)
      have hF := linkCall_fwd (prof := prof) (impl := impl) (ST := ST) (h₀ := hh) S₀ rfl hok R dr
        hokr hp he hans
      rw [hj, hv] at hF
      cases hout : out k with
      | some ws =>
        rw [hout] at hF
        obtain ⟨cs', ιe', ιi', G', ST', hc, R'⟩ := hF
        exact ⟨_, .ret hc, cs', ιe', ιi', G', ST', hh, rfl, R'⟩
      | none =>
        rw [hout] at hF
        obtain ⟨m', hc, hR'⟩ := hF
        refine ⟨_, .trap hc, m'.core, ιe, ιi, G, ST, m'.host,
          resumeCfg_readyL _ _ _ _ _ _ _ _, ?_⟩
        exact ⟨hR', R.thE, R.thI, R.leave, fresh_succL R.fresh⟩)
  refine ⟨afterLink P (reloc cse (Store.mapH Prod.fst r)) (fun k => Ie.addrs.getD k 0)
    (addrL (cse : Store _).funcs.length Ii) l h₀, ⟨0⟩, exportMapL l,
    fun k => ⟨l.exp.exports.length + (a k).1⟩, ?_, fun k => exportMapL_lookup hIg (a k).1,
    m, h0, hm⟩
  refine ⟨trD, .cons (Step.hostRun ⟨rfl, rfl, rfl⟩) d.steps, Adequacy.LRun.no_host d, rfl, rfl, ?_⟩
  rw [ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]

/-- **Productive executions are their finite prefixes** (deterministic profiles). -/
theorem refSessProd_iff_prefixL (o : GrowOracle) (prof : ProfileKind) {l : Linked2}
    (hl : l.Adequate) (a : ℕ → Fin l.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    Linked2.RefSessProd (profile o) prof l impl h₀ a out ↔
      ∀ k, refOuts (streamTake out k) ∈ Linked2.sessObs prof l impl h₀ (streamTake a k) :=
  ⟨refSessProd_prefixL, refSessProd_of_prefixL prof hl
    (fun _ _ _ _ => storeDet_compTripleS) a out ht impl h₀⟩

/-- **Productive executions are coherent rounds of the linked triple** (deterministic profiles). -/
theorem refSessProd_iff_infRoundsL (o : GrowOracle) (prof : ProfileKind) {l : Linked2}
    (hl : l.Adequate) {Ie Ii : SInst} (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii)
    (a : ℕ → Fin l.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    Linked2.RefSessProd (profile o) prof l impl h₀ a out ↔
      ∃ s, InfRounds (Linked2.compTripleS (profile o) l Ie Ii) (Ie.store, Ii.store)
        (fun k => (((a k).1 : Nat), Payload.vals (a k).2)) (fun k => ([], outAns (out k))) s := by
  rw [refSessProd_iff_prefixL o prof hl a out ht impl h₀]
  exact ⟨infRounds_of_prefixL prof hl hIe hIi storeDet_compTripleS a out ht impl h₀,
    fun ⟨_, hs⟩ => (sessInf_iff o prof hl a out ht impl h₀).mp
      (compSession_eq hIe hIi ▸ Silmaril.Games.Abstract.StratSession.InfRounds.mem_sinf hs)⟩

/-- **Productive executions are infinite plays of the session object** (deterministic
profiles). -/
theorem refSessProd_iff_infL (o : GrowOracle) (prof : ProfileKind) {l : Linked2}
    (hl : l.Adequate) (a : ℕ → Fin l.imp.exports.length × List IVal)
    (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList l.imp.exports[(a k).1].ty.params (a k).2 = true) {σ : Type}
    (impl : HostImpl (core3P (profile o)) σ) (h₀ : σ) :
    Linked2.RefSessProd (profile o) prof l impl h₀ a out ↔
      Silmaril.Games.Abstract.StratSession.sroundsPlay
        (fun k => (((a k).1 : Nat), Payload.vals (a k).2))
        (fun k => ([], outAns (out k))) ∈ (Linked2.compSession (profile o) l).inf :=
  (refSessProd_iff_prefixL o prof hl a out ht impl h₀).trans
    (sessInf_iff o prof hl a out ht impl h₀).symm

theorem castCalls_streamTakeL {l l' : Linked2} (len : l.imp.exports.length = l'.imp.exports.length)
    (a : ℕ → Fin l.imp.exports.length × List IVal) (n : ℕ) :
    Linked2.castCalls len (streamTake a n) = streamTake (Linked2.castStream len a) n := by
  simp only [Linked2.castCalls, streamTake, List.map_ofFn]
  rfl

/-- **The full equivalence is `Linked2.RefSessEquivD`** at the deterministic profiles. -/
theorem refSessEquivFull_iffL (o : GrowOracle) (prof : ProfileKind) {l l' : Linked2}
    (hl : l.Adequate) (hl' : l'.Adequate) :
    Linked2.RefSessEquivFull (profile o) prof l l' ↔
      Linked2.RefSessEquivD (profile o) prof l l' := by
  constructor
  · intro h
    exact ⟨h.toRefSessEquiv, fun calls j vs ht hvs σ impl h₀ => Set.ext fun outs =>
      h.quiet calls outs j vs ht hvs impl h₀⟩
  · intro h
    refine ⟨h.toRefSessEquiv, fun calls outs j vs ht hvs σ impl h₀ => ?_,
      fun a out ht σ impl h₀ => ?_⟩
    · have e := h.div calls j vs ht hvs impl h₀
      exact Set.ext_iff.mp e outs
    · have ht' : ∀ k, ValTy.checkList l'.imp.exports[(Linked2.castStream h.len a k).1].ty.params
          (Linked2.castStream h.len a k).2 = true := fun k => by
        show ValTy.checkList l'.imp.exports[Fin.cast h.len (a k).1].ty.params (a k).2 = true
        rw [h.ty]
        exact ht k
      rw [refSessProd_iff_prefixL o prof hl a out ht impl h₀,
        refSessProd_iff_prefixL o prof hl' _ out ht' impl h₀]
      refine forall_congr' fun n => ?_
      rw [h.obs _ (typed_streamTakeL ht n), castCalls_streamTakeL]

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs
