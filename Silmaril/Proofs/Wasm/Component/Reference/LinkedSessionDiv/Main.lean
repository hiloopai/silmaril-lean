module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv.Call

/-!
# Diverging linked sessions: specification to reference

* `sessDivL_fwd`: a specification session (`Linked2.SessSpec`) from the stores of `ReadyL`,
  followed by a round that never answers (`Linked2.RoundDiv`), is a resumable session of the
  reference machine ending in a diverging call (`SessDiv`): `linkCall_fwd` for each round (after
  a trap the session resumes from `resumeCfg`, as in `sessL_fwd`), then `linkDiv_fwd`;
* `linked2_divSpecToRef`: from the instantiation of `l.toRef` (as `linked2_sess_specToRef`),
  `Linked2.DivSpecToRef` holds under `Linked2.Adequate`, at every profile, component choice
  profile and host. The typing hypotheses of `DivSpecToRef` are not used: `DivRound.Ok` checks
  the arguments.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## Sessions between calls -/

section Sess

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

/-- **Specification sessions ending in a round that never answers are reference sessions
ending in a diverging call**, between linked calls. -/
theorem sessDivL_fwd (S₀ : LStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOk l Ii s₀ fs)
    {calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)}
    {outs : List (Option (List Silmaril.Wasm.Component.Val))} {u π u' π' : Store Nat}
    (hspec : Linked2.SessSpec P l Ie Ii u π calls outs u' π') {j : Fin l.imp.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} (hd : Linked2.RoundDiv P l Ie Ii u' π' j vs) :
    ∀ (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState) (G : Garb P σ)
      (ST : List Subtask) (h₀ : σ) (k : Nat),
      ReadyL P l Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k →
      SessDiv prof (linkHost impl) (readyCfgL cs ιe ιi fs G ST h₀) k (callArgsL l calls)
        (refOuts outs) ⟨l.exp.exports.length + j⟩ (vs.map toRefVal) := by
  induction hspec with
  | nil =>
    intro cs ιe ιi G ST h₀ k R
    exact .div (linkDiv_fwd (prof := prof) (impl := impl) (ST := ST) (h₀ := h₀) S₀ hB₀ hfs R hd)
  | @round u π u₁ π₁ u' π' cs outs o d hok hpath hexp hans _ ih =>
    intro cs₀ ιe ιi G ST h₀ k R
    cases o with
    | some ws =>
      obtain ⟨cs', ιe', ιi', G', ST', hc, R'⟩ := linkCall_fwd (prof := prof) (impl := impl)
        (ST := ST) (h₀ := h₀) S₀ hB₀ hfs R d hok hpath hexp hans
      exact .ret hc (ih hd _ _ _ _ _ _ _ R')
    | none =>
      obtain ⟨m', hc, hR'⟩ := linkCall_fwd (prof := prof) (impl := impl)
        (ST := ST) (h₀ := h₀) S₀ hB₀ hfs R d hok hpath hexp hans
      have R₁ : ReadyL P l Ie Ii s₀ u₀ F₀ m'.core ιe ιi G u₁ π₁ (k + 1) :=
        ⟨hR', R.thE, R.thI, R.leave, fresh_succL R.fresh⟩
      refine .trap hc ?_
      rw [resumeCfg_readyL]
      exact ih hd _ _ _ _ _ _ _ R₁

end Sess

/-! ## Assembly -/

/-- **Specification divergence of a linked session is reference divergence**: under
`Linked2.Adequate`, `Linked2.DivSpecToRef` holds at every profile and component choice
profile. -/
theorem linked2_divSpecToRef (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) : Linked2.DivSpecToRef P prof l := by
  intro calls j vs _ _ σ impl h₀ outs hout
  obtain ⟨Ie, Ii, u, π, hIe, hIi, hspec, hd⟩ := hout
  obtain ⟨hEg, hEi, hIg, hIi', har, hff, hW, hN, hn, hS⟩ := hl
  obtain ⟨Ie₀, cse, cie, hFe⟩ := coreFacts (Pf := P) hEg hEi
  obtain rfl : Ie = Ie₀ := NumModule.IsInst.unique hIe hFe.isInst
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
  have hSq := sessDivL_fwd (prof := prof) (impl := impl) S₀ rfl hok hspec hd _ _ _ _ [] h₀ 0 R₀
  refine ⟨afterLink P (reloc cse (Store.mapH Prod.fst r)) (fun k => Ie.addrs.getD k 0)
    (addrL (cse : Store _).funcs.length Ii) l h₀, ⟨0⟩, exportMapL l,
    calls.map fun q => (⟨l.exp.exports.length + q.1⟩ : FuncId), ⟨l.exp.exports.length + j⟩, ?_,
    mapM_lookupL hIg calls, exportMapL_lookup hIg j, ?_⟩
  · refine ⟨trD, .cons (Step.hostRun ⟨rfl, rfl, rfl⟩) d.steps, Adequacy.LRun.no_host d, rfl, rfl,
      ?_⟩
    rw [ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
  · have hz : (calls.map fun q => (⟨l.exp.exports.length + q.1⟩ : FuncId)).zip
        (calls.map fun q => q.2.map toRefVal) = callArgsL l calls := by
      rw [← zip_callArgsL calls, List.map_map]
      rfl
    rw [hz]
    exact hSq

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv
