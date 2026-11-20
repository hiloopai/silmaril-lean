module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.Call
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.IR
public import Silmaril.Wasm.Component.Reference.LinkedSessionFwd.Defs

/-!
# Linked sessions: specification to reference

* `sessL_fwd`: a specification session (`Linked2.SessSpec`) from the stores of `ReadyL` is a
  resumable session of the reference machine (`SessCalls`) from the configuration between calls,
  with the reference images of its outcomes (`linkCall_fwd` for each round; after a trap the
  session resumes from `resumeCfg`, where `LReady` holds);
* `instL_mem`: the instantiation of `l.toRef` reaches the configuration after linking
  (`instL_lrun`);
* `linked2_sess_specToRef`: the specification sessions from the instances' stores are session
  behaviours of `l.toRef`;
* `linked2_sessObs_eq`: with `linked2_sess_refToSpec` and the uniqueness of instances, the
  session observations of `l.toRef` for typed calls are exactly the reference images of the
  outcomes of specification sessions;
* `linked2_sessAdequacy`: every specification session is a reference session behaviour and an
  IR play (`linked2_sess_specToIR`);
* `linked2_sess_complete_of`, `linked2_sessObs_eq_ir_of`: given the read-back of IR plays into
  specification sessions (`Linked2.IRToSpec`, a hypothesis), IR plays are reference sessions,
  and the reference session outcomes are exactly those of IR plays.
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

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## Sessions between calls -/

section Sess

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

/-- **Specification sessions are resumable sessions of the machine between linked calls.** -/
theorem sessL_fwd (S₀ : LStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOk l Ii s₀ fs)
    {calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)}
    {outs : List (Option (List Silmaril.Wasm.Component.Val))} {u π u' π' : Store Nat}
    (hspec : Linked2.SessSpec P l Ie Ii u π calls outs u' π') :
    ∀ (cs : (core3P P).Store (CanonHost (core3P P))) (ιe ιi : InstState) (G : Garb P σ)
      (ST : List Subtask) (h₀ : σ) (k : Nat),
      ReadyL P l Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k →
      SessCalls prof (linkHost impl) (readyCfgL cs ιe ιi fs G ST h₀) k (callArgsL l calls)
        (refOuts outs) := by
  induction hspec with
  | nil => intro cs ιe ιi G ST h₀ k _; exact .nil _ _
  | @round u π u₁ π₁ u' π' cs outs o d hok hpath hexp hans _ ih =>
    intro cs₀ ιe ιi G ST h₀ k R
    cases o with
    | some ws =>
      obtain ⟨cs', ιe', ιi', G', ST', hc, R'⟩ := linkCall_fwd (prof := prof) (impl := impl)
        (ST := ST) (h₀ := h₀) S₀ hB₀ hfs R d hok hpath hexp hans
      exact .ret hc (ih _ _ _ _ _ _ _ R')
    | none =>
      obtain ⟨m', hc, hR'⟩ := linkCall_fwd (prof := prof) (impl := impl)
        (ST := ST) (h₀ := h₀) S₀ hB₀ hfs R d hok hpath hexp hans
      have R₁ : ReadyL P l Ie Ii s₀ u₀ F₀ m'.core ιe ιi G u₁ π₁ (k + 1) :=
        ⟨hR', R.thE, R.thI, R.leave, fresh_succL R.fresh⟩
      refine .trap hc ?_
      rw [resumeCfg_readyL]
      exact ih _ _ _ _ _ _ _ R₁

end Sess

/-! ## Assembly -/

/-- **Specification sessions of a linked component are reference sessions** (every profile and
component choice profile): under `Linked2.Adequate`, for the instances `Ie`, `Ii` of the
exporter's and the importer's core modules, the reference images of the outcomes of every
`Linked2.SessSpec` session from their stores are a resumable-session outcome list of `l.toRef`. -/
theorem linked2_sess_specToRef (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    {calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)}
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) {outs : List (Option (List Silmaril.Wasm.Component.Val))}
    {u' π' : Store Nat} (hspec : Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π') :
    refOuts outs ∈ Linked2.sessObs prof l impl h₀ calls := by
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
  have hSq := sessL_fwd (prof := prof) (impl := impl) S₀ rfl hok hspec _ _ _ _ [] h₀ 0 R₀
  refine ⟨afterLink P (reloc cse (Store.mapH Prod.fst r)) (fun k => Ie.addrs.getD k 0)
    (addrL (cse : Store _).funcs.length Ii) l h₀, ⟨0⟩, exportMapL l,
    calls.map fun q => (⟨l.exp.exports.length + q.1⟩ : FuncId), ?_, mapM_lookupL hIg calls, ?_⟩
  · refine ⟨trD, .cons (Step.hostRun ⟨rfl, rfl, rfl⟩) d.steps, Adequacy.LRun.no_host d, rfl, rfl,
      ?_⟩
    rw [ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
  · rw [zip_callArgsL]
    exact hSq

/-- **Reference session outcomes are specification session outcomes** (every profile and
component choice profile, typed calls). -/
theorem linked2_sessObs_eq (P : Profile) (prof : ProfileKind) (l : Linked2) (hl : l.Adequate)
    {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (ht : SimpleI.TypedCalls l.imp calls) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii) :
    Linked2.sessObs prof l impl h₀ calls =
      {o | ∃ (outs : List (Option (List Silmaril.Wasm.Component.Val))) (u' π' : Store Nat),
        Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π' ∧ o = refOuts outs} := by
  ext o
  constructor
  · intro ho
    obtain ⟨Ie', Ii', outs, u', π', hIe', hIi', hs, rfl⟩ :=
      linked2_sess_refToSpec P prof l hl impl h₀ calls ht ho
    obtain rfl := NumModule.IsInst.unique hIe' hIe
    obtain rfl := ImpModule.IsInst.unique hIi' hIi
    exact ⟨outs, u', π', hs, rfl⟩
  · rintro ⟨outs, u', π', hs, rfl⟩
    exact linked2_sess_specToRef P prof l hl impl h₀ hIe hIi hs

/-- **Finite session adequacy of a linked component, in the direction available**: every
specification session from the instances' stores is a reference session behaviour of `l.toRef`
and its session play is a play of `l.toComp.den (impSem P)`. -/
theorem linked2_sessAdequacy (P : Profile) (prof : ProfileKind) (l : Linked2) (hl : l.Adequate)
    {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    {calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val)}
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) {outs : List (Option (List Silmaril.Wasm.Component.Val))}
    {u' π' : Store Nat} (hspec : Linked2.SessSpec P l Ie Ii Ii.store Ie.store calls outs u' π') :
    refOuts outs ∈ Linked2.sessObs prof l impl h₀ calls ∧
      Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P) :=
  ⟨linked2_sess_specToRef P prof l hl impl h₀ hIe hIi hspec,
    linked2_sess_specToIR hl.expGood hl.impGood hIe hIi hspec⟩

/-! ## Conditional on the IR read-back -/

/-- **IR plays are reference sessions, given the read-back `Linked2.IRToSpec`.** -/
theorem linked2_sess_complete_of (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) (hir : Linked2.IRToSpec P l) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (outs : List (Option (List Silmaril.Wasm.Component.Val)))
    (ht : SimpleI.TypedCalls l.imp calls) (hlen : calls.length = outs.length)
    (h : Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P)) :
    refOuts outs ∈ Linked2.sessObs prof l impl h₀ calls := by
  obtain ⟨Ie, cse, cie, hFe⟩ := coreFacts (Pf := P) hl.expGood hl.expInst
  obtain ⟨Ii, hI⟩ := hl.impInst.inst
  obtain ⟨u', π', hs⟩ := hir Ie Ii hFe.isInst hI calls outs ht hlen h
  exact linked2_sess_specToRef P prof l hl impl h₀ hFe.isInst hI hs

/-- **Session adequacy of a linked component, given the read-back `Linked2.IRToSpec`**: the
reference session outcomes of typed calls are exactly the reference images of the outcomes whose
session play is an IR play. -/
theorem linked2_sessObs_eq_ir_of (P : Profile) (prof : ProfileKind) (l : Linked2)
    (hl : l.Adequate) (hir : Linked2.IRToSpec P l) {σ : Type} (impl : HostImpl (core3P P) σ)
    (h₀ : σ) (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (ht : SimpleI.TypedCalls l.imp calls) :
    Linked2.sessObs prof l impl h₀ calls =
      {o | ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
        Linked2.sessMoves l calls outs ∈ l.toComp.den (impSem P)} := by
  ext o
  constructor
  · exact linked2_sess_sound P prof l hl impl h₀ calls ht
  · rintro ⟨outs, rfl, hlen, h⟩
    exact linked2_sess_complete_of P prof l hl hir impl h₀ calls outs ht hlen h

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
