module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkSoundSeq
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallKI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallPhaseI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CallPhaseKI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.CalloutRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.FloatPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Inst
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpDefs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLink
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLinkCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLinkDefs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstLinkNames
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstNest
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkCall
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkCallK
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkCallPhaseK
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkCallout
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkExp
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkNext
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkPlay
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkSeg
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkSegs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkSound
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqBase
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqCall
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.SeqPath
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Seq
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Sound
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.SoundSeqI
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.LinkSoundSeq` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.LinkSoundSeq` that the
soundness of linked components (`linked2_sound`, `linked2_sound_seq`) uses and whose statements
mention the engine `core3R P V IR`, with `core3R P V IR` replaced by `core3R P V IR` (Core 3.0 with
validity `V` and an internal step `IR` contained in `InternalP P`, `Core3R.Sub`). The other
declarations of that module are engine-generic and reused from it. Proofs are unchanged except
where a core step of the machine is read as an `InternalP P` step (through `Sub P IR`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Proofs.Wasm.Component.Reference

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy Payload sigN)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P V IR) σ}

/-! ## Sequences of resolved calls -/

section Seq

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P V IR)))} {B₀ : Machine.Config (E3 P V IR) σ}
  {fs : List (CFuncInst (core3R P V IR))}

/-- What a sequence of resolved linked calls shows from a configuration between calls. -/
def SeqFactsL (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (l : Linked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
    (s₀ u₀ : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P V IR))))
    (fs : List (CFuncInst (core3R P V IR))) (h₀ : σ) (u π : Store Nat) (k : Nat)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (rss : List (List Val)) (mₙ : Machine.Config (E3 P V IR) σ) : Prop :=
  ∃ (lr : List (CRound Ii.E Ii.F)) (dss : List (List (Round (sigN l.imp.imports.length))))
    (wss : List (List Silmaril.Wasm.Component.Val)) (cs' : (core3R P V IR).Store (CanonHost (core3R P V IR)))
    (ιe' ιi' : InstState) (G' : Garb P V IR σ) (ST' : List Subtask) (u' π' : Store Nat),
    Ii.Activation P u (cplay lr) u' ∧
    List.Forall₂ (fun r uc => ∃ j vs, IRRoundI l.imp Ii j vs r uc) lr
      (seqRoundsI l.imp calls dss wss) ∧
    ExpSeg P l Ie π ((seqRoundsI l.imp calls dss wss).flatMap (·.cs)) π' ∧
    rss = wss.map (·.map toRefVal) ∧ calls.length = dss.length ∧ calls.length = wss.length ∧
    mₙ = readyCfgL cs' ιe' ιi' fs G' ST' h₀ ∧
    ReadyL P V IR l Ie Ii s₀ u₀ F₀ cs' ιe' ιi' G' u' π' (k + calls.length)

/-- **Sequences of resolved linked calls** from a configuration between calls. -/
theorem seqL_inv [Fact (Sub P IR)] (S₀ : LStat P V IR l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOk l Ii s₀ fs) (h₀ : σ) :
    ∀ (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
      (cs : (core3R P V IR).Store (CanonHost (core3R P V IR))) (ιe ιi : InstState) (G : Garb P V IR σ)
      (ST : List Subtask) (u π : Store Nat) (k : Nat) (rss : List (List Val))
      (mₙ : Machine.Config (E3 P V IR) σ),
      ReadyL P V IR l Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k → SimpleI.TypedCalls l.imp calls →
      SeqCalls prof (linkHost impl) (readyCfgL cs ιe ιi fs G ST h₀) k (callArgsL l calls) rss
        mₙ →
      SeqFactsL P V IR l Ie Ii s₀ u₀ F₀ fs h₀ u π k calls rss mₙ
  | [], cs, ιe, ιi, G, ST, u, π, k, rss, mₙ, R, _, hS => by
    cases hS
    exact ⟨[], [], [], cs, ιe, ιi, G, ST, u, π, .nil _, .nil, .nil π, rfl, rfl, rfl, rfl, R⟩
  | (j, vs) :: calls, cs, ιe, ιi, G, ST, u, π, k, rss, mₙ, R, ht, hS => by
    cases hS with
    | cons hcall hS' =>
      have hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true := ht _ List.mem_cons_self
      obtain ⟨r, uc, q, hu, -, hpath, hobs, hnext⟩ := linkCallK S₀ hB₀ hfs R j hvs hcall
      obtain ⟨ws, rfl, hua⟩ : ∃ ws : List Silmaril.Wasm.Component.Val,
          _ = ws.map toRefVal ∧ uc.a = some (.vals ws) := hobs
      obtain ⟨cs₁, ιe₁, ιi₁, G₁, ST₁, u₁, π₁, rfl, hexp₁, rfl, R₁⟩ := hnext _ rfl
      obtain ⟨lr, dss, wss, cs', ιe', ιi', G', ST', u', π', hact, hrel, hexp, rfl, hl₁, hl₂, hm,
        R'⟩ := seqL_inv S₀ hB₀ hfs h₀ calls cs₁ ιe₁ ιi₁ G₁ ST₁ u₁ π₁ (k + 1) _ _ R₁
          (fun q hq => ht q (List.mem_cons_of_mem _ hq)) hS'
      have hk : k + 1 + calls.length = k + ((j, vs) :: calls).length := by
        simp only [List.length_cons]
        omega
      have hu' : uc = ⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), uc.cs, some (.vals ws)⟩ :=
        hu.eq hua
      refine ⟨r :: lr, uc.cs :: dss, ws :: wss, cs', ιe', ιi', G', ST', u', π', ?_,
        .cons ⟨j, vs, hu' ▸ hu⟩ hrel, ?_, rfl, by rw [List.length_cons, hl₁, List.length_cons],
        by rw [List.length_cons, hl₂, List.length_cons], hm, hk ▸ R'⟩
      · show Ii.Path P _ (cplay ([r] ++ lr)) _
        rw [cplay_append]
        exact path_append hpath hact
      · rw [show seqRoundsI l.imp ((j, vs) :: calls) (uc.cs :: dss) (ws :: wss) =
          ⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), uc.cs, some (.vals ws)⟩ ::
            seqRoundsI l.imp calls dss wss from rfl, List.flatMap_cons]
        exact hexp₁.append hexp

end Seq

/-! ## Assembly -/

section Assembly

variable {l : Linked2}

/-- The component functions of `afterLink` lift the importer's exports at the relocated
addresses of its instance. -/
theorem liftedOk_afterLink {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : l.imp.mod.IsInst Ii)
    (hIg : l.imp.Good)
    {Ie : Silmaril.Wasm.Game.ScalarInstance} {cse : (E3 P V IR).Store (CanonHost (E3 P V IR))}
    {cie : (E3 P V IR).Inst} (hFe : CoreFacts (Pf := P) (V := V) (IR := IR) l.exp Ie cse cie) :
    LiftedOk l Ii Ie.store (liftedList (Pf := P) (V := V) (IR := IR) (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
      liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) := by
  intro j
  obtain ⟨nm, hcore⟩ := hIg.core _ (List.getElem_mem j.isLt)
  have hk : l.imp.exports[j].core < l.imp.mod.exports.length :=
    (List.getElem?_eq_some_iff.mp hcore).1
  have hlen : l.imp.exports[j].core < Ii.addrs.length := by
    rw [hI.1.choose_spec.ok.addrs_length, hI.2.2, List.length_map]
    exact hk
  rw [afterLink_lifted, addrL_eq _ hlen, coreFacts_length hFe]

/-- **Soundness of two linked components for sequences of calls on one instance** (every
profile and component choice profile): under the hypotheses of `linked2_sound`, every behaviour
of instantiating `l.toRef`, calling the importer's exports `calls` in order (each resolving),
then export `j`, on reference images of well-typed IR values, under `linkHost impl` from any
host state, records reference images of IR results `wss`; the linked IR plays the resolved
calls with these results (both instances' states persisting between questions), and the last
outcome as `Linked2.SeqIRObs` prescribes. -/
theorem linked2_sound_seq (P : Profile) [Fact (Sub P IR)] (prof : ProfileKind) (l : Linked2) (hEg : l.exp.Good)
    (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst) (har : l.imp.Arity)
    (hff : l.imp.FloatFree) (hW : l.WireTy) (hN : l.NamesOk) (hn : l.WireNodup)
    (hS : l.SplitOk) {σ : Type} (impl : HostImpl (core3R P V IR) σ) (h₀ : σ)
    (calls : List (Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (ht : SimpleI.TypedCalls l.imp calls)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    (p : List (List Val) × Silmaril.Wasm.Component.Reference.Outcome)
    (hp : p ∈ seqBehaviours prof (linkHost impl) h₀ l.toRef
      (calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)) l.imp.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      Linked2.seqMoves l calls wss ∈ l.toComp.den (impSem P) ∧
      Linked2.SeqIRObs P l calls wss j vs p.2 := by
  obtain ⟨Ie, cse, cie, hFe, hall⟩ := instBehavioursL_inst (Pf := P) (V := V) (IR := IR) (σ := σ) hEg hEi hIg hIi har
    ⟨hS.imp.data, hS.imp.elems⟩ hW hN
  obtain ⟨Ii, hI⟩ := hIi.inst
  obtain ⟨r, hrs, hh, hres⟩ := hall Ii hI
  rcases hp with ⟨m₀, inst, es, fs, mₙ, f, hr, hfs, hSq, hl, hb⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  rotate_left
  · exact absurd (hres prof (linkHost impl) h₀ _ hr) (by simp)
  · exact absurd (hres prof (linkHost impl) h₀ _ hr) (by simp)
  have he : m₀ = afterLink P (reloc cse (Store.mapH Prod.fst r))
      (fun k => Ie.addrs.getD k 0) (addrL (cse : Store _).funcs.length Ii) l h₀ ∧
      inst = ⟨0⟩ ∧ es = exportMapL l := by
    simpa only [InstResult.instance.injEq] using hres prof (linkHost impl) h₀ _ hr
  have hfs' : fs = calls.map fun q => (⟨l.exp.exports.length + q.1⟩ : FuncId) :=
    Option.some.inj (hfs.symm.trans (he.2.2 ▸ mapM_lookupL hIg calls))
  have hf' : f = ⟨l.exp.exports.length + j⟩ :=
    Option.some.inj (hl.symm.trans (he.2.2 ▸ exportMapL_lookup hIg j))
  have hSq₁ : SeqCalls prof (linkHost impl) (readyCfgL (σ := σ)
      (reloc (cse : Store (CanonHost (E3 P V IR))) (Store.mapH Prod.fst r)) {} {}
        (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
          liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) Garb.empty [] h₀)
      0 (callArgsL l calls) p.1 mₙ := by
    have hS₀ : SeqCalls prof (linkHost impl) (afterLink P (reloc cse (Store.mapH Prod.fst r))
        (fun k => Ie.addrs.getD k 0) (addrL (cse : Store _).funcs.length Ii) l h₀) 0
        (fs.zip ((calls.map fun q => (l.imp.exports[q.1].name, q.2.map toRefVal)).map
          Prod.snd)) p.1 mₙ := he.1 ▸ hSq
    rw [← zip_callArgsL, ← hfs']
    exact hS₀
  -- the static facts and the invariant after instantiation
  have S₀ : LStat P V IR l Ie Ii Ii.store
      (reloc (cse : Store (CanonHost (E3 P V IR))) (Store.mapH Prod.fst r)).funcs
      (readyCfgL (σ := σ) (reloc (cse : Store (CanonHost (E3 P V IR))) (Store.mapH Prod.fst r)) {} {}
        (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
          liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) Garb.empty [] h₀)
      (ownOf Ie.store) :=
    lstat_init hEg hIg hW hn har hff hFe hI hh _ rfl
  have hg₀ : StoreGood Ie.store := storeGood_inst hS.exp hFe.isInst.1.choose_spec
  have hgu : StoreGood Ii.store := storeGood_inst hS.imp hI.1.choose_spec
  have R₀ : ReadyL P V IR l Ie Ii Ie.store Ii.store
      (reloc (cse : Store (CanonHost (E3 P V IR))) (Store.mapH Prod.fst r)).funcs
      (reloc (cse : Store (CanonHost (E3 P V IR))) (Store.mapH Prod.fst r)) {} {}
      (Garb.empty : Garb P V IR σ) Ii.store Ie.store 0 :=
    { inv := lready_init hg₀ hgu (linkStore_mapH hn hW hFe hrs hh) rfl
        hFe.isInst.1.choose_spec.ok hI.1.choose_spec.ok
      thE := threadsOk_empty
      thI := threadsOk_empty
      leave := rfl
      fresh := { pending := (fun _ h => nomatch h), results := (fun _ h => nomatch h) } }
  have hok : LiftedOk l Ii Ie.store (liftedList (Pf := P) (V := V) (IR := IR) (fun k => Ie.addrs.getD k 0) ⟨1⟩
      l.exp.exports ++ liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) :=
    liftedOk_afterLink hI hIg hFe
  obtain ⟨lr, dss, wss, cs', ιe', ιi', G', ST', u', π', hact, hrel, hexp, hrss, hl₁, hl₂, hmₙ,
    R'⟩ := seqL_inv S₀ rfl hok h₀ calls _ _ _ _ _ _ _ 0 _ _ R₀ ht hSq₁
  have hb' : p.2 ∈ callBehaviours prof (linkHost impl) (readyCfgL cs' ιe' ιi'
      (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
        liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) G' ST' h₀)
      ⟨0 + calls.length⟩ ⟨l.exp.exports.length + j⟩ (vs.map toRefVal) := by
    have hmₙ' : mₙ = readyCfgL cs' ιe' ιi'
        (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
          liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) G' ST' h₀ := hmₙ
    rw [← hmₙ', ← hf', Nat.zero_add, ← List.length_map
      (f := fun q : Fin l.imp.exports.length × List Silmaril.Wasm.Component.Val =>
        (l.imp.exports[q.1].name, q.2.map toRefVal))]
    exact hb
  have hrun : Linked2.ExpRun P l Ie Ie.store
      ((seqRoundsI l.imp calls dss wss).flatMap (·.cs)) := by
    simpa only [List.append_nil] using hexp.run (.nil π')
  have hpre : Linked2.seqMoves l calls wss ∈ l.toComp.den (impSem P) := by
    rw [← cplay_seqRoundsL l calls dss wss hl₁ hl₂]
    exact linked_seq_den hEg hIg hFe.isInst hI hrel (cplay_mem_strategy hact) hrun
  refine ⟨wss, hrss, hpre, ?_⟩
  rcases hb' with ⟨m', out, hcalls, hpo⟩ | ⟨hd, -⟩
  · show Linked2.SeqIRObs P l calls wss j vs p.2
    obtain ⟨r₁, uc, q, hu, hrun₁, hpath, hobs, -⟩ := linkCallK S₀ rfl hok R' j hvs hcalls
    have hall : Ii.Path P (.idle Ii.store) (cplay (lr ++ [r₁])) q := by
      rw [cplay_append]
      exact path_append hact hpath
    have hrun' : Linked2.ExpRun P l Ie Ie.store
        ((seqRoundsI l.imp calls dss wss ++ [uc]).flatMap (·.cs)) := by
      rw [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact hexp.run hrun₁
    have hden : cplay ((seqRoundsI l.imp calls dss wss ++ [uc]).map (Linked2.linkRound l)) ∈
        l.toComp.den (impSem P) :=
      linked_seq_den hEg hIg hFe.isInst hI (forall₂_append hrel (.cons ⟨j, vs, hu⟩ .nil))
        (cplay_mem_strategy hall) hrun'
    rw [hpo]
    exact seqIRObsL_of hl₁ hl₂ hu _ (hpo ▸ hobs) hden
  · rw [hd]
    trivial

end Assembly

end Silmaril.Proofs.Wasm.Component.Param.Core3R
