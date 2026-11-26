module

import Silmaril.Wasm.Component.Reference.SyncImportRun.Thms
import Silmaril.Wasm.Component.Reference.SyncImportRun.Fixture.Thms
import Silmaril.Wasm.Component.Reference.Litmus.Thms
import Silmaril.Wasm.Abstract.BodyTrace.Thms

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Elgot
open Silmaril.Wasm.Game
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Component.SyncImportITree
open Silmaril.Wasm.Component.Reference.SyncImportRun.Fixture
open Silmaril.Wasm.Execution.Core (Val Result vals)
open Silmaril.Wasm.SingleThreaded (decompose? decompose?_top resumeResult neverFail hostArity?)

namespace SyncImportITreeRegression

private def ready : Ready fwdS where
  good := fwdS_good
  arity := by simp [SimpleI.Arity, fwdS, Silmaril.Wasm.Component.ValTy.flatList,
    Silmaril.Wasm.Component.ValTy.flat]
  floatFree := by simp [SimpleI.FloatFree, fwdS, floatFreeList, floatFree]
  inst := fwdInst
  isInst := fwd_isInst

private def question : Question (exportIface fwdS) := ⟨⟨0, by decide⟩, ⟨[.u32 3], rfl⟩⟩
private def request : Question fwdS.imports := ⟨⟨0, by decide⟩, ⟨[.u32 3], rfl⟩⟩

private def coreArg : Typed [.num (.int .i32)] :=
  ⟨[Val.i32 3], .cons ⟨3, rfl⟩ .nil⟩

private def exportOp : fwdInst.F.Op := ⟨⟨0, by decide⟩, coreArg⟩
private def importOp : fwdInst.E.Op := ⟨⟨0, by decide⟩, coreArg⟩
private def start : Cursor := (fwdStore, fwdInst.initThread exportOp)

private theorem entry_eq : entry ready question = some exportOp := by
  change ifaceOp? fwdInst.exports 0 [Val.i32 3] = some exportOp
  unfold ifaceOp?
  exact (dite_eq_left (show 0 < fwdInst.exports.length by decide)).trans (dite_eq_left coreArg.2)

private theorem decomposes :
    decompose? fwdStore (start.2.config fwdStore).code =
      some (.top [] [], 0, 0, [Val.i32 3]) := by
  have arity : hostArity? fwdStore 0 = some (0, 1) := by decide +kernel
  change decompose? fwdStore
    (vals ([Val.i32 3] ++ [.ref (.func 0)]) ++
      [.callRefType ((fwdStore.funcs[0]?.map Silmaril.Wasm.Execution.Core.FuncInst.type).getD default)]) = _
  rw [decompose?_top (pre := [Val.i32 3]) (n := 1) (by rfl) arity (Nat.le_refl 1)]
  rfl

private theorem import_eq : fwdInst.importOp? 0 [Val.i32 3] = some importOp := by
  unfold ScalarInstance.importOp? ifaceOp?
  exact (dite_eq_left (show 0 < fwdInst.imports.length by decide)).trans (dite_eq_left coreArg.2)

private noncomputable def resume (a : request.Answer) : Cursor :=
  (fwdStore, resumeResult fwdStore start.2
    (payloadAnswer (fwdInst.imports.get importOp.1)
      ((a.map (fun v => Silmaril.Wasm.Component.Payload.vals v.val)).bind
        (Silmaril.Wasm.Component.Adapter.lower fwdS.imports[request.index].2).up)).toResult)

private theorem reaches_request :
    ReachesFront neverFail ready question exportOp start (.request request resume) := by
  refine .inl ⟨.request importOp start, .ucall .refl ⟨_, _, decomposes⟩ import_eq, ?_⟩
  rfl

private def importReply (y : BitVec 32) : request.Answer := some ⟨[.u32 y], rfl⟩
private def exportReply (y : BitVec 32) : question.Answer := some ⟨[.u32 y], rfl⟩

private theorem resumes_value (y : BitVec 32) :
    resume (importReply y) = (fwdStore, .active {} (vals [Val.i32 y])) := by
  have typed : List.Forall₂ ScalarType.HasVal [.num (.int .i32)] [Val.i32 y] :=
    .cons ⟨y, rfl⟩ .nil
  have answer :
      payloadAnswer (fwdInst.imports.get importOp.1)
        (some (.flat [Silmaril.Wasm.Component.Flat.i32 y])) =
          .values ⟨[Val.i32 y], typed⟩ := by
    have h : List.Forall₂ ScalarType.HasVal (fwdInst.imports.get importOp.1).results
        ([Silmaril.Wasm.Component.Flat.i32 y].map Silmaril.Wasm.SingleThreaded.ofFlat) := typed
    simp only [payloadAnswer, typed?, dite_eq_left h]
    rfl
  change (fwdStore, resumeResult fwdStore start.2
    (payloadAnswer (fwdInst.imports.get importOp.1) (some (.flat [.i32 y]))).toResult) = _
  rw [answer]
  simp only [resumeResult, decomposes]
  rfl

private theorem reaches_reply (y : BitVec 32) :
    ReachesFront neverFail ready question exportOp (resume (importReply y))
      (.reply (exportReply y) fwdStore) := by
  rw [resumes_value]
  let core : fwdInst.F.Ar exportOp := .values ⟨[Val.i32 y], .cons ⟨y, rfl⟩ .nil⟩
  refine .inl ⟨.reply core fwdStore, .oret .refl (r := core.toResult) rfl
      (Answer.ofResult?_toResult core), ?_⟩
  rfl

private theorem reaches_trap :
    ReachesFront neverFail ready question exportOp (resume none) (.reply none fwdStore) := by
  have hr : resume none = (fwdStore, .active {} [.trap]) := by
    change (fwdStore, resumeResult fwdStore start.2 Result.trap) = _
    simp only [resumeResult, decomposes]
    rfl
  rw [hr]
  exact .inl ⟨.reply .trap fwdStore, .oret .refl (r := .trap) rfl rfl, rfl⟩

-- This is the actual visible suspension before the host has supplied a reply.
example : Sees ((body neverFail ready question).run ⟨fwdStore⟩).run [] (.pending request) :=
  (body_sees_iff entry_eq).mpr (.pending reaches_request)

-- The same suspended export accepts both replies and retains its Core store.
private theorem replies (y : BitVec 32) :
    Sees ((body neverFail ready question).run ⟨fwdStore⟩).run
      [⟨request, importReply y⟩] (.reply (exportReply y) fwdStore) :=
  (body_sees_iff entry_eq).mpr (.answer _ reaches_request (.reply (reaches_reply y)))

-- A supplied trap reply finishes the activation. Merely waiting is visible
-- without that reply and does not yield silent divergence.
example : Sees ((body neverFail ready question).run ⟨fwdStore⟩).run
    [⟨request, none⟩] (.reply none fwdStore) :=
  (body_sees_iff entry_eq).mpr (.answer _ reaches_request (.reply reaches_trap))

example : ¬ Sees ((body neverFail ready question).run ⟨fwdStore⟩).run [] .quiet := by
  simp only [body, StateT.run, ExceptT.run, entry_eq]
  change ¬ Sees (tree neverFail ready question exportOp start) [] .quiet
  rw [tree_request reaches_request]
  intro h
  obtain ⟨_, _, eq, _⟩ := Silmaril.Wasm.Abstract.BodyTrace.path_vis_inv h
  cases eq

-- Compare the abstract responses with the stock reference component litmus.
-- Both hosted executions invoke the same component export with input 3.
example :
    Sees ((body neverFail ready question).run ⟨fwdStore⟩).run
      [⟨request, importReply 4⟩] (.reply (exportReply 4) fwdStore) ∧
    Outcome.returns (some [toRefVal (.u32 4)]) ∈
      exportBehavioursI Core3Adder.first.prof (Host.ofEmbedder embI) () fwdS.toRef fwdS.imports "f"
        [toRefVal (.u32 3)] :=
  ⟨replies 4, fwd_ref⟩

example :
    Sees ((body neverFail ready question).run ⟨fwdStore⟩).run
      [⟨request, importReply 13⟩] (.reply (exportReply 13) fwdStore) ∧
    ([[toRefVal (.u32 13)]], Outcome.returns (some [toRefVal (.u32 14)])) ∈
      seqBehavioursI Core3Adder.first.prof (Host.ofEmbedder embC) 10 fwdS.toRef fwdS.imports
        [("f", [toRefVal (.u32 3)])] "f" [toRefVal (.u32 3)] :=
  ⟨replies 13, fwd_seq_refS⟩

open Silmaril.Wasm.Component (Calls Instantiates) in
open Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime in
open Silmaril.Wasm.SingleThreaded (profile) in
open Silmaril.Proofs.Wasm.Component.Reference (Store.mapH) in
-- The independently constructed tree path becomes a stock call when the
-- counter host admits its reply.
example {booted : Config (core3P (profile neverFail)) Nat}
    {exports : List (String × FuncId)} {f : FuncId}
    (init : let h := answerHostS (profile neverFail) fwdC
      Instantiates .deterministic h.hr h.dispatch
        (Config.init (hostFuncs 0 fwdS.imports CStore.empty) 10)
        fwdS.toRef (importArgs fwdS.imports) booted ⟨0⟩ exports)
    (lookup : exports.lookup "f" = some f) :
    let h := answerHostS (profile neverFail) fwdC
    ∃ finished,
      Calls .deterministic h.hr h.dispatch booted ⟨0⟩ f [toRefVal (.u32 3)] finished
        (.resolved (some [toRefVal (.u32 13)])) ∧
      finished.host = 11 ∧ Store.mapH trampIdx finished.store.core = fwdStore := by
  have admitted : HostReplies (c := fwdS) fwdC 10 [⟨request, importReply 13⟩] 11 :=
    .cons rfl (.nil 11)
  exact (reference_return_iff_sees (o := neverFail) ready fwdS_inst question fwdC_ok init lookup).mpr
    ⟨_, _, rfl, admitted, replies 13⟩

end SyncImportITreeRegression
