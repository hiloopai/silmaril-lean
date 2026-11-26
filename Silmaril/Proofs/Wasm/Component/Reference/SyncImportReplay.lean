module

public import Silmaril.Wasm.Component.Reference.SyncImportRun.Defs
public import Silmaril.Wasm.Component.Reference.SyncImportCut.Thms
import Silmaril.Proofs.Wasm.Component.Reference.SyncImportRun
import Silmaril.Proofs.Wasm.Component.Reference.SoundI
import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.RefRun

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.SyncImportReplay

open Silmaril.Games.Abstract (Call)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.SyncImportITree
open Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Component.Runtime hiding Thread
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store Result FuncInst)
open Silmaril.Wasm.SingleThreaded (GrowOracle Thread profile ofFlat toFlat? resumeResult)
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Core3G (statusP_of_values toFlat?_isSome)

local notation "P[" o "]" => profile o
local notation "E[" o "]" => core3P (profile o)

variable {c : SimpleI} {o : GrowOracle} {r : Ready c} {q : Question (exportIface c)}
  {op : r.inst.F.Op} {σ : Type} {prof : ProfileKind}
  {g : σ → HostFuncId → List Reference.Val → Option (List Reference.Val × σ)}

-- The decoder preserves the import index even outside the interface. Actual
-- callouts carry a bounded, typed import operation.
private noncomputable def trampoline (c : SimpleI) (o : GrowOracle) (k : Nat) : CanonHost E[o] :=
  .lowered ⟨k⟩ (witFt (((c.imports[k]?).map Prod.snd).getD ⟨[], []⟩)) {} ⟨0⟩

private theorem trampoline_at (i : Fin c.imports.length) :
    trampoline c o i.val = .lowered ⟨i.val⟩ (witFt c.imports[i].2) {} ⟨0⟩ := by
  simp only [trampoline, List.getElem?_eq_getElem i.isLt, Option.map_some, Option.getD_some]
  rfl

private theorem encode_decode (s : Store Nat) :
    Store.mapH trampIdx (Store.mapH (trampoline c o) s) = s := by
  have funcs : (s.funcs.map (FuncInst.mapH (trampoline c o))).map (FuncInst.mapH trampIdx) =
      s.funcs := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id s.funcs]
    apply List.map_congr_left
    rintro ⟨ty, mo, code⟩ _
    cases code <;> rfl
  cases s
  simp only [Store.mapH] at funcs ⊢
  rw [funcs]

private theorem decode_encode {s : Store (CanonHost E[o])} (ok : c.TrampOk s) :
    Store.mapH (trampoline c o) (Store.mapH trampIdx s) = s := by
  have funcs : (s.funcs.map (FuncInst.mapH trampIdx)).map (FuncInst.mapH (trampoline c o)) =
      s.funcs := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id s.funcs]
    apply List.map_congr_left
    rintro ⟨ty, mo, code⟩ mem
    cases code with
    | wasm fn => rfl
    | host h =>
      obtain ⟨addr, found⟩ := List.mem_iff_getElem?.mp mem
      obtain ⟨i, bound, rfl⟩ := ok addr _ h found rfl
      have eq := trampoline_at (o := o) (⟨i, bound⟩ : Fin c.imports.length)
      change FuncInst.mk ty mo (.host (trampoline c o i)) = _
      rw [eq]
      rfl
  cases s
  simp only [Store.mapH] at funcs ⊢
  rw [funcs]

private noncomputable def decode (c : SimpleI) (o : GrowOracle) (x : Cursor) : CoreSt E[o] :=
  (Store.mapH (trampoline c o) x.1, x.2)

private theorem request_cut {x : Cursor} {m : Question c.imports} {k : m.Answer → Cursor}
    (front : ReachesFront o r q op x (.request m k)) :
    ∃ (e : r.inst.E.Op) (p : Cursor), ReachesCut o r.inst op x (.request e p) ∧
      e.1.val = m.index.val ∧
      liftArgs c.imports[m.index].2.params (e.2.val.filterMap toFlat?) = some m.args.val ∧
      ∀ a : Values c.imports[m.index].2.results,
        decode c o (k (some a)) =
          ((decode c o p).1, (E[o]).resume (decode c o p).1 p.2
            (.values (lowerArgs c.imports[m.index].2.results a.val))) := by
  rcases front with ⟨cut, reached, eq⟩ | ⟨_, eq⟩
  · cases cut with
    | reply b s => cases eq
    | request e p =>
      have frontEq := eq
      simp only [cutFront] at eq
      split at eq
      next bound =>
        let i : Fin c.imports.length := ⟨e.1.val, bound⟩
        cases lift : liftArgs c.imports[i].2.params (e.2.val.filterMap toFlat?) with
        | none =>
          rw [show liftValues c.imports[i].2.params (e.2.val.filterMap toFlat?) = none from
            Option.pmap_none' lift] at eq
          cases eq
        | some ws =>
          let args : Values c.imports[i].2.params := ⟨ws, checkList_of_liftArgs lift⟩
          rw [show liftValues c.imports[i].2.params (e.2.val.filterMap toFlat?) = some args from
            Option.pmap_some' lift] at eq
          obtain ⟨rfl, _⟩ := Front.request.inj eq
          have canonical := cutFront_request (r := r) (q := q) (f := op)
            (p := p) (e := e) (⟨i, args⟩ : Question c.imports) rfl lift
          have kEq := eq_of_heq (Front.request.inj (frontEq.symm.trans canonical)).2
          subst k
          refine ⟨e, p, reached, rfl, lift, fun a => ?_⟩
          unfold decode
          rw [resume_values]
          have resumed := resumeResult_mapH trampIdx (Store.mapH (trampoline c o) p.1) p.2
            (.values ((lowerArgs c.imports[i].2.results a.val).map ofFlat))
          rw [encode_decode (c := c) (o := o)] at resumed
          exact congrArg (fun t => (Store.mapH (trampoline c o) p.1, t)) resumed
      next => cases eq
  · cases eq

private theorem translated_callout {x p : Cursor} {m : Question c.imports} {e : r.inst.E.Op}
    (cut : ReachesCut o r.inst op x (.request e p))
    (idx : e.1.val = m.index.val)
    (lift : liftArgs c.imports[m.index].2.params (e.2.val.filterMap toFlat?) = some m.args.val) :
    ∃ ys : List Flat,
      Reach P[o] x p ∧
      (E[o]).status (decode c o p).1 p.2 =
        .callout (.lowered ⟨m.index.val⟩ (witFt c.imports[m.index].2) {} ⟨0⟩) ys ∧
      ys.map (·.type) = ValTy.flatList c.imports[m.index].2.params ∧
      liftArgs c.imports[m.index].2.params ys = some m.args.val := by
  obtain ⟨xs, t⟩ := x
  obtain ⟨ps, u⟩ := p
  unfold ReachesCut at cut
  cases cut with
  | @ucall _ _ _ _ _ h args _ reach here imported =>
    obtain ⟨importIdx, importArgsEq⟩ := ifaceOp?_some imported
    have typed : List.Forall₂ ScalarType.HasVal (r.inst.imports.get e.1).params args :=
      importArgsEq ▸ e.2.property
    rw [imports_get r.good r.isInst e m.index.val m.index.isLt idx] at typed
    obtain ⟨ys, flat⟩ := toFlat?_isSome typed
    have gameStatus := (calloutAt_iff_status (P := P[o])).mp here
    obtain ⟨ctx, addr, decomp⟩ := here
    obtain ⟨ctx', mapped⟩ := decompose?_mapH (trampoline c o) decomp
    have status : statusP P[o] (Store.mapH (trampoline c o) ps) u =
        .callout (trampoline c o h) args := by
      unfold statusP at gameStatus ⊢
      dsimp only at gameStatus ⊢
      rw [config_code_mapH' (trampoline c o) ps u, mapped]
      rw [decomp] at gameStatus
      split_ifs at gameStatus ⊢ <;> rfl
    refine ⟨ys, reach, ?_, toFlat?_types _ _ _ typed flat, ?_⟩
    · change flatStatus (statusP P[o] (Store.mapH (trampoline c o) ps) u) = _
      rw [status, ← importIdx, idx, trampoline_at m.index]
      simp only [flatStatus, flat]
    · rwa [importArgsEq, filterMap_of_mapM flat] at lift

private theorem translated_return {x : Cursor} {store : Store Nat}
    {a : Values (exportIface c)[q.index].2.results} {exp : SimpleExport}
    (exportEq : (exportIface c)[q.index].2 = exp.ty)
    (exportTy : r.inst.exports.get op.1 = fnOf exp.ty.flat)
    (front : ReachesFront o r q op x (.reply (some a) store)) :
    ∃ (t : Thread) (ys : List Flat),
      Reach P[o] x (store, t) ∧
      (E[o]).status (Store.mapH (trampoline c o) store) t = .returned (.values ys) ∧
      ys.map (·.type) = ValTy.flatList exp.ty.results ∧
      liftArgs exp.ty.results ys = some a.val := by
  rcases front with ⟨cut, reached, eq⟩ | ⟨_, eq⟩
  · cases cut with
    | request e p =>
      simp only [cutFront] at eq
      split at eq <;> try cases eq
      split at eq <;> cases eq
    | reply w s =>
      have sameStore : s = store := (Front.reply.inj eq).2
      subst s
      unfold ReachesCut at reached
      cases reached with
      | @oret _ _ _ _ t result _ reach final answer =>
        have payload := answerPayload_of_ofResult? answer
        cases result with
        | trap | throw _ =>
          simp [cutFront, payload] at eq
        | values vs =>
          have typed : List.Forall₂ ScalarType.HasVal (r.inst.exports.get op.1).results vs := by
            unfold Answer.ofResult? at answer
            dsimp only at answer
            split_ifs at answer with valid
            exact valid
          rw [exportTy] at typed
          obtain ⟨ys, flat⟩ := toFlat?_isSome typed
          refine ⟨t, ys, reach, ?_, toFlat?_types _ _ _ typed flat, ?_⟩
          · change flatStatus (statusP P[o] (Store.mapH (trampoline c o) store) t) = _
            rw [statusP_of_values ((config_code_mapH' _ _ _).trans final)]
            simp only [flatStatus, flat]
          · simp only [cutFront, payload, flat, Option.map_some, Option.bind_some] at eq
            have sameAnswer := (Front.reply.inj eq).1
            rw [← exportEq]
            cases lifted : liftArgs (exportIface c)[q.index].2.results ys with
            | none =>
              rw [liftValues, Option.pmap_none' lifted] at sameAnswer
              cases sameAnswer
            | some ws =>
              rw [liftValues, Option.pmap_some' lifted] at sameAnswer
              exact congrArg (fun z : Values (exportIface c)[q.index].2.results => some z.val)
                (Option.some.inj sameAnswer)
  · cases eq

-- The dispatcher keeps the entry frame through each answered lower and
-- extends its subtask and caller records. Carry those records to the lift.
private theorem replay_to_return {exp : SimpleExport} {B : Config E[o] σ}
    {th : Option ThreadId} {K : List Flat → Canon.P E[o] σ (Canon.Ret E[o])}
    {segs : List (Seg E[o] σ)} {rest : List (Activation E[o] σ)}
    (frame : FrameOk (I := r.inst) c B.store th) (unlocked : B.store.lockdown = false)
    (typedHost : c.HostOkS g) (exportEq : (exportIface c)[q.index].2 = exp.ty)
    (exportTy : r.inst.exports.get op.1 = fnOf exp.ty.flat)
    {s s' : σ} {x : Cursor} {ST : List Subtask} {CL : List (Caller E[o])}
    {a : Values (exportIface c)[q.index].2.results} {store : Store Nat}
    {cs : List (Call (signature c.imports))}
    (replies : HostReplies (c := c) g s cs s')
    (seen : Observes o r q op x cs (.reply (some a) store)) :
    let host := answerHostS P[o] g
    ∃ tr ST' CL', ∃ (t : Thread) (ys : List Flat),
      Steps prof host.hr host.dispatch (coreCfg (extSC (withH B s) ST CL) th K segs rest (decode c o x))
        tr (coreCfg (extSC (withH B s') ST' CL') th K segs rest (decode c o (store, t))) ∧
      (∀ ev, Label.host ev ∉ tr) ∧
      (E[o]).status (Store.mapH (trampoline c o) store) t = .returned (.values ys) ∧
      ys.map (·.type) = ValTy.flatList exp.ty.results ∧ liftArgs exp.ty.results ys = some a.val := by
  induction replies generalizing x ST CL with
  | nil =>
    cases seen with
    | reply front =>
      obtain ⟨t, ys, reach, status, types, lift⟩ := translated_return exportEq exportTy front
      obtain ⟨tr, labels, run⟩ := coreCfg_steps_of (coreSteps_of_reach (trampoline c o) reach)
        (prof := prof) (hr := (answerHostS P[o] g).hr) (dispatch := DA P[o] g)
        (B := extSC (withH B _) ST CL) (th := th) (K := K) (segs := segs) (rest := rest)
      have noHost : ∀ ev, Label.host ev ∉ tr := by
        intro ev member
        cases labels _ member
      exact ⟨tr, ST, CL, t, ys, run, noHost, status, types, lift⟩
  | @cons s s₁ s' m b cs answer _ ih =>
    cases seen with
    | answer _ front tail =>
      obtain ⟨e, p, cut, index, lifted, resumes⟩ := request_cut front
      obtain ⟨ys, reach, status, types, args⟩ := translated_callout cut index lifted
      obtain ⟨pre, labels, run⟩ := coreCfg_steps_of (coreSteps_of_reach (trampoline c o) reach)
        (prof := prof) (hr := (answerHostS P[o] g).hr) (dispatch := DA P[o] g)
        (B := extSC (withH B s) ST CL) (th := th) (K := K) (segs := segs) (rest := rest)
      obtain ⟨st, found, leave⟩ := frame.inst
      let L : LowerSite P[o] := ⟨⟨m.index.val⟩, ⟨0⟩, st, witFt c.imports[m.index].2,
        ⟨m.index.val⟩, c.imports[m.index].2⟩
      have mem := List.getElem_mem (l := c.imports) m.index.isLt
      obtain ⟨pff, rff⟩ := r.floatFree.2 _ mem
      obtain ⟨maxp, maxr, res⟩ := r.arity.2 _ mem
      have ok : L.Ok g (withH B s).store th ys :=
        { entry := frame.entry _ _ _
          inst := found
          leave := leave
          func := by
            change B.store.funcs[m.index.val]? = _
            rw [frame.funcs, afterFuncs_host _ m.index.isLt]
            rfl
          pff := pff
          rff := rff
          typed := types
          maxp := maxp
          res := res
          maxr := maxr
          answers := fun s ws rs s' h => typedHost s m.index.val m.index.isLt ws rs s' h }
      have answered : L.Answers g s ys (lowerArgs c.imports[m.index].2.results b.val) s₁ :=
        ⟨m.args.val, b.val, args, answer, b.property, rfl⟩
      obtain ⟨ST₁, CL₁, middle, served⟩ :=
        callout_lrun (prof := prof) (B := withH B s) (ST := ST) (CL := CL)
          (K := K) (segs := segs) (rest := rest) unlocked status ok answered
      obtain ⟨post, ST', CL', t, flats, later, noHost, returned, resultTypes, resultLift⟩ :=
        ih (ST := ST₁) (CL := CL₁) tail
      rw [resumes b] at later
      refine ⟨_, ST', CL', t, flats, steps_append run (steps_append served.steps later),
        ?_, returned, resultTypes, resultLift⟩
      intro ev mem
      rcases List.mem_append.mp mem with mem | mem
      · cases labels _ mem
      rcases List.mem_append.mp mem with mem | mem
      · exact Adequacy.LRun.no_host served ev mem
      · exact noHost ev mem

theorem reference_return_of_sees (r : Ready c) (wired : c.Inst)
    (q : Question (exportIface c)) (typedHost : c.HostOkS g)
    {s₀ s' : σ} {ready : Config E[o] σ}
    {inst : InstId} {exports : List (String × FuncId)} {f : FuncId}
    {a : Values (exportIface c)[q.index].2.results} {store : Store Nat}
    {cs : List (Call (signature c.imports))}
    (init : let h := answerHostS P[o] g
      Instantiates prof h.hr h.dispatch (Config.init (hostFuncs 0 c.imports CStore.empty) s₀)
        c.toRef (importArgs c.imports) ready inst exports)
    (lookup : exports.lookup (exportIface c)[q.index].1 = some f)
    (replies : HostReplies (c := c) g s₀ cs s')
    (seen : Sees ((body o r q).run ⟨r.inst.store⟩).run cs (.reply (some a) store)) :
    let h := answerHostS P[o] g
    ∃ finished, Calls prof h.hr h.dispatch ready ⟨0⟩ f (q.args.val.map toRefVal) finished
        (.resolved (some (a.val.map toRefVal))) ∧
      finished.host = s' ∧ Store.mapH trampIdx finished.store.core = store := by
  obtain ⟨I, shared, hI, mapped, tramp, instantiated⟩ :=
    instPhaseIS P[o] prof c r.good wired r.arity
  have same : I = r.inst := ImpModule.IsInst.unique hI r.isInst
  subst I
  have initialized := instantiated σ (answerHostS P[o] g) s₀ (.instance ready inst exports) init
  obtain ⟨rfl, rfl, rfl⟩ := InstResult.instance.inj initialized
  let j : Fin c.exports.length := Fin.cast (by simp [exportIface]) q.index
  let exp := c.exports[j]
  have exportEq : (exportIface c)[q.index] = (exp.name, exp.ty) := List.getElem_map ..
  have argsTyped : ValTy.checkList exp.ty.params q.args.val = true := by
    simpa only [exportEq] using q.args.property
  have hf : f = ⟨c.imports.length + j.val⟩ :=
    Option.some.inj ((exportEq ▸ lookup).symm.trans (exportMapI_lookup r.good j j.isLt))
  subst f
  obtain ⟨op, entryEq⟩ := entry_exists r q
  have entryCore : ifaceOp? r.inst.exports exp.core
      ((lowerArgs exp.ty.params q.args.val).map ofFlat) = some op := by
    unfold entry at entryEq
    simpa only [exportEq] using entryEq
  obtain ⟨opIdx, opArgs⟩ := ifaceOp?_some entryCore
  let addr := r.inst.addrs.getD exp.core 0
  have threadEq : r.inst.initThread op = Thread.invokeFlat addr (lowerArgs exp.ty.params q.args.val) := by
    change Thread.pending (r.inst.addrs.getD op.1.val 0) op.2.1 = _
    rw [opIdx, opArgs]
    rfl
  have mem : exp ∈ c.exports := List.getElem_mem j.isLt
  obtain ⟨name, flat⟩ := r.good.core exp mem
  have flatTy : r.inst.exports.get op.1 = fnOf exp.ty.flat := by
    have eq : r.inst.exports[op.1.val]? = some (fnOf exp.ty.flat) := by
      rw [opIdx, r.isInst.2.2, List.getElem?_map, flat]
      rfl
    exact Option.some.inj ((List.getElem?_eq_getElem op.1.isLt).symm.trans eq)
  obtain ⟨maxParams, maxResult, oneResult⟩ := r.arity.1 _ mem
  obtain ⟨paramsFloatFree, resultFloatFree⟩ := r.floatFree.1 _ mem
  obtain ⟨M, th, K, segs, rest, pre, start, active, initialHost⟩ := call_atA (g := g) prof shared
    (c.afterFuncs P[o] fun i => r.inst.addrs.getD i 0) s₀ (c.imports.length + j.val) addr exp
    q.args.val paramsFloatFree argsTyped maxParams oneResult maxResult resultFloatFree
    (afterFuncs_lifted _ j.isLt)
  have decoded : decode c o (r.inst.store, r.inst.initThread op) =
      (shared, Thread.invokeFlat addr (lowerArgs exp.ty.params q.args.val)) := by
    change (Store.mapH (trampoline c o) r.inst.store, r.inst.initThread op) = _
    rw [← mapped, decode_encode (o := o) tramp, threadEq]
    rfl
  obtain ⟨middle, ST, CL, t, ys, replay, noHost, status, types, lift⟩ :=
    replay_to_return (prof := prof) (B := M) (th := th) (K := K) (segs := segs) (rest := rest)
      ⟨active.funcs, active.entry, active.inst⟩ active.lock typedHost (congrArg Prod.snd exportEq)
      flatTy (ST := []) (CL := []) replies ((body_sees_iff entryEq).mp seen)
  rw [decoded, ← initialHost] at replay
  erw [← coreCfg_start active] at replay
  have returned : Step prof (answerHostS P[o] g).hr (DA P[o] g)
      (coreCfg (extSC (withH M s') ST CL) th K segs rest (decode c o (store, t))) .tau
      (retCfg (extSC (withH M s') ST CL) th K segs rest (decode c o (store, t)) ys) :=
    .coreReturned rfl status
  obtain ⟨post, finished, tail, ctl, lock, result, core, host, _⟩ :=
    active.ret s' ST CL (decode c o (store, t)) ys a.val types lift
  refine ⟨finished, ⟨(pre ++ middle) ++ (.tau :: post), ?_, ?_,
    fun bad => CallOutcome.noConfusion bad, ctl, lock, result⟩, host, ?_⟩
  · exact .cons (.hostInvoke ⟨rfl, rfl, rfl⟩ (by simp [afterInstH, Config.init]))
      (steps_append (steps_append start.steps replay) (.cons returned tail.steps))
  · intro ev member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · exact (Adequacy.LRun.no_host start ev member).elim
      · exact (noHost ev member).elim
    · exact (Adequacy.LRun.no_host tail ev ((List.mem_cons.mp member).resolve_left (by simp))).elim
  · change Store.mapH trampIdx finished.store.core = store
    rw [core]
    exact encode_decode (c := c) (o := o) store

theorem reference_return_iff_sees {c : SimpleI} (r : Ready c) (wired : c.Inst)
    (q : Question (exportIface c)) {o : GrowOracle} {prof : ProfileKind} {σ : Type}
    {g : σ → HostFuncId → List Reference.Val → Option (List Reference.Val × σ)}
    (typedHost : c.HostOkS g) {s₀ s' : σ} {ready : Config (core3P (profile o)) σ}
    {inst : InstId} {exports : List (String × FuncId)} {f : FuncId}
    {rs : List Reference.Val} {store : Store Nat}
    (init : let h := answerHostS (profile o) g
      Instantiates prof h.hr h.dispatch (Config.init (hostFuncs 0 c.imports CStore.empty) s₀)
        c.toRef (importArgs c.imports) ready inst exports)
    (lookup : exports.lookup (exportIface c)[q.index].1 = some f) :
    (let h := answerHostS (profile o) g
      ∃ finished, Calls prof h.hr h.dispatch ready ⟨0⟩ f (q.args.val.map toRefVal) finished
          (.resolved (some rs)) ∧
        finished.host = s' ∧ Store.mapH trampIdx finished.store.core = store) ↔
    ∃ (a : Values (exportIface c)[q.index].2.results) (cs : List (Call (signature c.imports))),
      a.val.map toRefVal = rs ∧ HostReplies (c := c) g s₀ cs s' ∧
      Sees ((body o r q).run ⟨r.inst.store⟩).run cs (.reply (some a) store) := by
  constructor
  · rintro ⟨finished, run, host, projected⟩
    obtain ⟨a, cs, values, replies, seen⟩ :=
      SyncImportRun.sees_of_reference_return r wired q typedHost init lookup run
    exact ⟨a, cs, values, host ▸ replies, projected ▸ seen⟩
  · rintro ⟨a, cs, rfl, replies, seen⟩
    exact reference_return_of_sees r wired q typedHost init lookup replies seen

end Silmaril.Proofs.Wasm.Component.Reference.SyncImportReplay
