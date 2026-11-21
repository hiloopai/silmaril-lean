module

public import Silmaril.Wasm.Game.IOAccept.HostRound.Defs
public import Silmaril.Wasm.Abstract.HostSessionXP.Thms
public import Silmaril.Wasm.Game.IOAccept.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.IOAccept.HostRound

open Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
open Silmaril.Accept.IO Silmaril.Games.Abstract Silmaril.Wasm
open Silmaril.Wasm.Abstract (EvRun HEvStep wasmHostSig)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Game.Accept (Finished)

variable {X I O C : Type} {P : Numerics.Profile} {host : HostSemantics Nat}
  {m : Module} {mem : Option Nat} {R : Roles X I O C} {ready : Config Nat} {addr : Nat}

private theorem of_evRun {c d : Config Nat} {events : List (Call (wasmHostSig Nat))}
    (run : EvRun P host c events d) {tags : List (Tag X I O C)}
    (before : TSession P (SEnv.uOfHost host) m mem R ready () [addr] .run false (c, ()) tags) :
    TSession P (SEnv.uOfHost host) m mem R ready () [addr] .run false (d, ())
      (tags ++ events.flatMap (answerEventTags m mem R)) := by
  induction run generalizing tags with
  | refl => simpa using before
  | silent hstep _ ih =>
      rcases hstep with hstep | ⟨rfl, _⟩
      · exact ih (.internal before hstep)
      · exact ih before
  | @event c₁ c₂ c₃ event rest hstep hrun ih =>
      rcases hstep with ⟨ctx, callee, hcall, hstore, hans, rfl⟩
      have hc := TSession.call before hcall
      have ha := TSession.answer (q' := ()) (a := ⟨event.2.1, event.2.2⟩) hc hcall hans
      have ht := ih ha
      cases hh : m.imports[event.1.1]? <;> simpa [answerEventTags, calloutAt?, hcall, hstore,
        List.append_assoc, hh] using ht

private theorem completed_of_evRun {args : List Val} {done : Config Nat} {r : Result}
    {events : List (Call (wasmHostSig Nat))} (fin : Finished false ready)
    (hok : InvokeOk ready.store addr args) (hresult : done.code = r.toAdmin)
    (run : EvRun P host (Execution.Core.invoke ready.store addr args) events done) :
    TSession P (SEnv.uOfHost host) m mem R ready () [addr] .idle false (done, ())
      ([.enter (R.entry addr args)] ++ events.flatMap (answerEventTags m mem R) ++
        [.exit (R.exitVal r (memOf mem done.store))]) := by
  have hstart : TSession P (SEnv.uOfHost host) m mem R ready () [addr] .inst false (ready, ()) [] :=
    .start
  exact .ret (of_evRun run (.invoke hstart (by decide) fin (by simp) hok)) hresult

private theorem count_append (left right : List (Tag X I O C)) :
    entryCount (left ++ right) = entryCount left + entryCount right := List.countP_append

private theorem count_call (o : Option Silmaril.Wasm.Game.Accept.Callout) :
    entryCount (o.elim [] R.callTags) = 0 := by
  cases o with
  | none => rfl
  | some callout =>
      unfold Roles.callTags
      cases hi : R.callIn callout <;> cases ho : R.callOut callout <;> simp [entryCount, hi, ho]

private theorem count_answer (o : Option Silmaril.Wasm.Game.Accept.Callout) (reply : HostReply) :
    entryCount (o.elim [] fun callout => R.answerTags callout reply) = 0 := by
  cases o with
  | none => rfl
  | some callout =>
      unfold Roles.answerTags
      cases ha : R.answerIn callout reply <;> simp [entryCount, ha]

private theorem count_events (events : List (Call (wasmHostSig Nat))) :
    entryCount (events.flatMap (answerEventTags m mem R)) = 0 := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      rw [List.flatMap_cons, count_append, ih, Nat.add_zero]
      unfold answerEventTags
      cases ht : m.imports[event.1.1]? with
      | none => rfl
      | some imp =>
          rw [Option.elim_some, count_append]
          exact Nat.add_eq_zero_iff.mpr ⟨count_call (some _), count_answer (some _) _⟩

private theorem evRun_append {start mid end_ : Config Nat}
    {events tail : List (Call (wasmHostSig Nat))}
    (first : EvRun P host start events mid) (last : EvRun P host mid tail end_) :
    EvRun P host start (events ++ tail) end_ := by
  induction first with
  | refl => exact last
  | silent hstep _ ih => exact .silent hstep (ih last)
  | event hstep _ ih => exact .event hstep (ih last)

private theorem noCall_of_terminal {c : Config Nat} (h : c.Terminal) :
    decompose? c.store c.code = none := by
  obtain ⟨r, hr⟩ := h
  rw [hr]
  cases r with
  | values => exact decompose?_vals_nil
  | trap => exact decompose?_vals_cons_none (vs := []) (r := []) rfl (fun _ _ => decompHead_trap)
  | throw a =>
      exact decompose?_vals_cons_none (vs := [.ref (.exn a)]) (r := []) rfl
        (fun _ _ => decompHead_plain rfl)

private theorem noStep_of_terminal {c next : Config Nat} (h : c.Terminal)
    (hstep : Step P (fun _ _ _ _ => False) c next) : False := by
  obtain ⟨r, hr⟩ := h
  have lifted : Step P (fun _ _ _ _ => False) ⟨c.store, c.frame, r.toAdmin⟩ next := by
    rw [← hr]; exact hstep
  cases r with
  | values => exact Det.not_step_vals lifted
  | trap => exact Det.not_step_trap lifted
  | throw => exact Det.not_step_throwing lifted

private theorem waiting_decomp {p : Phase} {c : Config Nat} {q : Unit} {ts : List (Tag X I O C)}
    (h : TSession P (SEnv.uOfHost host) m mem R ready () [addr] p true (c, q) ts) :
    ∃ ctx index target args, decompose? c.store c.code = some (ctx, index, target, args) := by
  cases h with
  | call _ hcall => exact ⟨_, _, _, _, hcall⟩

private def roundLog (R : Roles X I O C) (pending : Bool) (c : Config Nat) (ts : List (Tag X I O C))
    (m : Module) (mem : Option Nat) (ready : Config Nat) (addr : Nat) (P : Numerics.Profile)
    (host : HostSemantics Nat) : Prop :=
  ∃ args events, InvokeOk ready.store addr args ∧
    EvRun P host (Execution.Core.invoke ready.store addr args) events c ∧
    ts = [.enter (R.entry addr args)] ++ events.flatMap (answerEventTags m mem R) ++
      (if pending then (calloutAt? m mem c).elim [] R.callTags else [])

private def completeLog (R : Roles X I O C) (c : Config Nat) (ts : List (Tag X I O C))
    (m : Module) (mem : Option Nat) (ready : Config Nat) (addr : Nat) (P : Numerics.Profile)
    (host : HostSemantics Nat) : Prop :=
  ∃ args events result, InvokeOk ready.store addr args ∧
    EvRun P host (Execution.Core.invoke ready.store addr args) events c ∧ c.code = result.toAdmin ∧
    ts = [.enter (R.entry addr args)] ++ events.flatMap (answerEventTags m mem R) ++
      [.exit (R.exitVal result (memOf mem c.store))]

private def sessionLog (R : Roles X I O C) (m : Module) (mem : Option Nat) (ready : Config Nat)
    (addr : Nat) (P : Numerics.Profile) (host : HostSemantics Nat) (p : Phase) (pending : Bool)
    (x : Config Nat × Unit) (tags : List (Tag X I O C)) : Prop :=
  match p with
    | .inst => x.1 = ready ∧ tags = [] ∧ pending = false
    | .run => entryCount tags ≠ 0 ∧ (entryCount tags = 1 → roundLog R pending x.1 tags m mem ready addr P host)
    | .idle => x.1.Terminal ∧ entryCount tags ≠ 0 ∧
        (entryCount tags = 1 → completeLog R x.1 tags m mem ready addr P host)

private theorem readback {p : Phase} {pending : Bool} {x : Config Nat × Unit} {tags : List (Tag X I O C)}
    (fin : Finished false ready)
    (h : TSession P (SEnv.uOfHost host) m mem R ready () [addr] p pending x tags) :
    sessionLog R m mem ready addr P host p pending x tags := by
  have hready : ready.Terminal := by
    obtain ⟨vs, hv⟩ := fin
    exact ⟨.values vs, hv⟩
  refine TSession.rec (motive := fun phase waiting state trace _ =>
    sessionLog R m mem ready addr P host phase waiting state trace) ?_ ?_ ?_ ?_ ?_ ?_ h
  · exact ⟨rfl, rfl, rfl⟩
  case refine_2 =>
      intro phase waiting c next q trace hs hstep ih
      cases phase with
      | inst =>
          have hc : c = ready := ih.1
          subst c
          exact (noStep_of_terminal hready hstep).elim
      | idle => exact (noStep_of_terminal ih.1 hstep).elim
      | run =>
          cases waiting with
          | true =>
              obtain ⟨ctx, index, target, args, hh⟩ := waiting_decomp hs
              rw [decompose?_none_of_noRedex (Step.noRedex hstep)] at hh
              contradiction
          | false =>
              refine ⟨ih.1, fun he => ?_⟩
              obtain ⟨args, events, hok, hrun, htrace⟩ := ih.2 he
              refine ⟨args, events, hok, ?_, htrace⟩
              simpa using evRun_append hrun (.silent (.inl hstep) (.refl _))
  case refine_3 =>
      intro phase c q trace ctx index target args hs hcall ih
      have he : entryCount (trace ++ (calloutAt? m mem c).elim [] R.callTags) = entryCount trace := by
        rw [count_append, count_call, Nat.add_zero]
      cases phase with
      | inst =>
          have hc : c = ready := ih.1
          subst c
          rw [noCall_of_terminal hready] at hcall
          contradiction
      | idle =>
          rw [noCall_of_terminal ih.1] at hcall
          contradiction
      | run =>
          refine ⟨fun hn => ih.1 (he ▸ hn), fun hcount => ?_⟩
          obtain ⟨as, events, hok, hrun, htrace⟩ := ih.2 (he ▸ hcount)
          exact ⟨as, events, hok, hrun, by simp [htrace]⟩
  case refine_4 =>
      intro phase c q q' trace ctx index target args reply hs hcall hans ih
      have he : entryCount (trace ++ (calloutAt? m mem c).elim [] fun o =>
          R.answerTags o ⟨reply.result, memOf mem reply.store⟩) = entryCount trace := by
        rw [count_append, count_answer, Nat.add_zero]
      cases phase with
      | inst => exact (Bool.noConfusion ih.2.2)
      | idle =>
          rw [noCall_of_terminal ih.1] at hcall
          contradiction
      | run =>
          refine ⟨fun hn => ih.1 (he ▸ hn), fun hcount => ?_⟩
          obtain ⟨as, events, hok, hrun, htrace⟩ := ih.2 (he ▸ hcount)
          let event : Call (wasmHostSig Nat) := ⟨⟨target, c.store, args⟩, reply.store, reply.result⟩
          have hstep : HEvStep P host c (some event) ⟨reply.store, c.frame, ctx.fill reply.result.toAdmin⟩ :=
            ⟨ctx, index, hcall, rfl, hans, rfl⟩
          refine ⟨as, events ++ [event], hok, evRun_append hrun (.event hstep (.refl _)), ?_⟩
          rw [htrace]
          cases ht : m.imports[target]? <;>
            simp [answerEventTags, event, calloutAt?, hcall, ht, List.append_assoc]
  case refine_5 =>
      intro phase waiting c q trace func args hs hp finished ha hok ih
      have haddr : func = addr := by simpa using ha
      subst func
      have he : entryCount (trace ++ [.enter (R.entry addr args)]) = entryCount trace + 1 :=
        count_append _ _
      refine ⟨by rw [he]; omega, fun hcount => ?_⟩
      cases phase with
      | run => exact (hp rfl).elim
      | idle => exact (ih.2.1 (by omega)).elim
      | inst =>
          obtain ⟨rfl, rfl, _⟩ := ih
          exact ⟨args, [], hok, .refl _, rfl⟩
  case refine_6 =>
      intro waiting c q trace result hs hresult ih
      have hterminal : c.Terminal := ⟨_, hresult⟩
      have he : entryCount (trace ++ [.exit (R.exitVal result (memOf mem c.store))]) = entryCount trace :=
        count_append _ _ |>.trans (Nat.add_zero _)
      refine ⟨hterminal, fun hn => ih.1 (he ▸ hn), fun hcount => ?_⟩
      cases waiting with
      | true =>
          obtain ⟨ctx, index, target, args, hh⟩ := waiting_decomp hs
          rw [noCall_of_terminal hterminal] at hh
          contradiction
      | false =>
          obtain ⟨args, events, hok, hrun, htrace⟩ := ih.2 (he ▸ hcount)
          exact ⟨args, events, result, hok, hrun, hresult, by simp [htrace]⟩

theorem completed_iff_evRun {done : Config Nat} {tags : List (Tag X I O C)}
    (fin : Finished false ready) :
    (TSession P (SEnv.uOfHost host) m mem R ready () [addr] .idle false (done, ()) tags ∧ entryCount tags = 1) ↔
    ∃ args events result, InvokeOk ready.store addr args ∧
      EvRun P host (Execution.Core.invoke ready.store addr args) events done ∧ done.code = result.toAdmin ∧
      tags = [.enter (R.entry addr args)] ++ events.flatMap (answerEventTags m mem R) ++
        [.exit (R.exitVal result (memOf mem done.store))] := by
  constructor
  · rintro ⟨h, hcount⟩
    exact (readback fin h).2.2 hcount
  · rintro ⟨args, events, result, hok, hrun, hresult, rfl⟩
    exact ⟨completed_of_evRun fin hok hresult hrun, by
      rw [count_append, count_append, count_events]; rfl⟩

open Silmaril.Wasm.Abstract (HostTyped InvOkXP natTripleSXP natTripleSXP_mem_iff)
open Silmaril.Wasm.Interp (HostSliceT HostSliceE StoreChkE ehExt TagsOk)

theorem completed_iff_native {o : GrowOracle} {tagTypes : List TagInst}
    {done : Config Nat} {tags : List (Tag X I O C)} (hframe : done.frame = {})
    (fin : Finished false ready) (hstore : StoreOk ready.store)
    (hcheck : StoreChkE (ehExt tagTypes) ready.store.funcs) (htags : TagsOk tagTypes ready.store)
    (htyped : HostTyped host) (hslice : HostSliceT host) (heh : HostSliceE tagTypes host) :
    (TSession (profile o) (SEnv.uOfHost host) m mem R ready () [addr] .idle false (done, ()) tags ∧
        entryCount tags = 1) ↔
    ∃ args events result, done.code = result.toAdmin ∧
      (events, .ret (nativeResult result) done.store) ∈
        (natTripleSXP host (InvOkXP tagTypes)).1 ready.store (addr, args) ∧
      tags = [.enter (R.entry addr args)] ++ events.flatMap (answerEventTags m mem R) ++
        [.exit (R.exitVal result (memOf mem done.store))] := by
  rw [completed_iff_evRun fin]
  have exactFrame : done = ⟨done.store, {}, done.code⟩ := by cases done; cases hframe; rfl
  have native_iff (args : List Val) (events : List (Call (wasmHostSig Nat))) (result : Result)
      (hcode : done.code = result.toAdmin) :
      (events, .ret (nativeResult result) done.store) ∈
        (natTripleSXP host (InvOkXP tagTypes)).1 ready.store (addr, args) ↔
      InvokeOk ready.store addr args ∧
        EvRun (profile o) host (Execution.Core.invoke ready.store addr args) events done := by
    rw [natTripleSXP_mem_iff (o := o) htyped hslice heh]
    have hd : done = ⟨done.store, {}, result.toAdmin⟩ := exactFrame.trans (by rw [hcode])
    constructor
    · rintro ⟨hok, hrun⟩
      refine ⟨hok.2.2.2, ?_⟩
      rw [hd]
      cases result <;> exact hrun
    · rintro ⟨hok, hrun⟩
      refine ⟨⟨hstore, hcheck, htags, hok⟩, ?_⟩
      rw [hd] at hrun
      cases result <;> exact hrun
  constructor
  · rintro ⟨args, events, result, hok, hrun, hcode, htrace⟩
    exact ⟨args, events, result, hcode, (native_iff args events result hcode).2 ⟨hok, hrun⟩, htrace⟩
  · rintro ⟨args, events, result, hcode, hn, htrace⟩
    obtain ⟨hok, hrun⟩ := (native_iff args events result hcode).1 hn
    exact ⟨args, events, result, hok, hrun, hcode, htrace⟩

end Silmaril.Proofs.Wasm.Game.IOAccept.HostRound
