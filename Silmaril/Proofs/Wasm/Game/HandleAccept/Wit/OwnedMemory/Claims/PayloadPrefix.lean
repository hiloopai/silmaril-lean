module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Local.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCollection.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
import Silmaril.Wasm.Component.Reference.Machine.Oracle.Defs
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
import Silmaril.Wasm.Component.Reference.ABI.Layout.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims

variable {E : CoreEngine} {Host Result Next : Type}
  {profile : ProfileKind} {ready : HostReady Host} {dispatch : Call E → P E Host (Ret E)}

private theorem chain {before middle after : Config E Host} {front back : List (Label E Host)}
    (left : Steps profile ready dispatch before front middle) (right : Steps profile ready dispatch middle back after) :
    Steps profile ready dispatch before (front ++ back) after := by
  induction left with
  | refl => exact right
  | cons step _ ih => exact .cons step (ih right)

private theorem silent {labels : List (Label E Host)} (allTau : ∀ label ∈ labels, label = .tau) :
    visible labels = [] := by
  induction labels with
  | nil => rfl
  | cons label rest ih =>
    have head := allTau label (List.mem_cons_self ..)
    simp only [head, visible, List.filter_cons, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun other member => allTau other (List.mem_cons_of_mem _ member))

private theorem visible_append (front back : List (Label E Host)) :
    visible (front ++ back) = visible front ++ visible back := List.filter_append ..

private theorem trace {outcome : Except TrapReason Result} {labels : List (Label E Host)}
    (valid : LocalLeafLabels outcome labels) :
    visible labels = match outcome with | .ok _ => [] | .error reason => [.trap reason] := by
  cases outcome with
  | ok _ =>
    apply silent
    intro label member
    have test := List.all_eq_true.mp valid label member
    cases label <;> simp_all
  | error reason =>
    obtain ⟨count, rfl⟩ := valid
    have prefixSilent : visible (List.replicate count (.tau : Label E Host)) = [] :=
      silent (fun label member => (List.eq_of_mem_replicate member))
    rw [visible_append, prefixSilent, List.nil_append]
    rfl

private theorem returned (value : Result) :
    Compare profile ready dispatch (pure (.ok value)) (pure value) := by
  intro left right same checkCursor canonCursor _ checkNext canonNext checkAt canonAt
  exact ⟨.returned value, [], [], left, right, .refl _, .refl _, same, rfl, checkAt, canonAt⟩

theorem sequential {checked : P E Host (Except RecordLower.Issue Result)} {canonical : P E Host Result}
    (first : Compare profile ready dispatch checked canonical)
    (checkTail : Result → P E Host (Except RecordLower.Issue Next)) (canonTail : Result → P E Host Next)
    (rest : ∀ value, Compare profile ready dispatch (checkTail value) (canonTail value)) :
    Compare profile ready dispatch
      (checked >>= fun result => match result with | .error issue => pure (.error issue) | .ok value => checkTail value)
      (canonical >>= canonTail) := by
  intro left right same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  let checkSuffix := fun (result : Except RecordLower.Issue Result) =>
    (match result with | .error issue => pure (.error issue) | .ok value => checkTail value) >>= checkNext
  let canonSuffix := fun value => canonTail value >>= canonNext
  obtain ⟨outcome, chk, ref, left', right', runChk, runRef, stores, labels, status⟩ :=
    first left right same checkCursor canonCursor sameThread checkSuffix canonSuffix
      (by simpa only [checkSuffix, Prog.bind_eq, Prog.bind_assoc] using checkAt)
      (by simpa only [canonSuffix, Prog.bind_eq, Prog.bind_assoc] using canonAt)
  cases outcome with
  | refused issue => exact ⟨.refused issue, chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | trapped reason => exact ⟨.trapped reason, chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | returned value =>
    obtain ⟨outcome, chk', ref', left'', right'', runChk', runRef', stores', labels', status'⟩ :=
      rest value left' right' stores checkCursor canonCursor sameThread checkNext canonNext status.1 status.2
    refine ⟨outcome, chk ++ chk', ref ++ ref', left'', right'', chain runChk runChk', chain runRef runRef',
      stores', ?_, ?_⟩
    · rw [visible_append, visible_append, labels, labels']
    · cases outcome with
      | returned _ | refused _ => exact status'
      | trapped reason =>
        obtain ⟨emptyCheck, emptyCanon, leading, last⟩ := status'
        refine ⟨emptyCheck, emptyCanon, visible ref ++ leading, ?_⟩
        rw [visible_append, last, List.append_assoc]

private theorem mapResult {checked : P E Host (Except RecordLower.Issue Result)} {canonical : P E Host Result}
    (compare : Compare profile ready dispatch checked canonical) (resultMap : Result → Next)
    (issueMap : RecordLower.Issue → RecordLower.Issue) :
    Compare profile ready dispatch (do return ((← checked).map resultMap).mapError issueMap)
      (do return resultMap (← canonical)) := by
  intro left right same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  obtain ⟨outcome, chk, ref, left', right', runChk, runRef, stores, labels, status⟩ :=
    compare left right same checkCursor canonCursor sameThread
      (fun result => checkNext ((result.map resultMap).mapError issueMap)) (fun value => canonNext (resultMap value))
      (by simpa only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using checkAt) (by
        simpa only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using canonAt)
  cases outcome with
  | returned value => exact ⟨.returned (resultMap value), chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | refused issue => exact ⟨.refused (issueMap issue), chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | trapped reason => exact ⟨.trapped reason, chk, ref, left', right', runChk, runRef, stores, labels, status⟩

private theorem map_id (result : Except RecordLower.Issue Result) : result.map id = result := by
  cases result <;> rfl

private theorem mapError_id (result : Except RecordLower.Issue Result) : result.mapError id = result := by
  cases result <;> rfl

private theorem mapIssue {checked : P E Host (Except RecordLower.Issue Result)} {canonical : P E Host Result}
    (compare : Compare profile ready dispatch checked canonical) (issueMap : RecordLower.Issue → RecordLower.Issue) :
    Compare profile ready dispatch (do return (← checked).mapError issueMap) canonical := by
  intro left right same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  obtain ⟨outcome, chk, ref, left', right', runChk, runRef, stores, labels, status⟩ :=
    compare left right same checkCursor canonCursor sameThread (fun result => checkNext (result.mapError issueMap)) canonNext
      (by simpa only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using checkAt) canonAt
  cases outcome with
  | returned value => exact ⟨.returned value, chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | refused issue => exact ⟨.refused (issueMap issue), chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | trapped reason => exact ⟨.trapped reason, chk, ref, left', right', runChk, runRef, stores, labels, status⟩

private def ClosedOp (profile : ProfileKind) (keep : CStore E → Prop := fun _ => True) : Op E Host → Prop
  | .choose choice => ∃ answer, Allowed profile choice answer
  | .modify update => ∀ store, keep store → keep (update store)
  | .get | .currentThread | .trap _ => True
  | _ => False

theorem forgetKeeping {left right : Config E Host} {keep : CStore E → Prop}
    {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (reaches : ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor checkNext canonNext) :
    Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext := by
  obtain ⟨outcome, chk, ref, checkEnd, canonEnd, runChk, runRef, stores, labels, _, status⟩ := reaches
  exact ⟨outcome, chk, ref, checkEnd, canonEnd, runChk, runRef, stores, labels, status⟩

theorem rememberTrue {left right : Config E Host} {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (reaches : Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext) :
    ReachesKeeping profile ready dispatch (fun _ => True) left right checkCursor canonCursor checkNext canonNext := by
  obtain ⟨outcome, chk, ref, checkEnd, canonEnd, runChk, runRef, stores, labels, status⟩ := reaches
  exact ⟨outcome, chk, ref, checkEnd, canonEnd, runChk, runRef, stores, labels, by cases outcome <;> trivial, status⟩

theorem weakenKeeping {left right : Config E Host} {keep weaker : CStore E → Prop}
    {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (reaches : ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor checkNext canonNext)
    (weaken : ∀ store, keep store → weaker store) :
    ReachesKeeping profile ready dispatch weaker left right checkCursor canonCursor checkNext canonNext := by
  obtain ⟨outcome, chk, ref, checkEnd, canonEnd, runChk, runRef, stores, labels, kept, status⟩ := reaches
  refine ⟨outcome, chk, ref, checkEnd, canonEnd, runChk, runRef, stores, labels, ?_, status⟩
  cases outcome with
  | returned => exact weaken canonEnd.store kept
  | refused | trapped => trivial

theorem continueKeeping {keep : CStore E → Prop} {left right : Config E Host}
    {checkCursor canonCursor : Cursor (E := E) Host} (thread : checkCursor.thread = canonCursor.thread)
    {checkNext : Except RecordLower.Issue Next → P E Host (Ret E)} {canonNext : Next → P E Host (Ret E)}
    (mapIssue : RecordLower.Issue → RecordLower.Issue)
    (checkTail : Result → P E Host (Except RecordLower.Issue Next)) (canonTail : Result → P E Host Next)
    (first : ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor
      (checkedSequenceNext mapIssue checkTail checkNext) (fun value => canonTail value >>= canonNext))
    (rest : ∀ value entered reference, keep reference.store →
      CompareKeepingAt profile ready dispatch keep entered reference (checkTail value) (canonTail value)) :
    ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor checkNext canonNext := by
  obtain ⟨outcome, chk, ref, left', right', runChk, runRef, stores, labels, kept, status⟩ := first
  cases outcome with
  | refused issue =>
    refine ⟨.refused (mapIssue issue), chk, ref, left', right', runChk, runRef, stores, labels, kept, ?_⟩
    simpa only [checkedSequenceNext, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] using status
  | trapped reason => exact ⟨.trapped reason, chk, ref, left', right', runChk, runRef, stores, labels, kept, status⟩
  | returned value =>
    obtain ⟨outcome, chk', ref', left'', right'', runChk', runRef', stores', labels', kept', status'⟩ :=
      rest value left' right' kept stores checkCursor canonCursor thread checkNext canonNext status.1 status.2
    refine ⟨outcome, chk ++ chk', ref ++ ref', left'', right'', chain runChk runChk', chain runRef runRef',
      stores', ?_, kept', ?_⟩
    · rw [visible_append, visible_append, labels, labels']
    · cases outcome with
      | returned _ | refused _ => exact status'
      | trapped reason =>
        obtain ⟨emptyCheck, emptyCanon, leading, last⟩ := status'
        exact ⟨emptyCheck, emptyCanon, visible ref ++ leading, by rw [visible_append, last, List.append_assoc]⟩

private theorem sequentialKeeping {keep : CStore E → Prop} {left right : Config E Host}
    {checked : P E Host (Except RecordLower.Issue Result)} {canonical : P E Host Result}
    (first : CompareKeepingAt profile ready dispatch keep left right checked canonical)
    (mapIssue : RecordLower.Issue → RecordLower.Issue)
    (checkTail : Result → P E Host (Except RecordLower.Issue Next)) (canonTail : Result → P E Host Next)
    (rest : ∀ value entered reference, keep reference.store →
      CompareKeepingAt profile ready dispatch keep entered reference (checkTail value) (canonTail value)) :
    CompareKeepingAt profile ready dispatch keep left right
      (checked >>= fun result => match result with | .error issue => pure (.error (mapIssue issue)) | .ok value => checkTail value)
      (canonical >>= canonTail) := by
  intro same checkCursor canonCursor thread checkNext canonNext checkAt canonAt
  exact continueKeeping thread mapIssue checkTail canonTail (first same checkCursor canonCursor thread
    (checkedSequenceNext mapIssue checkTail checkNext) (fun value => canonTail value >>= canonNext)
    (by
      unfold checkedSequenceNext
      simp only [Prog.bind_eq, Prog.bind_assoc] at checkAt ⊢
      convert checkAt using 3)
    (by simpa only [Prog.bind_eq, Prog.bind_assoc] using canonAt)) rest

theorem localSteps {before finish labels} (run : LocalSteps profile ready dispatch before labels finish) :
    Steps profile ready dispatch before labels finish := by
  induction run with
  | refl => exact .refl _
  | cons _ step _ ih => exact .cons step ih

theorem localAppend {before middle finish leading trailing}
    (front : LocalSteps profile ready dispatch before leading middle)
    (back : LocalSteps profile ready dispatch middle trailing finish) :
    LocalSteps profile ready dispatch before (leading ++ trailing) finish := by
  induction front with
  | refl => exact back
  | cons focus step _ ih => exact .cons focus step (ih back)

private theorem closedCut {body : P E Host Result} {keep : CStore E → Prop}
    (closed : Prog.Every (ClosedOp profile keep) body) :
    ∀ (left right : Config E Host) (check canon : Cursor (E := E) Host)
      (checkNext canonNext : Result → P E Host (Ret E)),
      keep right.store → left.store = right.store → check.thread = canon.thread →
      left.ctl = check.control (body >>= checkNext) → right.ctl = canon.control (body >>= canonNext) →
      LocalCutKeeping profile ready dispatch keep left right check canon checkNext canonNext := by
  induction closed with
  | pure value =>
    intro left right check canon checkNext canonNext kept same _ checkAt canonAt
    have checkEnd : localLeafEnd left left.host right.store check.thread check.frames check.rest checkNext (.ok value) = left := by
      cases left
      simp_all only [localLeafEnd, Cursor.control, Prog.bind_eq, Prog.pure_bind']
    have canonEnd : localLeafEnd right right.host right.store canon.thread canon.frames canon.rest canonNext (.ok value) = right := by
      cases right
      simp_all only [localLeafEnd, Cursor.control, Prog.bind_eq, Prog.pure_bind']
    refine ⟨right.store, .ok value, [], [], by rw [checkEnd]; exact .refl _, by rw [canonEnd]; exact .refl _, rfl, kept, ?_, ?_⟩
    · intro depth
      rw [checkEnd]
      exact .done _ (.active 0 depth)
    · intro depth
      rw [canonEnd]
      exact .done _ (.active 0 depth)
  | @op operation next admitted _ ih =>
    intro left right check canon checkNext canonNext kept same thread checkAt canonAt
    have advance (label : Label E Host) (response : (Eff E Host).Resp operation)
        (leftStore rightStore : CStore E) (kept : keep rightStore) (same : leftStore = rightStore)
        (checked : Step profile ready dispatch left label
          { left with store := leftStore, ctl := check.control (next response >>= checkNext) })
        (canonical : Step profile ready dispatch right label
          { right with store := rightStore, ctl := canon.control (next response >>= canonNext) })
        (localFocus : LocalFocus right)
        (checkEdit : ReturnFrame.Occurrence.transitionEdit left label = .same)
        (canonEdit : ReturnFrame.Occurrence.transitionEdit right label = .same) :
        LocalCutKeeping profile ready dispatch keep left right check canon checkNext canonNext := by
      obtain ⟨store, result, chk, ref, runChk, runRef, labels, outcome⟩ :=
        ih response { left with store := leftStore, ctl := check.control (next response >>= checkNext) }
          { right with store := rightStore, ctl := canon.control (next response >>= canonNext) }
          check canon checkNext canonNext kept same thread rfl rfl
      have final : ∀ (start : Config E Host) (localStore : CStore E) ctl (cursor : Cursor (E := E) Host) finish,
          localLeafEnd { start with store := localStore, ctl } start.host store cursor.thread cursor.frames cursor.rest finish result =
          localLeafEnd start start.host store cursor.thread cursor.frames cursor.rest finish result := by
        intro start localStore ctl cursor finish
        cases result <;> rfl
      rw [final] at runChk runRef
      refine ⟨store, result, label :: chk, label :: ref, .cons checked runChk, .cons localFocus canonical runRef, ?_, ?_⟩
      · change visible ([label] ++ chk) = visible ([label] ++ ref)
        rw [visible_append, visible_append, labels]
      · cases result with
        | ok value =>
          obtain ⟨kept, checkTrack, canonTrack⟩ := outcome
          refine ⟨kept, ?_, ?_⟩
          · intro depth
            have tracked := checkTrack depth
            rw [final] at tracked
            exact .step checked (by rw [checkEdit]; rfl) tracked
          · intro depth
            have tracked := canonTrack depth
            rw [final] at tracked
            exact .step canonical (by rw [canonEdit]; rfl) tracked
        | error reason =>
          obtain ⟨leading, last⟩ := outcome
          refine ⟨visible [label] ++ leading, ?_⟩
          change visible ([label] ++ ref) = _
          rw [visible_append, last, List.append_assoc]
    cases operation with
    | get =>
      exact advance .tau right.store left.store right.store kept same
        (by simpa only [same, Cursor.control, Prog.bind_eq] using
          (Step.get (prof := profile) (hr := ready) (dispatch := dispatch) checkAt)) (.get canonAt)
        (by simp only [LocalFocus, canonAt, Cursor.control, Prog.bind_eq, Prog.bind])
        (by rw [ReturnFrame.Occurrence.transitionEdit, checkAt]; rfl) (by rw [ReturnFrame.Occurrence.transitionEdit, canonAt]; rfl)
    | modify update =>
      exact advance .tau () (update left.store) (update right.store) (admitted right.store kept)
        (congrArg update same) (.modify checkAt) (.modify canonAt)
        (by simp only [LocalFocus, canonAt, Cursor.control, Prog.bind_eq, Prog.bind])
        (by rw [ReturnFrame.Occurrence.transitionEdit, checkAt]; rfl) (by rw [ReturnFrame.Occurrence.transitionEdit, canonAt]; rfl)
    | currentThread =>
      exact advance .tau canon.thread left.store right.store kept same
        (by simpa only [thread, Cursor.control, Prog.bind_eq] using
          (Step.currentThread (prof := profile) (hr := ready) (dispatch := dispatch) checkAt))
        (.currentThread canonAt) (by simp only [LocalFocus, canonAt, Cursor.control, Prog.bind_eq, Prog.bind])
        (by rw [ReturnFrame.Occurrence.transitionEdit, checkAt]; rfl) (by rw [ReturnFrame.Occurrence.transitionEdit, canonAt]; rfl)
    | trap reason =>
      refine ⟨right.store, .error reason, [.trap reason], [.trap reason], ?_,
        .cons (by simp only [LocalFocus, canonAt, Cursor.control, Prog.bind_eq, Prog.bind]) (.trap canonAt) (.refl _), rfl, [], rfl⟩
      rw [← same]
      exact .cons (.trap checkAt) (.refl _)
    | choose choice =>
      obtain ⟨answer, allowed⟩ := admitted
      exact advance (.choice choice answer) answer left.store right.store kept same
        (.choose answer checkAt allowed) (.choose answer canonAt allowed)
        (by simp only [LocalFocus, canonAt, Cursor.control, Prog.bind_eq, Prog.bind]) rfl rfl
    | _ => contradiction

private theorem localCutReaches {keep : CStore E → Prop} {left right : Config E Host} {check canon : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (cut : LocalCutKeeping profile ready dispatch keep left right check canon (fun value => checkNext (.ok value)) canonNext) :
    ReachesKeeping profile ready dispatch keep left right check canon checkNext canonNext := by
  obtain ⟨store, result, chk, ref, runChk, runRef, labels, status⟩ := cut
  cases result with
  | ok value => exact ⟨.returned value, chk, ref, _, _, runChk, localSteps runRef, rfl, labels, status.1, rfl, rfl⟩
  | error reason => exact ⟨.trapped reason, chk, ref, _, _, runChk, localSteps runRef, rfl, labels, trivial, rfl, rfl, status⟩

private theorem compareClosedKeeping {body : P E Host Result} {keep : CStore E → Prop}
    (closed : Prog.Every (ClosedOp profile keep) body) :
    ∀ left right : Config E Host, keep right.store →
      CompareKeepingAt profile ready dispatch keep left right (do return .ok (← body)) body := by
  intro left right kept same check canon thread checkNext canonNext checkAt canonAt
  apply localCutReaches
  refine closedCut closed left right check canon (fun value => checkNext (.ok value)) canonNext kept same thread ?_ canonAt
  simpa only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using checkAt

private theorem compareClosed {body : P E Host Result} (closed : Prog.Every (ClosedOp profile) body) :
    Compare profile ready dispatch (do return .ok (← body)) body := by
  intro left right same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  exact forgetKeeping (compareClosedKeeping closed left right trivial same checkCursor canonCursor sameThread
    checkNext canonNext checkAt canonAt)

private theorem closedLowerFloat (profile : ProfileKind) (kind : FloatType) (bits : BitVec kind.width)
    {keep : CStore E → Prop} :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile keep) (lowerFloat kind bits) := by
  unfold lowerFloat
  split
  · exact .op ⟨firstNan profile kind bits, firstNan_allowed profile kind bits⟩ (fun _ => .pure _)
  · exact .pure _

private theorem encodeCoercion (profile : ProfileKind) (kind : FloatType) (bits : BitVec kind.width)
    {keep : CStore E → Prop} :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile keep) (encodeFloat kind bits) :=
  (closedLowerFloat profile kind bits).bind (fun _ => .pure _)

private theorem coerceWord (profile : ProfileKind) (haveType wantType : CoreType) (word : FlatValue)
    {keep : CStore E → Prop} :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile keep) (coerceLower haveType wantType word) := by
  unfold coerceLower
  split
  · exact (encodeCoercion profile .f32 _).bind (fun _ => .pure _)
  · exact .pure _
  · exact (encodeCoercion profile .f32 _).bind (fun _ => .pure _)
  · exact (encodeCoercion profile .f64 _).bind (fun _ => .pure _)
  · exact .pure _

private theorem coerceWords (profile : ProfileKind) (haves wants : List CoreType) (words : List FlatValue)
    {keep : CStore E → Prop} :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile keep) (coerceLowerSlots haves wants words) := by
  induction haves generalizing wants words with
  | nil => exact .pure _
  | cons haveType remaining ih =>
    cases words with
    | nil => cases wants <;> exact .pure _
    | cons word remainingWords =>
      cases wants with
      | nil => exact .op trivial (fun impossible => nomatch impossible)
      | cons wantType remainingWants =>
        exact (coerceWord profile haveType wantType word).bind fun _ =>
          (ih remainingWants remainingWords).bind fun _ => .pure _

private theorem variantTailClosed (count : Nat) (wanted : List CoreType) (tag : Nat) (haves : List CoreType)
    (words : List FlatValue) {keep : CStore E → Prop} :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile keep) (lowerFlatVariantWith count wanted tag haves (pure words)) := by
  unfold lowerFlatVariantWith
  split
  · exact (coerceWords profile haves wanted words).bind (fun _ => .pure _)
  · exact .op trivial (fun impossible => nomatch impossible)

private theorem variantTail (count : Nat) (wanted : List CoreType) (tag : Nat) (haves : List CoreType)
    (words : List FlatValue) :
    Compare profile ready dispatch
      (do return .ok (← lowerFlatVariantWith count wanted tag haves (pure words)))
      (lowerFlatVariantWith count wanted tag haves (pure words)) :=
  compareClosed (variantTailClosed count wanted tag haves words)

theorem variantTailFrame (count : Nat) (wanted : List CoreType) (tag : Nat) (haves : List CoreType)
    (words : List FlatValue) {keep : CStore E → Prop} (left right : Config E Host) (kept : keep right.store) :
    CompareLocalKeepingAt profile ready dispatch keep left right
      (do return .ok (← lowerFlatVariantWith count wanted tag haves (pure words)))
      (lowerFlatVariantWith count wanted tag haves (pure words)) := by
  intro same check canon thread checkNext canonNext checkAt canonAt
  refine closedCut (variantTailClosed count wanted tag haves words) left right check canon
    (fun value => checkNext (.ok value)) canonNext kept same thread ?_ canonAt
  simpa only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using checkAt

private theorem localGet {keep : CStore E → Prop} :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile keep) getStore := .op trivial (fun _ => .pure _)

private def WriteClosed (keep : CStore E → Prop) : Prop :=
  ∀ store memory ptr bytes, keep store → keep (writeMemSt memory ptr bytes store)

private theorem closedOrTrap {keep : CStore E → Prop} {Result : Type} (reason : TrapReason) (value : Option Result) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile keep) (orTrap reason value) := by
  cases value
  · exact .op trivial (fun impossible => nomatch impossible)
  · exact .pure _

private theorem closedWriteMem {keep : CStore E → Prop} (writes : WriteClosed keep)
    (cx : LiftLowerContext E) (ptr : Nat) (bytes : ByteArray) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile keep) (writeMem cx ptr bytes) := by
  unfold writeMem memAddr
  refine (closedOrTrap .noMemory cx.opts.memory).bind fun address => localGet.bind fun store => ?_
  split
  · exact .op trivial (fun impossible => nomatch impossible)
  · exact .op (fun _ kept => writes _ _ _ _ kept) (fun _ => .pure _)

private theorem closedIntKeeping {keep : CStore E → Prop} (writes : WriteClosed keep)
    (cx : LiftLowerContext E) (number : Int) (ptr bytes : Nat) (signed : Bool := false) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile keep) (storeInt cx number ptr bytes signed) :=
  closedWriteMem writes cx ptr _

private theorem closedReadMem (cx : LiftLowerContext E) (ptr size : Nat) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile) (readMem cx ptr size) := by
  unfold readMem memAddr
  exact (closedOrTrap .noMemory cx.opts.memory).bind fun addr => localGet.bind fun store =>
    closedOrTrap .outOfBounds (E.memRead? store.core addr ptr size)

private theorem closedTrapIf (condition : Bool) (reason : TrapReason) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile) (trapIf condition reason) := by
  cases condition
  · exact .pure _
  · exact .op trivial (fun impossible => nomatch impossible)

private theorem closedStringStep (cx : LiftLowerContext E) (ptr : Nat) (action : StoreStep)
    (localStep : LocalStringStep action) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile) (runStoreStep cx ptr action) := by
  have write (address : Nat) (bytes : ByteArray) :
      Prog.Every (ClosedOp (E := E) (Host := Host) profile) (writeMem cx address bytes) :=
    closedWriteMem (fun _ _ _ _ _ => trivial) cx address bytes
  cases action with
  | allocate | reallocate => cases localStep
  | trapIfMisaligned alignment =>
    exact (closedTrapIf (decide (ptr ≠ ABI.alignTo ptr alignment)) .unalignedPointer).bind (fun _ => .pure _)
  | trapIfOutOfBounds size =>
    unfold runStoreStep checkInBounds memLen memAddr
    simp only [Prog.bind_eq, Prog.bind_assoc]
    exact (closedOrTrap .noMemory cx.opts.memory).bind fun addr => localGet.bind fun store =>
      (closedOrTrap (.internal "dangling memory address") (E.memSize? store.core addr)).bind fun bytes =>
        (closedTrapIf (decide (ptr + size > bytes)) .outOfBounds).bind (fun _ => .pure _)
  | write offset bytes => exact (write (ptr + offset) bytes.toByteArray).bind (fun _ => .pure _)
  | inflateLatin1 size => exact (closedReadMem cx ptr (2 * size)).bind fun data =>
      (write ptr (ABI.memInflateLatin1 data.toList 0 size).toByteArray).bind (fun _ => .pure _)
  | deflateUtf16 size => exact (closedReadMem cx ptr (2 * size)).bind fun data =>
      (write ptr (ABI.memDeflateUtf16 data.toList 0 size).toByteArray).bind (fun _ => .pure _)

theorem localStringSteps (cx : LiftLowerContext E) (ptr : Nat) (steps : List StoreStep)
    (localSteps : ∀ action ∈ steps, LocalStringStep action) :
    Compare profile ready dispatch (do return .ok (← runStoreSteps cx ptr steps)) (runStoreSteps cx ptr steps) := by
  apply compareClosed
  induction steps generalizing ptr with
  | nil => exact .pure _
  | cons action rest ih =>
    exact (closedStringStep cx ptr action (localSteps action (List.mem_cons_self ..))).bind fun next =>
      ih next (fun child member => localSteps child (List.mem_cons_of_mem _ member))

private theorem closedInt (cx : LiftLowerContext E) (number : Int) (ptr bytes : Nat) (signed : Bool := false) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile) (storeInt cx number ptr bytes signed) :=
  closedIntKeeping (fun _ _ _ _ _ => trivial) cx number ptr bytes signed

private theorem closedStorePrim {keep : CStore E → Prop} (writes : WriteClosed keep)
    (cx : LiftLowerContext E) (primitive : WIT.Primitive) (value : Value.Val)
    (nonString : primitive ≠ .string) (ptr : Nat) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile keep) (storePrim Limits.spec Quirks.none cx primitive value ptr) := by
  unfold storePrim
  split
  · exact closedIntKeeping writes cx _ ptr _
  · exact (encodeCoercion profile .f32 _).bind (fun _ => closedIntKeeping writes cx _ ptr _)
  · exact (encodeCoercion profile .f64 _).bind (fun _ => closedIntKeeping writes cx _ ptr _)
  · exact closedIntKeeping writes cx _ ptr _
  · contradiction
  · split
    · exact closedIntKeeping writes cx _ ptr _ _
    · exact .op trivial (fun impossible => nomatch impossible)
  · exact .op trivial (fun impossible => nomatch impossible)

private theorem closedFlatPrim (cx : LiftLowerContext E) (width : AddrType) (primitive : WIT.Primitive)
    (value : Value.Val) (nonString : primitive ≠ .string) {keep : CStore E → Prop} :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile keep) (lowerFlatPrim Limits.spec Quirks.none cx width primitive value) := by
  unfold lowerFlatPrim
  split
  · exact .pure _
  · exact (closedLowerFloat profile .f32 _).bind (fun _ => .pure _)
  · exact (closedLowerFloat profile .f64 _).bind (fun _ => .pure _)
  · exact .pure _
  · contradiction
  · split
    · exact .pure _
    · exact .op trivial (fun impossible => nomatch impossible)
  · exact .op trivial (fun impossible => nomatch impossible)

private theorem variantHead (cx : LiftLowerContext E) (count : Nat) (alignment : Alignment) (tag ptr : Nat) :
    Compare profile ready dispatch
      (do return .ok (← storeVariantHead cx count alignment tag ptr))
      (storeVariantHead cx count alignment tag ptr) :=
  compareClosed ((closedInt cx tag ptr (discSize count)).bind (fun _ => .pure _))

private theorem closedDescriptor {keep : CStore E → Prop} (writes : WriteClosed keep)
    (cx : LiftLowerContext E) (width : AddrType) (ptr count : Nat) (output : Lower.Output) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile keep) (ListLower.publish cx width ptr count output) := by
  cases output with
  | flat => exact .pure _
  | memory dest =>
    have localSize : Prog.Every (ClosedOp (E := E) (Host := Host) profile keep) (ptrSize cx) :=
      localGet.bind (fun _ => .pure _)
    exact localSize.bind (fun size => (closedIntKeeping writes cx ptr dest size).bind
      (fun _ => closedIntKeeping writes cx count (dest + size) size))

private theorem descriptor (cx : LiftLowerContext E) (width : AddrType) (ptr count : Nat) (output : Lower.Output) :
    Compare profile ready dispatch (do return .ok (← ListLower.publish cx width ptr count output))
      (ListLower.publish cx width ptr count output) :=
  compareClosed (closedDescriptor (fun _ _ _ _ _ => trivial) cx width ptr count output)

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {scheduledReady : HostReady (HostState sig)}
  {scheduledDispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}

private theorem handleKeeping (destination : RecordDestination) (inst : InstId) (item : Field) (isHandle : CanonicalHandle item)
    (index : Nat) (output : Lower.Output) (origin : CStore (core3 grow))
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core) :
    CompareKeepingAt profile scheduledReady scheduledDispatch (fun store => Core3.Grows origin.core store.core) left right
      (Record.Effects.checkedLeaf recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item index output)
      (CanonicalTree.leaf Limits.spec Quirks.none (destination.context inst) destination.width item output) := by
  intro same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  rcases checkCursor with ⟨thread, checkFrames, checkRest⟩
  rcases canonCursor with ⟨otherThread, canonFrames, canonRest⟩
  change thread = otherThread at sameThread
  subst otherThread
  have paired := RecordDestination.compare_handle_leaf (profile := profile) (ready := scheduledReady)
    (dispatch := scheduledDispatch) same destination inst item isHandle index output checkNext canonNext checkAt canonAt
  cases verdict : liveLeafPlan left.store left.host.writer index item with
  | error issue =>
    rw [verdict] at paired
    obtain ⟨labels, allTau, tracks⟩ := paired
    exact ⟨.refused issue, labels, [], _, right, (ReturnFrame.Occurrence.prefix_survives (tracks 0)).1,
      .refl right, same, silent allTau, trivial, rfl⟩
  | ok plan =>
    rw [verdict] at paired
    obtain ⟨reached, outcome, leading, chk, ref, grown, allTau, checkTrace, canonTrace, checkRun, canonRun, _⟩ := paired
    have labels : visible (leading ++ chk) = visible ref := by
      cases outcome <;> rw [visible_append, silent allTau, List.nil_append, trace checkTrace, trace canonTrace]
    cases outcome with
    | ok value => exact ⟨.returned value, _, _, _, _, checkRun, canonRun, rfl, labels, growth.trans grown, rfl, rfl⟩
    | error reason =>
      exact ⟨.trapped reason, _, _, _, _, checkRun, canonRun, rfl, labels, trivial, rfl, rfl, [], trace canonTrace⟩

theorem handle (destination : RecordDestination) (inst : InstId) (item : Field) (isHandle : CanonicalHandle item)
    (index : Nat) (output : Lower.Output) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.checkedLeaf recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item index output)
      (CanonicalTree.leaf Limits.spec Quirks.none (destination.context inst) destination.width item output) := by
  intro left right same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  exact forgetKeeping (handleKeeping destination inst item isHandle index output right.store left right (Core3.Grows.refl _)
    same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt)

private theorem guardedTail {checked : P E Host (Except RecordLower.Issue Result)} {canonical : P E Host Result}
    (first : Compare profile ready dispatch checked canonical) (mapIssue : RecordLower.Issue → RecordLower.Issue)
    (checkTail : Result → P E Host (Except RecordLower.Issue Next)) (canonTail : Result → P E Host Next)
    (later : ∀ value, Compare profile ready dispatch (checkTail value) (canonTail value)) :
    Compare profile ready dispatch
      (checked >>= fun result => match result with
        | .error issue => pure (.error (mapIssue issue)) | .ok value => checkTail value)
      (canonical >>= canonTail) := by
  have compared := sequential (mapResult first id mapIssue) checkTail canonTail later
  simp only [map_id, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] at compared ⊢
  convert compared using 2 <;> try rfl
  funext verdict
  cases verdict <;> rfl

private theorem readWidth (cx : LiftLowerContext E) (left right : Config E Host) (width : AddrType)
    (reachedWidth : ptrTypeIn right.store cx = width) (checked : P E Host (Except RecordLower.Issue Result))
    (canonical : AddrType → P E Host Result) (tail : Compare profile ready dispatch checked (canonical width)) :
    CompareAt profile ready dispatch left right checked (ptrType cx >>= canonical) := by
  intro same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  let entered := { right with ctl := canonCursor.control (canonical width >>= canonNext) }
  have step : Step profile ready dispatch right .tau entered := by
    have read := Step.get (prof := profile) (hr := ready) (dispatch := dispatch)
      (k := fun store => canonical (ptrTypeIn store cx) >>= canonNext) canonAt
    simpa only [entered, Cursor.control, reachedWidth] using read
  obtain ⟨outcome, chk, ref, checkEnd, canonEnd, runChk, runRef, stores, labels, status⟩ :=
    tail left entered same checkCursor canonCursor sameThread checkNext canonNext checkAt rfl
  exact ⟨outcome, chk, .tau :: ref, checkEnd, canonEnd, runChk, .cons step runRef, stores, labels, status⟩

private theorem readWidthKeeping {keep : CStore E → Prop}
    (cx : LiftLowerContext E) (left right : Config E Host) (width : AddrType)
    (reachedWidth : ptrTypeIn right.store cx = width) (checked : P E Host (Except RecordLower.Issue Result))
    (canonical : AddrType → P E Host Result)
    (tail : ∀ entered : Config E Host, entered.store = right.store → entered.host = right.host →
      CompareKeepingAt profile ready dispatch keep left entered checked (canonical width)) :
    CompareKeepingAt profile ready dispatch keep left right checked (ptrType cx >>= canonical) := by
  intro same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  let entered := { right with ctl := canonCursor.control (canonical width >>= canonNext) }
  have step : Step profile ready dispatch right .tau entered := by
    have read := Step.get (prof := profile) (hr := ready) (dispatch := dispatch)
      (k := fun store => canonical (ptrTypeIn store cx) >>= canonNext) canonAt
    simpa only [entered, Cursor.control, reachedWidth] using read
  obtain ⟨outcome, chk, ref, checkEnd, canonEnd, runChk, runRef, stores, labels, kept, status⟩ :=
    tail entered rfl rfl same checkCursor canonCursor sameThread checkNext canonNext checkAt rfl
  exact ⟨outcome, chk, .tau :: ref, checkEnd, canonEnd, runChk, .cons step runRef, stores, labels, kept, status⟩

theorem memorySum (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (arms : List (Option TypeOf)) (tag index ptr : Nat) (selected : Option Field)
    (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn right.store (destination.context inst) = destination.width)
    (child : ∀ item address, selected = some item → Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item 0 (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    CompareAt profile scheduledReady scheduledDispatch left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) index (.memory ptr))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) (.memory ptr)) := by
  rw [Record.Effects.field, CanonicalTree.field]
  apply readWidth _ left right destination.width width
  let head := storeVariantHead (σ := HostState sig) (destination.context (grow := grow) inst) arms.length
    (maxCaseAlignment (arms.map (layoutOption destination.width))) tag ptr
  have compared : Compare profile scheduledReady scheduledDispatch (do return .ok (← head)) head :=
    variantHead (destination.context inst) arms.length (maxCaseAlignment (arms.map (layoutOption destination.width))) tag ptr
  cases selected with
  | none =>
    have composed := sequential compared (fun _ => pure (.ok ())) (fun _ => pure ()) (fun _ => returned ())
    simpa only [Lower.Output.Result, head, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using composed
  | some active =>
    have composed := sequential compared
      (fun address => do
        return (← Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
          destination.width active 0 (.memory address)).mapError (.nested index))
      (fun address => CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
        destination.width active (.memory address))
      (fun address => mapIssue (child active address rfl) (.nested index))
    simpa only [Lower.Output.Result, head, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using composed

theorem memorySumTag (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (arms : List (Option TypeOf)) (tag index base : Nat) (selected : Option Field)
    (origin : CStore (core3 grow)) (left right : Config (core3 grow) (HostState sig))
    (check canon : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (same : left.store = right.store) (thread : check.thread = canon.thread)
    (width : ptrTypeIn right.store (destination.context inst) = destination.width)
    (growth : Core3.Grows origin.core right.store.core)
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.sum type arms tag selected) index (.memory base) >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.sum type arms tag selected) (.memory base) >>= canonNext)) :
    let address := sumPayloadAddress destination.width arms base
    LocalCutKeeping profile scheduledReady scheduledDispatch (fun store => Core3.Grows origin.core store.core) left right check canon
      (sumCheckedNext destination inst selected index address checkNext)
      (sumCanonicalNext destination inst selected address canonNext) := by
  intro address
  let cx := destination.context (grow := grow) inst
  let body : Session grow sig Unit := storeInt cx tag base (discSize arms.length)
  let checked := sumCheckedNext destination inst selected index address checkNext
  let resumed := fun reached => sumCanonicalNext destination inst selected (sumPayloadAddress reached arms base) canonNext
  let entered := { right with ctl := canon.control (body.bind (resumed destination.width)) }
  have checkBody : left.ctl = check.control (body.bind checked) := by
    rw [checkAt, Record.Effects.field]
    cases selected with
    | none =>
      change check.control (((body.bind fun () => Prog.pure address).bind fun _ => Prog.pure (.ok ())).bind checkNext) = _
      simp only [Prog.bind_assoc, Prog.pure_bind']
      rfl
    | some child =>
      let field : Nat → Session grow sig (Except RecordLower.Issue Unit) := fun ptr =>
        Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width child 0 (.memory ptr)
      change check.control (((body.bind fun () => Prog.pure address).bind fun ptr =>
        (field ptr).bind fun verdict => Prog.pure (verdict.mapError (.nested index))).bind checkNext) = _
      simp only [Prog.bind_assoc, Prog.pure_bind']
      rfl
  have focus : right.ctl = canon.control (.op .get (fun store => body.bind (resumed (ptrTypeIn store cx)))) := by
    rw [canonAt, CanonicalTree.field]
    congr 1
    change (Prog.op (S := Eff (core3 grow) (HostState sig)) .get _).bind canonNext = _
    apply congrArg (Prog.op (S := Eff (core3 grow) (HostState sig)) .get)
    funext store
    let ptr := sumPayloadAddress (ptrTypeIn store cx) arms base
    cases selected with
    | none =>
      change (((body.bind fun () => Prog.pure ptr).bind fun _ => Prog.pure ()).bind canonNext) = _
      simp only [Prog.bind_assoc, Prog.pure_bind']
      rfl
    | some child =>
      let field : Nat → Session grow sig Unit := fun ptr =>
        CanonicalTree.field Limits.spec Quirks.none cx destination.width child (.memory ptr)
      change (((body.bind fun () => Prog.pure ptr).bind field).bind canonNext) = _
      simp only [Prog.bind_assoc, Prog.pure_bind']
      rfl
  have read : Step profile scheduledReady scheduledDispatch right .tau entered := by
    simpa only [entered, Cursor.control, show ptrTypeIn right.store cx = destination.width from width] using
      (Step.get (prof := profile) (hr := scheduledReady) (dispatch := scheduledDispatch) focus)
  have localBody := closedIntKeeping (profile := profile) (Host := HostState sig)
    (keep := fun store => Core3.Grows origin.core store.core)
    (fun store memory ptr data growing => growing.trans (writeMemSt_grows store memory ptr data))
    cx tag base (discSize arms.length)
  obtain ⟨store, result, chk, ref, runChk, runRef, labels, status⟩ := closedCut (profile := profile)
    (ready := scheduledReady) (dispatch := scheduledDispatch) localBody left entered check canon checked (resumed destination.width)
    growth same thread checkBody rfl
  have final : localLeafEnd entered entered.host store canon.thread canon.frames canon.rest (resumed destination.width) result =
      localLeafEnd right right.host store canon.thread canon.frames canon.rest (resumed destination.width) result := by cases result <;> rfl
  rw [final] at runRef
  refine ⟨store, result, chk, .tau :: ref, runChk, .cons ?_ read runRef, labels, ?_⟩
  · simp only [LocalFocus, focus, Cursor.control]
  · cases result with
    | error _ => exact status
    | ok _ =>
      obtain ⟨kept, checkTrack, canonTrack⟩ := status
      refine ⟨kept, checkTrack, ?_⟩
      intro depth
      have tracked := canonTrack depth
      rw [final] at tracked
      exact .step read (by rw [ReturnFrame.Occurrence.transitionEdit, focus]; rfl) tracked

theorem memoryHandleLeaf (destination : RecordDestination) (inst : InstId) (field : Field) (index ptr : Nat)
    (fragment : CanonicalHandle field) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        field index (.memory ptr))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width field (.memory ptr)) := by
  cases field with
  | owner _ | endpoint _ _ _ | context _ =>
    rw [Record.Effects.field, CanonicalTree.field]
    exact handle destination inst _ fragment index (.memory ptr)
  | _ => exact False.elim fragment

theorem memoryHandleRoot (destination : RecordDestination) (inst : InstId) (field : Field) (index ptr : Nat)
    (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn right.store (destination.context inst) = destination.width) (fragment : MemoryHandleRoot field) :
    CompareAt profile scheduledReady scheduledDispatch left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        field index (.memory ptr))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width field (.memory ptr)) := by
  cases field with
  | owner _ | endpoint _ _ _ | context _ => exact memoryHandleLeaf destination inst _ index ptr (by trivial) left right
  | sum type arms tag selected =>
    apply memorySum destination inst type arms tag index ptr selected left right width
    cases selected with
    | none => intro item address impossible; contradiction
    | some active =>
      intro item address same
      cases same
      exact memoryHandleLeaf destination inst active 0 address fragment
  | _ => exact False.elim fragment

theorem flatSum (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (arms : List (Option TypeOf)) (tag index : Nat) (selected : Option Field) (valid : tag < arms.length)
    (child : ∀ item, selected = some item → Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item 0 .flat)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item .flat)) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) index .flat)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) .flat) := by
  cases selected with
  | none =>
    rw [Record.Effects.field, CanonicalTree.field]
    exact variantTail arms.length ((flatten destination.width type).drop 1) tag [] []
  | some item =>
    rw [Record.Effects.field, CanonicalTree.field]
    let wanted := (flatten destination.width type).drop 1
    let haves := flatten destination.width item.type
    have placed := guardedTail (child item rfl) (.nested index)
      (fun words => do return .ok (← lowerFlatVariantWith arms.length wanted tag haves (pure words)))
      (fun words => lowerFlatVariantWith arms.length wanted tag haves (pure words))
      (variantTail arms.length wanted tag haves)
    simp only [Lower.Output.Result, lowerFlatVariantWith, valid, ↓reduceIte, Prog.bind_eq, Prog.bind_assoc,
      Prog.pure_eq, Prog.pure_bind'] at placed ⊢
    convert placed using 2
    funext verdict
    cases verdict <;> rfl

mutual
theorem flatField (destination : RecordDestination) (inst : InstId) (item : Field)
    (fragment : HandleField item) (index : Nat) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item index .flat)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item .flat) := by
  cases item with
  | aggregate type children | fixed type size children =>
    simp only [HandleField, HandleFieldWhere] at fragment
    have compared := flatFields destination inst children fragment 0
    rw [Record.Effects.field, CanonicalTree.field]
    simpa only [Lower.Output.Result, map_id, id_eq, Prog.bind_eq, Prog.pure_eq, Prog.bind_pure] using
      mapResult compared id (.nested index)
  | owner _ | endpoint _ _ _ | context _ =>
    rw [Record.Effects.field, CanonicalTree.field]
    exact handle destination inst _ fragment index .flat
  | sum type arms tag selected =>
    simp only [HandleField, HandleFieldWhere] at fragment
    apply flatSum destination inst type arms tag index selected fragment.1
    cases selected with
    | none => intro item impossible; contradiction
    | some active =>
      intro item same
      cases same
      exact flatField destination inst active fragment.2 0
  | data _ _ | dynamic _ _ _ => exact False.elim fragment
termination_by structural item

theorem flatFields (destination : RecordDestination) (inst : InstId) (items : List Field)
    (fragment : HandleFieldsWhere Nat.lt items) (index : Nat) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.flat recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width items index)
      (CanonicalTree.flat Limits.spec Quirks.none (destination.context inst) destination.width items) := by
  cases items with
  | nil => rw [Record.Effects.flat, CanonicalTree.flat]; exact returned []
  | cons child rest =>
    rw [HandleFieldsWhere] at fragment
    rw [Record.Effects.flat, CanonicalTree.flat]
    have first := flatField destination inst child fragment.1 index
    have later := flatFields destination inst rest fragment.2 (index + 1)
    have composed := sequential first _ _ (fun words => by
      let headWords : List FlatValue := words
      simpa only [mapError_id] using mapResult later (headWords ++ ·) id)
    convert composed using 2 <;> try rfl
    funext verdict
    cases verdict <;> rfl
termination_by structural items
end

theorem flatFieldsPrepend (destination : RecordDestination) (inst : InstId) (items : List Field)
    (fragment : HandleFieldsWhere Nat.lt items) (index : Nat) (words : List FlatValue) :
    Compare profile scheduledReady scheduledDispatch
      (do return (← Record.Effects.flat recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width items index).map (words ++ ·))
      (do return words ++ (← CanonicalTree.flat Limits.spec Quirks.none (destination.context inst)
        destination.width items)) := by
  simpa only [mapError_id] using mapResult (flatFields destination inst items fragment index) (words ++ ·) id

theorem certifyField {field : Field} {type : TypeOf} (layout : Field.LayoutMatches field type)
    (fragment : HandleShape field) : HandleField field := by
  exact Field.LayoutMatches.rec
    (motive_1 := fun item _ _ => HandleShape item → HandleField item)
    (motive_2 := fun fields _ _ => HandleFieldsWhere (fun _ _ => True) fields → HandleFieldsWhere Nat.lt fields)
    (motive_3 := fun fields _ _ => HandleFieldsWhere (fun _ _ => True) fields → HandleFieldsWhere Nat.lt fields)
    (motive_4 := fun arm _ _ => HandleArmWhere (fun _ _ => True) arm → HandleArmWhere Nat.lt arm)
    (fun _ bad => False.elim bad)
    (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
    (fun _ children => children) (fun _ children => children) (fun _ _ children => children)
    (fun _ _ bad => False.elim bad) (fun _ _ bad => False.elim bad)
    (fun found _ active shape => ⟨(List.getElem?_eq_some_iff.mp found).1, active shape.2⟩)
    (fun _ => ⟨show 0 < 2 by decide, trivial⟩)
    (fun _ active shape => ⟨show 1 < 2 by decide, active shape.2⟩)
    (fun _ active shape => ⟨show 0 < 2 by decide, active shape.2⟩)
    (fun _ active shape => ⟨show 1 < 2 by decide, active shape.2⟩)
    (fun _ => trivial) (fun _ _ child rest shape => ⟨child shape.1, rest shape.2⟩)
    (fun _ => trivial) (fun _ _ child rest shape => ⟨child shape.1, rest shape.2⟩)
    (fun _ => trivial) (fun _ child => child) layout fragment

private theorem prependCheck {left entered right : Config E Host} {labels : List (Label E Host)}
    {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (entry : Steps profile ready dispatch left labels entered) (allTau : ∀ label ∈ labels, label = .tau)
    (continued : Reaches profile ready dispatch entered right checkCursor canonCursor checkNext canonNext) :
    Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext := by
  obtain ⟨outcome, chk, ref, left', right', runChk, runRef, stores, observations, status⟩ := continued
  refine ⟨outcome, labels ++ chk, ref, left', right', chain entry runChk, runRef, stores, ?_, ?_⟩
  · rw [visible_append, silent allTau, List.nil_append, observations]
  · cases outcome <;> exact status

private theorem prependCheckKeeping {left entered right : Config E Host} {labels : List (Label E Host)}
    {keep : CStore E → Prop} {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (entry : Steps profile ready dispatch left labels entered) (allTau : ∀ label ∈ labels, label = .tau)
    (continued : ReachesKeeping profile ready dispatch keep entered right checkCursor canonCursor checkNext canonNext) :
    ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor checkNext canonNext := by
  obtain ⟨outcome, chk, ref, left', right', runChk, runRef, stores, observations, kept, status⟩ := continued
  refine ⟨outcome, labels ++ chk, ref, left', right', chain entry runChk, runRef, stores, ?_, kept, status⟩
  rw [visible_append, silent allTau, List.nil_append, observations]

theorem prependKeeping {left left' right right' : Config E Host} {checkLabels canonLabels : List (Label E Host)}
    {keep : CStore E → Prop} {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (lhs : Steps profile ready dispatch left checkLabels left') (rhs : Steps profile ready dispatch right canonLabels right')
    (seen : visible checkLabels = visible canonLabels)
    (rest : ReachesKeeping profile ready dispatch keep left' right' checkCursor canonCursor checkNext canonNext) :
    ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor checkNext canonNext := by
  obtain ⟨outcome, checkTail, canonTail, checkEnd, canonEnd, checkRun, canonRun, stores, same, kept, status⟩ := rest
  refine ⟨outcome, checkLabels ++ checkTail, canonLabels ++ canonTail, checkEnd, canonEnd,
    chain lhs checkRun, chain rhs canonRun, stores, ?_, kept, ?_⟩
  · rw [visible_append, visible_append, seen, same]
  · cases outcome with
    | returned _ | refused _ => exact status
    | trapped _ =>
      obtain ⟨checkDone, canonDone, leading, trapLabel⟩ := status
      exact ⟨checkDone, canonDone, visible canonLabels ++ leading, by rw [visible_append, trapLabel, List.append_assoc]⟩

theorem prepend {left left' right right' : Config E Host} {checkLabels canonLabels : List (Label E Host)}
    {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (lhs : Steps profile ready dispatch left checkLabels left') (rhs : Steps profile ready dispatch right canonLabels right')
    (seen : visible checkLabels = visible canonLabels)
    (rest : Reaches profile ready dispatch left' right' checkCursor canonCursor checkNext canonNext) :
    Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext :=
  forgetKeeping (prependKeeping lhs rhs seen (rememberTrue rest))

private theorem collectionElements (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (stride ptr index : Nat) (compared : ∀ item ∈ entries, ∀ address pos,
      Compare profile scheduledReady scheduledDispatch
        (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
          item pos (.memory address))
        (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.elements recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        entries stride ptr index)
      (CanonicalTree.elements Limits.spec Quirks.none (destination.context inst) destination.width entries
        .value stride ptr) := by
  induction entries generalizing ptr index with
  | nil => rw [Record.Effects.elements, CanonicalTree.elements]; exact returned ()
  | cons item rest ih =>
    rw [Record.Effects.elements, CanonicalTree.elements]
    have head := compared item (List.mem_cons_self ..) ptr index
    have tail := ih (ptr + stride) (index + 1)
      (fun entry member => compared entry (List.mem_cons_of_mem _ member))
    have paired := sequential head _ _ (fun _ => tail)
    convert paired using 2 <;> try rfl
    funext verdict
    cases verdict with
    | ok value => cases value; rfl
    | error _ => rfl

private theorem collectionTail (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index ptr : Nat)
    (compared : ∀ item ∈ entries, ∀ address pos, Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        item pos (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    Compare profile scheduledReady scheduledDispatch
      (checkedCollectionTail destination inst entries area index output ptr (.ok ()))
      (canonicalCollectionTail destination inst entries area output ptr) := by
  let publish := (ListLower.publish (destination.context inst) destination.width ptr entries.length output : Session grow sig output.Result)
  have paired := guardedTail (collectionElements destination inst entries area.size ptr 0 compared) (.nested index)
    (fun _ => do return .ok (← publish)) (fun _ => publish)
    (fun _ => descriptor (destination.context inst) destination.width ptr entries.length output)
  unfold checkedCollectionTail canonicalCollectionTail
  convert paired using 2
  funext verdict
  cases verdict with
  | ok value => cases value; rfl
  | error _ => rfl

theorem collectionReturnKeepingAt (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat)
    (left right : Config (core3 grow) (HostState sig)) (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (checkResume canonResume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (paired : HostFrame.Paired checkResume canonResume left right) (sameThread : checkCursor.thread = canonCursor.thread)
    (leftAt : left.ctl = { checkCursor with frames := .prog checkResume :: checkCursor.frames }.control (pure (.nat pointer)))
    (rightAt : right.ctl = { canonCursor with frames := .prog canonResume :: canonCursor.frames }.control (pure (.nat pointer)))
    (checkBody : checkResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : canonResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    {bytes : Nat} (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    {keep : CStore (core3 grow) → Prop}
    (compared : CollectionTailKeepingAt profile scheduledReady scheduledDispatch keep destination inst entries area output index
      pointer bytes left right) :
    ReachesKeeping profile scheduledReady scheduledDispatch keep left right checkCursor canonCursor checkNext canonNext := by
  rcases checkCursor with ⟨thread, checkFrames, checkRest⟩
  rcases canonCursor with ⟨otherThread, canonFrames, canonRest⟩
  change thread = otherThread at sameThread
  subst otherThread
  let checkSuffix := fun ptr live => checkedCollectionTail destination inst entries area index output ptr live >>= checkNext
  let canonSuffix := fun ptr => canonicalCollectionTail destination inst entries area output ptr >>= canonNext
  have prefixed := destination.paired_range_recheck (profile := profile) (ready := scheduledReady)
    (dispatch := scheduledDispatch) paired inst area entries.length pointer (Field.listObjects entries)
    checkSuffix canonSuffix checkBody canonBody leftAt rightAt sized
  have finishTrap (reason : TrapReason)
      (leftRun : ∃ count, Steps profile scheduledReady scheduledDispatch left (List.replicate count .tau ++ [.trap reason])
        (StepDefs.trapCfg left))
      (rightRun : ∃ count, Steps profile scheduledReady scheduledDispatch right (List.replicate count .tau ++ [.trap reason])
        (StepDefs.trapCfg right)) :
      ReachesKeeping profile scheduledReady scheduledDispatch keep left right ⟨thread, checkFrames, checkRest⟩
        ⟨thread, canonFrames, canonRest⟩ checkNext canonNext := by
    obtain ⟨leftCount, checkSteps⟩ := leftRun
    obtain ⟨rightCount, canonSteps⟩ := rightRun
    have hide (count : Nat) : visible (List.replicate count .tau ++ [.trap reason] : List (Label (core3 grow) (HostState sig))) =
        [.trap reason] := trace (outcome := (.error reason : Except TrapReason Unit)) ⟨count, rfl⟩
    exact ⟨.trapped reason, _, _, _, _, checkSteps, canonSteps, congrArg StepDefs.lockdownSt paired.data.1,
      (hide leftCount).trans (hide rightCount).symm, trivial, rfl, rfl, [], hide rightCount⟩
  dsimp only at prefixed
  by_cases aligned : pointer ≠ alignTo pointer area.alignment
  · simp only [ite_eq_left aligned] at prefixed
    exact finishTrap .unalignedPointer prefixed.1 prefixed.2
  by_cases fits : pointer + entries.length * area.size ≤ bytes
  · simp only [ite_eq_right aligned, ite_eq_left fits] at prefixed
    obtain ⟨⟨checkLabels, checkSilent, checkTracks⟩, ⟨canonLabels, canonSilent, canonTracks⟩⟩ := prefixed
    have checkSteps := (ReturnFrame.Occurrence.prefix_survives (checkTracks 0)).1
    have canonSteps := (ReturnFrame.Occurrence.prefix_survives (canonTracks 0)).1
    cases verdict : Record.prepare left.store left.host.writer (Field.listObjects entries) with
    | ok passed =>
      cases passed
      rw [verdict] at checkSteps
      let checkEntered := { left with ctl := Cursor.control ⟨thread, checkFrames, checkRest⟩ (checkSuffix pointer (.ok ())) }
      let canonEntered := { right with ctl := Cursor.control ⟨thread, canonFrames, canonRest⟩ (canonSuffix pointer) }
      have continued := compared (Classical.not_not.mp aligned) fits verdict checkEntered canonEntered rfl rfl rfl rfl
        paired.data.1 ⟨thread, checkFrames, checkRest⟩ ⟨thread, canonFrames, canonRest⟩ rfl checkNext canonNext rfl rfl
      exact prependKeeping checkSteps canonSteps ((silent checkSilent).trans (silent canonSilent).symm) continued
    | error issue =>
      rw [verdict] at checkSteps
      cases issue <;> exact ⟨.refused _, checkLabels, canonLabels, _, _, checkSteps, canonSteps,
        paired.data.1, (silent checkSilent).trans (silent canonSilent).symm, trivial, rfl⟩
  · simp only [ite_eq_right aligned, ite_eq_right fits] at prefixed
    exact finishTrap .outOfBounds prefixed.1 prefixed.2

theorem collectionReturnAt (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat)
    (left right : Config (core3 grow) (HostState sig)) (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (checkResume canonResume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (paired : HostFrame.Paired checkResume canonResume left right) (sameThread : checkCursor.thread = canonCursor.thread)
    (leftAt : left.ctl = { checkCursor with frames := .prog checkResume :: checkCursor.frames }.control (pure (.nat pointer)))
    (rightAt : right.ctl = { canonCursor with frames := .prog canonResume :: canonCursor.frames }.control (pure (.nat pointer)))
    (checkBody : checkResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : canonResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    {bytes : Nat} (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (compared : CollectionTailAt profile scheduledReady scheduledDispatch destination inst entries area output index
      pointer bytes left right) :
    Reaches profile scheduledReady scheduledDispatch left right checkCursor canonCursor checkNext canonNext := by
  apply forgetKeeping (keep := fun _ => True)
  apply collectionReturnKeepingAt destination inst entries area output index pointer left right checkCursor canonCursor
    checkNext canonNext checkResume canonResume paired sameThread leftAt rightAt checkBody canonBody sized
  intro aligned fits live checked canonical checkStore canonStore checkHost canonHost same check canon thread finish next checkAt canonAt
  exact rememberTrue (compared aligned fits live checked canonical checkStore canonStore checkHost canonHost
    same check canon thread finish next checkAt canonAt)

theorem collectionTailFromChildren (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer bytes : Nat) (left right : Config (core3 grow) (HostState sig))
    (compared : ∀ item ∈ entries, ∀ address pos, Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        item pos (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    CollectionTailAt profile scheduledReady scheduledDispatch destination inst entries area output index pointer bytes left right :=
  fun _ _ _ checked canonical _ _ _ _ => collectionTail destination inst entries area output index pointer compared checked canonical

theorem collectionCallback (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index : Nat)
    {left right last : Config (core3 grow) (HostState sig)} {labels}
    (callback : CoreGrowthSteps profile scheduledReady scheduledDispatch left labels last)
    (destinationChecked : destination.check left.store = .ok ()) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {checkResume canonResume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (paired : HostFrame.Paired checkResume canonResume left right)
    (checkBody : ∀ pointer, checkResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : ∀ pointer, canonResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    (compared : ∀ item ∈ entries, ∀ address pos, Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        item pos (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    (∃ other, CoreGrowthSteps profile scheduledReady scheduledDispatch right labels other ∧ HostFrame.Paired checkResume canonResume last other) ∨
    (∃ leading label trailing atLeft atRight afterLeft afterRight,
      labels = leading ++ label :: trailing ∧ CoreGrowthSteps profile scheduledReady scheduledDispatch left leading atLeft ∧
      CoreGrowthSteps profile scheduledReady scheduledDispatch right leading atRight ∧ HostFrame.Paired checkResume canonResume atLeft atRight ∧
      Step profile scheduledReady scheduledDispatch atLeft label afterLeft ∧ Step profile scheduledReady scheduledDispatch atRight label afterRight ∧
      CoreGrowthSteps profile scheduledReady scheduledDispatch afterLeft trailing last ∧
      ((∃ alternate, HostFrame.ReadCut atLeft atRight.host label afterLeft alternate ∧
          ReturnFrame.Paired checkResume canonResume alternate afterRight) ∨
       (∃ thread value frames rest,
          (∀ pointer, value ≠ .nat pointer) ∧
          atLeft.ctl = ⟨thread, .prog (.pure value), .prog checkResume :: frames⟩ :: rest ∧
          ReturnFrame.Returned checkResume canonResume (HostFrame.replace atLeft atRight.host) atRight label
            (HostFrame.replace afterLeft atRight.host) afterRight) ∨
       (∃ (pointer : Nat) (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig)),
          atLeft.ctl = { checkCursor with frames := .prog checkResume :: checkCursor.frames }.control (pure (.nat pointer)) ∧
          atRight.ctl = { canonCursor with frames := .prog canonResume :: canonCursor.frames }.control (pure (.nat pointer)) ∧
          canonCursor.thread = checkCursor.thread ∧
          Reaches profile scheduledReady scheduledDispatch left right checkCursor canonCursor checkNext canonNext))) := by
  rcases HostFrame.paired_growing_steps paired callback with replayed |
    ⟨leading, label, trailing, atLeft, atRight, afterLeft, afterRight, split, lhs, rhs, reached, cut, leftStep, rightStep, suffix⟩
  · exact .inl replayed
  refine .inr ⟨leading, label, trailing, atLeft, atRight, afterLeft, afterRight, split,
    lhs, rhs, reached, leftStep, rightStep, suffix, ?_⟩
  cases cut with
  | read differs otherAligned => exact .inl ⟨_, differs, otherAligned⟩
  | returned popped =>
    obtain ⟨thread, value, leftFrames, rightFrames, leftRest, rightRest, atChecked, atCanonical⟩ :=
      ReturnFrame.Returned.inputs popped
    cases value with
    | unit | flat _ | vals _ | optVals _ | cancel _ | thread _ | invoked _ _ | items _ =>
      exact .inr (.inl ⟨thread, _, leftFrames, leftRest, by simp, atChecked, popped⟩)
    | nat pointer =>
      let checkCursor : Cursor (E := core3 grow) (HostState sig) := ⟨thread, leftFrames, leftRest⟩
      let canonCursor : Cursor (E := core3 grow) (HostState sig) := ⟨thread, rightFrames, rightRest⟩
      have region := lhs.linked_region (destination.context inst) (start := 0) (length := 0)
        rfl (destination.check_width left.store destinationChecked) sized (by simp)
      obtain ⟨_, reachedSize, _, _⟩ := region.2.2
      have continued := collectionReturnAt destination inst entries area output index pointer atLeft atRight
        checkCursor canonCursor checkNext canonNext checkResume canonResume reached rfl atChecked atCanonical
        (checkBody pointer) (canonBody pointer) reachedSize
        (collectionTailFromChildren destination inst entries area output index pointer _ atLeft atRight compared)
      exact .inr (.inr ⟨pointer, checkCursor, canonCursor, atChecked, atCanonical, rfl,
        prepend lhs.steps rhs.steps rfl continued⟩)

theorem dynamicRefusal (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (left right : Config (core3 grow) (HostState sig)) (cursor canonCursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : left.store = right.store) (issue : RecordLower.Issue)
    (refused : Record.prepare left.store left.host.writer (Field.listObjects entries) = .error issue)
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    {keep : CStore (core3 grow) → Prop} :
    ReachesKeeping profile scheduledReady scheduledDispatch keep left right cursor canonCursor checkNext canonNext := by
  let cx := destination.context (grow := grow) inst
  let checked := fun verdict : Except RecordLower.Issue Unit =>
    (match verdict with
     | .error (.preflight issue) => pure (.error (.field index (.beforeAllocation issue)))
     | .error issue => pure (.error (.nested index issue))
     | .ok () => do
        let area := layout destination.width element
        let ptr ← allocateListRange cx area entries.length
        let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
        checkedCollectionTail destination inst entries area index output ptr live) >>= checkNext
  have getAt : left.ctl = cursor.control (.op .get fun store => .op .hostGet fun host =>
      checked (Record.prepare store host.writer (Field.listObjects entries))) := by
    rw [Record.Effects.field] at checkAt
    exact checkAt
  let afterRead := { left with ctl := cursor.control (checked (Record.prepare left.store left.host.writer (Field.listObjects entries))) }
  have run : Steps profile scheduledReady scheduledDispatch left [.tau, .tau] afterRead :=
    .cons (.get getAt) (.cons (.hostGet rfl) (.refl _))
  have stop : afterRead.ctl = cursor.control (checked (.error issue)) := by simp only [afterRead, refused]
  cases issue <;> exact ⟨.refused _, _, [], _, right, run, .refl _, same, rfl, trivial, stop⟩

theorem collectionInstallTracks (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (reachedWidth : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    let checkCall := collectionEntry destination inst area entries.length scheduledDispatch left check checkResume
    let canonCall := collectionEntry destination inst area entries.length scheduledDispatch right canon canonResume
    ∀ depth, ReturnFrame.Occurrence.Prefix profile scheduledReady scheduledDispatch left (.active 0 depth)
      [.tau, .tau, .tau] checkCall (.active 0 (depth + 1)) ∧
    ReturnFrame.Occurrence.Prefix profile scheduledReady scheduledDispatch right (.active 0 depth)
      [.tau, .tau] canonCall (.active 0 (depth + 1)) := by
  let cx := destination.context (grow := grow) inst
  let area := layout destination.width element
  have width : ptrTypeIn right.store (destination.context inst) = destination.width := by
    simp [ptrTypeIn, RecordDestination.context, CanonOpts.ptrType, reachedWidth]
  let liveObjects := Field.listObjects entries
  let checkedTail := fun ptr => do
    let live ← Record.Effects.reserve recordClaims liveObjects
    checkedCollectionTail destination inst entries area index output ptr live >>= checkNext
  let preflightBranch := fun (verdict : Except RecordLower.Issue Unit) =>
    (match verdict with
     | .error (.preflight issue) => pure (.error (.field index (.beforeAllocation issue)))
     | .error issue => pure (.error (.nested index issue))
     | .ok () => do
        let ptr ← allocateListRange cx area entries.length
        let live ← Record.Effects.reserve recordClaims liveObjects
        checkedCollectionTail destination inst entries area index output ptr live) >>= checkNext
  have checkRead : left.ctl = check.control (.op .get fun store => .op .hostGet fun host =>
      preflightBranch (Record.prepare store host.writer liveObjects)) := by
    rw [Record.Effects.field] at checkAt
    exact checkAt
  let checkEntered := { left with ctl := check.control (preflightBranch (Record.prepare left.store left.host.writer liveObjects)) }
  have checkAlloc : checkEntered.ctl = check.control (allocateListRange cx area entries.length >>= checkedTail) := by
    simp only [checkEntered, liveObjects, preflightBranch, prepared, checkedTail, Prog.bind_eq, Prog.bind_assoc]
  let canonTail := fun ptr => canonicalCollectionTail destination inst entries area output ptr
    (CanonicalTree.EntryMode.forOutput destination.width type output) >>= canonNext
  let canonProgram : AddrType → Session grow sig output.Result := fun reached => do
    let shape := layout reached element
    let ptr ← allocateListRange cx shape entries.length
    CanonicalTree.elements Limits.spec Quirks.none cx destination.width entries
      (CanonicalTree.EntryMode.forOutput reached type output) shape.size ptr
    ListLower.publish cx destination.width ptr entries.length output
  have canonRead : right.ctl = canon.control (.op .get fun store => canonProgram (ptrTypeIn store cx) >>= canonNext) := by
    rw [CanonicalTree.field] at canonAt
    exact canonAt
  let canonEntered := { right with ctl := canon.control (canonProgram (ptrTypeIn right.store cx) >>= canonNext) }
  have canonStep : Step profile scheduledReady scheduledDispatch right .tau canonEntered := .get canonRead
  have canonAlloc : canonEntered.ctl = canon.control (allocateListRange cx area entries.length >>= canonTail) := by
    simp only [canonEntered, cx, area, canonProgram, width, canonTail, canonicalCollectionTail, Prog.bind_eq, Prog.bind_assoc]
  have checkInstall := listRange_install
    (profile := profile) (ready := scheduledReady) (dispatch := scheduledDispatch) cx area entries.length checkedTail checkAlloc
  have canonInstall := listRange_install
    (profile := profile) (ready := scheduledReady) (dispatch := scheduledDispatch) cx area entries.length canonTail canonAlloc
  dsimp only
  intro depth
  refine ⟨.step (middle := .active 0 depth) (.get checkRead) ?_
      (.step (middle := .active 0 depth) (.hostGet rfl) rfl (.step checkInstall ?_ (.done _ _))),
    .step (middle := .active 0 depth) canonStep ?_ (.step canonInstall ?_ (.done _ _))⟩
  · rw [ReturnFrame.Occurrence.transitionEdit, checkRead]
    rfl
  · change (ReturnFrame.Occurrence.transitionEdit checkEntered .tau).follow _ = _
    rw [ReturnFrame.Occurrence.transitionEdit, checkAlloc, listRange_focus]
    rfl
  · rw [ReturnFrame.Occurrence.transitionEdit, canonRead]
    rfl
  · rw [ReturnFrame.Occurrence.transitionEdit, canonAlloc, listRange_focus]
    rfl

theorem collectionInstallMode (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (left right : Config (core3 grow) (HostState sig)) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (reachedWidth : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    let checkCall := collectionEntry destination inst area entries.length scheduledDispatch left cursor checkResume
    let canonCall := collectionEntry destination inst area entries.length scheduledDispatch right cursor canonResume
    Machine.Steps profile scheduledReady scheduledDispatch left [.tau, .tau, .tau] checkCall ∧
    Machine.Steps profile scheduledReady scheduledDispatch right [.tau, .tau] canonCall ∧
    HostFrame.Paired checkResume canonResume checkCall canonCall := by
  obtain ⟨checked, canonical⟩ := collectionInstallTracks destination inst type element entries output index
    left right cursor cursor checkNext canonNext reachedWidth prepared checkAt canonAt 0
  refine ⟨(ReturnFrame.Occurrence.prefix_survives checked).1, (ReturnFrame.Occurrence.prefix_survives canonical).1, ?_⟩
  dsimp only [collectionEntry, HostFrame.Paired]
  conv => rhs; rw [← same]
  exact ReturnFrame.installed (HostFrame.replace left right.host) cursor.thread _ cursor.frames cursor.rest

theorem collectionInstall (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (left right : Config (core3 grow) (HostState sig)) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (reachedWidth : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (mode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
    let checkCall := collectionEntry destination inst area entries.length scheduledDispatch left cursor checkResume
    let canonCall := collectionEntry destination inst area entries.length scheduledDispatch right cursor canonResume
    Steps profile scheduledReady scheduledDispatch left [.tau, .tau, .tau] checkCall ∧
    Steps profile scheduledReady scheduledDispatch right [.tau, .tau] canonCall ∧
    HostFrame.Paired checkResume canonResume checkCall canonCall := by
  simpa only [mode] using collectionInstallMode destination inst type element entries output index left right cursor
    checkNext canonNext same reachedWidth prepared checkAt canonAt

theorem checkPlacementRun {placementDispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    (destination : RecordDestination) (inst : InstId)
    (start : Config (core3 grow) Host) (area : Layout) (ptr : Nat) (cursor : Cursor (E := core3 grow) Host)
    (finish : P (core3 grow) Host (Ret (core3 grow)))
    (focused : start.ctl = cursor.control (do
      checkAligned ptr area.alignment.bytes
      checkInBounds (destination.context inst) ptr area.size
      finish)) :
    match placement destination start.store area ptr with
    | .ok () => ReturnFrame.Occurrence.RetainsActiveSlots profile ready placementDispatch start [.tau]
        { start with ctl := cursor.control finish }
    | .error reason => ∃ count, Machine.Steps profile ready placementDispatch start
        (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg start) := by
  by_cases aligned : ptr % area.alignment.bytes = 0
  · let sizeCheck := fun (store : CStore (core3 grow)) =>
      (orTrap (.internal "dangling memory address") ((core3 grow).memSize? store.core destination.memory) >>=
        fun size => trapIf (decide (ptr + area.size > size)) .outOfBounds) >>= fun _ => finish
    have getAt : start.ctl = cursor.control (.op .get sizeCheck) := by
      have boundsAt : start.ctl = cursor.control (checkInBounds (destination.context inst) ptr area.size >>= fun _ => finish) := by
        simpa [checkAligned, trapIf, aligned] using focused
      exact boundsAt
    let read := Step.get (prof := profile) (hr := ready) (dispatch := placementDispatch) getAt
    cases sized : (core3 grow).memSize? start.store.core destination.memory with
    | none =>
      have trapAt : sizeCheck start.store = trap (.internal "dangling memory address") := by
        simp [sizeCheck, sized, orTrap, trap, Prog.bind_eq, Prog.bind]
        congr 1
        funext answer
        exact nomatch answer
      simp [placement, aligned, sized]
      exact ⟨1, .cons read (.cons (.trap (congrArg cursor.control trapAt)) (.refl _))⟩
    | some size =>
      by_cases fits : ptr + area.size ≤ size
      · have done : sizeCheck start.store = finish := by
          simp [sizeCheck, sized, orTrap, trapIf, Nat.not_lt.mpr fits]
        simp [placement, aligned, sized, Nat.not_lt.mpr fits]
        intro depth
        simpa only [done, Cursor.control] using
          (ReturnFrame.Occurrence.Prefix.read (profile := profile) (ready := ready) (dispatch := placementDispatch) depth getAt)
      · have trapAt : sizeCheck start.store = trap .outOfBounds := by
          simp [sizeCheck, sized, orTrap, trapIf, Nat.lt_of_not_ge fits, trap, Prog.bind_eq, Prog.bind]
          congr 1
          funext answer
          exact nomatch answer
        simp [placement, aligned, sized, Nat.lt_of_not_ge fits]
        exact ⟨1, .cons read (.cons (.trap (congrArg cursor.control trapAt)) (.refl _))⟩
  · simp [checkAligned, trapIf, aligned, trap, Prog.bind_eq, Prog.bind] at focused
    simp [placement, aligned]
    exact ⟨0, .cons (.trap focused) (.refl _)⟩

theorem checkPlacement {placementDispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    (destination : RecordDestination) (inst : InstId)
    (start : Config (core3 grow) Host) (area : Layout) (ptr : Nat) (cursor : Cursor (E := core3 grow) Host)
    (finish : P (core3 grow) Host (Ret (core3 grow)))
    (focused : start.ctl = cursor.control (do
      checkAligned ptr area.alignment.bytes
      checkInBounds (destination.context inst) ptr area.size
      finish)) :
    match placement destination start.store area ptr with
    | .ok () => Machine.Steps profile ready placementDispatch start [.tau] { start with ctl := cursor.control finish }
    | .error reason => ∃ count, Machine.Steps profile ready placementDispatch start
        (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg start) := by
  have run := checkPlacementRun (profile := profile) (ready := ready) (placementDispatch := placementDispatch)
    destination inst start area ptr cursor finish focused
  cases placed : placement destination start.store area ptr with
  | error reason => simpa only [placed] using run
  | ok value =>
    cases value
    rw [placed] at run
    exact (ReturnFrame.Occurrence.prefix_survives (run 0)).1

private theorem listEntryBounds (area : Layout) {base count index bytes : Nat}
    (aligned : base = alignTo base area.alignment)
    (bounds : base + count * area.size ≤ bytes) (entry : index < count) :
    (base + index * area.size) % area.alignment.bytes = 0 ∧ base + index * area.size + area.size ≤ bytes := by
  have baseDiv : area.alignment.bytes ∣ base :=
    ⟨(base + area.alignment.bytes - 1) / area.alignment.bytes, aligned.trans (Nat.mul_comm ..)⟩
  have offsetDiv : area.alignment.bytes ∣ index * area.size := ⟨index * area.units, by simp [Layout.size]; ac_rfl⟩
  refine ⟨Nat.mod_eq_zero_of_dvd (Nat.dvd_add baseDiv offsetDiv), ?_⟩
  rw [Nat.add_assoc, ← Nat.succ_mul]
  exact (Nat.add_le_add_left (Nat.mul_le_mul_right area.size (Nat.succ_le_of_lt entry)) base).trans bounds

private theorem listEntryPlacementOfGrowth (destination : RecordDestination) (inst : InstId) (element : TypeOf)
    {before after : CStore (core3 grow)} {base count index bytes : Nat}
    (growth : Core3.Grows before.core after.core)
    (width : (core3 grow).memAddrType? before.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? before.core destination.memory = some bytes)
    (aligned : base = alignTo base (layout destination.width element).alignment)
    (bounds : base + count * (layout destination.width element).size ≤ bytes) (entry : index < count) :
    let area := layout destination.width element
    ptrTypeIn after (destination.context inst) = destination.width ∧
      placement destination after area (base + index * area.size) = .ok () := by
  let area := layout destination.width element
  have reachedWidth : (core3 grow).memAddrType? after.core destination.memory = some destination.width := growth.memAddrType width
  obtain ⟨reachedSize, sized', larger⟩ := growth.memSize sized
  have reached : (core3 grow).memSize? after.core destination.memory = some reachedSize := sized'
  refine ⟨by simp [ptrTypeIn, CanonOpts.ptrType, RecordDestination.context, reachedWidth], ?_⟩
  change placement destination after area (base + index * area.size) = .ok ()
  obtain ⟨modulo, within⟩ := listEntryBounds area aligned bounds entry
  simp [placement, modulo, reached, Nat.not_lt.mpr (within.trans larger)]
  rfl

theorem mapEntryPlacement (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf)
    {origin reached : CStore (core3 grow)} {base count index bytes : Nat}
    (growth : Core3.Grows origin.core reached.core)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : base = alignTo base (layout destination.width (.record (mapEntryFields key element))).alignment)
    (bounds : base + count * (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    (entry : index < count) :
    let keyArea := layout destination.width (.prim key.toPrimitive : TypeOf)
    let valueArea := layout destination.width element
    let address := base + index * (layout destination.width (.record (mapEntryFields key element))).size
    let keyPtr := alignTo address keyArea.alignment
    let valuePtr := alignTo (keyPtr + keyArea.size) valueArea.alignment
    ptrTypeIn reached (destination.context inst) = destination.width ∧
      placement destination reached keyArea keyPtr = .ok () ∧
      placement destination reached valueArea valuePtr = .ok () := by
  let area := layout destination.width (.record (mapEntryFields key element))
  let keyArea := layout destination.width (.prim key.toPrimitive : TypeOf)
  let valueArea := layout destination.width element
  let address := base + index * area.size
  let keyPtr := alignTo address keyArea.alignment
  let valuePtr := alignTo (keyPtr + keyArea.size) valueArea.alignment
  have recordArea : area = recordLayout [keyArea, valueArea] := by
    simp only [area, mapEntryFields, layout, layoutFields, keyArea, valueArea]
  obtain ⟨slotAligned, slotFits⟩ := listEntryBounds area aligned bounds entry
  change address % area.alignment.bytes = 0 at slotAligned
  rw [recordArea] at slotAligned
  have divisor : (recordAlignment [keyArea, valueArea]).bytes ∣ address := Nat.dvd_of_mod_eq_zero slotAligned
  obtain ⟨_, keyAligned, keyFits⟩ := recordLayout_field_fits [keyArea, valueArea] address 0 keyPtr keyArea divisor rfl rfl
  obtain ⟨_, valueAligned, valueFits⟩ := recordLayout_field_fits [keyArea, valueArea] address 1 valuePtr valueArea divisor rfl rfl
  obtain ⟨larger, reachedSize, grows⟩ := growth.memSize sized
  change (core3 grow).memSize? reached.core destination.memory = some larger at reachedSize
  have reachedWidth : (core3 grow).memAddrType? reached.core destination.memory = some destination.width :=
    growth.memAddrType width
  have within : address + (recordLayout [keyArea, valueArea]).size ≤ bytes := by
    simpa only [← recordArea] using slotFits
  have keyWithin : keyPtr + keyArea.size ≤ larger := keyFits.trans (within.trans grows)
  have valueWithin : valuePtr + valueArea.size ≤ larger := valueFits.trans (within.trans grows)
  change ptrTypeIn reached (destination.context inst) = destination.width ∧
    placement destination reached keyArea keyPtr = .ok () ∧ placement destination reached valueArea valuePtr = .ok ()
  refine ⟨?_, ?_, ?_⟩
  · simp [ptrTypeIn, CanonOpts.ptrType, RecordDestination.context, reachedWidth]
  · simp [placement, reachedSize, keyAligned, Nat.not_lt.mpr keyWithin]
    rfl
  · simp [placement, reachedSize, valueAligned, Nat.not_lt.mpr valueWithin]
    rfl

theorem listEntryPlacement {entryDispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    (destination : RecordDestination) (inst : InstId) (element : TypeOf)
    {before after : Config (core3 grow) Host} {labels} {base count index bytes : Nat}
    (run : CoreGrowthSteps profile ready entryDispatch before labels after)
    (checked : destination.check before.store = .ok ())
    (sized : (core3 grow).memSize? before.store.core destination.memory = some bytes)
    (aligned : base = alignTo base (layout destination.width element).alignment)
    (bounds : base + count * (layout destination.width element).size ≤ bytes) (entry : index < count) :
    let area := layout destination.width element
    ptrTypeIn after.store (destination.context inst) = destination.width ∧
      placement destination after.store area (base + index * area.size) = .ok () :=
  listEntryPlacementOfGrowth destination inst element run.grows (destination.check_width before.store checked) sized aligned bounds entry

private theorem primitiveSchema (primitive : WIT.Primitive) : Lower.checkSchema (.prim primitive) = .ok () := by
  let type : TypeOf := .prim primitive
  have well : ABI.ValType.WellFormedCM type := by
    refine ⟨.prim _, rfl, rfl, rfl, ?_⟩
    cases primitive <;> simp [type, ABI.ValType.anySub, oversizedNode, layout, primitiveLayout, pointerLayout,
      pointerAlignment, Layout.size, Alignment.bytes]
  have plain : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.checkSchema type = .ok () := by
    unfold Silmaril.Wasm.Game.HandleAccept.Wit.Stored.checkSchema
    rw [ite_eq_right (show ¬ containsBorrow type = true from Bool.not_eq_true _ |>.mpr rfl),
      ite_eq_right (show ¬ payloadContainsOwn type = true from Bool.not_eq_true _ |>.mpr rfl), ite_eq_left well]
  unfold Lower.checkSchema
  rw [plain]
  rfl

private theorem dataEntry (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (payload : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Payload type) (index : Nat) (output : Lower.Output)
    (start : Config (core3 grow) (HostState sig)) (cursor : Cursor (E := core3 grow) (HostState sig))
    (finish : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (width : ptrTypeIn start.store (destination.context inst) = destination.width)
    (schema : Lower.checkSchema type = .ok ())
    (options : Lower.checkOptions (destination.context (grow := grow) inst) type output = .ok ())
    (fit : Lower.fits Quirks.none destination.encoding destination.width type payload.val = true)
    (placed : rootPlacement destination start.store type output = .ok ())
    (focused : start.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.data type payload) index output >>= finish)) :
    let program := CanonicalTree.field (World := HostState sig) Limits.spec Quirks.none
      (destination.context inst) destination.width (.data type payload) output
    ∃ reads, ReturnFrame.Occurrence.RetainsActiveSlots profile scheduledReady scheduledDispatch start
      (List.replicate reads .tau) { start with ctl := cursor.control (program >>= fun value => finish (.ok value)) } := by
  let cx := destination.context (grow := grow) inst
  have accepted : (Lower.checkSchema type >>= fun _ => Lower.checkOptions cx type output) = .ok () := by
    rw [schema]
    exact options
  let checkedResult := fun verdict : Except Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Issue output.Result =>
    finish (verdict.mapError (.field index ∘ .beforeAllocation ∘ .abi))
  let branch := fun current =>
    if !Lower.fits Quirks.none cx.opts.encoding current type payload.val then
      checkedResult (.error .allocationPrecondition)
    else (Lower.emit Limits.spec Quirks.none cx current type payload output).bind (fun value => finish (.ok value))
  have atRead : start.ctl = cursor.control (.op .get fun store => branch (ptrTypeIn store cx)) := by
    rw [Record.Effects.field, Lower.lower, accepted] at focused
    refine focused.trans (congrArg cursor.control ?_)
    change ((((ptrType cx).bind fun current => if !Lower.fits Quirks.none cx.opts.encoding current type payload.val then
      .pure (.error .allocationPrecondition : Except Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Issue output.Result)
      else (Lower.emit Limits.spec Quirks.none cx current type payload output).bind (fun value => .pure (.ok value))).bind
        fun verdict => .pure (verdict.mapError (.field index ∘ .beforeAllocation ∘ .abi))).bind finish) = _
    simp only [Prog.bind_assoc, Prog.pure_bind']
    change (Prog.op (S := Eff (core3 grow) (HostState sig)) .get (fun store =>
      (if !Lower.fits Quirks.none cx.opts.encoding (ptrTypeIn store cx) type payload.val then
        .pure (.error .allocationPrecondition : Except Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Issue output.Result)
      else (Lower.emit Limits.spec Quirks.none cx (ptrTypeIn store cx) type payload output).bind
        (fun value => .pure (.ok value))).bind checkedResult)) = _
    apply congrArg (Prog.op (S := Eff (core3 grow) (HostState sig)) .get)
    funext store
    unfold branch
    split <;> simp only [Prog.pure_bind', Prog.bind_assoc, checkedResult, Except.mapError]
  let emit := Lower.emit (World := HostState sig) Limits.spec Quirks.none cx destination.width type payload output
  let entered := { start with ctl := cursor.control (emit.bind fun value => finish (.ok value)) }
  have read (depth : Nat) : ReturnFrame.Occurrence.Prefix profile scheduledReady scheduledDispatch start
      (.active 0 depth) [.tau] entered (.active 0 depth) := by
    have reachedFit : Lower.fits Quirks.none cx.opts.encoding destination.width type payload.val = true := fit
    have run := ReturnFrame.Occurrence.Prefix.read (profile := profile) (ready := scheduledReady)
      (dispatch := scheduledDispatch) depth atRead
    simpa only [branch, width, reachedFit, Bool.not_true, Bool.false_eq_true, ↓reduceIte, entered, emit, cx,
      Cursor.control] using run
  cases output with
  | flat => exact ⟨1, read⟩
  | memory address =>
    let body : Session grow sig Unit := store Limits.spec Quirks.none cx payload.val type address
    let next := body.bind fun value => finish (.ok value)
    let area := layout destination.width type
    have placedHere : placement destination entered.store area address = .ok () := placed
    have guarded : entered.ctl = cursor.control (do
        checkAligned address area.alignment.bytes
        checkInBounds cx address area.size
        next) := by
      change cursor.control ((do checkAligned address area.alignment.bytes; checkInBounds cx address area.size; body).bind
        (fun value => finish (.ok value))) = _
      simp only [Prog.bind_eq, Prog.bind_assoc, next]
    have bounds := checkPlacementRun (profile := profile) (ready := scheduledReady) (placementDispatch := scheduledDispatch)
      destination inst entered area address cursor next guarded
    rw [placedHere] at bounds
    exact ⟨2, fun depth => (read depth).append (bounds depth)⟩

theorem stringPlanEntry (destination : RecordDestination) (inst : InstId) (str : Value.StrVal) (valid : str.Valid)
    (index : Nat) (output : Lower.Output) (left right : Config (core3 grow) (HostState sig))
    (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : left.store = right.store)
    (present : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (fit : StoreStringPre Quirks.none destination.encoding destination.width str)
    (placed : rootPlacement destination left.store (.prim .string) output = .ok ())
    (checkAt : left.ctl = checkCursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.data (.prim .string) ⟨.string str, .string valid⟩) index output >>= checkNext))
    (canonAt : right.ctl = canonCursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.data (.prim .string) ⟨.string str, .string valid⟩) output >>= canonNext)) :
    let cx := destination.context inst
    let plan := storePlanFor Quirks.none destination.encoding destination.width str
    let body := runStoreSteps cx 0 plan.steps
    ∃ reads, ReturnFrame.Occurrence.RetainsActiveSlots profile scheduledReady scheduledDispatch left (List.replicate reads .tau)
      { left with ctl := checkCursor.control (body >>= fun ptr => stringPlanTail cx destination.width output plan ptr >>=
          fun value => checkNext (.ok value)) } ∧
      ReturnFrame.Occurrence.RetainsActiveSlots profile scheduledReady scheduledDispatch right [.tau]
        { right with ctl := canonCursor.control (body >>= fun ptr => stringPlanTail cx destination.width output plan ptr >>= canonNext) } := by
  let cx := destination.context (grow := grow) inst
  let payload : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Payload (.prim .string) := ⟨.string str, .string valid⟩
  have width : ptrTypeIn right.store cx = destination.width := by
    simp [cx, ptrTypeIn, RecordDestination.context, CanonOpts.ptrType, present]
  have options : Lower.checkOptions cx (.prim .string) output = .ok () := by
    cases output <;> simp [cx, RecordDestination.context, Lower.checkOptions, Lower.Output.needsMemory,
      Validation.containsPtr, realloc] <;> rfl
  obtain ⟨reads, entered⟩ := dataEntry (profile := profile) (scheduledReady := scheduledReady)
    (scheduledDispatch := scheduledDispatch) destination inst (.prim .string) payload index output left checkCursor checkNext
    (same ▸ width) (primitiveSchema .string) options (by simpa [Lower.fits, payload] using fit) placed checkAt
  let enteredBody := CanonicalTree.field (World := HostState sig) Limits.spec Quirks.none cx destination.width
    (.data (.prim .string) payload) output
  let rest : AddrType → Session grow sig output.Result := fun reached =>
    let plan := storePlanFor Quirks.none destination.encoding reached str
    runStoreSteps cx 0 plan.steps >>= stringPlanTail cx destination.width output plan
  have program : enteredBody = .op .get fun store => rest (ptrTypeIn store cx) := by
    cases output with
    | flat =>
      simp only [enteredBody, CanonicalTree.field, CanonicalTree.leaf, Field.type, Field.value,
        payload, lowerFlatAt, lowerFlatPrim, Canon.storeStringIntoRange, rest, Prog.bind_eq, Prog.bind_assoc]
      rfl
    | memory address =>
      simp only [enteredBody, CanonicalTree.field, CanonicalTree.leaf, Field.type, Field.value,
        payload, Canon.store, storePrim, storeString, Canon.storeStringIntoRange, rest, Prog.bind_eq, Prog.bind_assoc]
      rfl
  change right.ctl = canonCursor.control (enteredBody >>= canonNext) at canonAt
  rw [program] at canonAt
  have reference (depth : Nat) : ReturnFrame.Occurrence.Prefix profile scheduledReady scheduledDispatch right (.active 0 depth)
      [.tau] { right with ctl := canonCursor.control (rest destination.width >>= canonNext) } (.active 0 depth) := by
    simpa only [width, Cursor.control, Prog.bind_eq] using (ReturnFrame.Occurrence.Prefix.read (profile := profile)
      (ready := scheduledReady) (dispatch := scheduledDispatch) depth canonAt)
  change ReturnFrame.Occurrence.RetainsActiveSlots profile scheduledReady scheduledDispatch left (List.replicate reads .tau)
    { left with ctl := checkCursor.control (enteredBody >>= fun value => checkNext (.ok value)) } at entered
  rw [program] at entered
  have checkRead (depth : Nat) : ReturnFrame.Occurrence.Prefix profile scheduledReady scheduledDispatch
      { left with ctl := checkCursor.control ((Prog.op .get fun store => rest (ptrTypeIn store cx)) >>=
          fun value => checkNext (.ok value)) } (.active 0 depth) [.tau]
      { left with ctl := checkCursor.control (rest destination.width >>= fun value => checkNext (.ok value)) } (.active 0 depth) := by
    have reachedWidth : ptrTypeIn left.store cx = destination.width := same ▸ width
    simpa only [Cursor.control, reachedWidth, Prog.bind_eq] using
      (ReturnFrame.Occurrence.Prefix.read (profile := profile) (ready := scheduledReady) (dispatch := scheduledDispatch)
        (before := { left with ctl := checkCursor.control ((Prog.op .get fun store => rest (ptrTypeIn store cx)) >>=
          fun value => checkNext (.ok value)) }) depth rfl)
  refine ⟨reads + 1, ?_, ?_⟩
  · intro depth
    simpa only [List.replicate_add, List.replicate_one, rest, Prog.bind_eq, Prog.bind_assoc] using
      (entered depth).append (checkRead depth)
  · simpa only [rest, Prog.bind_eq, Prog.bind_assoc] using reference

theorem stringReallocFocus (cx : LiftLowerContext E) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep) (finish : Nat → P E Host (Ret E)) :
    let request := Call.reallocate cx (oldSize.elim 0 (fun _ => ptr)) (oldSize.getD 0) alignment.bytes size
    (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= finish) =
        .op (.call request) (stringPlanResume cx steps finish) := by
  let request := Call.reallocate cx (oldSize.elim 0 (fun _ => ptr)) (oldSize.getD 0) alignment.bytes size
  change ((runStoreStep cx ptr (oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) >>=
    fun next => runStoreSteps cx next steps) >>= finish) = _
  have alloc : (runStoreStep cx ptr (oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :
      P E Host Nat) = callNat request := by cases oldSize <;> rfl
  rw [alloc]
  unfold callNat callRet perform Prog.lift
  simp only [Prog.bind_eq, Prog.bind_assoc]
  apply congrArg (Prog.op (S := Eff E Host) (.call request))
  funext result
  simp only [stringPlanResume, Prog.bind_eq]
  cases result <;> rfl

theorem stringReallocInstall (cx : LiftLowerContext E) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep) (finish : Nat → P E Host (Ret E))
    (start : Config E Host) (cursor : Cursor (E := E) Host)
    (focused : start.ctl = cursor.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= finish)) :
    let request := Call.reallocate cx (oldSize.elim 0 (fun _ => ptr)) (oldSize.getD 0) alignment.bytes size
    let resumed := stringPlanResume cx steps finish
    Step profile ready dispatch start .tau
      { start with ctl := { cursor with frames := .prog resumed :: cursor.frames }.control (dispatch request) } := by
  rw [stringReallocFocus cx ptr oldSize alignment size steps finish] at focused
  exact .call focused

private theorem prependLocalCut {left right : Config E Host} {enteredCtl : List (Activation E Host)}
    {leading : List (Label E Host)} {keep : CStore E → Prop} {check canon : Cursor (E := E) Host}
    {checkNext canonNext : Result → P E Host (Ret E)}
    (tracked : ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch left leading { left with ctl := enteredCtl })
    (silent : visible leading = [])
    (cut : LocalCutKeeping profile ready dispatch keep { left with ctl := enteredCtl } right check canon checkNext canonNext) :
    LocalCutKeeping profile ready dispatch keep left right check canon checkNext canonNext := by
  obtain ⟨store, result, chk, ref, runChk, runRef, seen, status⟩ := cut
  have final : localLeafEnd { left with ctl := enteredCtl } left.host store check.thread check.frames check.rest checkNext result =
      localLeafEnd left left.host store check.thread check.frames check.rest checkNext result := by cases result <;> rfl
  rw [final] at runChk
  refine ⟨store, result, leading ++ chk, ref, chain (ReturnFrame.Occurrence.prefix_survives (tracked 0)).1 runChk, runRef,
    by rw [visible_append, silent, List.nil_append, seen], ?_⟩
  cases result with
  | error _ => exact status
  | ok _ =>
    obtain ⟨kept, checkTrack, canonTrack⟩ := status
    refine ⟨kept, ?_, canonTrack⟩
    intro depth
    have tail := checkTrack depth
    rw [final] at tail
    exact (tracked depth).append tail

private theorem primitiveLeafLocal {keep : CStore (core3 grow) → Prop} (writes : WriteClosed keep)
    (destination : RecordDestination) (inst : InstId) (primitive : WIT.Primitive)
    (payload : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Payload (.prim primitive))
    (nonString : primitive ≠ .string) (index : Nat) (output : Lower.Output)
    (left right : Config (core3 grow) (HostState sig)) (kept : keep right.store)
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (placed : rootPlacement destination left.store (.prim primitive) output = .ok ()) :
    CompareLocalKeepingAt profile scheduledReady scheduledDispatch keep left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) index output)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) output) := by
  let cx := destination.context (grow := grow) inst
  change ptrTypeIn left.store cx = destination.width at width
  have well : ABI.ValType.WellFormedCM (.prim primitive : TypeOf) := by
    refine ⟨.prim _, rfl, rfl, rfl, ?_⟩
    cases primitive <;> simp [ABI.ValType.anySub, oversizedNode, layout, primitiveLayout, pointerLayout,
      pointerAlignment, Layout.size, Alignment.bytes]
  have plain : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.checkSchema (.prim primitive) = .ok () := by
    unfold Silmaril.Wasm.Game.HandleAccept.Wit.Stored.checkSchema
    rw [ite_eq_right (show ¬ containsBorrow (.prim primitive : TypeOf) = true from Bool.not_eq_true _ |>.mpr rfl),
      ite_eq_right (show ¬ payloadContainsOwn (.prim primitive) = true from Bool.not_eq_true _ |>.mpr rfl), ite_eq_left well]
  have schema : Lower.checkSchema (.prim primitive) = .ok () := by
    unfold Lower.checkSchema
    rw [plain]
    rfl
  have options : Lower.checkOptions cx (.prim primitive) output = .ok () := by
    cases primitive <;> first | contradiction | cases output <;> rfl
  have fit (width : AddrType) : Lower.fits Quirks.none cx.opts.encoding width (.prim primitive) payload.val = true := by
    cases primitive <;> first | contradiction | cases payload.val <;> rfl
  intro same checkCursor canonCursor thread checkNext canonNext checkAt canonAt
  rw [Record.Effects.field] at checkAt
  cases output with
  | flat =>
    rw [Lower.lower_flat_reference Limits.spec Quirks.none cx _ payload schema options fit] at checkAt
    let body := fun w => lowerFlatPrim (σ := HostState sig) Limits.spec Quirks.none cx w primitive payload.val
    let checkedBody : Session grow sig (Except RecordLower.Issue (List FlatValue)) := do
      return .ok (← body destination.width)
    have focus : left.ctl = checkCursor.control (.op .get (fun store =>
        (do return (Except.ok (← body (ptrTypeIn store cx)) : Except RecordLower.Issue _)) >>= checkNext)) := by
      change left.ctl = checkCursor.control
        ((((ptrType cx).bind (fun current => (body current).bind (fun words =>
          .pure (Except.ok words : Except Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Issue _)))).bind (fun
          verdict => .pure (verdict.mapError (.field index ∘ .beforeAllocation ∘ .abi)))).bind checkNext) at checkAt
      simp only [Prog.bind_assoc, Prog.pure_bind', Except.mapError] at checkAt
      change left.ctl = checkCursor.control ((Prog.op (S := Eff (core3 grow) (HostState sig)) .get
        (fun store => (body (ptrTypeIn store cx)).bind fun words => .pure (.ok words))).bind checkNext) at checkAt
      exact checkAt
    let entered := { left with ctl := checkCursor.control (checkedBody >>= checkNext) }
    have read : Step profile scheduledReady scheduledDispatch left .tau entered := by
      simpa only [width, entered, checkedBody, Cursor.control] using
        (Step.get (prof := profile) (hr := scheduledReady) (dispatch := scheduledDispatch) focus)
    have compared := closedCut (profile := profile) (ready := scheduledReady) (dispatch := scheduledDispatch)
      (closedFlatPrim (Host := HostState sig) cx destination.width primitive payload.val nonString)
      entered right checkCursor canonCursor (fun value => checkNext (.ok value)) canonNext kept same thread (by
        change checkCursor.control ((body destination.width).bind (fun value => .pure (.ok value)) >>= checkNext) = _
        simp only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_bind']
        rfl) canonAt
    exact prependLocalCut (fun depth => .step read (by rw [ReturnFrame.Occurrence.transitionEdit, focus]; rfl) (.done _ _))
      rfl compared
  | memory ptr =>
    rw [Lower.lower_memory_reference Limits.spec Quirks.none cx _ payload ptr schema options fit] at checkAt
    rw [CanonicalTree.field, CanonicalTree.leaf, Field.type, Field.value, Canon.store] at canonAt
    let area := layout destination.width (.prim primitive : TypeOf)
    let body := storePrim (σ := HostState sig) Limits.spec Quirks.none cx primitive payload.val ptr
    let guarded := fun current => do
      let area := layout current (.prim primitive : TypeOf)
      checkAligned ptr area.alignment.bytes
      checkInBounds cx ptr area.size
      body
    let entered := { left with ctl := checkCursor.control (do
      checkAligned ptr area.alignment.bytes
      checkInBounds cx ptr area.size
      checkNext (.ok (← body))) }
    have focus : left.ctl = checkCursor.control (.op .get (fun store => do
        let area := layout (ptrTypeIn store cx) (.prim primitive : TypeOf)
        checkAligned ptr area.alignment.bytes
        checkInBounds cx ptr area.size
        checkNext (.ok (← body)))) := by
      rw [Canon.store] at checkAt
      change left.ctl = checkCursor.control
        ((((ptrType cx).bind (fun current => (guarded current).bind (fun value =>
          .pure (Except.ok value : Except Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Issue _)))).bind (fun
          verdict => .pure (verdict.mapError (.field index ∘ .beforeAllocation ∘ .abi)))).bind checkNext) at checkAt
      simp only [Prog.bind_assoc, Prog.pure_bind', Except.mapError] at checkAt
      change left.ctl = checkCursor.control (Prog.op (S := Eff (core3 grow) (HostState sig)) .get
        (fun store => ((guarded (ptrTypeIn store cx)).bind fun value => .pure (.ok value)).bind checkNext)) at checkAt
      refine checkAt.trans (congrArg checkCursor.control ?_)
      apply congrArg (Prog.op (S := Eff (core3 grow) (HostState sig)) .get)
      funext store
      simp only [guarded, Prog.bind_eq, Prog.bind_assoc, Prog.pure_bind']
    have read : Step profile scheduledReady scheduledDispatch left .tau entered := by
      simpa only [width, entered, area, Cursor.control] using
        (Step.get (prof := profile) (hr := scheduledReady) (dispatch := scheduledDispatch) focus)
    have guard := checkPlacementRun (profile := profile) (ready := scheduledReady) (placementDispatch := scheduledDispatch)
      destination inst entered area ptr checkCursor (do checkNext (.ok (← body))) rfl
    change placement destination entered.store area ptr = .ok () at placed
    rw [placed] at guard
    let checkedEnd := { entered with ctl := checkCursor.control (do checkNext (.ok (← body))) }
    have compared := closedCut (profile := profile) (ready := scheduledReady) (dispatch := scheduledDispatch)
      (closedStorePrim (Host := HostState sig) writes cx primitive payload.val nonString ptr)
      checkedEnd right checkCursor canonCursor (fun value => checkNext (.ok value)) canonNext kept same thread rfl canonAt
    exact prependLocalCut (fun depth => .step read (by rw [ReturnFrame.Occurrence.transitionEdit, focus]; rfl) (guard depth))
      rfl compared

private theorem primitiveLeafKeeping {keep : CStore (core3 grow) → Prop} (writes : WriteClosed keep)
    (destination : RecordDestination) (inst : InstId) (primitive : WIT.Primitive)
    (payload : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Payload (.prim primitive))
    (nonString : primitive ≠ .string) (index : Nat) (output : Lower.Output)
    (left right : Config (core3 grow) (HostState sig)) (kept : keep right.store)
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (placed : rootPlacement destination left.store (.prim primitive) output = .ok ()) :
    CompareKeepingAt profile scheduledReady scheduledDispatch keep left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) index output)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) output) := by
  intro same check canon thread checkNext canonNext checkAt canonAt
  exact localCutReaches (primitiveLeafLocal writes destination inst primitive payload nonString index output left right kept width placed
    same check canon thread checkNext canonNext checkAt canonAt)

theorem primitiveLeaf (destination : RecordDestination) (inst : InstId) (primitive : WIT.Primitive)
    (payload : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Payload (.prim primitive))
    (nonString : primitive ≠ .string) (index : Nat) (output : Lower.Output)
    (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (placed : rootPlacement destination left.store (.prim primitive) output = .ok ()) :
    CompareAt profile scheduledReady scheduledDispatch left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) index output)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) output) := by
  intro same checkCursor canonCursor thread checkNext canonNext checkAt canonAt
  exact forgetKeeping (primitiveLeafKeeping (keep := fun _ => True) (fun _ _ _ _ _ => trivial) destination inst primitive payload
    nonString index output left right trivial width placed same checkCursor canonCursor thread checkNext canonNext checkAt canonAt)

private theorem growthWrites (origin : CStore (core3 grow)) :
    WriteClosed (fun (store : CStore (core3 grow)) => Core3.Grows origin.core store.core) :=
  fun store memory ptr bytes growing => growing.trans (writeMemSt_grows store memory ptr bytes)

theorem primitiveLeafFrame (destination : RecordDestination) (inst : InstId) (primitive : WIT.Primitive)
    (payload : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Payload (.prim primitive))
    (nonString : primitive ≠ .string) (index : Nat) (output : Lower.Output) (origin : CStore (core3 grow))
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core)
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (placed : rootPlacement destination left.store (.prim primitive) output = .ok ()) :
    CompareLocalKeepingAt profile scheduledReady scheduledDispatch (fun store => Core3.Grows origin.core store.core) left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) index output)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) output) :=
  primitiveLeafLocal (growthWrites origin) destination inst primitive payload nonString index output left right growth width placed

private theorem localDataProgram {keep : CStore (core3 grow) → Prop} (writes : WriteClosed keep)
    (destination : RecordDestination) (inst : InstId) (type : TypeOf) (data : LocalDataType type)
    (payload : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Payload type) (output : Lower.Output) :
    Prog.Every (ClosedOp (E := core3 grow) (Host := HostState sig) profile keep)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width (.data type payload) output) := by
  let cx := destination.context (grow := grow) inst
  cases data with
  | primitive nonString =>
    cases output with
    | flat => exact closedFlatPrim cx destination.width _ payload.val nonString
    | memory address =>
      rw [CanonicalTree.field, CanonicalTree.leaf, Field.type, Field.value, Canon.store]
      exact closedStorePrim writes cx _ payload.val nonString address
  | enum schema =>
    rename_i labels
    cases output with
    | flat =>
      change Prog.Every _ (lowerFlatAt Limits.spec Quirks.none cx destination.width payload.val (.enum labels))
      cases payload.val <;> simp only [lowerFlatAt] <;> try exact .op trivial (fun impossible => nomatch impossible)
      unfold lowerFlatVariantWith
      split
      · exact .pure _
      · exact .op trivial (fun impossible => nomatch impossible)
    | memory address =>
      change Prog.Every _ (Canon.store Limits.spec Quirks.none cx payload.val (.enum labels) address)
      cases payload.val <;> simp only [Canon.store] <;> try exact .op trivial (fun impossible => nomatch impossible)
      split
      · unfold storeVariantHead
        exact ((closedIntKeeping writes cx _ address (discSize labels.length)).bind
          (fun _ => .pure _)).bind (fun _ => .pure _)
      · exact .op trivial (fun impossible => nomatch impossible)
  | flags schema =>
    rename_i labels
    cases output with
    | flat =>
      change Prog.Every _ (lowerFlatAt Limits.spec Quirks.none cx destination.width payload.val (.flags labels))
      cases payload.val <;> simp only [lowerFlatAt] <;>
        first | exact .pure _ | exact .op trivial (fun impossible => nomatch impossible)
    | memory address =>
      change Prog.Every _ (Canon.store Limits.spec Quirks.none cx payload.val (.flags labels) address)
      cases payload.val <;> simp only [Canon.store] <;>
        first | exact closedIntKeeping writes cx _ address (flagsSize labels.length) |
          exact .op trivial (fun impossible => nomatch impossible)

theorem localDataLeafFrame (destination : RecordDestination) (inst : InstId) (type : TypeOf) (data : LocalDataType type)
    (payload : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Payload type) (index : Nat) (output : Lower.Output) (origin : CStore (core3 grow))
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core)
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (placed : rootPlacement destination left.store type output = .ok ()) :
    CompareLocalKeepingAt profile scheduledReady scheduledDispatch (fun store => Core3.Grows origin.core store.core) left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.data type payload) index output)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.data type payload) output) := by
  have schema : Lower.checkSchema type = .ok () := by
    cases data with
    | primitive _ => exact primitiveSchema _
    | enum checked | flags checked => exact checked
  have options : Lower.checkOptions (destination.context (grow := grow) inst) type output = .ok () := by
    cases data with
    | @primitive primitive nonString => cases primitive <;> first | contradiction | cases output <;> rfl
    | enum | flags => cases output <;> rfl
  have fit : Lower.fits Quirks.none destination.encoding destination.width type payload.val = true := by
    cases data with
    | @primitive primitive nonString => cases primitive <;> first | contradiction | cases payload.val <;> rfl
    | enum | flags => cases payload.val <;> rfl
  intro same check canon thread checkedNext canonNext checkAt canonAt
  obtain ⟨reads, entered⟩ := dataEntry destination inst type payload index output left check checkedNext
    width schema options fit placed checkAt
  exact prependLocalCut entered (silent (fun _ member => List.eq_of_mem_replicate member))
    (closedCut (localDataProgram (growthWrites origin) destination inst type data payload output)
      _ right check canon (fun value => checkedNext (.ok value)) canonNext growth same thread rfl canonAt)

private theorem scalarField {primitive : WIT.Primitive} {item : Field}
    (layoutMatch : item.LayoutMatches (.prim primitive)) :
    ∃ payload : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Payload (.prim primitive), item = .data (.prim primitive) payload := by
  cases item with
  | data _ payload => cases layoutMatch; exact ⟨payload, rfl⟩
  | endpoint channel _ _ => cases channel <;> cases layoutMatch
  | _ => cases layoutMatch

private theorem memoryElements (destination : RecordDestination) (inst : InstId) (element : TypeOf)
    (origin : CStore (core3 grow)) (base count bytes : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : base = alignTo base (layout destination.width element).alignment)
    (bounds : base + count * (layout destination.width element).size ≤ bytes)
    (entries : List Field) (index : Nat) (room : index + entries.length ≤ count)
    (child : ∀ item ∈ entries, MemoryChildRule profile scheduledReady scheduledDispatch destination inst item element)
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core) :
    let cx := destination.context inst
    let stride := (layout destination.width element).size
    CompareKeepingAt profile scheduledReady scheduledDispatch (fun store => Core3.Grows origin.core store.core) left right
      (Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width entries stride (base + index * stride) index)
      (CanonicalTree.elements Limits.spec Quirks.none cx destination.width entries .value stride (base + index * stride)) := by
  let cx := destination.context (grow := grow) inst
  let stride := (layout destination.width element).size
  let keep := fun (store : CStore (core3 grow)) => Core3.Grows origin.core store.core
  dsimp only
  induction entries generalizing index left right with
  | nil =>
    rw [Record.Effects.elements, CanonicalTree.elements]
    intro same checkCursor canonCursor _ checkNext canonNext checkAt canonAt
    exact ⟨.returned (), [], [], left, right, .refl _, .refl _, same, rfl, growth, checkAt, canonAt⟩
  | cons item rest ih =>
    have entry : index < count := by simp only [List.length_cons] at room; omega
    have nextRoom : index + 1 + rest.length ≤ count := by simp only [List.length_cons] at room; omega
    have nextPtr : base + (index + 1) * stride = (base + index * stride) + stride := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    rw [Record.Effects.elements, CanonicalTree.elements]
    let ptr := base + index * stride
    obtain ⟨modulo, within⟩ := listEntryBounds (layout destination.width element) aligned bounds entry
    have first := child item List.mem_cons_self origin index ptr bytes width sized modulo within left right growth
    have later : ∀ (_ : Unit) entered reference, keep reference.store →
        CompareKeepingAt profile scheduledReady scheduledDispatch keep entered reference
          (Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width rest stride (ptr + stride) (index + 1))
          (CanonicalTree.elements Limits.spec Quirks.none cx destination.width rest .value stride (ptr + stride)) := by
      intro _ entered reference grown
      have continued := ih (index + 1) nextRoom (fun item member => child item (List.mem_cons_of_mem _ member))
        entered reference grown
      simpa only [nextPtr, ptr, stride, cx, keep] using continued
    have compared := sequentialKeeping first id _ _ later
    convert compared using 2 <;> try rfl
    funext verdict
    cases verdict with
    | ok result => cases result; rfl
    | error _ => rfl

theorem memoryCollectionTailKeeping (destination : RecordDestination) (inst : InstId) (element : TypeOf)
    (entries : List Field)
    (child : ∀ item ∈ entries, MemoryChildRule profile scheduledReady scheduledDispatch destination inst item element)
    (output : Lower.Output) (index pointer bytes : Nat) (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes) :
    CollectionTailKeepingAt profile scheduledReady scheduledDispatch (fun store => Core3.Grows left.store.core store.core)
      destination inst entries (layout destination.width element) output index pointer bytes left right := by
  intro aligned bounds _ checked canonical checkedStore _ _ _ same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  have memWidth : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width := by
    change (core3 grow).memSize? left.store.core destination.memory = some bytes at sized
    change SingleThreaded.memSize? left.store.core destination.memory = some bytes at sized
    change SingleThreaded.memAddrType? left.store.core destination.memory = some destination.width
    unfold SingleThreaded.memSize? at sized
    unfold ptrTypeIn CanonOpts.ptrType RecordDestination.context at width
    change (SingleThreaded.memAddrType? left.store.core destination.memory).getD .i32 = destination.width at width
    unfold SingleThreaded.memAddrType? at width ⊢
    cases found : left.store.core.mems[destination.memory]? with
    | none => simp only [found, Option.map_none, reduceCtorEq] at sized
    | some memory =>
      simp only [found, Option.map_some, Option.getD_some] at width ⊢
      exact congrArg some width
  have growth : Core3.Grows left.store.core canonical.store.core := by rw [← same, checkedStore]; exact Core3.Grows.refl _
  let cx := destination.context (grow := grow) inst
  let publish := (ListLower.publish cx destination.width pointer entries.length output : Session grow sig output.Result)
  have elements := memoryElements (profile := profile) (scheduledReady := scheduledReady) (scheduledDispatch := scheduledDispatch)
    destination inst element left.store pointer entries.length bytes memWidth sized aligned bounds entries 0
    (by simp) child checked canonical growth
  dsimp only at elements
  simp only [Nat.zero_mul, Nat.add_zero] at elements
  have compared := sequentialKeeping elements (.nested index) (fun _ => do return .ok (← publish)) (fun _ => publish)
    (fun _ entered reference kept => compareClosedKeeping (closedDescriptor (growthWrites left.store) cx destination.width
      pointer entries.length output) entered reference kept)
  apply compared same checkCursor canonCursor sameThread checkNext canonNext _ canonAt
  unfold checkedCollectionTail at checkAt
  convert checkAt using 4
  funext verdict
  cases verdict with
  | ok result => cases result; rfl
  | error _ => rfl

theorem memoryCollectionTail (destination : RecordDestination) (inst : InstId) (element : TypeOf)
    (entries : List Field)
    (child : ∀ item ∈ entries, MemoryChildRule profile scheduledReady scheduledDispatch destination inst item element)
    (output : Lower.Output) (index pointer bytes : Nat) (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes) :
    CollectionTailAt profile scheduledReady scheduledDispatch destination inst entries
      (layout destination.width element) output index pointer bytes left right := by
  intro aligned fits live checked canonical checkStore canonStore checkHost canonHost same check canon thread finish next checkAt canonAt
  exact forgetKeeping (memoryCollectionTailKeeping destination inst element entries child output index pointer bytes left right width sized
    aligned fits live checked canonical checkStore canonStore checkHost canonHost same check canon thread finish next checkAt canonAt)

theorem entriesMatchOfMem {entries : List Field} {type : TypeOf} {item : Field}
    (matched : Field.EntriesMatch entries type) (member : item ∈ entries) : item.LayoutMatches type := by
  induction entries with
  | nil => simp at member
  | cons head rest ih =>
    cases matched with
    | cons first later =>
      rcases List.mem_cons.mp member with rfl | tail
      · exact first
      · exact ih later tail

private theorem primitiveChildRule (destination : RecordDestination) (inst : InstId) (primitive : WIT.Primitive)
    (nonString : primitive ≠ .string) (payload : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Payload (.prim primitive)) :
    MemoryChildRule profile scheduledReady scheduledDispatch destination inst (.data (.prim primitive) payload) (.prim primitive) := by
  intro origin slot address capacity memoryWidth memorySize aligned bounds checked canonical growth same
  have reachedWidth : (core3 grow).memAddrType? checked.store.core destination.memory = some destination.width := by
    rw [same]; exact growth.memAddrType memoryWidth
  obtain ⟨enlarged, reachedSize, widened⟩ := growth.memSize memorySize
  have sizeAt : (core3 grow).memSize? checked.store.core destination.memory = some enlarged := by rw [same]; exact reachedSize
  have placed : rootPlacement destination checked.store (.prim primitive) (.memory address) = .ok () := by
    simp [rootPlacement, placement, aligned, sizeAt, Nat.not_lt.mpr (bounds.trans widened)]
    rfl
  exact primitiveLeafKeeping (growthWrites origin) destination inst primitive payload nonString slot (.memory address)
    checked canonical growth (by simp [ptrTypeIn, CanonOpts.ptrType, RecordDestination.context, reachedWidth]) placed same

theorem scalarCollectionTail (destination : RecordDestination) (inst : InstId) (primitive : WIT.Primitive)
    (nonString : primitive ≠ .string) (entries : List Field) (layoutMatch : Field.EntriesMatch entries (.prim primitive))
    (output : Lower.Output) (index pointer bytes : Nat) (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes) :
    CollectionTailAt profile scheduledReady scheduledDispatch destination inst entries
      (layout destination.width (.prim primitive : TypeOf)) output index pointer bytes left right := by
  apply memoryCollectionTail destination inst (.prim primitive) entries _ output index pointer bytes left right width sized
  intro item member
  obtain ⟨payload, rfl⟩ := scalarField (entriesMatchOfMem layoutMatch member)
  exact primitiveChildRule destination inst primitive nonString payload

theorem memoryFieldsKeeping (destination : RecordDestination) (inst : InstId)
    {keep : CStore (core3 grow) → Prop} (fields : List Field) (cursor index : Nat)
    (width : ∀ store, keep store → ptrTypeIn store (destination.context inst) = destination.width)
    (child : ∀ slot item address, fields[slot]? = some item →
      (fieldOffsets cursor (fields.map fun field => layout destination.width field.type))[slot]? = some address →
      ∀ left right : Config (core3 grow) (HostState sig), keep right.store →
        CompareKeepingAt profile scheduledReady scheduledDispatch keep left right
          (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
            item (index + slot) (.memory address))
          (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address)))
    (left right : Config (core3 grow) (HostState sig)) (kept : keep right.store) :
    CompareKeepingAt profile scheduledReady scheduledDispatch keep left right
      (Record.Effects.memory recordClaims Limits.spec Quirks.none (destination.context inst) destination.width fields cursor index)
      (CanonicalTree.memory Limits.spec Quirks.none (destination.context inst) destination.width fields cursor) := by
  let cx := destination.context (grow := grow) inst
  induction fields generalizing cursor index left right with
  | nil =>
    rw [Record.Effects.memory, CanonicalTree.memory]
    intro same checkCursor canonCursor _ checkNext canonNext checkAt canonAt
    exact ⟨.returned (), [], [], left, right, .refl _, .refl _, same, rfl, kept, checkAt, canonAt⟩
  | cons head rest ih =>
    let address := fun width => alignTo cursor (layout width head.type).alignment
    let advanced := fun width => address width + (layout width head.type).size
    rw [CanonicalTree.memory, Record.Effects.memory]
    apply readWidthKeeping cx left right destination.width (width right.store kept)
    intro entered stored _
    have initial : keep entered.store := stored ▸ kept
    have paired := child 0 head (address destination.width) rfl rfl left entered initial
    rw [Nat.add_zero] at paired
    have later := fun (_ : Unit) nextLeft nextRight valid => ih (advanced destination.width) (index + 1)
      (fun slot item addr found placed => by
        have continued := child (slot + 1) item addr found placed
        simpa only [Nat.add_assoc, Nat.add_comm 1 slot] using continued) nextLeft nextRight valid
    have compared := sequentialKeeping paired id _ _ later
    convert compared using 2 <;> try rfl
    funext verdict
    cases verdict with
    | ok result => cases result; rfl
    | error _ => rfl

theorem memoryFieldsOf (destination : RecordDestination) (inst : InstId) (origin : CStore (core3 grow))
    (fields : List Field) (base index bytes : Nat)
    (memoryWidth : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : (recordAlignment (fields.map fun item => layout destination.width item.type)).bytes ∣ base)
    (bounds : base + (recordLayout (fields.map fun item => layout destination.width item.type)).size ≤ bytes)
    (child : ∀ item ∈ fields, MemoryChildRule profile scheduledReady scheduledDispatch destination inst item item.type)
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core) :
    CompareKeepingAt profile scheduledReady scheduledDispatch (fun store => Core3.Grows origin.core store.core) left right
      (Record.Effects.memory recordClaims Limits.spec Quirks.none (destination.context inst) destination.width fields base index)
      (CanonicalTree.memory Limits.spec Quirks.none (destination.context inst) destination.width fields base) := by
  let cx := destination.context (grow := grow) inst
  let shapes := fields.map fun item => layout destination.width item.type
  have width (store : CStore (core3 grow)) (grown : Core3.Grows origin.core store.core) : ptrTypeIn store cx = destination.width := by
    have observed : (core3 grow).memAddrType? store.core destination.memory = some destination.width := grown.memAddrType memoryWidth
    simp [ptrTypeIn, CanonOpts.ptrType, cx, RecordDestination.context, observed]
  apply memoryFieldsKeeping destination inst fields base index width _ left right growth
  intro slot item address found offset checked reference grown
  have foundLayout : shapes[slot]? = some (layout destination.width item.type) := by
    simp only [shapes, List.getElem?_map, found, Option.map_some]
  obtain ⟨_, addressAligned, fits⟩ := recordLayout_field_fits shapes base slot address _ aligned foundLayout offset
  exact child item (List.mem_of_getElem? found) origin (index + slot) address bytes memoryWidth sized addressAligned
    (fits.trans bounds) checked reference grown

theorem closedLeafChild (destination : RecordDestination) (inst : InstId) (item : Field)
    (closed : ClosedMemoryLeaf item) : MemoryChildRule profile scheduledReady scheduledDispatch destination inst item item.type := by
  rcases closed with handle | ⟨primitive, nonString, payload, rfl⟩
  · intro origin index address _ _ _ _ _ checked reference grown
    have paired := handleKeeping (profile := profile) (scheduledReady := scheduledReady) (scheduledDispatch := scheduledDispatch)
      destination inst item handle index (.memory address) origin checked reference grown
    cases item <;> first | contradiction | simpa only [Record.Effects.field, CanonicalTree.field] using paired
  · exact primitiveChildRule destination inst primitive nonString payload

theorem closedMemoryFields (destination : RecordDestination) (inst : InstId) (origin : CStore (core3 grow))
    (fields : List Field) (base index bytes : Nat)
    (memoryWidth : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : (recordAlignment (fields.map fun item => layout destination.width item.type)).bytes ∣ base)
    (bounds : base + (recordLayout (fields.map fun item => layout destination.width item.type)).size ≤ bytes)
    (closed : ∀ item ∈ fields, ClosedMemoryLeaf item)
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core) :
    CompareKeepingAt profile scheduledReady scheduledDispatch (fun store => Core3.Grows origin.core store.core) left right
      (Record.Effects.memory recordClaims Limits.spec Quirks.none (destination.context inst) destination.width fields base index)
      (CanonicalTree.memory Limits.spec Quirks.none (destination.context inst) destination.width fields base) :=
  memoryFieldsOf destination inst origin fields base index bytes memoryWidth sized aligned bounds
    (fun item member => closedLeafChild destination inst item (closed item member)) left right growth

private theorem fieldLayouts (width : AddrType) {fields : List Field} {types : List TypeOf}
    (matched : Field.FieldsMatch fields types) : (fields.map fun item => layout width item.type) = layoutTypes width types := by
  induction fields generalizing types with
  | nil => cases matched; rw [layoutTypes]; rfl
  | cons head rest ih =>
    cases matched with
    | cons found tail => rw [List.map_cons, layoutTypes, found.type_eq, ih tail]

private theorem recordLayouts (width : AddrType) (schema : List (String × TypeOf)) :
    layoutFields width schema = layoutTypes width (schema.map Prod.snd) := by
  induction schema with
  | nil => rw [List.map_nil, layoutFields, layoutTypes]
  | cons pair rest ih => cases pair; rw [List.map_cons, layoutFields, layoutTypes, ih]

theorem aggregateLayout (width : AddrType) {type : TypeOf} {fields : List Field}
    (matched : Field.LayoutMatches (.aggregate type fields) type) :
    layout width type = recordLayout (fields.map fun item => layout width item.type) := by
  cases matched with
  | record children => rw [layout, recordLayouts, fieldLayouts width children]
  | tuple children => rw [layout, fieldLayouts width children]

theorem aggregateChildRule (destination : RecordDestination) (inst : InstId) (type : TypeOf) (fields : List Field)
    (matched : Field.LayoutMatches (.aggregate type fields) type)
    (child : ∀ item ∈ fields, MemoryChildRule profile scheduledReady scheduledDispatch destination inst item item.type) :
    MemoryChildRule profile scheduledReady scheduledDispatch destination inst (.aggregate type fields) type := by
  intro origin index address bytes memoryWidth sized aligned bounds left right growth
    same checkCursor canonCursor thread checkNext canonNext checkAt canonAt
  let cx := destination.context (grow := grow) inst
  let area := layout destination.width type
  let body : Session grow sig (Except RecordLower.Issue Unit) :=
    Record.Effects.memory recordClaims Limits.spec Quirks.none cx destination.width fields address 0
  let mapped := fun verdict : Except RecordLower.Issue Unit => checkNext (verdict.mapError (.nested index))
  let entered := { left with ctl := checkCursor.control (body >>= mapped) }
  have oldLayout := aggregateLayout destination.width matched
  have alignRecord : (recordAlignment (fields.map fun item => layout destination.width item.type)).bytes ∣ address := by
    have valid := Nat.dvd_of_mod_eq_zero aligned
    rw [oldLayout] at valid
    exact valid
  have fitsRecord : address + (recordLayout (fields.map fun item => layout destination.width item.type)).size ≤ bytes := by
    rw [← oldLayout]; exact bounds
  obtain ⟨reachedBytes, reachedSize, widened⟩ := growth.memSize sized
  have sizeAt : (core3 grow).memSize? left.store.core destination.memory = some reachedBytes := by rw [same]; exact reachedSize
  have placementAt : placement destination left.store area address = .ok () := by
    simp [placement, area, aligned, sizeAt, Nat.not_lt.mpr (bounds.trans widened)]
    rfl
  have guardAt : left.ctl = checkCursor.control (do
      checkAligned address area.alignment.bytes
      checkInBounds cx address area.size
      body >>= mapped) := by
    rw [Record.Effects.field] at checkAt
    simpa [checkAligned, trapIf, area, aligned, cx, body, mapped, Prog.bind_eq, Prog.bind_assoc, Prog.pure_bind'] using checkAt
  have guard := checkPlacement (profile := profile) (ready := scheduledReady) (placementDispatch := scheduledDispatch)
    destination inst left area address checkCursor (body >>= mapped) guardAt
  rw [placementAt] at guard
  rw [CanonicalTree.field] at canonAt
  have compared := memoryFieldsOf (profile := profile) (scheduledReady := scheduledReady) (scheduledDispatch := scheduledDispatch)
    destination inst origin fields address 0 bytes memoryWidth sized alignRecord fitsRecord child entered right growth
    same checkCursor canonCursor thread mapped canonNext rfl canonAt
  obtain ⟨outcome, checkLabels, canonLabels, reached, reference, checkRun, canonRun, stores, labels, kept, status⟩ :=
    prependCheckKeeping guard (by simp) compared
  cases outcome with
  | returned value => exact ⟨.returned value, _, _, _, _, checkRun, canonRun, stores, labels, kept, status⟩
  | refused issue => exact ⟨.refused (.nested index issue), _, _, _, _, checkRun, canonRun, stores, labels, kept, status⟩
  | trapped reason => exact ⟨.trapped reason, _, _, _, _, checkRun, canonRun, stores, labels, kept, status⟩

theorem closedMemoryAggregate (destination : RecordDestination) (inst : InstId) (origin : CStore (core3 grow))
    (type : TypeOf) (fields : List Field) (index address bytes : Nat)
    (matched : Field.LayoutMatches (.aggregate type fields) type)
    (memoryWidth : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : address % (layout destination.width type).alignment.bytes = 0)
    (bounds : address + (layout destination.width type).size ≤ bytes)
    (closed : ∀ item ∈ fields, ClosedMemoryLeaf item)
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core) :
    CompareKeepingAt profile scheduledReady scheduledDispatch (fun store => Core3.Grows origin.core store.core) left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.aggregate type fields) index (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width (.aggregate type fields)
        (.memory address)) :=
  aggregateChildRule destination inst type fields matched
    (fun item member => closedLeafChild destination inst item (closed item member)) origin index address bytes
    memoryWidth sized aligned bounds left right growth

private theorem mapEntryChildren (destination : RecordDestination) (inst : InstId) (origin : CStore (core3 grow))
    (key : WIT.KeyType) (element : TypeOf) (keyField valueField : Field) (index address bytes : Nat)
    (keyLayout : keyField.LayoutMatches (.prim key.toPrimitive)) (valueLayout : valueField.LayoutMatches element)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : address % (layout destination.width (.record (mapEntryFields key element))).alignment.bytes = 0)
    (bounds : address + (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    (keyRule : MemoryChildRule profile scheduledReady scheduledDispatch destination inst keyField (.prim key.toPrimitive))
    (valueRule : MemoryChildRule profile scheduledReady scheduledDispatch destination inst valueField element)
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core) :
    let cx := destination.context inst
    let keyArea := layout destination.width keyField.type
    let keyPtr := alignTo address keyArea.alignment
    let valuePtr := alignTo (keyPtr + keyArea.size) (layout destination.width valueField.type).alignment
    CompareKeepingAt profile scheduledReady scheduledDispatch (fun store => Core3.Grows origin.core store.core) left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
        (.aggregate (.record (mapEntryFields key element)) [keyField, valueField]) index (.memory address))
      (do
        CanonicalTree.field Limits.spec Quirks.none cx destination.width keyField (.memory keyPtr)
        CanonicalTree.field Limits.spec Quirks.none cx destination.width valueField (.memory valuePtr)) := by
  let cx := destination.context (grow := grow) inst
  let entryType : TypeOf := .record (mapEntryFields key element)
  let area := layout destination.width entryType
  let keyArea := layout destination.width keyField.type
  let valueArea := layout destination.width valueField.type
  let keyPtr := alignTo address keyArea.alignment
  let valuePtr := alignTo (keyPtr + keyArea.size) valueArea.alignment
  let shapes := [keyArea, valueArea]
  have matched : Field.LayoutMatches (.aggregate entryType [keyField, valueField]) entryType :=
    .record (.cons keyLayout (.cons valueLayout .nil))
  have layoutEntry : area = recordLayout shapes := aggregateLayout destination.width matched
  have alignRecord : (recordAlignment shapes).bytes ∣ address := by
    have valid := Nat.dvd_of_mod_eq_zero aligned
    change area.alignment.bytes ∣ address at valid
    rw [layoutEntry] at valid
    exact valid
  have fitsRecord : address + (recordLayout shapes).size ≤ bytes := by
    rw [← layoutEntry]; exact bounds
  obtain ⟨_, keyAligned, keyBounds⟩ := recordLayout_field_fits shapes address 0 keyPtr keyArea alignRecord rfl rfl
  obtain ⟨_, valueAligned, valueBounds⟩ := recordLayout_field_fits shapes address 1 valuePtr valueArea alignRecord rfl rfl
  change keyPtr % (layout destination.width keyField.type).alignment.bytes = 0 at keyAligned
  change keyPtr + (layout destination.width keyField.type).size ≤ _ at keyBounds
  change valuePtr % (layout destination.width valueField.type).alignment.bytes = 0 at valueAligned
  change valuePtr + (layout destination.width valueField.type).size ≤ _ at valueBounds
  rw [keyLayout.type_eq] at keyAligned keyBounds
  rw [valueLayout.type_eq] at valueAligned valueBounds
  dsimp only
  intro same checkCursor canonCursor thread checkNext canonNext checkAt canonAt
  let body : Session grow sig (Except RecordLower.Issue Unit) :=
    Record.Effects.memory recordClaims Limits.spec Quirks.none cx destination.width [keyField, valueField] address 0
  let mapped := fun verdict : Except RecordLower.Issue Unit => checkNext (verdict.mapError (.nested index))
  let entered := { left with ctl := checkCursor.control (body >>= mapped) }
  obtain ⟨reachedBytes, reachedSize, widened⟩ := growth.memSize sized
  have sizeAt : (core3 grow).memSize? left.store.core destination.memory = some reachedBytes := by rw [same]; exact reachedSize
  have placed : placement destination left.store area address = .ok () := by
    simp [placement, area, entryType, aligned, sizeAt, Nat.not_lt.mpr (bounds.trans widened)]
    rfl
  have guardAt : left.ctl = checkCursor.control (do
      checkAligned address area.alignment.bytes
      checkInBounds cx address area.size
      body >>= mapped) := by
    rw [Record.Effects.field] at checkAt
    simpa [checkAligned, trapIf, area, entryType, aligned, cx, body, mapped, Prog.bind_eq, Prog.bind_assoc, Prog.pure_bind'] using checkAt
  have guard := checkPlacement (profile := profile) (ready := scheduledReady) (placementDispatch := scheduledDispatch)
    destination inst left area address checkCursor (body >>= mapped) guardAt
  rw [placed] at guard
  have first := keyRule origin 0 keyPtr bytes width sized keyAligned (keyBounds.trans fitsRecord) entered right growth
  have second := fun (_ : Unit) nextLeft nextRight grown =>
    valueRule origin 1 valuePtr bytes width sized valueAligned (valueBounds.trans fitsRecord) nextLeft nextRight grown
  have comparison := sequentialKeeping first id _ _ second same checkCursor canonCursor thread mapped canonNext
  have compared := comparison (by
    change checkCursor.control (body >>= mapped) = _
    apply congrArg checkCursor.control
    apply congrArg (· >>= mapped)
    simp only [body, Record.Effects.memory, keyPtr, keyArea, valuePtr, valueArea, Prog.bind_eq]
    congr 1
    funext verdict
    cases verdict with
    | error issue => rfl
    | ok value =>
      cases value
      refine (congrArg (Prog.bind _) ?_).trans (Prog.bind_pure _)
      funext result
      cases result with
      | error issue => rfl
      | ok value => cases value; rfl) (by exact canonAt)
  obtain ⟨outcome, checkLabels, canonLabels, reached, reference, checkRun, canonRun, stores, labels, kept, status⟩ :=
    prependCheckKeeping guard (by simp) compared
  cases outcome with
  | returned value => exact ⟨.returned value, _, _, _, _, checkRun, canonRun, stores, labels, kept, status⟩
  | refused issue => exact ⟨.refused (.nested index issue), _, _, _, _, checkRun, canonRun, stores, labels, kept, status⟩
  | trapped reason => exact ⟨.trapped reason, _, _, _, _, checkRun, canonRun, stores, labels, kept, status⟩

theorem memoryMapElements (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf)
    (origin : CStore (core3 grow)) (base count bytes : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : base = alignTo base (layout destination.width (.record (mapEntryFields key element))).alignment)
    (bounds : base + count * (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    (entries : List Field) (index : Nat) (room : index + entries.length ≤ count)
    (children : ∀ entry ∈ entries, MapEntryRules profile scheduledReady scheduledDispatch destination inst key element entry)
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core) :
    let cx := destination.context inst
    let stride := (layout destination.width (.record (mapEntryFields key element))).size
    CompareKeepingAt profile scheduledReady scheduledDispatch (fun store => Core3.Grows origin.core store.core) left right
      (Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width entries stride (base + index * stride) index)
      (CanonicalTree.elements Limits.spec Quirks.none cx destination.width entries (.memoryMap destination.width key element)
        stride (base + index * stride)) := by
  let cx := destination.context (grow := grow) inst
  let area := layout destination.width (.record (mapEntryFields key element))
  let stride := area.size
  let mode := CanonicalTree.EntryMode.memoryMap destination.width key element
  let keep := fun (store : CStore (core3 grow)) => Core3.Grows origin.core store.core
  dsimp only
  induction entries generalizing index left right with
  | nil =>
    rw [Record.Effects.elements, CanonicalTree.elements]
    intro same checkCursor canonCursor _ checkNext canonNext checkAt canonAt
    exact ⟨.returned (), [], [], left, right, .refl _, .refl _, same, rfl, growth, checkAt, canonAt⟩
  | cons head rest ih =>
    have entry : index < count := by simp only [List.length_cons] at room; omega
    have nextRoom : index + 1 + rest.length ≤ count := by simp only [List.length_cons] at room; omega
    have nextPtr : base + (index + 1) * stride = (base + index * stride) + stride := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    let ptr := base + index * stride
    obtain ⟨keyField, valueField, shape, keyLayout, valueLayout, keyRule, valueRule⟩ := children head List.mem_cons_self
    obtain ⟨modulo, within⟩ := listEntryBounds area aligned bounds entry
    have headRule := mapEntryChildren destination inst origin key element keyField valueField index ptr bytes
      keyLayout valueLayout width sized modulo within keyRule valueRule left right growth
    have later : ∀ (_ : Unit) entered reference, keep reference.store →
        CompareKeepingAt profile scheduledReady scheduledDispatch keep entered reference
          (Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width rest stride (ptr + stride) (index + 1))
          (CanonicalTree.elements Limits.spec Quirks.none cx destination.width rest mode stride (ptr + stride)) := by
      intro _ entered reference grown
      have continued := ih (index + 1) nextRoom (fun item member => children item (List.mem_cons_of_mem _ member))
        entered reference grown
      simpa only [nextPtr, ptr, stride, area, mode, cx, keep] using continued
    have compared := sequentialKeeping headRule id _ _ later
    rw [shape, Record.Effects.elements, CanonicalTree.elements]
    convert compared using 2
    · funext verdict
      cases verdict with
      | ok result => cases result; rfl
      | error issue => rfl
    · exact (Prog.bind_assoc _ _ _).symm

theorem memoryMapTail (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf)
    (origin : CStore (core3 grow)) (pointer bytes index outputAddress : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (entries : List Field)
    (aligned : pointer = alignTo pointer (layout destination.width (.record (mapEntryFields key element))).alignment)
    (bounds : pointer + entries.length * (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    (children : ∀ entry ∈ entries, MapEntryRules profile scheduledReady scheduledDispatch destination inst key element entry)
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core) :
    let area := layout destination.width (.record (mapEntryFields key element))
    CompareKeepingAt profile scheduledReady scheduledDispatch (fun store => Core3.Grows origin.core store.core) left right
      (checkedCollectionTail destination inst entries area index (.memory outputAddress) pointer (.ok ()))
      (canonicalCollectionTail destination inst entries area (.memory outputAddress) pointer (.memoryMap destination.width key element)) := by
  let cx := destination.context (grow := grow) inst
  let publish : Session grow sig Unit := ListLower.publish cx destination.width pointer entries.length (.memory outputAddress)
  have elements := memoryMapElements destination inst key element origin pointer entries.length bytes width sized
    aligned bounds entries 0 (by simp) children left right growth
  dsimp only at elements
  simp only [Nat.zero_mul, Nat.add_zero] at elements
  have compared := sequentialKeeping elements (.nested index) (fun _ => do return .ok (← publish)) (fun _ => publish)
    (fun _ entered reference kept => compareClosedKeeping (closedDescriptor (growthWrites origin) cx destination.width
      pointer entries.length (.memory outputAddress)) entered reference kept)
  dsimp only
  intro same checkCursor canonCursor thread checkNext canonNext checkAt canonAt
  apply compared same checkCursor canonCursor thread checkNext canonNext _ canonAt
  unfold checkedCollectionTail at checkAt
  refine checkAt.trans (congrArg checkCursor.control ?_)
  apply congrArg (· >>= checkNext)
  simp only [Prog.bind_eq]
  congr 1
  funext verdict
  cases verdict with
  | ok result => cases result; rfl
  | error issue => rfl

private theorem fieldsMatchOfMem {fields : List Field} {types : List TypeOf} {item : Field}
    (matched : Field.FieldsMatch fields types) (member : item ∈ fields) : item.LayoutMatches item.type := by
  induction fields generalizing types with
  | nil => simp at member
  | cons head rest ih =>
    cases matched with
    | cons first later =>
      rcases List.mem_cons.mp member with rfl | tail
      · rw [first.type_eq]; exact first
      · exact ih later tail

theorem localMemoryChild (destination : RecordDestination) (inst : InstId) {item : Field} {type : TypeOf}
    (fragment : LocalMemory item) (matched : item.LayoutMatches type) :
    MemoryChildRule profile scheduledReady scheduledDispatch destination inst item type := by
  induction fragment generalizing type with
  | leaf closed =>
    rw [← matched.type_eq]
    exact closedLeafChild destination inst _ closed
  | aggregate _ ih =>
    cases matched with
    | record children =>
      exact aggregateChildRule destination inst _ _ (.record children)
        (fun child member => ih child member (fieldsMatchOfMem children member))
    | tuple children =>
      exact aggregateChildRule destination inst _ _ (.tuple children)
        (fun child member => ih child member (fieldsMatchOfMem children member))

theorem rootPlacementSteps (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (field : Field) (output : Lower.Output) (start : Config (core3 grow) (HostState sig))
    (cursor : Cursor (E := core3 grow) (HostState sig))
    (finish : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (focused : start.ctl = cursor.control (Record.Effects.root recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width type field output >>= finish)) :
    let child := cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width field 0 output >>= finish)
    match rootPlacement destination start.store type output with
    | .ok () => ∃ labels, visible labels = [] ∧
        Steps profile scheduledReady scheduledDispatch start labels { start with ctl := child }
    | .error reason => ∃ count, Steps profile scheduledReady scheduledDispatch start
        (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg start) := by
  cases output with
  | flat =>
    refine ⟨[], rfl, ?_⟩
    change start.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width field 0 .flat >>= finish) at focused
    have entered : start = { start with ctl := cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
        (destination.context inst) destination.width field 0 .flat >>= finish) } := by
      conv => rhs; rw [← focused]
    exact entered ▸ .refl start
  | memory ptr =>
    let area := layout destination.width type
    let body := Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width field 0 (.memory ptr) >>= finish
    have guardAt : start.ctl = cursor.control (do
        checkAligned ptr area.alignment.bytes
        checkInBounds (destination.context inst) ptr area.size
        body) := by
      rw [focused]
      simp only [Record.Effects.root, body, area, Prog.bind_eq, Prog.bind_assoc]
    have run := checkPlacement (profile := profile) (ready := scheduledReady) (placementDispatch := scheduledDispatch)
      destination inst start area ptr cursor body guardAt
    change (match placement destination start.store area ptr with
      | .ok () => _ | .error _ => _)
    cases verdict : placement destination start.store area ptr with
    | error _ => rw [verdict] at run; exact run
    | ok result => cases result; rw [verdict] at run; exact ⟨[.tau], rfl, run⟩

theorem compiledFlat (left right : Config (core3 grow) (HostState sig)) (sameStore : left.store = right.store)
    (destination : RecordDestination) (inst : InstId) (tag : sig.Tag)
    (payload : OwnedMemory.Payload (sig.payload tag)) {arity : Nat} (children : Fin arity → OwnedMemory.Tree sig)
    (field : Field) (plan : List Object)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload .flat = .ok (field, plan)) (fragment : HandleShape field)
    (checked : destination.check left.store = .ok ()) (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig))
    (sameThread : checkCursor.thread = canonCursor.thread)
    (checkNext : Except RecordLower.Issue (List FlatValue) → Session grow sig (Ret (core3 grow)))
    (canonNext : List FlatValue → Session grow sig (Ret (core3 grow)))
    (checkAt : left.ctl = checkCursor.control (Record.Effects.lowerTree recordClaims Limits.spec Quirks.none
      (destination.context inst) (.tag ⟨tag, payload⟩ arity children) .flat >>= checkNext))
    (canonAt : right.ctl = canonCursor.control (lowerFlatAt Limits.spec Quirks.none (destination.context inst)
      destination.width payload.val.value (sig.payload tag) >>= canonNext)) :
    Reaches profile scheduledReady scheduledDispatch left right checkCursor canonCursor checkNext canonNext := by
  have start := destination.compiled_payload_effects (profile := profile) (ready := scheduledReady)
    (dispatch := scheduledDispatch) left inst tag payload .flat field plan checkNext compiled checked checkAt
  have certified := certifyField start.2.1 fragment
  have reference := destination.compiled_payload_reference (grow := grow) (World := HostState sig)
    inst (sig.payload tag) payload .flat field plan compiled
  have canonField : right.ctl = canonCursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width field .flat >>= canonNext) := by
    rw [reference]
    exact canonAt
  have entry := start.2.2.2
  cases verdict : Record.prepare left.store left.host.writer field.objects with
  | error issue =>
    rw [verdict] at entry
    exact ⟨.refused issue, [.tau, .tau], [], _, right, entry, .refl right, sameStore, rfl, rfl⟩
  | ok passed =>
    cases passed
    rw [verdict] at entry
    cases fits : Lower.fits Quirks.none destination.encoding destination.width (sig.payload tag) payload.val.value with
    | false =>
      simp only [fits, Bool.not_false, ↓reduceIte] at entry
      exact ⟨.refused (.preflight (.abi .allocationPrecondition)), [.tau, .tau, .tau], [], _, right,
        entry, .refl right, sameStore, rfl, rfl⟩
    | true =>
      simp only [fits, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at entry
      let entered := { left with ctl := checkCursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
        (destination.context inst) destination.width field 0 .flat >>= checkNext) }
      have continued := flatField (profile := profile) (scheduledReady := scheduledReady)
        (scheduledDispatch := scheduledDispatch) destination inst field certified 0 entered right sameStore
        checkCursor canonCursor sameThread checkNext canonNext rfl canonField
      exact prependCheck entry (by simp) continued

theorem parkedFlat (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (handleWord : BitVec IntType.i32.width) (destination : RecordDestination) (inst : InstId) (schema : TypeOf)
    (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag)) {arity : Nat}
    (children : Fin arity → OwnedMemory.Tree sig) (field : Field) (plan : List Object)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload .flat = .ok (field, plan)) (fragment : HandleShape field)
    (start reference : Config (core3 grow) (HostState sig)) (sameStore : start.store = reference.store)
    (canonCursor : Cursor (E := core3 grow) (HostState sig)) (canonNext : List FlatValue → Session grow sig (Ret (core3 grow)))
    {thread core continuation segments rest} (sameThread : thread = canonCursor.thread)
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) [.int .i32 handleWord])
    (linked : resolveBinding bindings name type = .ok ⟨name, inst, .giveFlat destination schema⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (mayLeave : (start.store.inst? inst).any (·.mayLeave) = true)
    (destinationChecked : destination.check start.store = .ok ())
    (selected : Endpoints.Core.childFromHistory start.host.writer.accepted handleWord =
      some (.tag ⟨tag, payload⟩ arity children))
    (schemaChecked : rootHasSchema (.tag ⟨tag, payload⟩ arity children) schema = true)
    (canonicalAt : reference.ctl = canonCursor.control (lowerFlatAt Limits.spec Quirks.none (destination.context inst)
      destination.width payload.val.value (sig.payload tag) >>= canonNext)) :
    Reaches profile scheduledReady (specDispatch scheduledReady (host (grow := grow) bindings)) start reference
      ⟨thread, .core core continuation :: segments, rest⟩ canonCursor
      (flatReply destination schema start.host.nextTicket) canonNext := by
  let route := GiveEffectRoute.flat schema
  let tree : OwnedMemory.Tree sig := .tag ⟨tag, payload⟩ arity children
  let entered := { start with
    host := start.host.enter name type (route.args handleWord)
    ctl := ⟨thread, .prog (route.run destination inst tree start.host.nextTicket),
      .core core continuation :: segments⟩ :: rest }
  obtain ⟨labels, allTau, run⟩ := route.parked bindings name type handleWord inst destination tree
    start thread profile scheduledReady parked calling linked caller mayLeave destinationChecked selected schemaChecked
  have continued := compiledFlat (profile := profile) (scheduledReady := scheduledReady)
    (scheduledDispatch := specDispatch scheduledReady (host bindings)) entered reference sameStore
    destination inst tag payload children field plan compiled fragment destinationChecked
    ⟨thread, .core core continuation :: segments, rest⟩ canonCursor sameThread
    (flatReply destination schema start.host.nextTicket) canonNext rfl canonicalAt
  exact prependCheck run (fun label member => by
    have test := List.all_eq_true.mp allTau label member
    cases label <;> simp_all) continued

private theorem closedMemoryRoot (destination : RecordDestination) (inst : InstId) (ptr : Nat) (type : TypeOf) (field : Field)
    (matched : field.LayoutMatches type) (fragment : ClosedMemoryRoot field)
    (left right : Config (core3 grow) (HostState sig))
    (memoryWidth : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width)
    (placed : placement destination left.store (layout destination.width type) ptr = .ok ()) :
    CompareAt profile scheduledReady scheduledDispatch left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width field 0 (.memory ptr))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width field (.memory ptr)) := by
  rcases fragment with handles | ⟨aggregateType, fields, rfl, closed⟩
  · intro same
    have width : ptrTypeIn right.store (destination.context inst) = destination.width := by
      rw [← same]
      simp [ptrTypeIn, RecordDestination.context, CanonOpts.ptrType, memoryWidth]
    exact memoryHandleRoot destination inst field 0 ptr left right width handles same
  · have typed := matched.type_eq
    change aggregateType = type at typed
    subst aggregateType
    let area := layout destination.width type
    have aligned : ptr % area.alignment.bytes = 0 := by
      by_contra invalid
      simp [placement, area, invalid] at placed
      change Except.error TrapReason.unalignedPointer = .ok () at placed
      contradiction
    cases sized : (core3 grow).memSize? left.store.core destination.memory with
    | none => simp [placement, area, aligned, sized] at placed
    | some bytes =>
      have fits : ptr + area.size ≤ bytes := by
        by_contra invalid
        simp [placement, area, aligned, sized, Nat.lt_of_not_ge invalid] at placed
      intro same checkCursor canonCursor thread checkNext canonNext checkAt canonAt
      have growth : Core3.Grows left.store.core right.store.core := same ▸ Core3.Grows.refl _
      exact forgetKeeping (closedMemoryAggregate destination inst left.store type fields 0 ptr bytes matched memoryWidth sized
        aligned fits closed left right growth same checkCursor canonCursor thread checkNext canonNext checkAt canonAt)

private theorem compiledMemory (left right : Config (core3 grow) (HostState sig)) (sameStore : left.store = right.store)
    (destination : RecordDestination) (inst : InstId) (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag))
    {arity : Nat} (children : Fin arity → OwnedMemory.Tree sig) (field : Field) (plan : List Object) (ptr : Nat)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload (.memory ptr) = .ok (field, plan)) (fragment : ClosedMemoryRoot field)
    (destinationChecked : destination.check left.store = .ok ())
    (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig)) (sameThread : checkCursor.thread = canonCursor.thread)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (checkAt : left.ctl = checkCursor.control (Record.Effects.lowerTree recordClaims Limits.spec Quirks.none
      (destination.context inst) (.tag ⟨tag, payload⟩ arity children) (.memory ptr) >>= checkNext))
    (canonAt : right.ctl = canonCursor.control (store Limits.spec Quirks.none (destination.context inst)
      payload.val.value (sig.payload tag) ptr >>= canonNext)) :
    MemoryReaches profile scheduledReady scheduledDispatch left right checkCursor canonCursor checkNext canonNext
      (placement destination left.store (layout destination.width (sig.payload tag)) ptr) := by
  have started := destination.compiled_payload_effects (profile := profile) (ready := scheduledReady)
    (dispatch := scheduledDispatch) (reached := left) inst tag payload (.memory ptr) field plan checkNext
    compiled destinationChecked checkAt
  have reference := destination.compiled_payload_reference (grow := grow) (World := HostState sig)
    inst (sig.payload tag) payload (.memory ptr) field plan compiled
  have canonField : right.ctl = canonCursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width field (.memory ptr) >>= canonNext) := by
    rw [reference]
    exact canonAt
  have entry := started.2.2.2
  cases verdict : Record.prepare left.store left.host.writer field.objects with
  | error issue =>
    rw [verdict] at entry
    exact .inl ⟨.refused issue, [.tau, .tau], [], _, right, entry, .refl right, sameStore, rfl, rfl⟩
  | ok passed =>
    cases passed
    rw [verdict] at entry
    cases fits : Lower.fits Quirks.none destination.encoding destination.width (sig.payload tag) payload.val.value with
    | false =>
      simp only [fits, Bool.not_false, ↓reduceIte] at entry
      exact .inl ⟨.refused (.preflight (.abi .allocationPrecondition)), [.tau, .tau, .tau], [], _, right,
        entry, .refl right, sameStore, rfl, rfl⟩
    | true =>
      simp only [fits, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at entry
      let area := layout destination.width (sig.payload tag)
      let emit : Session grow sig (Except RecordLower.Issue Unit) :=
        Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width field 0 (.memory ptr)
      let body := emit >>= checkNext
      let guarded := { left with ctl := checkCursor.control (Record.Effects.root recordClaims Limits.spec Quirks.none
        (destination.context inst) destination.width (sig.payload tag) field (.memory ptr) >>= checkNext) }
      have entered : Machine.Steps profile scheduledReady scheduledDispatch left [.tau, .tau, .tau] guarded := entry
      have guardAt : guarded.ctl = checkCursor.control (do
        checkAligned ptr area.alignment.bytes
        checkInBounds (destination.context inst) ptr area.size
        body) := by
        change checkCursor.control (((checkAligned ptr area.alignment.bytes).bind fun _ =>
          (checkInBounds (destination.context inst) ptr area.size).bind fun _ => emit).bind checkNext) = _
        simp only [body, Prog.bind_eq, Prog.bind_assoc]
      have checked := checkPlacement (profile := profile) (ready := scheduledReady) (placementDispatch := scheduledDispatch)
        destination inst guarded area ptr checkCursor body guardAt
      change (match placement destination left.store area ptr with
        | .ok () => _ | .error reason => _) at checked
      cases result : placement destination left.store area ptr with
      | ok valid =>
        cases valid
        rw [result] at checked
        let placed := { left with ctl := checkCursor.control body }
        have layoutMatch := Record.preflightValue_layout _ _ _ _ _ _ compiled
        have continued := closedMemoryRoot (profile := profile) (scheduledReady := scheduledReady)
          (scheduledDispatch := scheduledDispatch) destination inst ptr (sig.payload tag) field layoutMatch fragment placed right
          (destination.check_width left.store destinationChecked) result sameStore
          checkCursor canonCursor sameThread checkNext canonNext rfl canonField
        exact .inl (prependCheck (chain entered checked) (by simp) continued)
      | error reason =>
        rw [result] at checked
        obtain ⟨count, halted⟩ := checked
        refine .inr ⟨reason, 3 + count, StepDefs.trapCfg guarded, rfl, ?_, rfl, rfl⟩
        rw [List.replicate_add, List.append_assoc]
        exact chain entered halted

theorem parkedMemory (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (handleWord : BitVec IntType.i32.width) (pointer : FlatValue) (destination : RecordDestination) (inst : InstId)
    (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag)) {arity : Nat}
    (children : Fin arity → OwnedMemory.Tree sig) (field : Field) (plan : List Object)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload (.memory (flatNat pointer)) = .ok (field, plan)) (fragment : ClosedMemoryRoot field)
    (start reference : Config (core3 grow) (HostState sig)) (sameStore : start.store = reference.store)
    (canonCursor : Cursor (E := core3 grow) (HostState sig)) (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {thread core continuation segments rest} (sameThread : thread = canonCursor.thread)
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) [.int .i32 handleWord, pointer])
    (linked : resolveBinding bindings name type = .ok ⟨name, inst, .givePayload destination⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (mayLeave : (start.store.inst? inst).any (·.mayLeave) = true)
    (destinationChecked : destination.check start.store = .ok ())
    (selected : Endpoints.Core.childFromHistory start.host.writer.accepted handleWord =
      some (.tag ⟨tag, payload⟩ arity children))
    (pointerChecked : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.flatType pointer = pointerType destination.width)
    (canonicalAt : reference.ctl = canonCursor.control (store Limits.spec Quirks.none (destination.context inst)
      payload.val.value (sig.payload tag) (flatNat pointer) >>= canonNext)) :
    MemoryReaches profile scheduledReady (specDispatch scheduledReady (host (grow := grow) bindings)) start reference
      ⟨thread, .core core continuation :: segments, rest⟩ canonCursor
      (memoryReply destination pointer start.host.nextTicket) canonNext
      (placement destination start.store (layout destination.width (sig.payload tag)) (flatNat pointer)) := by
  let route := GiveEffectRoute.memory pointer
  let tree : OwnedMemory.Tree sig := .tag ⟨tag, payload⟩ arity children
  let entered := { start with
    host := start.host.enter name type (route.args handleWord)
    ctl := ⟨thread, .prog (route.run destination inst tree start.host.nextTicket),
      .core core continuation :: segments⟩ :: rest }
  obtain ⟨labels, allTau, run⟩ := route.parked bindings name type handleWord inst destination tree
    start thread profile scheduledReady parked calling linked caller mayLeave destinationChecked selected pointerChecked
  have continued := compiledMemory (profile := profile) (scheduledReady := scheduledReady)
    (scheduledDispatch := specDispatch scheduledReady (host bindings)) entered reference sameStore
    destination inst tag payload children field plan (flatNat pointer) compiled fragment destinationChecked
    ⟨thread, .core core continuation :: segments, rest⟩ canonCursor sameThread
    (memoryReply destination pointer start.host.nextTicket) canonNext rfl canonicalAt
  have noEvents : ∀ label ∈ labels, label = (.tau : Label (core3 grow) (HostState sig)) := by
    intro label member
    have test := List.all_eq_true.mp allTau label member
    cases label <;> simp_all
  rcases continued with paired | ⟨reason, count, reached, refused, halted, empty, stores⟩
  · exact .inl (prependCheck run noEvents paired)
  · have replicated : labels = List.replicate labels.length (.tau : Label (core3 grow) (HostState sig)) :=
      List.eq_replicate_length.mpr noEvents
    refine .inr ⟨reason, labels.length + count, reached, refused, ?_, empty, stores⟩
    rw [List.replicate_add, ← replicated, List.append_assoc]
    exact chain run halted

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix
