module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCollection.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Local.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component.Machine.ReturnFrame
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}
  {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}

private theorem silent (count : Nat) :
    PayloadPrefix.visible (List.replicate count .tau : List (Label (core3 grow) (HostState sig))) = [] := by
  induction count with
  | zero => rfl
  | succ _ ih => simpa only [List.replicate_succ, PayloadPrefix.visible, List.filter_cons, Bool.false_eq_true, ↓reduceIte] using ih

private theorem matchedEdit {left right : State grow sig}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired changes left right) (label : Label (core3 grow) (HostState sig)) :
    Occurrence.transitionEdit left label = Occurrence.transitionEdit right label :=
  Occurrence.pair_edit paired label

private theorem trailUnchanged {left right : State grow sig} {labels}
    (run : Steps profile ready (specDispatch ready (host bindings)) left labels right)
    (tracks : ∀ place, Occurrence.Prefix profile ready (specDispatch ready (host bindings)) left place labels right place)
    (mark : Option Occurrence.Location) : Occurrence.Trail profile ready (specDispatch ready (host bindings))
      left mark labels right mark := by
  cases mark with
  | none => exact Occurrence.Trail.absent run
  | some place => exact (tracks place).toTrail

theorem replayMarked {left right last : State grow sig} {visibleLabels}
    {older changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop}
    (path : PrefixFor profile ready bindings protectedReturn left visibleLabels last)
    (covers : ∀ first second, changes first second → protectedReturn first)
    (paired : HostFrame.Related.Paired changes left right) {mark : Option Occurrence.Location}
    (outside : Occurrence.Outside older (Occurrence.segmentStorage left) (Occurrence.segmentStorage right) mark) :
    MarkedReplay profile ready bindings older changes left right last mark visibleLabels := by
  induction path generalizing right mark with
  | done cfg =>
    exact ⟨[], [], right, mark, .refl _, .refl _, paired, rfl, rfl, outside, .done _ _, .done _ _⟩
  | @step start next last label labels inside growth run _ ih =>
    obtain ⟨otherStep, replay, matched⟩ := HostFrame.Related.interior_step covers paired inside growth run
    have stepRight : Machine.Step profile ready (specDispatch ready (host (grow := grow) bindings)) right label otherStep := by
      cases replay with
      | cons _ step tail => cases tail; exact step
    have same := matchedEdit paired label
    have nextOutside : Occurrence.Outside older (Occurrence.segmentStorage next) (Occurrence.segmentStorage otherStep)
        (mark.bind (Occurrence.transitionEdit start label).follow) := by
      rw [Occurrence.step_edit run, Occurrence.step_edit stepRight, ← same]
      exact Occurrence.outside_edit outside _
    obtain ⟨leftLabels, rightLabels, other, reached, lhs, rhs, still, seenLeft, seenRight, remaining, leftTrail, rightTrail⟩ :=
      ih matched nextOutside
    refine ⟨label :: leftLabels, label :: rightLabels, other, reached, .cons growth run lhs,
      replay.append rhs, still, ?_, ?_, remaining, .step run leftTrail, .step stepRight (by rwa [← same])⟩
    · exact (List.filter_append [_] leftLabels).trans (congrArg (PayloadPrefix.visible [_] ++ ·) seenLeft)
    · exact (List.filter_append [_] rightLabels).trans (congrArg (PayloadPrefix.visible [_] ++ ·) seenRight)
  | closedGive callout _ ih =>
    obtain ⟨leftCount, rightCount, _, _, _, lhs, rhs, _, matched, _, _, leftTrack, rightTrack⟩ :=
      Plain.parked_closed_give_rejoin bindings callout.name callout.type callout.args callout.inst
        callout.destination callout.schema paired callout.thread profile ready callout.parked
        callout.calling callout.linked callout.caller callout.live callout.closed
    have nextOutside := fun place offMark first second leftAt rightAt => outside place offMark first second
      ((Occurrence.prefix_survives (leftTrack place)).2.symm.trans leftAt)
      ((Occurrence.prefix_survives (rightTrack place)).2.symm.trans rightAt)
    obtain ⟨leftLabels, rightLabels, other, reached, leftTail, rightTail, still, seenLeft, seenRight, remaining,
      leftTrail, rightTrail⟩ := ih matched nextOutside
    refine ⟨_, _, other, reached, lhs.append leftTail, rhs.append rightTail, still, ?_, ?_, remaining,
      (trailUnchanged lhs.steps leftTrack mark).append leftTrail, (trailUnchanged rhs.steps rightTrack mark).append rightTrail⟩
    · rw [PayloadPrefix.visible, List.filter_append]
      exact (congrArg (· ++ PayloadPrefix.visible leftLabels) (silent leftCount)).trans seenLeft
    · rw [PayloadPrefix.visible, List.filter_append]
      exact (congrArg (· ++ PayloadPrefix.visible rightLabels) (silent rightCount)).trans seenRight
  | @syncReady start _ _ task inst thread frames rest focused agrees _ ih =>
    let chooseNext := syncLiftCandidates (E := core3 grow) (σ := HostState sig) task
    let residual := chooseNext (start.store.instCandidates (ready start.host) inst)
    obtain ⟨otherFrames, otherRest, atOther, matched⟩ := paired.retarget focused (.prog residual) start.host right.host
    have candidates := HostFrame.instCandidates_eq start.store inst (ready start.host) (ready right.host)
      (fun entry live thread member suspended found blocked query condition =>
        agrees entry live thread member suspended found blocked query condition right.host)
    have stepRight : Machine.Step profile ready (specDispatch ready (host (grow := grow) bindings)) right .tau
        { right with ctl := ⟨thread, .prog residual, otherFrames⟩ :: otherRest } := by
      change Machine.Step _ _ _ _ _ { right with ctl := ⟨thread,
        .prog (chooseNext (start.store.instCandidates (ready start.host) inst)), otherFrames⟩ :: otherRest }
      rw [candidates]
      exact .hostGet atOther
    have segmentLeft : Occurrence.segmentStorage { start with ctl := ⟨thread, .prog residual, frames⟩ :: rest } =
        Occurrence.segmentStorage start := by simp [Occurrence.segmentStorage, focused]
    have segmentRight : Occurrence.segmentStorage { right with ctl := ⟨thread, .prog residual, otherFrames⟩ :: otherRest } =
        Occurrence.segmentStorage right := by simp [Occurrence.segmentStorage, atOther]
    obtain ⟨leftLabels, rightLabels, other, reached, lhs, rhs, still, seenLeft, seenRight, remaining, leftTrail, rightTrail⟩ :=
      ih matched (by rwa [segmentLeft, segmentRight])
    refine ⟨.tau :: leftLabels, .tau :: rightLabels, other, reached,
      .cons (by simp [CoreUpdateGrows, focused]) (.hostGet focused) lhs,
      .cons (by simp [CoreUpdateGrows, atOther]) stepRight rhs, still, seenLeft, seenRight, remaining, ?_, ?_⟩
    · exact .step (.hostGet focused) (by
        rw [show mark.bind (Occurrence.transitionEdit start .tau).follow = mark by
          rw [Occurrence.transitionEdit, focused]; cases mark <;> rfl]; exact leftTrail)
    · exact .step stepRight (by
        rw [show mark.bind (Occurrence.transitionEdit right .tau).follow = mark by
          rw [Occurrence.transitionEdit, atOther]; cases mark <;> rfl]; exact rightTrail)

theorem replayFor {left right last : State grow sig} {visibleLabels}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop}
    (path : PrefixFor profile ready bindings protectedReturn left visibleLabels last)
    (covers : ∀ first second, changes first second → protectedReturn first)
    (paired : HostFrame.Related.Paired changes left right) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    ∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels last ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Related.Paired changes last other ∧
      PayloadPrefix.visible leftLabels = visibleLabels ∧ PayloadPrefix.visible rightLabels = visibleLabels := by
  obtain ⟨leftLabels, rightLabels, other, _, lhs, rhs, final, seenLeft, seenRight, _⟩ :=
    replayMarked path covers paired (Occurrence.paired_outside (left := HostFrame.replace left right.host) paired)
  exact ⟨leftLabels, rightLabels, other, lhs, rhs, final, seenLeft, seenRight⟩

theorem replay {left right last : State grow sig} {visibleLabels}
    (path : Prefix profile ready bindings first left visibleLabels last)
    (paired : HostFrame.Paired first second left right) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    ∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels last ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Paired first second last other ∧
      PayloadPrefix.visible leftLabels = visibleLabels ∧ PayloadPrefix.visible rightLabels = visibleLabels :=
  replayFor path (fun _ _ edge => by cases edge; rfl) paired

theorem syncLift {start last : State grow sig} {labels task thread frames rest} {entry : Task (core3 grow)}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop}
    (focused : start.ctl = ⟨thread, .prog (syncLiftLoopBody ready task), frames⟩ :: rest)
    (found : ArenaField.tasks.get? start.store task = some entry) (waiting : entry.state ≠ .resolved)
    (agrees : ReadyAgreement ready start entry.inst)
    (path : PrefixFor profile ready bindings protectedReturn { start with ctl := ⟨thread,
      .prog (syncLiftCandidates task (start.store.instCandidates (ready start.host) entry.inst)), frames⟩ :: rest }
      labels last) : PrefixFor profile ready bindings protectedReturn start labels last := by
  let read : CStore (core3 grow) → Session grow sig (Ret (core3 grow)) := fun store =>
    .op .hostGet fun current => syncLiftCandidates task (store.instCandidates (ready current) entry.inst)
  let begin : CStore (core3 grow) → Session grow sig (Ret (core3 grow)) := fun store =>
    ((match ArenaField.tasks.get? store task with
      | some info => pure info
      | none => internal "dangling arena id") : Session grow sig (Task (core3 grow))) >>= fun info =>
    if info.state = .resolved then pure .unit else .op .get fun reached =>
      .op .hostGet fun current => syncLiftCandidates task (reached.instCandidates (ready current) info.inst)
  have body : syncLiftLoopBody ready task = .op .get begin := by
    change Prog.op (S := Eff (core3 grow) (HostState sig)) .get _ = Prog.op (S := Eff (core3 grow) (HostState sig)) .get _
    congr 1
    funext store
    dsimp only [begin, Prog.bind]
    cases ArenaField.tasks.get? store task
    · rfl
    · simp only [Prog.bind_eq, Prog.pure_eq, Prog.pure_bind']
      split <;> rfl
  have atStart : start.ctl = ⟨thread, .prog (.op .get begin), frames⟩ :: rest := body ▸ focused
  have firstRead : begin start.store = .op .get read := by
    simp only [begin, found, pure_bind, ite_eq_right waiting]
    rfl
  have stepFirst := Machine.Step.get (prof := profile) (hr := ready)
    (dispatch := specDispatch ready (host (grow := grow) bindings)) atStart
  rw [firstRead] at stepFirst
  refine .step ?_ (by simp [CoreUpdateGrows, atStart]) stepFirst
    (.step ?_ (by trivial) (.get rfl) (.syncReady rfl agrees path))
  · rw [HostFrame.InteriorFor, atStart]
    refine ⟨?_, ?_⟩
    · intro _ _ _ _ impossible
      cases impossible
    · intro _ _ _ _ _ _ impossible
      cases impossible
  · unfold HostFrame.InteriorFor
    refine ⟨?_, ?_⟩
    · intro _ _ _ _ impossible
      cases impossible
    · intro _ _ _ _ _ _ impossible
      cases impossible

private theorem classifyPopFor {left right : State grow sig} {thread value frames rest}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {resume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (commonHost : HostState sig) (paired : ReturnFrame.Related.Paired changes (HostFrame.replace left commonHost) right)
    (focused : left.ctl = ⟨thread, .prog (.pure value), .prog resume :: frames⟩ :: rest) :
    ∃ otherFrames otherRest,
      (∃ otherResume, changes resume otherResume ∧
        right.ctl = ⟨thread, .prog (.pure value), .prog otherResume :: otherFrames⟩ :: otherRest ∧
        ChildFrameOver changes left right ⟨thread, frames, rest⟩ ⟨thread, otherFrames, otherRest⟩) ∨
      (right.ctl = ⟨thread, .prog (.pure value), .prog resume :: otherFrames⟩ :: otherRest ∧
       HostFrame.Related.Paired changes { left with ctl := ⟨thread, .prog (resume value), frames⟩ :: rest }
         { right with ctl := ⟨thread, .prog (resume value), otherFrames⟩ :: otherRest }) := by
  cases paired with
  | mk control blocked =>
    change List.Forall₂ _ left.ctl _ at control
    rw [focused] at control
    cases control with
    | cons active tail =>
      cases active with
      | mk segments =>
        cases segments with
        | cons top below =>
          cases top with
          | swap edge => exact ⟨_, _, .inl ⟨_, edge, rfl, ⟨rfl, rfl, rfl, rfl, blocked, rfl, below, tail⟩⟩⟩
          | same => exact ⟨_, _, .inr ⟨rfl, .mk (.cons (.mk below) tail) blocked⟩⟩

private theorem classifyPop {left right : State grow sig} {thread value frames rest}
    (commonHost : HostState sig) (paired : ReturnFrame.Paired first second (HostFrame.replace left commonHost) right)
    (focused : left.ctl = ⟨thread, .prog (.pure value), .prog first :: frames⟩ :: rest) :
    ∃ otherFrames otherRest,
      (right.ctl = ⟨thread, .prog (.pure value), .prog second :: otherFrames⟩ :: otherRest ∧
        ChildFrame first second left right ⟨thread, frames, rest⟩ ⟨thread, otherFrames, otherRest⟩) ∨
      (right.ctl = ⟨thread, .prog (.pure value), .prog first :: otherFrames⟩ :: otherRest ∧
       HostFrame.Paired first second { left with ctl := ⟨thread, .prog (first value), frames⟩ :: rest }
         { right with ctl := ⟨thread, .prog (first value), otherFrames⟩ :: otherRest }) := by
  obtain ⟨otherFrames, otherRest, ⟨_, edge, atOther, frame⟩ | common⟩ := classifyPopFor commonHost paired focused
  · cases edge
    exact ⟨otherFrames, otherRest, .inl ⟨atOther, frame⟩⟩
  · exact ⟨otherFrames, otherRest, .inr common⟩

theorem returnCutFor {left right last : State grow sig} {seen value}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop}
    {resume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (path : PrefixFor profile ready bindings protectedReturn left seen last)
    (covers : ∀ first second, changes first second → protectedReturn first)
    (paired : HostFrame.Related.Paired changes left right) (cursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { cursor with frames := .prog resume :: cursor.frames }.control (pure value)) :
    CallbackReturnFor profile ready bindings changes left right last cursor resume value seen := by
  obtain ⟨leftLabels, rightLabels, other, lhs, rhs, reached, seenLeft, seenRight⟩ := replayFor path covers paired
  have checked := lhs.append (.cons (by simp [CoreUpdateGrows, leftAt, Cursor.control]) (.popProg leftAt) (.refl _))
  have invisible (labels : List (Label (core3 grow) (HostState sig))) : visible (labels ++ [.tau]) = visible labels :=
    (List.filter_append labels [.tau]).trans (List.append_nil _)
  obtain ⟨otherFrames, otherRest, ⟨_, edge, atPop, frame⟩ | ⟨atCommon, still⟩⟩ :=
    classifyPopFor other.host reached leftAt
  · have canonical := rhs.append (.cons (by simp [CoreUpdateGrows, atPop]) (.popProg atPop) (.refl _))
    exact .substituted edge frame checked canonical ((invisible _).trans seenLeft) ((invisible _).trans seenRight)
  · have canonical := rhs.append (.cons (by simp [CoreUpdateGrows, atCommon]) (.popProg atCommon) (.refl _))
    exact .common checked canonical still ((invisible _).trans seenLeft) ((invisible _).trans seenRight)

theorem returnCut {left right last : State grow sig} {seen value}
    (path : Prefix profile ready bindings first left seen last) (paired : HostFrame.Paired first second left right)
    (cursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { cursor with frames := .prog first :: cursor.frames }.control (pure value)) :
    CallbackReturn profile ready bindings first second left right last cursor value seen := by
  cases returnCutFor path (fun _ _ edge => by cases edge; rfl) paired cursor leftAt with
  | substituted edge frame checked canonical seenLeft seenRight =>
    cases edge
    exact .designated frame checked canonical seenLeft seenRight
  | common checked canonical still seenLeft seenRight => exact .common checked canonical still seenLeft seenRight

theorem stringReallocPair (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (left right : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (checkAt : left.ctl = cursor.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : right.ctl = cursor.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext)) :
    let dispatch := specDispatch ready (host bindings)
    let leftEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext left cursor
    let rightEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps canonNext right cursor
    Step profile ready dispatch left .tau leftEntry ∧ Step profile ready dispatch right .tau rightEntry ∧
    HostFrame.Paired (stringPlanResume cx steps checkNext) (stringPlanResume cx steps canonNext) leftEntry rightEntry := by
  refine ⟨string_realloc_install cx ptr oldSize alignment size steps checkNext left cursor checkAt,
    string_realloc_install cx ptr oldSize alignment size steps canonNext right cursor canonAt, ?_⟩
  dsimp only [stringReallocEntry, HostFrame.Paired]
  conv => rhs; rw [← same]
  exact ReturnFrame.installed (HostFrame.replace left right.host) cursor.thread _ cursor.frames cursor.rest

private theorem childFrameFocus {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (body : Session grow sig (Ret (core3 grow))) :
    HostFrame.Related.Paired changes { left with ctl := check.control body } { right with ctl := canon.control body } := by
  have data : { HostFrame.replace left right.host with ctl := canon.control body, conts := right.conts } =
      { right with ctl := canon.control body } := by
    have store := frame.store
    have pending := frame.pending
    have results := frame.results
    have cancels := frame.cancels
    cases left; cases right; simp_all [HostFrame.replace]
  change ReturnFrame.Related.Paired changes
    { HostFrame.replace left right.host with ctl := check.control body } { right with ctl := canon.control body }
  rw [← data]
  have head : ReturnFrame.Related.Active changes ⟨check.thread, .prog body, check.frames⟩
      ⟨canon.thread, .prog body, canon.frames⟩ := by
    rw [← frame.thread]
    exact .mk frame.frames
  exact .mk (.cons head frame.rest) frame.blocked

private theorem childFrameEnter {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (body : Session grow sig (Ret (core3 grow)))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig)) :
    HostFrame.Related.Paired (ReturnFrame.Extend changes first second)
      { left with ctl := { check with frames := .prog first :: check.frames }.control body }
      { right with ctl := { canon with frames := .prog second :: canon.frames }.control body } := by
  have paired := childFrameFocus frame body
  change ReturnFrame.Related.Paired changes { HostFrame.replace left right.host with ctl := check.control body }
    { right with ctl := canon.control body } at paired
  obtain ⟨otherFrames, otherRest, otherAt, installed⟩ := ReturnFrame.Related.Paired.push paired
    (thread := check.thread) (focus := .prog body) (frames := check.frames) (rest := check.rest) rfl body first second
  change canon.control body = ⟨check.thread, .prog body, otherFrames⟩ :: otherRest at otherAt
  have tails : canon.frames = otherFrames ∧ canon.rest = otherRest := by
    simpa [Cursor.control, frame.thread] using otherAt
  simpa only [Cursor.control, HostFrame.Related.Paired, HostFrame.replace, ← tails.1, ← tails.2, frame.thread]
    using installed

private theorem childFrameOutside {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (body : Session grow sig (Ret (core3 grow))) (first second : ReturnFrame.Continuation (core3 grow) (HostState sig)) :
    Occurrence.Outside changes
      (Occurrence.segmentStorage { left with ctl := { check with frames := .prog first :: check.frames }.control body })
      (Occurrence.segmentStorage { right with ctl := { canon with frames := .prog second :: canon.frames }.control body })
      (some (.active 0 0)) := by
  have paired := childFrameFocus frame body
  change ReturnFrame.Related.Paired changes
    { HostFrame.replace left right.host with ctl := check.control body } { right with ctl := canon.control body } at paired
  exact Occurrence.outside_push (.prog first) (.prog second) (Occurrence.paired_outside paired)

private theorem childFrameExtract {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : State grow sig} {thread : Option ThreadId} {body : Session grow sig (Ret (core3 grow))}
    {leftFrames rightFrames : List (Seg (core3 grow) (HostState sig))} {leftRest rightRest}
    (paired : HostFrame.Related.Paired changes
      { left with ctl := ⟨thread, .prog body, leftFrames⟩ :: leftRest }
      { right with ctl := ⟨thread, .prog body, rightFrames⟩ :: rightRest }) :
    ChildFrameOver changes left right ⟨thread, leftFrames, leftRest⟩ ⟨thread, rightFrames, rightRest⟩ := by
  have data := paired.data
  have frames {lhs rhs : State grow sig} (linked : ReturnFrame.Related.Paired changes lhs rhs) :
      List.Forall₂ (ReturnFrame.Related.Active changes) lhs.ctl rhs.ctl ∧
        List.Forall₂ (ReturnFrame.Related.Saved changes) lhs.conts rhs.conts := by
    cases linked with
    | mk control saved => exact ⟨control, saved⟩
  obtain ⟨control, blocked⟩ := frames (lhs := HostFrame.replace _ right.host) paired
  change List.Forall₂ _ (_ :: leftRest) (_ :: rightRest) at control
  cases control with
  | cons head tail => cases head with
    | mk segments => exact ⟨data.1, data.2.1, data.2.2.1, data.2.2.2, blocked, rfl, segments, tail⟩

theorem markedReturn {older changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : State grow sig} {check : Cursor (E := core3 grow) (HostState sig)}
    {value : Ret (core3 grow)} {resume otherResume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired changes left right)
    (outside : Occurrence.Outside older (Occurrence.segmentStorage left) (Occurrence.segmentStorage right)
      (some (.active 0 0)))
    (leftAt : left.ctl = { check with frames := .prog resume :: check.frames }.control (.pure value))
    (rightMark : Occurrence.segmentAt (Occurrence.segmentStorage right) (.active 0 0) = some (.prog otherResume)) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    ∃ canon : Cursor (E := core3 grow) (HostState sig),
      ChildFrameOver older left right check canon ∧
      right.ctl = { canon with frames := .prog otherResume :: canon.frames }.control (.pure value) ∧
      Step profile ready dispatch left .tau { left with ctl := check.control (resume value) } ∧
      Step profile ready dispatch right .tau { right with ctl := canon.control (otherResume value) } := by
  obtain ⟨otherFrames, otherRest, atOther, _⟩ := paired.retarget leftAt (.prog (.pure .unit)) left.host right.host
  cases otherFrames with
  | nil => simp [Occurrence.segmentAt, Occurrence.segmentStorage, atOther] at rightMark
  | cons top frames =>
    have selected : top = .prog otherResume := by simpa [Occurrence.segmentAt, Occurrence.segmentStorage, atOther] using rightMark
    subst top
    let canon : Cursor (E := core3 grow) (HostState sig) := ⟨check.thread, frames, otherRest⟩
    have retired := Occurrence.retire_top (left := HostFrame.replace left right.host) paired outside leftAt atOther
      (.prog (.pure .unit))
    exact ⟨canon, childFrameExtract retired, atOther, .popProg leftAt, .popProg atOther⟩

theorem childStringRealloc {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (checkAt : left.ctl = check.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : right.ctl = canon.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext)) :
    let dispatch := specDispatch ready (host bindings)
    let leftEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext left check
    let rightEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps canonNext right canon
    Step profile ready dispatch left .tau leftEntry ∧ Step profile ready dispatch right .tau rightEntry ∧
    HostFrame.Related.Paired (ReturnFrame.Extend changes (stringPlanResume cx steps checkNext)
      (stringPlanResume cx steps canonNext)) leftEntry rightEntry :=
  ⟨string_realloc_install cx ptr oldSize alignment size steps checkNext left check checkAt,
    string_realloc_install cx ptr oldSize alignment size steps canonNext right canon canonAt,
    childFrameEnter frame _ _ _⟩

theorem stringReturnTracks (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep) (finish : Nat → Session grow sig (Ret (core3 grow)))
    (start last : State grow sig) (cursor reached : Cursor (E := core3 grow) (HostState sig)) (value : Nat)
    (focused : start.ctl = cursor.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= finish))
    {labels} (marked : Occurrence.Trail profile ready (specDispatch ready (host bindings))
      (stringReallocEntry ready bindings cx ptr oldSize alignment size steps finish start cursor)
      (some (.active 0 0)) labels last (some (.active 0 0)))
    (returning : last.ctl = { reached with frames := .prog (stringPlanResume cx steps finish) :: reached.frames }.control
      (.pure (.nat value))) (depth : Nat) :
    Occurrence.Prefix profile ready (specDispatch ready (host bindings)) start (.active 0 depth)
      (.tau :: labels ++ [.tau])
      { last with ctl := reached.control (stringPlanResume cx steps finish (.nat value)) } (.active 0 depth) := by
  obtain ⟨mark, same, run⟩ := marked.survives
  cases same
  have install := string_realloc_install (profile := profile) (ready := ready) (dispatch := specDispatch ready (host bindings))
    cx ptr oldSize alignment size steps finish start cursor focused
  have pops : (Occurrence.transitionEdit last .tau).pops (.active 0 0) := by
    rw [Occurrence.transitionEdit, returning]
    trivial
  rw [string_realloc_focus cx ptr oldSize alignment size steps finish] at focused
  exact Occurrence.Prefix.under_call focused install run (.popProg returning) pops depth

private theorem stringInstallEdit (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep) (finish : Nat → Session grow sig (Ret (core3 grow)))
    (start : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig)) (depth : Nat)
    (focused : start.ctl = cursor.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= finish)) :
    (Occurrence.transitionEdit start .tau).follow (.active 0 depth) = some (.active 0 (depth + 1)) := by
  rw [Occurrence.transitionEdit, focused, string_realloc_focus]
  rfl

theorem stringPlanCut {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (checkAt : left.ctl = check.control (runStoreSteps cx ptr steps >>= checkNext))
    (canonAt : right.ctl = canon.control (runStoreSteps cx ptr steps >>= canonNext)) :
    StringPlanCut profile ready bindings changes cx steps.length left right check canon checkNext canonNext := by
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  obtain ⟨store, outcome, labels, observed, lhs, rhs, tracked⟩ :=
    string_front_cut (profile := profile) (ready := ready) (dispatch := dispatch)
      cx ptr steps left right check canon checkNext canonNext frame.store checkAt canonAt
  cases outcome with
  | error reason => exact .done ⟨store, .error reason, labels, observed, lhs, rhs, fun _ returned => by cases returned⟩
  | ok front =>
    cases front with
    | done returned => exact .done ⟨store, .ok returned, labels, observed, lhs, rhs, fun _ _ depth => tracked (.done returned) rfl depth⟩
    | call pointer oldSize alignment size rest shorter =>
      let action : StoreStep := oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)
      let checkStart := { left with store, ctl := check.control (runStoreSteps cx pointer (action :: rest) >>= checkNext) }
      let canonStart := { right with store, ctl := canon.control (runStoreSteps cx pointer (action :: rest) >>= canonNext) }
      have middle : ChildFrameOver changes checkStart canonStart check canon :=
        ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
      obtain ⟨leftStep, rightStep, paired⟩ := childStringRealloc (profile := profile) (ready := ready)
        (bindings := bindings) cx pointer oldSize alignment size rest checkNext canonNext middle rfl rfl
      have leftGrow : CoreUpdateGrows checkStart := by cases oldSize <;> trivial
      have rightGrow : CoreUpdateGrows canonStart := by cases oldSize <;> trivial
      unfold LocalLeafLabels at observed
      refine .installed pointer oldSize alignment size rest shorter
        (lhs.append (.cons leftGrow leftStep (.refl _))) (rhs.append (.cons rightGrow rightStep (.refl _)))
        (by simpa only [LocalLeafLabels, List.all_append, List.all_cons, List.all_nil, Bool.and_true] using observed) ?_
        paired (childFrameOutside middle _ _ _)
      intro depth
      obtain ⟨leftTrack, rightTrack⟩ := tracked (.call pointer oldSize alignment size rest shorter) rfl depth
      have leftEdit := stringInstallEdit cx pointer oldSize alignment size rest checkNext checkStart check depth rfl
      have rightEdit := stringInstallEdit cx pointer oldSize alignment size rest canonNext canonStart canon depth rfl
      exact ⟨leftTrack.append (.step leftStep leftEdit (.done _ _)), rightTrack.append (.step rightStep rightEdit (.done _ _))⟩

theorem stringReplay {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (growth : Core3.Grows origin.core left.store.core)
    (checkAt : left.ctl = check.control (runStoreSteps cx ptr steps >>= checkNext))
    (canonAt : right.ctl = canon.control (runStoreSteps cx ptr steps >>= canonNext))
    {finish : State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Nat → Prop}
    (ends : ∀ left right check canon pointer, ChildFrameOver changes left right check canon →
      Core3.Grows origin.core left.store.core →
      left.ctl = check.control (checkNext pointer) → right.ctl = canon.control (canonNext pointer) →
      finish left right check canon pointer) :
    StringReplay profile ready bindings changes cx checkNext canonNext steps.length left right check canon finish := by
  induction measured : steps.length using Nat.strong_induction_on generalizing ptr steps left right check canon with
  | ind length ih =>
    have cut := stringPlanCut (profile := profile) (ready := ready) (bindings := bindings)
      cx ptr steps checkNext canonNext frame checkAt canonAt
    rw [measured] at cut
    rw [StringReplay]
    cases cut with
    | done localRun =>
      obtain ⟨store, result, labels, silent, checked, canonical, tracked⟩ := localRun
      refine .done silent checked canonical (fun pointer done depth => ?_) (fun pointer done => ends _ _ _ _ pointer
        ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩ ?_ rfl rfl)
      · subst result
        exact tracked pointer rfl depth
      · subst result
        exact growth.trans checked.grows
    | @installed pointer oldSize alignment size rest shorter store labels checked canonical silent tracked paired outside =>
      refine .allocated pointer oldSize alignment size rest shorter checked canonical silent tracked ?_
      intro dispatch leftEntry rightEntry first second wider last seen protectedReturn path covers
      obtain ⟨leftLabels, rightLabels, other, mark, lhs, rhs, matched, leftSeen, rightSeen, remaining, leftTrail, rightTrail⟩ :=
        replayMarked path covers paired outside
      refine ⟨leftLabels, rightLabels, other, mark, lhs, rhs, leftSeen, rightSeen, matched, leftTrail, rightTrail, ?_⟩
      intro value cursor atMark leftAt
      obtain ⟨original, same, track⟩ := Occurrence.Trail.survives (atMark ▸ rightTrail)
      cases same
      have rightMark := (Occurrence.prefix_survives track).2
      have rightInstalled : Occurrence.segmentAt (Occurrence.segmentStorage rightEntry) (.active 0 0) =
          some (.prog second) := rfl
      have old : Occurrence.Outside changes (Occurrence.segmentStorage last) (Occurrence.segmentStorage other)
          (some (.active 0 0)) := atMark ▸ remaining
      obtain ⟨otherCursor, residual, rightAt, leftPop, rightPop⟩ := markedReturn (profile := profile) (ready := ready)
        (bindings := bindings) matched old leftAt (rightMark.trans rightInstalled)
      have resumedLeft : first (.nat value) = (runStoreSteps cx value rest >>= checkNext) := rfl
      have resumedRight : second (.nat value) = (runStoreSteps cx value rest >>= canonNext) := rfl
      rw [resumedLeft] at leftPop
      rw [resumedRight] at rightPop
      refine ⟨otherCursor, leftPop, rightPop, ?_, ?_⟩
      · intro depth
        obtain ⟨leftTrack, rightTrack⟩ := tracked depth
        exact ⟨Occurrence.Trail.through_return leftTrack (atMark ▸ leftTrail) leftAt,
          Occurrence.Trail.through_return rightTrack (atMark ▸ rightTrail) rightAt⟩
      · exact ih rest.length shorter value rest
          (show ChildFrameOver changes { last with ctl := cursor.control (runStoreSteps cx value rest >>= checkNext) }
            { other with ctl := otherCursor.control (runStoreSteps cx value rest >>= canonNext) } cursor otherCursor from
            ⟨residual.store, residual.pending, residual.results, residual.cancels, residual.blocked, residual.thread,
              residual.frames, residual.rest⟩)
          ((growth.trans checked.grows).trans lhs.grows) rfl rfl rfl

theorem stringFieldReplay {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (str : Value.StrVal) (valid : str.Valid)
    (index : Nat) (output : Lower.Output)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (present : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (fit : StoreStringPre Quirks.none destination.encoding destination.width str)
    (placed : rootPlacement destination left.store (.prim .string) output = .ok ())
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.data (.prim .string) ⟨.string str, .string valid⟩) index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.data (.prim .string) ⟨.string str, .string valid⟩) output >>= canonNext)) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let cx := destination.context inst
    let plan := storePlanFor Quirks.none destination.encoding destination.width str
    let checked := fun ptr => stringPlanTail cx destination.width output plan ptr >>= fun value => checkNext (.ok value)
    let canonical := fun ptr => stringPlanTail cx destination.width output plan ptr >>= canonNext
    let lhs := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checked) }
    let rhs := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonical) }
    ∃ reads, Occurrence.RetainsActiveSlots profile ready dispatch left (List.replicate reads .tau) lhs ∧
      Occurrence.RetainsActiveSlots profile ready dispatch right [.tau] rhs ∧
      StringReplay profile ready bindings changes cx checked canonical plan.steps.length lhs rhs check canon
        (fun left right check canon _ =>
          StringLocalCut profile ready dispatch left right check canon (fun value => checkNext (.ok value)) canonNext) := by
  intro dispatch cx plan checked canonical lhs rhs
  obtain ⟨reads, memory, flat⟩ := string_plan_entry (profile := profile) (ready := ready) (dispatch := dispatch)
    destination inst str valid index output left right check canon checkNext canonNext
    frame.store present realloc fit placed checkAt canonAt
  have entered : ChildFrameOver changes lhs rhs check canon :=
    ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
  refine ⟨reads, memory, flat, stringReplay (origin := lhs.store) cx 0 plan.steps checked canonical entered
    (Core3.Grows.refl _) rfl rfl ?_⟩
  intro left right check canon pointer frame _ checkAt canonAt
  exact string_descriptor_cut cx destination.width output plan pointer left right check canon
    (fun value => checkNext (.ok value)) canonNext frame.store checkAt canonAt

theorem stringFieldThen {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (item : StringField) (output : Lower.Output) (index : Nat)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (fit : StoreStringPre Quirks.none destination.encoding destination.width item.value)
    (placed : rootPlacement destination left.store (.prim .string) output = .ok ())
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item.field index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width item.field output >>= canonNext))
    {next : output.Result → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Prop}
    (ends : ∀ words left right check canon, ChildFrameOver older left right check canon →
      Core3.Grows origin.core left.store.core → left.ctl = check.control (checkNext (.ok words)) →
      right.ctl = canon.control (canonNext words) → next words left right check canon) :
    StringFieldThen profile ready bindings older destination inst item.value output left right check canon checkNext canonNext next := by
  dsimp only [StringFieldThen]
  let cx := destination.context (grow := grow) inst
  let plan := storePlanFor Quirks.none destination.encoding destination.width item.value
  let checked := fun ptr => stringPlanTail cx destination.width output plan ptr >>= fun value => checkNext (.ok value)
  let canonical := fun ptr => stringPlanTail cx destination.width output plan ptr >>= canonNext
  have reached := growth.memAddrType present
  obtain ⟨reads, memory, flat⟩ := string_plan_entry (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (host bindings)) destination inst item.value item.valid index output left right check canon
    checkNext canonNext frame.store (frame.store ▸ reached) realloc fit placed checkAt canonAt
  let lhs := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checked) }
  let rhs := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonical) }
  have entered : ChildFrameOver older lhs rhs check canon :=
    ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
  refine ⟨reads, memory, flat, stringReplay (profile := profile) (ready := ready) (bindings := bindings)
    cx 0 plan.steps checked canonical entered growth rfl rfl ?_⟩
  intro lhs rhs check canon pointer frame growing lhsAt rhsAt
  obtain ⟨store, result, labels, silent, lhsRun, rhsRun, tracked⟩ := string_descriptor_cut cx destination.width output plan pointer
    lhs rhs check canon (fun value => checkNext (.ok value)) canonNext frame.store lhsAt rhsAt
  refine ⟨store, result, labels, silent, lhsRun, rhsRun, ?_⟩
  intro value success
  subst result
  exact ⟨fun depth => (tracked value rfl depth).1, fun depth => (tracked value rfl depth).2,
    ends value _ _ _ _ ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
      (growing.trans lhsRun.grows) rfl rfl⟩

theorem flatSequenceReplay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (items : List Field) (index : Nat) (leading : List FlatValue)
    (compare : FlatFieldComparison grow sig) (checkNext : FlatSequenceCheckNext grow sig) (canonNext : FlatSequenceCanonNext grow sig)
    (finish : FlatResultCut grow sig)
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (rules : ∀ item ∈ items, FlatFieldRule compare older origin destination inst item)
    (ends : ∀ words reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok words)) →
      reference.ctl = canon.control (canonNext words) → finish words reached reference check canon)
    (checkAt : left.ctl = check.control (flatSequenceChecked destination inst items index leading checkNext))
    (canonAt : right.ctl = canon.control (flatSequenceCanonical destination inst items leading canonNext)) :
    FlatSequenceReplay compare older destination inst checkNext canonNext finish items index leading left right check canon := by
  induction items generalizing index leading left right check canon with
  | nil =>
    change finish leading left right check canon
    apply ends leading left right check canon frame growth
    · simpa [flatSequenceChecked, Record.Effects.flat, Prog.bind_eq, Prog.pure_eq, Except.map] using checkAt
    · simpa [flatSequenceCanonical, CanonicalTree.flat, Prog.bind_eq, Prog.pure_eq] using canonAt
  | cons item rest ih =>
    rw [FlatSequenceReplay]
    apply rules item (by simp) index _ _ left right check canon frame growth
    · rw [checkAt]
      congr 1
      simp only [flatSequenceChecked, Record.Effects.flat, Prog.bind_eq, Prog.bind_assoc]
      congr 1
      funext result
      cases result with
      | error _ => rfl
      | ok words =>
        simp only [Prog.bind_assoc]
        congr 1
        funext tailResult
        cases tailResult with
        | error _ => rfl
        | ok later =>
          change checkNext (.ok (leading ++ ((show List FlatValue from words) ++ later))) =
            checkNext (.ok ((leading ++ (show List FlatValue from words)) ++ later))
          rw [List.append_assoc]
    · rw [canonAt]
      congr 1
      let head : Session grow sig (List FlatValue) := CanonicalTree.field Limits.spec Quirks.none
        (destination.context inst) destination.width item .flat
      let tail : Session grow sig (List FlatValue) := CanonicalTree.flat Limits.spec Quirks.none
        (destination.context inst) destination.width rest
      change (head.bind (fun words => tail.bind (fun later => .pure (words ++ later)))).bind
        (fun words => canonNext (leading ++ words)) =
        head.bind (fun words => tail.bind (fun later => canonNext ((leading ++ words) ++ later)))
      simp only [Prog.bind_assoc, Prog.pure_bind', List.append_assoc]
    · intro words reached reference check canon paired grown checkAt canonAt
      exact ih (index + 1) (leading ++ words) paired grown (fun item member => rules item (List.mem_cons_of_mem _ member))
        checkAt canonAt

theorem flatAggregateThen {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (children : List Field) (index : Nat)
    (compare : FlatFieldComparison grow sig) (checkNext : FlatSequenceCheckNext grow sig) (canonNext : FlatSequenceCanonNext grow sig)
    (finish : FlatResultCut grow sig) {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (rules : ∀ item ∈ children, FlatFieldRule compare older origin destination inst item)
    (ends : ∀ words reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok words)) →
      reference.ctl = canon.control (canonNext words) → finish words reached reference check canon)
    (checkAt : left.ctl = check.control (do
      let verdict ← Record.Effects.flat recordClaims Limits.spec Quirks.none (destination.context inst) destination.width children 0
      checkNext (verdict.mapError (.nested index))))
    (canonAt : right.ctl = canon.control (CanonicalTree.flat Limits.spec Quirks.none (destination.context inst)
      destination.width children >>= canonNext)) :
    FlatAggregateThen compare older destination inst children index left right check canon checkNext canonNext finish := by
  have noLeading (verdict : Except RecordLower.Issue (List FlatValue)) : verdict.map ([] ++ ·) = verdict := by cases verdict <;> rfl
  exact flatSequenceReplay destination inst children 0 [] compare (fun verdict => checkNext (verdict.mapError (.nested index)))
    canonNext finish frame growth rules ends (by simpa only [flatSequenceChecked, noLeading] using checkAt)
    (by simpa [flatSequenceCanonical] using canonAt)

private theorem flatSumThen {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (type : TypeOf) (arms : List (Option TypeOf))
    (tag index : Nat) (selected : Option Field) (valid : tag < arms.length)
    (compare : FlatFieldComparison grow sig) (checkNext : FlatSequenceCheckNext grow sig) (canonNext : FlatSequenceCanonNext grow sig)
    (finish : FlatResultCut grow sig) {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (rules : ∀ item, selected = some item → FlatFieldRule compare older origin destination inst item)
    (ends : ∀ words reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok words)) →
      reference.ctl = canon.control (canonNext words) → finish words reached reference check canon)
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.sum type arms tag selected) index .flat >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.sum type arms tag selected) .flat >>= canonNext)) :
    FlatSumThen profile ready bindings compare destination.width type arms.length tag selected index left right check canon
      checkNext canonNext finish := by
  have tailRule (haves : List CoreType) (words : List FlatValue) (reached reference : State grow sig)
      (check canon : Cursor (E := core3 grow) (HostState sig)) (paired : ChildFrameOver older reached reference check canon)
      (grown : Core3.Grows origin.core reached.store.core)
      (checkAt : reached.ctl = check.control (flatSumTail destination.width type arms.length tag haves words >>= fun value => checkNext (.ok value)))
      (canonAt : reference.ctl = canon.control (flatSumTail destination.width type arms.length tag haves words >>= canonNext)) :
      LocalFieldThen profile ready bindings .flat reached reference check canon checkNext canonNext finish := by
    have checked : reached.ctl = check.control ((do return .ok (← flatSumTail destination.width type arms.length tag haves words)) >>= checkNext) := by
      simpa only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using checkAt
    obtain ⟨store, result, chk, ref, checkRun, canonRun, labels, status⟩ :=
      variant_tail_frame (profile := profile) (ready := ready) (dispatch := specDispatch ready (host bindings))
        arms.length ((flatten destination.width type).drop 1) tag haves words
        (keep := fun store => Core3.Grows origin.core store.core) reached reference (paired.store ▸ grown)
        paired.store check canon paired.thread checkNext canonNext checked canonAt
    refine ⟨store, result, chk, ref, checkRun, canonRun, labels, ?_⟩
    cases result with
    | error _ => exact status
    | ok value =>
      exact ⟨status.2.1, status.2.2,
        ends value _ _ _ _ ⟨rfl, paired.pending, paired.results, paired.cancels, paired.blocked, paired.thread, paired.frames, paired.rest⟩
          status.1 rfl rfl⟩
  cases selected with
  | none =>
    have checked : left.ctl = check.control (flatSumTail destination.width type arms.length tag [] [] >>= fun value => checkNext (.ok value)) := by
      let body : Session grow sig (List FlatValue) := flatSumTail destination.width type arms.length tag [] []
      rw [checkAt]
      change check.control ((body.bind fun value => .pure (.ok value)).bind checkNext) = _
      rw [Prog.bind_assoc]
      rfl
    have canonical : right.ctl = canon.control (flatSumTail destination.width type arms.length tag [] [] >>= canonNext) := canonAt
    exact ⟨checked, canonical, tailRule [] [] left right check canon frame growth checked canonical⟩
  | some child =>
    unfold FlatSumThen
    apply rules child rfl 0 _ _ left right check canon frame growth
    · rw [checkAt]
      let body : Session grow sig (Except RecordLower.Issue (List FlatValue)) :=
        Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width child 0 .flat
      let tail : List FlatValue → Session grow sig (List FlatValue) :=
        flatSumTail destination.width type arms.length tag (flatten destination.width child.type)
      change check.control ((body.bind fun verdict => match verdict with
        | .error issue => .pure (.error (.nested index issue))
        | .ok words => (tail words).bind fun value => .pure (.ok value)).bind checkNext) =
          check.control (body.bind (flatSumCheckNext destination.width type arms.length tag index
            (flatten destination.width child.type) checkNext))
      rw [Prog.bind_assoc]
      apply congrArg (fun next => check.control (body.bind next))
      funext verdict
      cases verdict with
      | error _ => rfl
      | ok words => rw [Prog.bind_assoc]; rfl
    · rw [canonAt]
      congr 1
      let body : Session grow sig (List FlatValue) := CanonicalTree.field Limits.spec Quirks.none
        (destination.context inst) destination.width child .flat
      let haves := flatten destination.width child.type
      change (lowerFlatVariantWith arms.length ((flatten destination.width type).drop 1) tag haves body).bind canonNext =
        body.bind fun words => (flatSumTail destination.width type arms.length tag haves words).bind canonNext
      simp only [flatSumTail, lowerFlatVariantWith, valid, ↓reduceIte, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
    · intro words reached reference check canon paired grown checkAt canonAt
      exact ⟨checkAt, canonAt, tailRule (flatten destination.width child.type) words reached reference check canon paired grown checkAt canonAt⟩

private theorem flatChildPath {field child leaf : Field} {children : List Field}
    (atChildren : flatChildren field = some children) (member : child ∈ children)
    (path : Field.Descendant child leaf) : Field.Descendant field leaf := by
  cases field <;> cases atChildren
  · exact .aggregate member path
  · exact .fixed member path
  · rename_i type arms tag selected
    cases selected with
    | none => simp at member
    | some item =>
      have same : child = item := by simpa using member
      subst child
      exact .sum path

theorem flatNestedRefine {shapeAt fitsAt : Field → Prop} (depth : Nat) (field : Field)
    (shape : FlatNestedFits shapeAt depth field)
    (reached : ∀ leaf, Field.Descendant field leaf → shapeAt leaf → fitsAt leaf) : FlatNestedFits fitsAt depth field := by
  induction depth generalizing field with
  | zero => exact reached field (.self field) shape
  | succ depth ih =>
    cases childrenAt : flatChildren field with
    | none =>
      simp only [FlatNestedFits, childrenAt] at shape
      simpa only [FlatNestedFits, childrenAt] using reached field (.self field) shape
    | some children =>
      simp only [FlatNestedFits, childrenAt] at shape
      simp only [FlatNestedFits, childrenAt]
      intro child member
      apply ih child (shape child member)
      intro leaf path leafShape
      exact reached leaf (flatChildPath childrenAt member path) leafShape

theorem nestedFlatRule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (leaf : Field → Prop) (compare : FlatFieldComparison grow sig)
    (rules : ∀ field, leaf field → FlatFieldRule compare older origin destination inst field)
    (depth : Nat) (field : Field) (fits : FlatNestedFits leaf depth field) (tags : FlatTagBounds field) :
    FlatFieldRule (nestedFlatComparison profile ready bindings compare older destination inst depth) older origin destination inst field := by
  induction depth generalizing field with
  | zero => exact rules field fits
  | succ depth ih =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt next ends
    cases childrenAt : flatChildren field with
    | none =>
      have admissible : leaf field := by simpa only [FlatNestedFits, childrenAt] using fits
      simpa only [nestedFlatComparison, childrenAt] using
        rules field admissible index checkNext canonNext left right check canon frame growth checkAt canonAt next ends
    | some children =>
      have admissible : ∀ child ∈ children, FlatNestedFits leaf depth child := by
        simpa only [FlatNestedFits, childrenAt] using fits
      have childRule : ∀ item ∈ children, FlatFieldRule
          (nestedFlatComparison profile ready bindings compare older destination inst depth) older origin destination inst item :=
        fun item member => ih item (admissible item member) (fun path => tags (flatChildPath childrenAt member path))
      simp only [nestedFlatComparison, childrenAt]
      cases field <;> cases childrenAt
      case sum.refl type arms tag selected =>
        refine flatSumThen destination inst type arms tag index selected (tags (.self _)) _ checkNext canonNext next frame growth
          (fun item same => childRule item (by simp [same])) ends checkAt canonAt
      case aggregate.refl | fixed.refl =>
        apply flatAggregateThen destination inst _ index _ checkNext canonNext next frame growth childRule ends
        · rw [checkAt]
          let body : Session grow sig (Except RecordLower.Issue (List FlatValue)) :=
            Record.Effects.flat recordClaims Limits.spec Quirks.none (destination.context inst) destination.width children 0
          change check.control ((body.bind fun verdict => .pure (verdict.mapError (.nested index))).bind checkNext) = _
          rw [Prog.bind_assoc]
          rfl
        · exact canonAt

theorem stringFlatRule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (item : StringField)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (fit : StoreStringPre Quirks.none destination.encoding destination.width item.value) :
    FlatFieldRule (stringFlatComparison profile ready bindings older destination inst) older origin destination inst item.field := by
  intro index checkNext canonNext left right check canon frame growth checkAt canonAt next ends
  exact ⟨item, rfl, stringFieldThen destination inst item .flat index checkNext canonNext frame growth present realloc fit rfl
    checkAt canonAt ends⟩

theorem handleFieldThen {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (item : Field) (handle : CanonicalHandle item)
    (index : Nat) (output : Lower.Output)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width item output >>= canonNext))
    {next : output.Result → State grow sig → State grow sig → Cursor (E := core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Prop}
    (ends : ∀ value reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok value)) →
      reference.ctl = canon.control (canonNext value) → next value reached reference check canon) :
    HandleFieldThen profile ready bindings item index output left right check canon checkNext canonNext next := by
  have checkLeaf : left.ctl = check.control (Record.Effects.checkedLeaf recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index output >>= checkNext) := by
    cases item <;> first | exact checkAt | exact False.elim handle
  have canonLeaf : right.ctl = canon.control (CanonicalTree.leaf Limits.spec Quirks.none
      (destination.context inst) destination.width item output >>= canonNext) := by
    cases item <;> first | exact canonAt | exact False.elim handle
  have run := RecordDestination.compare_handle_leaf (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (host bindings)) frame.store destination inst item handle index output checkNext canonNext
    (thread := check.thread) (checkFrames := check.frames) (checkRest := check.rest)
    (canonFrames := canon.frames) (canonRest := canon.rest) checkLeaf (by simpa only [Cursor.control, frame.thread] using canonLeaf)
  unfold HandleFieldThen
  cases planned : liveLeafPlan left.store left.host.writer index item with
  | error issue => simpa only [planned, Cursor.control] using run
  | ok plan =>
    rw [planned] at run
    obtain ⟨store, result, leading, checkLabels, canonLabels, grew, silent, checkTrace, canonTrace, checked, canonical, tracks⟩ := run
    have canonThread := frame.thread
    refine ⟨store, result, leading, checkLabels, canonLabels, silent, checkTrace, canonTrace, checked, ?_, ?_⟩
    · simpa only [canonThread] using canonical
    · intro value success
      obtain ⟨checkTrack, canonTrack⟩ := tracks value success
      refine ⟨checkTrack, by simpa only [canonThread, localLeafEnd, Cursor.control] using canonTrack, ?_⟩
      exact ends value _ _ _ _ ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
        ((frame.store ▸ growth).trans grew) rfl rfl

theorem mixedFlatRule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (item : Field)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (allocator : Validation.containsPtr item.type = true → ∃ addr, destination.realloc = some addr)
    (fit : CanonicalHandle item ∨ StringField.Fits destination item) :
    FlatFieldRule (mixedFlatComparison profile ready bindings older destination inst) older origin destination inst item := by
  intro index checkNext canonNext left right check canon frame growth checkAt canonAt next ends
  rcases fit with handle | ⟨str, rfl, fits⟩
  · exact .inl ⟨handle, handleFieldThen destination inst item handle index .flat checkNext canonNext frame growth checkAt canonAt ends⟩
  · obtain ⟨_, realloc⟩ := allocator rfl
    exact .inr (stringFlatRule destination inst str present realloc fits index checkNext canonNext left right check canon
      frame growth checkAt canonAt next ends)

theorem childCollectionInstall {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (reachedWidth : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let dispatch := specDispatch ready (host bindings)
    let area := layout destination.width element
    let first := checkedCollectionResume destination inst entries area index output checkNext
    let second := canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    let checkCall := collectionEntry destination inst area entries.length dispatch left check first
    let canonCall := collectionEntry destination inst area entries.length dispatch right canon second
    (∀ depth, Occurrence.Prefix profile ready dispatch left (.active 0 depth) [.tau, .tau, .tau]
      checkCall (.active 0 (depth + 1))) ∧
    (∀ depth, Occurrence.Prefix profile ready dispatch right (.active 0 depth) [.tau, .tau]
      canonCall (.active 0 (depth + 1))) ∧
    HostFrame.Related.Paired (ReturnFrame.Extend changes first second) checkCall canonCall := by
  have tracks := collection_install_tracks (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (host (grow := grow) bindings)) destination inst type element entries output index
    left right check canon checkNext canonNext reachedWidth prepared checkAt canonAt
  exact ⟨fun depth => (tracks depth).1, fun depth => (tracks depth).2, childFrameEnter frame _ _ _⟩

private theorem rangeAtReturn (destination : RecordDestination) (inst : InstId) (area : Layout)
    (count pointer : Nat) (plan : List Object) {left right last other : State grow sig} {seen leftLabels rightLabels}
    {changes older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {allowCommon : Prop} {mark}
    {cursor canonCursor : Cursor (E := core3 grow) (HostState sig)}
    (lhs : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) left leftLabels last)
    (rhs : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) right rightLabels other)
    (checkTrail : Occurrence.Trail profile ready (specDispatch ready (host bindings)) left mark leftLabels last mark)
    (canonTrail : Occurrence.Trail profile ready (specDispatch ready (host bindings)) right mark rightLabels other mark)
    (reached : HostFrame.Related.Paired changes last other)
    (frame : ChildFrameOver older last other cursor canonCursor)
    (seenLeft : visible leftLabels = seen) (seenRight : visible rightLabels = seen)
    (leftAt : last.ctl = { cursor with frames := .prog first :: cursor.frames }.control (pure (.nat pointer)))
    (atPop : other.ctl = ⟨cursor.thread, .prog (.pure (.nat pointer)), .prog second :: canonCursor.frames⟩ :: canonCursor.rest)
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Nat → Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (checkBody : first (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area count pointer
      let live ← Record.Effects.reserve recordClaims plan
      checkNext ptr live))
    (canonBody : second (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= canonNext)) :
    RangeCutOver profile ready bindings older first left right last cursor destination area count pointer plan checkNext canonNext seen allowCommon mark := by
    have width := lhs.grows.memAddrType present
    obtain ⟨reachedBytes, reachedSize, _⟩ := lhs.grows.memSize sized
    have validation := destination.paired_range_recheck (profile := profile) (ready := ready)
      (dispatch := specDispatch ready (host (grow := grow) bindings)) reached inst area count pointer plan
      checkNext canonNext checkBody canonBody leftAt atPop reachedSize
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    have append {start middle finish : State grow sig} {leading trailing : List (Label (core3 grow) (HostState sig))}
        (run : Steps profile ready dispatch start leading middle)
        (next : Steps profile ready dispatch middle trailing finish) :
        Steps profile ready dispatch start (leading ++ trailing) finish := by
      induction run with
      | refl => exact next
      | cons step _ ih => exact .cons step (ih next)
    have trapped (reason : TrapReason)
        (checked : ∃ steps, Steps profile ready dispatch last (List.replicate steps .tau ++ [.trap reason])
          (StepDefs.trapCfg last))
        (canonical : ∃ steps, Steps profile ready dispatch other (List.replicate steps .tau ++ [.trap reason])
          (StepDefs.trapCfg other)) :
        RangeCutOver profile ready bindings older first left right last cursor destination area count pointer plan checkNext canonNext seen allowCommon mark := by
      obtain ⟨checkCount, checked⟩ := checked
      obtain ⟨canonCount, canonical⟩ := canonical
      refine .trapped (reason := reason) frame.store (append lhs.steps checked) (append rhs.steps canonical) ?_ ?_
      · rw [show visible (leftLabels ++ (List.replicate checkCount .tau ++ [.trap reason])) =
          visible leftLabels ++ (visible (List.replicate checkCount .tau) ++ visible [.trap reason]) from by
          simp only [visible, List.filter_append], seenLeft, silent checkCount]; rfl
      · rw [show visible (rightLabels ++ (List.replicate canonCount .tau ++ [.trap reason])) =
          visible rightLabels ++ (visible (List.replicate canonCount .tau) ++ visible [.trap reason]) from by
          simp only [visible, List.filter_append], seenRight, silent canonCount]; rfl
    dsimp only at validation
    by_cases unaligned : pointer ≠ alignTo pointer area.alignment
    · rw [ite_eq_left unaligned] at validation
      exact trapped .unalignedPointer validation.1 validation.2
    by_cases fits : pointer + count * area.size ≤ reachedBytes
    · rw [ite_eq_right unaligned, ite_eq_left fits] at validation
      obtain ⟨⟨checkLabels, checkSilent, checkTracks⟩, ⟨canonLabels, canonSilent, canonTracks⟩⟩ := validation
      have hide {labels : List (Label (core3 grow) (HostState sig))}
          (allTau : ∀ label ∈ labels, label = .tau) : visible labels = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro label member
        simp only [allTau label member, Bool.false_eq_true, not_false_eq_true]
      have canonThread : canonCursor.thread = cursor.thread := frame.thread.symm
      have canonRun : Occurrence.RetainsBelowTop profile ready dispatch other canonLabels
          { other with ctl := canonCursor.control (canonNext pointer) } := by
        simpa only [Cursor.control, canonThread] using canonTracks
      refine .reached (canonCursor := canonCursor) width reachedSize (Classical.not_not.mp unaligned) fits frame lhs.grows
        ⟨leftLabels, checkLabels, rfl, lhs.steps, checkTrail, checkTracks⟩
        ⟨rightLabels, canonLabels, rfl, rhs.steps, canonTrail, canonRun⟩ ?_ ?_
      · rw [show visible (leftLabels ++ checkLabels) = visible leftLabels ++ visible checkLabels from List.filter_append ..,
          seenLeft, hide checkSilent, List.append_nil]
      · rw [show visible (rightLabels ++ canonLabels) = visible rightLabels ++ visible canonLabels from List.filter_append ..,
          seenRight, hide canonSilent, List.append_nil]
    · rw [ite_eq_right unaligned, ite_eq_right fits] at validation
      exact trapped .outOfBounds validation.1 validation.2

theorem rangeCutOver (destination : RecordDestination) (inst : InstId) (area : Layout) (count pointer : Nat) (plan : List Object)
    {left right last : State grow sig} {seen}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop}
    (path : PrefixFor profile ready bindings protectedReturn left seen last)
    (covers : ∀ first second, changes first second → protectedReturn first)
    (paired : HostFrame.Related.Paired changes left right) (cursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { cursor with frames := .prog first :: cursor.frames }.control (pure (.nat pointer)))
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Nat → Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (checkBody : first (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area count pointer
      let live ← Record.Effects.reserve recordClaims plan
      checkNext ptr live))
    (canonBody : ∀ resume, changes first resume →
      resume (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= canonNext)) :
    RangeCutOver profile ready bindings changes first left right last cursor destination area count pointer plan checkNext canonNext seen := by
  obtain ⟨leftLabels, rightLabels, other, lhs, rhs, reached, seenLeft, seenRight⟩ := replayFor path covers paired
  obtain ⟨otherFrames, otherRest, ⟨resume, edge, atPop, frame⟩ | ⟨atCommon, still⟩⟩ := classifyPopFor other.host reached leftAt
  · exact rangeAtReturn destination inst area count pointer plan lhs rhs (Occurrence.Trail.absent lhs.steps)
      (Occurrence.Trail.absent rhs.steps) reached frame seenLeft seenRight
      leftAt atPop present sized checkNext canonNext checkBody (canonBody resume edge)
  · refine .common ⟨leftLabels ++ [.tau], rightLabels ++ [.tau], _,
      (lhs.append (.cons ?_ (.popProg leftAt) (.refl _))).steps,
      (rhs.append (.cons ?_ (.popProg atCommon) (.refl _))).steps, still, ?_, ?_⟩ trivial
    · simp [CoreUpdateGrows, leftAt, Cursor.control]
    · simp [CoreUpdateGrows, atCommon]
    · simpa only [visible, List.filter_append, List.filter_cons, List.filter_nil, Bool.false_eq_true,
        ↓reduceIte, List.append_nil] using seenLeft
    · simpa only [visible, List.filter_append, List.filter_cons, List.filter_nil, Bool.false_eq_true,
        ↓reduceIte, List.append_nil] using seenRight

theorem collectionReplay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (index : Nat) (output : Lower.Output)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon)
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    CollectionReplay profile ready bindings older destination inst type element entries index output left right check canon checkNext canonNext := by
  dsimp only [CollectionReplay, CollectionReplayFor]
  obtain ⟨checkInstall, canonInstall, paired⟩ := childCollectionInstall (profile := profile) (ready := ready) (bindings := bindings)
    destination inst type element entries output index checkNext canonNext frame (frame.store ▸ present) prepared checkAt canonAt
  refine ⟨checkInstall, canonInstall, ?_⟩
  intro last seen protectedReturn path covers
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  let area := layout destination.width element
  let first := checkedCollectionResume destination inst entries area index output checkNext
  let second := canonicalCollectionResume destination inst entries area output canonNext
    (CanonicalTree.EntryMode.forOutput destination.width type output)
  let checked := collectionEntry destination inst area entries.length dispatch left check first
  let canonical := collectionEntry destination inst area entries.length dispatch right canon second
  have outside := childFrameOutside frame
    (dispatch (.reallocate (destination.context inst) 0 0 area.alignment.bytes (entries.length * area.size))) first second
  obtain ⟨leftLabels, rightLabels, other, mark, lhs, rhs, matched, leftSeen, rightSeen, remaining, leftTrail, rightTrail⟩ :=
    replayMarked path covers paired outside
  refine ⟨leftLabels, rightLabels, other, mark, lhs, rhs, leftSeen, rightSeen, matched, leftTrail, rightTrail, ?_⟩
  intro pointer cursor atMark leftAt
  obtain ⟨original, same, track⟩ := Occurrence.Trail.survives (atMark ▸ rightTrail)
  cases same
  have rightMark := (Occurrence.prefix_survives track).2
  have installed : Occurrence.segmentAt (Occurrence.segmentStorage canonical) (.active 0 0) = some (.prog second) := rfl
  obtain ⟨otherCursor, residual, rightAt, _, _⟩ := markedReturn (profile := profile) (ready := ready) (bindings := bindings)
    matched (atMark ▸ remaining) leftAt (rightMark.trans installed)
  have alignedThread : otherCursor.thread = cursor.thread := residual.thread.symm
  exact rangeAtReturn destination inst _ entries.length pointer _ lhs rhs (atMark ▸ leftTrail) (atMark ▸ rightTrail)
    matched residual leftSeen rightSeen leftAt
    (by simpa only [Cursor.control, alignedThread] using rightAt) present sized _ _ rfl rfl

theorem rangeCut (destination : RecordDestination) (inst : InstId) (area : Layout) (count pointer : Nat) (plan : List Object)
    {left right last : State grow sig} {seen} (path : Prefix profile ready bindings first left seen last)
    (paired : HostFrame.Paired first second left right) (cursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { cursor with frames := .prog first :: cursor.frames }.control (pure (.nat pointer)))
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Nat → Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (checkBody : first (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area count pointer
      let live ← Record.Effects.reserve recordClaims plan
      checkNext ptr live))
    (canonBody : second (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= canonNext)) :
    RangeCut profile ready bindings first second left right last cursor destination area count pointer plan checkNext canonNext seen :=
  rangeCutOver destination inst area count pointer plan path (fun _ _ edge => by cases edge; rfl)
    paired cursor leftAt present sized checkNext canonNext checkBody (fun _ edge => by cases edge; exact canonBody)

theorem collectionDescent (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (output : Lower.Output) (index : Nat) (left right : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (present : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? right.store.core destination.memory = some bytes)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    CollectionDescent profile ready bindings destination inst type element entries output index left right cursor checkNext canonNext := by
  dsimp only [CollectionDescent]
  obtain ⟨checked, canonical, paired⟩ := PayloadPrefix.collection_install_mode (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (host (grow := grow) bindings)) destination inst type element entries output index
    left right cursor checkNext canonNext same present prepared checkAt canonAt
  have stores : left.store = right.store := by simpa only using congrArg (fun cfg : State grow sig => cfg.store) same
  refine ⟨checked, canonical, paired, ?_⟩
  intro last seen path reached pointer atReturn
  exact rangeCut destination inst (layout destination.width element) entries.length pointer (Field.listObjects entries)
    path paired reached atReturn (stores ▸ present) (stores ▸ sized) _ _ rfl rfl

private theorem collectionReturnKeeping (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat)
    {left right last : State grow sig} {labels} (path : Prefix profile ready bindings first left labels last)
    (paired : HostFrame.Paired first second left right) (checkCursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { checkCursor with frames := .prog first :: checkCursor.frames }.control (pure (.nat pointer)))
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (checkBody : first (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : second (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    {keep : CStore (core3 grow) → Prop}
    (compared : Core3.Grows left.store.core last.store.core → ∀ reference reachedBytes,
      ptrTypeIn last.store (destination.context inst) = destination.width →
      (core3 grow).memSize? last.store.core destination.memory = some reachedBytes →
      CollectionTailKeepingAt profile ready (specDispatch ready (host bindings)) keep destination inst entries area
        output index pointer reachedBytes last reference) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    (∃ canonCursor, canonCursor.thread = checkCursor.thread ∧
      ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor checkNext canonNext) ∨
    (∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels { last with ctl := checkCursor.control (first (.nat pointer)) } ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Paired first second { last with ctl := checkCursor.control (first (.nat pointer)) } other ∧
      visible leftLabels = labels ∧ visible rightLabels = labels) := by
  obtain ⟨leftLabels, rightLabels, other, lhs, rhs, reached, seenLeft, seenRight⟩ := replay path paired
  obtain ⟨otherFrames, otherRest, ⟨atPop, _⟩ | ⟨atCommon, still⟩⟩ := classifyPop other.host reached leftAt
  · let canonCursor : Cursor (E := core3 grow) (HostState sig) := ⟨checkCursor.thread, otherFrames, otherRest⟩
    have region := lhs.linked_region (destination.context inst) (start := 0) (length := 0)
      rfl present sized (by simp)
    obtain ⟨_, reachedWidth, bytes, reachedSize, _, _⟩ := region
    have continued := PayloadPrefix.collection_return_keeping_at destination inst entries area output index pointer last other
      checkCursor canonCursor checkNext canonNext first second reached rfl leftAt atPop checkBody canonBody reachedSize
      (compared lhs.grows other bytes reachedWidth reachedSize)
    exact .inl ⟨canonCursor, rfl, continued.prepend lhs.steps rhs.steps (seenLeft.trans seenRight.symm)⟩
  · refine .inr ⟨leftLabels ++ [.tau], rightLabels ++ [.tau], _, lhs.append (.cons ?_ (.popProg leftAt) (.refl _)),
      rhs.append (.cons ?_ (.popProg atCommon) (.refl _)), still, ?_, ?_⟩
    · simp [CoreUpdateGrows, leftAt, Cursor.control]
    · simp [CoreUpdateGrows, atCommon]
    · simpa only [visible, List.filter_append, List.filter_cons, List.filter_nil, Bool.false_eq_true,
        ↓reduceIte, List.append_nil] using seenLeft
    · simpa only [visible, List.filter_append, List.filter_cons, List.filter_nil, Bool.false_eq_true,
        ↓reduceIte, List.append_nil] using seenRight

theorem collectionReturn (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat)
    {left right last : State grow sig} {labels} (path : Prefix profile ready bindings first left labels last)
    (paired : HostFrame.Paired first second left right) (checkCursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { checkCursor with frames := .prog first :: checkCursor.frames }.control (pure (.nat pointer)))
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (checkBody : first (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : second (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    (compared : ReachedCollectionTail profile ready bindings destination inst entries area output index pointer last) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    (∃ canonCursor, canonCursor.thread = checkCursor.thread ∧
      Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext) ∨
    (∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels { last with ctl := checkCursor.control (first (.nat pointer)) } ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Paired first second { last with ctl := checkCursor.control (first (.nat pointer)) } other ∧
      visible leftLabels = labels ∧ visible rightLabels = labels) := by
  have cut := collectionReturnKeeping destination inst entries area output index pointer path paired checkCursor leftAt
    present sized checkNext canonNext checkBody canonBody (keep := fun _ => True) (by
      intro _ reference reachedBytes width size aligned fits live checked canonical checkStore canonStore checkHost canonHost
        same check canon thread finish next checkAt canonAt
      exact (compared reference reachedBytes width size aligned fits live checked canonical checkStore canonStore checkHost canonHost
        same check canon thread finish next checkAt canonAt).remember_true)
  rcases cut with ⟨cursor, thread, rest⟩ | common
  · exact .inl ⟨cursor, thread, rest.forget⟩
  · exact .inr common

private theorem chain {before middle after : State grow sig} {leading trailing : List (Label (core3 grow) (HostState sig))}
    (lhs : Steps profile ready (specDispatch ready (host (grow := grow) bindings)) before leading middle)
    (rhs : Steps profile ready (specDispatch ready (host (grow := grow) bindings)) middle trailing after) :
    Steps profile ready (specDispatch ready (host (grow := grow) bindings)) before (leading ++ trailing) after := by
  induction lhs with
  | refl => exact rhs
  | cons step _ ih => exact .cons step (ih rhs)

theorem collection (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (output : Lower.Output) (index pointer : Nat) {initial left right last : State grow sig} {before seen}
    (cursor reached : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (prefixRun : CoreGrowthSteps profile ready (specDispatch ready (host (grow := grow) bindings)) initial before right)
    (checkedDestination : destination.check initial.store = .ok ()) {bytes : Nat}
    (sized : (core3 grow).memSize? initial.store.core destination.memory = some bytes)
    (mode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
    let call := collectionEntry destination inst area entries.length dispatch left cursor checkResume
    Prefix profile ready bindings checkResume call seen last →
    last.ctl = { reached with frames := .prog checkResume :: reached.frames }.control (pure (.nat pointer)) →
    ReachedCollectionTail profile ready bindings destination inst entries area output index pointer last →
    CollectionCut profile ready bindings checkResume canonResume left right
      { last with ctl := reached.control (checkResume (.nat pointer)) } reached checkNext canonNext seen := by
  dsimp only
  intro path returned compared
  have original := destination.check_width initial.store checkedDestination
  have atEntry := prefixRun.grows.memAddrType original
  obtain ⟨checkEnter, canonEnter, paired⟩ := PayloadPrefix.collection_install destination inst type element entries
    output index left right cursor checkNext canonNext same atEntry mode prepared checkAt canonAt
  have region := prefixRun.linked_region (destination.context inst) (start := 0) (length := 0)
    rfl original sized (by simp)
  obtain ⟨size, readySize, _, _⟩ := region.2.2
  have sameStore : left.store = right.store := by
    simpa only using congrArg (fun (config : State grow sig) => config.store) same
  have seenWidth : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width := sameStore ▸ atEntry
  have seenSize : (core3 grow).memSize? left.store.core destination.memory = some size := sameStore ▸ readySize
  rcases collectionReturn destination inst entries (layout destination.width element) output index pointer path paired
    reached returned seenWidth seenSize checkNext canonNext rfl rfl compared with joined | common
  · obtain ⟨other, thread, tail⟩ := joined
    exact .inl ⟨other, thread, tail.prepend checkEnter canonEnter rfl⟩
  · obtain ⟨checkLabels, canonLabels, other, lhs, rhs, still, checkSeen, canonSeen⟩ := common
    exact .inr ⟨_, _, other, chain checkEnter lhs.steps, chain canonEnter rhs.steps, still, checkSeen, canonSeen⟩

theorem collectionMemory (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (output : Lower.Output) (index pointer : Nat) {origin : CStore (core3 grow)} {left right last : State grow sig} {seen}
    (cursor reached : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (growth : Core3.Grows origin.core right.store.core)
    (memoryWidth : (core3 grow).memAddrType? origin.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (mode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
    let call := collectionEntry destination inst area entries.length dispatch left cursor checkResume
    Prefix profile ready bindings checkResume call seen last →
    last.ctl = { reached with frames := .prog checkResume :: reached.frames }.control (pure (.nat pointer)) →
    (∀ item ∈ entries, MemoryChildRule profile ready dispatch destination inst item element) →
    CollectionCutKeeping profile ready bindings (fun store => Core3.Grows origin.core store.core)
      checkResume canonResume left right { last with ctl := reached.control (checkResume (.nat pointer)) }
      reached checkNext canonNext seen := by
  dsimp only
  intro path returned child
  have referenceWidth := growth.memAddrType memoryWidth
  obtain ⟨checkEnter, canonEnter, paired⟩ := PayloadPrefix.collection_install destination inst type element entries
    output index left right cursor checkNext canonNext same referenceWidth mode prepared checkAt canonAt
  obtain ⟨size, readySize, _⟩ := growth.memSize sized
  have sameStore : left.store = right.store := by
    simpa only using congrArg (fun (config : State grow sig) => config.store) same
  have seenWidth : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width :=
    sameStore ▸ referenceWidth
  have seenSize : (core3 grow).memSize? left.store.core destination.memory = some size := sameStore ▸ readySize
  have prior : Core3.Grows origin.core left.store.core := sameStore ▸ growth
  have cut := collectionReturnKeeping destination inst entries (layout destination.width element) output index pointer
    path paired reached returned seenWidth seenSize checkNext canonNext rfl rfl
    (keep := fun store => Core3.Grows origin.core store.core) (by
      intro callbackGrowth reference reachedBytes width reachedSize aligned fits live checked canonical checkStore canonStore
        checkHost canonHost same check canon thread finish next checkAt canonAt
      exact (CollectionTailKeepingAt.memory_entries destination inst element entries child output index pointer reachedBytes
        last reference width reachedSize aligned fits live checked canonical checkStore canonStore checkHost canonHost
        same check canon thread finish next checkAt canonAt).weaken (fun _ later => prior.trans (callbackGrowth.trans later)))
  rcases cut with joined | common
  · obtain ⟨referenceCursor, thread, tail⟩ := joined
    exact .inl ⟨referenceCursor, thread, tail.prepend checkEnter canonEnter rfl⟩
  · obtain ⟨checkLabels, canonLabels, other, lhs, rhs, still, checkSeen, canonSeen⟩ := common
    exact .inr ⟨_, _, other, chain checkEnter lhs.steps, chain canonEnter rhs.steps, still, checkSeen, canonSeen⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback
