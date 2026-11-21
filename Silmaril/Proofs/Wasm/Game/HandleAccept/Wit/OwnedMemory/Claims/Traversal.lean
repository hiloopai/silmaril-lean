module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Traversal.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.CollectionVisit.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Traversal

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open ReturnFrame.Occurrence
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open LinkedCallback PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

theorem advanceAppend {left right middle other reached reference : State grow sig}
    (leading : TrackedAdvance profile ready bindings left right middle other)
    (trailing : TrackedAdvance profile ready bindings middle other reached reference) :
    TrackedAdvance profile ready bindings left right reached reference := by
  obtain ⟨leftLabels, rightLabels, same, leftPath, rightPath⟩ := leading
  obtain ⟨tailLeft, tailRight, sameTail, leftTail, rightTail⟩ := trailing
  refine ⟨leftLabels ++ tailLeft, rightLabels ++ tailRight, ?_,
    fun depth => (leftPath depth).append (leftTail depth), fun depth => (rightPath depth).append (rightTail depth)⟩
  simp only [visible, List.filter_append] at *
  rw [same, sameTail]

private theorem localTrackFinish {Result : Type} {originLeft originRight left right : State grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    {checkNext canonNext : Result → Session grow sig (Ret (core3 grow))} {finish target}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : LocalThen profile ready bindings left right check canon checkNext canonNext finish)
    (next : ∀ value lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish value lhs rhs check canon → target value lhs rhs check canon) :
    LocalThen profile ready bindings left right check canon checkNext canonNext target := by
  obtain ⟨store, result, labels, silent, checked, canonical, returned⟩ := run
  refine ⟨store, result, labels, silent, checked, canonical, fun value valid => ?_⟩
  obtain ⟨leftPath, rightPath, tail⟩ := returned value valid
  exact ⟨leftPath, rightPath, next _ _ _ _ _ (advanceAppend leading ⟨labels, labels, rfl, leftPath, rightPath⟩) tail⟩

theorem localFieldTrackFinish {originLeft originRight left right : State grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)} {output : Lower.Output} {checkNext canonNext finish target}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : LocalFieldThen profile ready bindings output left right check canon checkNext canonNext finish)
    (next : ∀ value lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish value lhs rhs check canon → target value lhs rhs check canon) :
    LocalFieldThen profile ready bindings output left right check canon checkNext canonNext target := by
  obtain ⟨store, result, leftLabels, rightLabels, checked, canonical, seen, outcome⟩ := run
  refine ⟨store, result, leftLabels, rightLabels, checked, canonical, seen, ?_⟩
  cases result with
  | error reason => exact outcome
  | ok value =>
    obtain ⟨lhs, rhs, tail⟩ := outcome
    exact ⟨lhs, rhs, next _ _ _ _ _ (advanceAppend leading ⟨leftLabels, rightLabels, seen, lhs, rhs⟩) tail⟩

private theorem silentOfAllTau {labels : List (Label (core3 grow) (HostState sig))}
    (allTau : ∀ label ∈ labels, label = .tau) : visible labels = [] :=
  List.filter_eq_nil_iff.mpr (fun label member => by simp [allTau label member])

theorem handleTrackFinish {originLeft originRight left right : State grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)} {item : Field} {index : Nat} {output : Lower.Output}
    {checkNext canonNext finish target}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : HandleFieldThen profile ready bindings item index output left right check canon checkNext canonNext finish)
    (next : ∀ value lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish value lhs rhs check canon → target value lhs rhs check canon) :
    HandleFieldThen profile ready bindings item index output left right check canon checkNext canonNext target := by
  unfold HandleFieldThen at run ⊢
  split <;> rename_i verdict live <;> simp only [live] at run
  · exact run
  · obtain ⟨store, result, reads, checkLabels, canonLabels, readTau, checkSilent, canonSilent, checked, canonical, tail⟩ := run
    refine ⟨store, result, reads, checkLabels, canonLabels, readTau, checkSilent, canonSilent, checked, canonical, ?_⟩
    intro value returned
    subst result
    obtain ⟨lhs, rhs, finish⟩ := tail value rfl
    refine ⟨lhs, rhs, next _ _ _ _ _ (advanceAppend leading ⟨reads ++ checkLabels, canonLabels, ?_, lhs, rhs⟩) finish⟩
    have allTau {labels : List (Label (core3 grow) (HostState sig))} (silent : LocalLeafLabels (.ok value) labels) :
        ∀ label ∈ labels, label = .tau := by
      intro label member
      have accepted := (List.all_eq_true.mp silent) label member
      cases label <;> simp_all
    exact (silentOfAllTau (fun label member => (List.mem_append.mp member).elim (readTau label) (allTau checkSilent label))).trans
      (silentOfAllTau (allTau canonSilent)).symm

private theorem stringTrackFinish {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {cx : LiftLowerContext (core3 grow)} {checkNext canonNext : Nat → Session grow sig (Ret (core3 grow))}
    {length : Nat} {originLeft originRight left right : State grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)} {finish target}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : StringReplay profile ready bindings older cx checkNext canonNext length left right check canon finish)
    (next : ∀ lhs rhs check canon pointer, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish lhs rhs check canon pointer → target lhs rhs check canon pointer) :
    StringReplay profile ready bindings older cx checkNext canonNext length left right check canon target := by
  induction length using Nat.strong_induction_on generalizing left right check canon with
  | _ length ih =>
    rw [StringReplay] at run ⊢
    cases run with
    | @done store result labels silent checked canonical tracked finished =>
      exact .done silent checked canonical tracked (fun pointer done =>
        next _ _ _ _ _ (advanceAppend leading ⟨labels, labels, rfl, fun depth => (tracked pointer done depth).1,
          fun depth => (tracked pointer done depth).2⟩) (finished pointer done))
    | @allocated pointer oldSize alignment size rest shorter store labels checked canonical silent tracked replay =>
      refine .allocated pointer oldSize alignment size rest shorter checked canonical silent tracked ?_
      intro dispatch leftEntry rightEntry first second changes last seen protectedReturn path covers
      obtain ⟨leftLabels, rightLabels, other, mark, lhs, rhs, leftSeen, rightSeen, paired, leftTrail, rightTrail, returns⟩ :=
        replay path covers
      refine ⟨leftLabels, rightLabels, other, mark, lhs, rhs, leftSeen, rightSeen, paired, leftTrail, rightTrail, ?_⟩
      intro value cursor atMark atReturn
      obtain ⟨otherCursor, leftPop, rightPop, retained, smaller⟩ := returns value cursor atMark atReturn
      refine ⟨otherCursor, leftPop, rightPop, retained, ih rest.length shorter ?_ smaller⟩
      apply advanceAppend leading
      refine ⟨labels ++ (leftLabels ++ [.tau]), labels ++ (rightLabels ++ [.tau]), ?_,
        fun depth => (retained depth).1, fun depth => (retained depth).2⟩
      simp only [show ∀ front back : List (Label (core3 grow) (HostState sig)),
        visible (front ++ back) = visible front ++ visible back from fun _ _ => List.filter_append .., leftSeen, rightSeen]

private theorem silentReads (count : Nat) :
    visible (List.replicate count (.tau : Label (core3 grow) (HostState sig))) = [] := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [List.replicate_succ, visible, List.filter_cons, Bool.false_eq_true, ite_false] using ih

theorem stringFieldTrackFinish {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {destination : RecordDestination} {inst : InstId} {str : Value.StrVal} {output : Lower.Output}
    {originLeft originRight left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {checkNext canonNext finish target}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : StringFieldThen profile ready bindings older destination inst str output left right check canon checkNext canonNext finish)
    (next : ∀ value lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish value lhs rhs check canon → target value lhs rhs check canon) :
    StringFieldThen profile ready bindings older destination inst str output left right check canon checkNext canonNext target := by
  obtain ⟨reads, leftPath, rightPath, rest⟩ := run
  refine ⟨reads, leftPath, rightPath, ?_⟩
  exact stringTrackFinish (advanceAppend leading
    ⟨List.replicate reads .tau, [.tau], silentReads reads, leftPath, rightPath⟩) rest
    (fun _ _ _ _ _ path run => localTrackFinish path run next)

theorem collectionTrackEntries {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {destination : RecordDestination} {inst : InstId} {type element : TypeOf} {entries : List Field}
    {index : Nat} {output : Lower.Output} {originLeft originRight left right : State grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)} {checkNext canonNext}
    {next target : Nat → CollectionVisit.Next grow sig}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : CollectionReplayFor profile ready bindings older destination inst type element entries index output left right check canon
      checkNext canonNext (fun lhs rhs last cursor pointer seen => CollectionVisit.Outcome profile ready bindings older destination inst
        type (layout destination.width element) entries index pointer output lhs rhs last cursor checkNext canonNext seen (next pointer)))
    (visit : ∀ pointer bytes lhs rhs check canon,
      TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      next pointer bytes lhs rhs check canon → target pointer bytes lhs rhs check canon) :
    CollectionReplayFor profile ready bindings older destination inst type element entries index output left right check canon
      checkNext canonNext (fun lhs rhs last cursor pointer seen => CollectionVisit.Outcome profile ready bindings older destination inst
        type (layout destination.width element) entries index pointer output lhs rhs last cursor checkNext canonNext seen (target pointer)) := by
  obtain ⟨leftInstall, rightInstall, replay⟩ := run
  refine ⟨leftInstall, rightInstall, ?_⟩
  intro last seen protectedReturn path covers
  obtain ⟨leftLabels, rightLabels, other, mark, lhs, rhs, leftSeen, rightSeen, paired, outside, leftTrail, rightTrail, returns⟩ :=
    replay path covers
  refine ⟨leftLabels, rightLabels, other, mark, lhs, rhs, leftSeen, rightSeen, paired, outside, leftTrail, rightTrail, ?_⟩
  intro pointer cursor atMark atReturn
  cases returns pointer cursor atMark atReturn with
  | admitted region checked canonical checkedSeen canonSeen tail =>
    refine .admitted region checked canonical checkedSeen canonSeen (visit _ _ _ _ _ _ (advanceAppend leading ?_) tail)
    refine ⟨_, _, ?_, checked.through_install leftInstall, canonical.through_install rightInstall⟩
    simp only [show ∀ front back : List (Label (core3 grow) (HostState sig)),
      visible (front ++ back) = visible front ++ visible back from fun _ _ => List.filter_append .., checkedSeen, canonSeen]
    rfl
  | refused live frame checked canonical checkedSeen canonSeen =>
    exact .refused live frame checked canonical checkedSeen canonSeen
  | rangeTrap same checked canonical checkedSeen canonSeen =>
    exact .rangeTrap same checked canonical checkedSeen canonSeen

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Traversal
