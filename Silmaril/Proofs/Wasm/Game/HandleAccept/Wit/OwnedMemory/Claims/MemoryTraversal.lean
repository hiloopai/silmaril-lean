module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Traversal.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Traversal.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Public.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemoryTraversal

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open ReturnFrame.Occurrence
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open LinkedCallback LinkedCallback.MemorySequence PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

private theorem checkedSilent {left right reached : State grow sig}
    (read : RetainsActiveSlots profile ready (specDispatch ready (host bindings)) left [.tau] reached) :
    TrackedAdvance profile ready bindings left right reached right :=
  .of_segment (leftLabels := [.tau]) (rightLabels := []) rfl read (fun _ => .done _ _)

private theorem canonicalSilent {left right reached : State grow sig} (mode : Track)
    (read : RetainsActiveSlots profile ready (specDispatch ready (host bindings)) right mode.readLabels reached) :
    TrackedAdvance profile ready bindings left right left reached :=
  .of_segment (by cases mode <;> rfl) (fun _ => .done _ _) read

theorem sequenceTrack {compare : FieldComparison grow sig} (child : CarriesFinish profile ready bindings compare)
    {mode : Track} {destination : RecordDestination} {inst : InstId} {items : List Field} {index cursor : Nat}
    {originLeft originRight left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {checkNext canonNext finish target}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : Replay profile ready bindings mode destination inst compare checkNext canonNext finish items index cursor left right check canon)
    (next : ∀ lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish lhs rhs check canon → target lhs rhs check canon) :
    Replay profile ready bindings mode destination inst compare checkNext canonNext target items index cursor left right check canon := by
  induction items generalizing index cursor left right check canon with
  | nil => exact next left right check canon leading run
  | cons item rest ih =>
    rw [Replay] at run ⊢
    refine ⟨run.1, child item index _ _ _ check canon _ _ (leading.append (canonicalSilent mode run.1)) run.2 ?_⟩
    intro lhs rhs check canon path tail
    exact ih path tail

private theorem mapEntriesTrack {compare : FieldComparison grow sig} (child : CarriesFinish profile ready bindings compare)
    {destination : RecordDestination} {inst : InstId} {key : WIT.KeyType} {element : TypeOf}
    {items : List Field} {index cursor : Nat} {originLeft originRight left right : State grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)} {checkNext canonNext finish target}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : MapEntriesReplay profile ready bindings destination inst compare key element checkNext canonNext finish
      items index cursor left right check canon)
    (next : ∀ lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish lhs rhs check canon → target lhs rhs check canon) :
    MapEntriesReplay profile ready bindings destination inst compare key element checkNext canonNext target
      items index cursor left right check canon := by
  induction items generalizing index cursor left right check canon with
  | nil => exact next left right check canon leading run
  | cons item rest ih =>
    rw [MapEntriesReplay] at run ⊢
    obtain ⟨keyField, valueField, pair, placed, fields⟩ := run
    refine ⟨keyField, valueField, pair, placed, sequenceTrack child (leading.append (checkedSilent placed)) fields ?_⟩
    intro lhs rhs check canon path tail
    exact ih path tail

private theorem mixedTrack {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {destination : RecordDestination} {inst : InstId} :
    CarriesFinish profile ready bindings (mixed profile ready bindings older destination inst) := by
  intro item index address left right check canon checkNext canonNext originLeft originRight finish target leading run next
  rcases run with ⟨handle, run⟩ | ⟨string, field, run⟩
  · exact .inl ⟨handle, run.track_finish leading (fun () => next)⟩
  · exact .inr ⟨string, field, run.track_finish leading (fun () => next)⟩

private theorem leafTrack {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {destination : RecordDestination} {inst : InstId} :
    CarriesFinish profile ready bindings (memoryLeaf profile ready bindings older destination inst) := by
  intro item index address left right check canon checkNext canonNext originLeft originRight finish target leading run next
  rcases run with mixed | ⟨localType, run⟩
  · exact .inl (mixedTrack item index address left right check canon checkNext canonNext leading mixed next)
  · exact .inr ⟨localType, run.track_finish leading (fun () => next)⟩

private theorem sumTrack {compare : FieldComparison grow sig} (child : CarriesFinish profile ready bindings compare)
    {destination : RecordDestination} {inst : InstId} {arms : List (Option TypeOf)} {selected : Option Field}
    {index base : Nat} {originLeft originRight left right : State grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)} {checkNext canonNext finish target}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : SumThen profile ready bindings destination inst compare arms selected index base checkNext canonNext finish left right check canon)
    (next : ∀ lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish lhs rhs check canon → target lhs rhs check canon) :
    SumThen profile ready bindings destination inst compare arms selected index base checkNext canonNext target left right check canon := by
  obtain ⟨store, result, leftLabels, rightLabels, checked, canonical, seen, outcome⟩ := run
  refine ⟨store, result, leftLabels, rightLabels, checked, canonical, seen, ?_⟩
  cases result with
  | error reason => exact outcome
  | ok _ =>
    obtain ⟨lhs, rhs, tail⟩ := outcome
    have advance := leading.append (.of_segment seen lhs rhs)
    refine ⟨lhs, rhs, ?_⟩
    cases selected with
    | none => exact next _ _ _ _ advance tail
    | some item => exact child item 0 _ _ _ check canon _ _ advance tail next

private theorem descriptorTrack {output : Lower.Output} {checkNext canonNext finish target}
    {originLeft originRight left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : DescriptorThen profile ready bindings output checkNext canonNext finish left right check canon)
    (next : ∀ value lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish value lhs rhs check canon → target value lhs rhs check canon) :
    DescriptorThen profile ready bindings output checkNext canonNext target left right check canon := by
  obtain ⟨store, result, labels, silent, checked, canonical, finish⟩ := run
  refine ⟨store, result, labels, silent, checked, canonical, fun value done => ?_⟩
  obtain ⟨lhs, rhs, tail⟩ := finish value done
  exact ⟨lhs, rhs, next _ _ _ _ _ (leading.append (.of_segment rfl lhs rhs)) tail⟩

theorem entriesTrack {compare : FieldComparison grow sig} (child : CarriesFinish profile ready bindings compare)
    {destination : RecordDestination} {inst : InstId} {element : TypeOf} {entries : List Field} {index pointer : Nat}
    {output : Lower.Output} {checkNext canonNext finish target}
    {originLeft originRight left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : ValueEntriesReplay profile ready bindings destination inst compare element entries index pointer output checkNext canonNext
      finish left right check canon)
    (next : ∀ value lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish value lhs rhs check canon → target value lhs rhs check canon) :
    ValueEntriesReplay profile ready bindings destination inst compare element entries index pointer output checkNext canonNext
      target left right check canon :=
  sequenceTrack child leading run (fun _ _ _ _ path tail => descriptorTrack path tail next)

theorem listTreeTracks {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {destination : RecordDestination} {inst : InstId} (depth : Nat) :
    CarriesFinish profile ready bindings (listTree profile ready bindings older destination inst depth) := by
  induction depth with
  | zero => exact leafTrack
  | succ depth ih =>
    intro item index address left right check canon checkNext canonNext originLeft originRight finish target leading run next
    rw [listTree] at run ⊢
    rcases run with leaf | aggregate | list | map | sum | fixed
    · exact .inl (leafTrack item index address left right check canon checkNext canonNext leading leaf next)
    · obtain ⟨type, children, shape, placed, tail⟩ := aggregate
      exact .inr (.inl ⟨type, children, shape, placed, sequenceTrack ih (leading.append (checkedSilent placed)) tail next⟩)
    · right; right; left
      obtain ⟨element, entries, shape, run⟩ := list
      refine ⟨element, entries, shape, ?_⟩
      split <;> rename_i verdict live <;> simp only [live] at run
      · exact run
      · exact CollectionReplayFor.track_entries leading run fun _ _ _ _ _ _ path tail =>
          entriesTrack ih path tail (fun () => next)
    · right; right; right; left
      obtain ⟨key, element, entries, shape, run⟩ := map
      refine ⟨key, element, entries, shape, ?_⟩
      split <;> rename_i verdict live <;> simp only [live] at run
      · exact run
      · exact CollectionReplayFor.track_entries leading run fun _ _ _ _ _ _ path tail =>
          mapEntriesTrack ih path tail fun _ _ _ _ path tail => descriptorTrack path tail (fun () => next)
    · obtain ⟨type, arms, tag, selected, shape, run⟩ := sum
      exact .inr (.inr (.inr (.inr (.inl ⟨type, arms, tag, selected, shape, sumTrack ih leading run next⟩))))
    · obtain ⟨element, length, entries, shape, placed, tail⟩ := fixed
      exact .inr (.inr (.inr (.inr (.inr ⟨element, length, entries, shape, placed,
        sequenceTrack ih (leading.append (canonicalSilent .fields placed)) tail next⟩))))

private theorem flatSequenceTrack {compare : FlatFieldComparison grow sig} (child : CarriesFlatFinish profile ready bindings compare)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {destination : RecordDestination} {inst : InstId}
    {items : List Field} {index : Nat} {words : List FlatValue}
    {originLeft originRight left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {checkNext canonNext finish target}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : FlatSequenceReplay compare older destination inst checkNext canonNext finish items index words left right check canon)
    (next : ∀ words lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish words lhs rhs check canon → target words lhs rhs check canon) :
    FlatSequenceReplay compare older destination inst checkNext canonNext target items index words left right check canon := by
  induction items generalizing index words left right check canon with
  | nil => exact next words left right check canon leading run
  | cons item rest ih =>
    rw [FlatSequenceReplay] at run ⊢
    exact child item index left right check canon _ _ leading run (fun _ _ _ _ _ path tail => ih path tail)

private theorem flatSumTrack {compare : FlatFieldComparison grow sig} (child : CarriesFlatFinish profile ready bindings compare)
    {width : AddrType} {type : TypeOf} {count tag index : Nat} {selected : Option Field}
    {originLeft originRight left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {checkNext canonNext finish target}
    (leading : TrackedAdvance profile ready bindings originLeft originRight left right)
    (run : FlatSumThen profile ready bindings compare width type count tag selected index left right check canon checkNext canonNext finish)
    (next : ∀ words lhs rhs check canon, TrackedAdvance profile ready bindings originLeft originRight lhs rhs →
      finish words lhs rhs check canon → target words lhs rhs check canon) :
    FlatSumThen profile ready bindings compare width type count tag selected index left right check canon checkNext canonNext target := by
  cases selected with
  | none => exact ⟨run.1, run.2.1, run.2.2.track_finish leading next⟩
  | some item =>
    exact child item 0 left right check canon _ _ leading run
      (fun _ _ _ _ _ path tail => ⟨tail.1, tail.2.1, tail.2.2.track_finish path next⟩)

private theorem allocatingFlatTracks {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {destination : RecordDestination} {inst : InstId} (entryDepth : Nat) :
    CarriesFlatFinish profile ready bindings (flatAllocating profile ready bindings older destination inst entryDepth) := by
  intro item index left right check canon checkNext canonNext originLeft originRight finish target leading run next
  rcases run with (⟨handle, run⟩ | ⟨str, shape, run⟩) | ⟨localType, run⟩ | ⟨type, element, entries, shape, run⟩
  · exact .inl (.inl ⟨handle, run.track_finish leading next⟩)
  · exact .inl (.inr ⟨str, shape, run.track_finish leading next⟩)
  · exact .inr (.inl ⟨localType, run.track_finish leading next⟩)
  · refine .inr (.inr ⟨type, element, entries, shape, ?_⟩)
    split <;> rename_i verdict live <;> simp only [live] at run
    · exact run
    · exact CollectionReplayFor.track_entries leading run fun _ _ _ _ _ _ path tail =>
        entriesTrack (listTreeTracks entryDepth) path tail next

theorem flatTreeTracks {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {destination : RecordDestination} {inst : InstId} (flatDepth entryDepth : Nat) :
    CarriesFlatFinish profile ready bindings
      (nestedFlatComparison profile ready bindings (flatAllocating profile ready bindings older destination inst entryDepth)
        older destination inst flatDepth) := by
  induction flatDepth with
  | zero => exact allocatingFlatTracks entryDepth
  | succ depth ih =>
    intro item index left right check canon checkNext canonNext originLeft originRight finish target leading run next
    cases item <;> first
    | exact flatSumTrack ih leading run next
    | exact flatSequenceTrack ih leading run next
    | exact allocatingFlatTracks entryDepth _ _ _ _ _ _ _ _ leading run next

private theorem rejoin {route : GiveEffectRoute} (call : PayloadRoot.Site grow sig route) (value : route.output.Result)
    {reached reference : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (advance : TrackedAdvance profile ready bindings call.checked (call.reference call.referenceReply) reached reference)
    (frame : ChildFrameOver (fun _ _ => False) reached reference check canon)
    (checked : reached.ctl = check.control (call.reply (.ok value)))
    (canonical : reference.ctl = canon.control (call.referenceReply value)) :
    RejoinedGive call value profile ready bindings reached reference := by
  refine ⟨advance, ?_⟩
  obtain ⟨_, _, _, path, _, _⟩ := advance
  exact resume_returned_give call value frame (path 0) checked canonical

theorem parkedMemoryThen {pointer : FlatValue} (call : PayloadRoot.Site grow sig (.memory pointer))
    (linked : call.Linked bindings) (impl : HostImpl (core3 grow) (HostState sig))
    (embedder : impl.embedder = (host (grow := grow) bindings).embedder) {finish : State grow sig → State grow sig → Prop}
    (onReturn : OnGiveReturn call profile ready bindings impl (fun _ => finish)) :
    ∃ depth, PayloadRoot.Cut call profile ready bindings (ParkedMemoryBody call depth profile ready bindings finish) impl := by
  obtain ⟨depth, cut⟩ := parked_compiled_memory (profile := profile) (ready := ready) call linked call.referenceReply impl embedder
  refine ⟨depth, ?_⟩
  cases cut with
  | refused issue silent run => exact .refused issue silent run
  | placementTrap reason count verdict run => exact .placementTrap reason count verdict run
  | placed silent verdict prepared run body =>
    refine .placed silent verdict prepared run (listTreeTracks depth call.field 0 (flatNat pointer) _ _ _ _ _ _
      (.refl _ _) body ?_)
    intro lhs rhs check canon path atReturn
    exact onReturn silent verdict prepared run () lhs rhs (rejoin call () path atReturn.1 atReturn.2.1 atReturn.2.2)

theorem parkedFlatThen {schema : TypeOf} (call : PayloadRoot.Site grow sig (.flat schema))
    (linked : call.Linked bindings) (impl : HostImpl (core3 grow) (HostState sig))
    (embedder : impl.embedder = (host (grow := grow) bindings).embedder)
    {finish : List FlatValue → State grow sig → State grow sig → Prop}
    (onReturn : OnGiveReturn call profile ready bindings impl finish) :
    ∃ flatDepth entryDepth, PayloadRoot.Cut call profile ready bindings
      (ParkedFlatResult call flatDepth entryDepth profile ready bindings finish) impl := by
  obtain ⟨flatDepth, entryDepth, cut⟩ := parked_compiled_flat (profile := profile) (ready := ready) call linked call.referenceReply impl embedder
  refine ⟨flatDepth, entryDepth, ?_⟩
  cases cut with
  | refused issue silent run => exact .refused issue silent run
  | placementTrap reason count verdict run => exact .placementTrap reason count verdict run
  | placed silent verdict prepared run body =>
    refine .placed silent verdict prepared run (flatTreeTracks flatDepth entryDepth call.field 0 _ _ _ _ _ _
      (.refl _ _) body ?_)
    intro words lhs rhs check canon path atReturn
    exact onReturn silent verdict prepared run words lhs rhs (rejoin call words path atReturn.1 atReturn.2.1 atReturn.2.2)

theorem parkedMemoryRejoined {pointer : FlatValue} (call : PayloadRoot.Site grow sig (.memory pointer))
    (linked : call.Linked bindings) (impl : HostImpl (core3 grow) (HostState sig))
    (embedder : impl.embedder = (host (grow := grow) bindings).embedder) :
    ∃ depth, PayloadRoot.Cut call profile ready bindings (ParkedRejoinedMemory call depth profile ready bindings) impl :=
  parkedMemoryThen call linked impl embedder (fun _ _ _ _ _ _ _ compared => compared)

theorem parkedFlatRejoined {schema : TypeOf} (call : PayloadRoot.Site grow sig (.flat schema))
    (linked : call.Linked bindings) (impl : HostImpl (core3 grow) (HostState sig))
    (embedder : impl.embedder = (host (grow := grow) bindings).embedder) :
    ∃ flatDepth entryDepth, PayloadRoot.Cut call profile ready bindings
      (ParkedRejoinedFlat call flatDepth entryDepth profile ready bindings) impl :=
  parkedFlatThen call linked impl embedder (fun _ _ _ _ _ _ _ compared => compared)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemoryTraversal
