module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.CollectionVisit.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.CollectionVisit

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.CollectionVisit

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

private theorem returnRangeSteps {start reached after : State grow sig} {labels mark}
    (run : ReturnRangeTrace profile ready bindings start reached labels after mark) :
    Steps profile ready (specDispatch ready (host bindings)) start labels after := by
  obtain ⟨leading, trailing, rfl, leadingRun, marked, suffix⟩ := run
  have tail := (ReturnFrame.Occurrence.prefix_survives (suffix 0)).1
  clear marked suffix
  induction leadingRun with
  | refl => exact tail
  | cons step _ ih => exact .cons step (ih tail)

theorem returnRangeThroughInstall {start entered reached after : State grow sig} {leading labels}
    (install : ∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (host bindings))
      start (.active 0 depth) leading entered (.active 0 (depth + 1)))
    (run : ReturnRangeTrace profile ready bindings entered reached labels after (some (.active 0 0))) :
    ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (host bindings)) start (leading ++ labels) after := by
  obtain ⟨callbackLabels, localLabels, rfl, _, marked, tail⟩ := run
  exact ReturnFrame.Occurrence.Trail.through_return_suffix install marked tail

theorem afterRange {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {resume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (type : TypeOf) (area : Layout) (entries : List Field)
    (index pointer : Nat) (output : Lower.Output) {left right last : State grow sig}
    {check : Cursor (E := core3 grow) (HostState sig)} {seen}
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow))) (next : Next grow sig)
    (cut : RangeCutOver profile ready bindings older resume left right last check destination area entries.length pointer
      (Field.listObjects entries) (fun ptr live => checkedCollectionTail destination inst entries area index output ptr live >>= checkNext)
      (fun ptr => canonicalCollectionTail destination inst entries area output ptr
        (CanonicalTree.EntryMode.forOutput destination.width type output) >>= canonNext) seen False (some (.active 0 0)))
    (visit : ∀ bytes reference canon, Admitted older destination area entries pointer bytes left last reference check canon →
      next bytes
        { last with ctl := check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) }
        { reference with ctl := canon.control (canonicalCollectionTail destination inst entries area output pointer
          (CanonicalTree.EntryMode.forOutput destination.width type output) >>= canonNext) } check canon) :
    CollectionVisit.Outcome profile ready bindings older destination inst type area entries index pointer output
      left right last check checkNext canonNext seen next := by
  cases cut with
  | @reached reference canon bytes checkLabels canonLabels width sized aligned bounds frame growth checked canonical checkSeen canonSeen =>
    cases live : Record.prepare last.store last.host.writer (Field.listObjects entries) with
    | error issue =>
      have stopped : (checkedCollectionTail destination inst entries area index output pointer (.error issue) >>= checkNext) =
          checkNext (.error (afterAllocation index issue)) := by cases issue <;> rfl
      rw [live, stopped] at checked
      exact .refused live frame checked canonical checkSeen canonSeen
    | ok result =>
      cases result
      rw [live] at checked
      have region : Admitted older destination area entries pointer bytes left last reference check canon :=
        ⟨width, sized, aligned, bounds, frame, growth, live⟩
      exact .admitted region checked canonical checkSeen canonSeen (visit bytes reference canon region)
  | trapped same checked canonical checkSeen canonSeen => exact .rangeTrap same checked canonical checkSeen canonSeen
  | common _ allowed => exact False.elim allowed

theorem memoryMap {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {resume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf) (entries : List Field)
    (index pointer address : Nat) {left right last : State grow sig}
    {check : Cursor (E := core3 grow) (HostState sig)} {seen}
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (children : ∀ entry ∈ entries, MapEntryRules (grow := grow) profile ready (specDispatch ready (host bindings))
      destination inst key element entry)
    (cut : let area := layout destination.width (.record (mapEntryFields key element))
      RangeCutOver profile ready bindings older resume left right last check destination area entries.length pointer
        (Field.listObjects entries) (fun ptr live => checkedCollectionTail destination inst entries area index (.memory address) ptr live >>= checkNext)
        (fun ptr => canonicalCollectionTail destination inst entries area (.memory address) ptr
          (.memoryMap destination.width key element) >>= canonNext) seen False (some (.active 0 0))) :
    let area := layout destination.width (.record (mapEntryFields key element))
    CollectionVisit.Outcome profile ready bindings older destination inst (.map key element) area entries index pointer (.memory address)
      left right last check checkNext canonNext seen (reachesNext profile ready bindings left.store checkNext canonNext) := by
  dsimp only
  refine afterRange destination inst (.map key element) _ entries index pointer (.memory address) checkNext canonNext _ cut ?_
  intro bytes reference canon region
  let entryArea := layout destination.width (.record (mapEntryFields key element))
  have grown : Core3.Grows last.store.core reference.store.core := by rw [← region.frame.store]; exact Core3.Grows.refl _
  have compared := PayloadPrefix.memory_map_tail destination inst key element last.store pointer bytes index address
    region.width region.sized entries region.aligned region.bounds children
    { last with ctl := check.control (checkedCollectionTail destination inst entries entryArea index (.memory address) pointer (.ok ()) >>= checkNext) }
    { reference with ctl := canon.control (canonicalCollectionTail destination inst entries entryArea (.memory address) pointer
      (.memoryMap destination.width key element) >>= canonNext) }
    grown
  exact (compared region.frame.store check canon region.frame.thread checkNext canonNext rfl rfl).weaken
    fun _ growth => region.growth.trans growth

theorem reaches {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {destination : RecordDestination}
    {inst : InstId} {type : TypeOf} {area : Layout} {entries : List Field} {index pointer : Nat} {output : Lower.Output}
    {left right last : State grow sig} {check : Cursor (E := core3 grow) (HostState sig)} {seen}
    {checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow))}
    {canonNext : output.Result → Session grow sig (Ret (core3 grow))}
    (cut : CollectionVisit.Outcome profile ready bindings older destination inst type area entries index pointer output
      left right last check checkNext canonNext seen (reachesNext profile ready bindings left.store checkNext canonNext)) :
    ∃ canon, ReachesKeeping profile ready (specDispatch ready (host bindings))
      (fun store => Core3.Grows left.store.core store.core) left right check canon checkNext canonNext := by
  cases cut with
  | admitted _ checked canonical checkSeen canonSeen visit =>
    exact ⟨_, ReachesKeeping.prepend (returnRangeSteps checked) (returnRangeSteps canonical) (checkSeen.trans canonSeen.symm) visit⟩
  | @refused reference canon issue checkLabels canonLabels _ frame checked canonical checkSeen canonSeen =>
    exact ⟨canon, .refused _, checkLabels, canonLabels, _, _, returnRangeSteps checked, returnRangeSteps canonical, frame.store,
      checkSeen.trans canonSeen.symm, trivial, rfl⟩
  | @rangeTrap reference reason checkLabels canonLabels same checked canonical checkSeen canonSeen =>
    exact ⟨check, .trapped reason, checkLabels, canonLabels, StepDefs.trapCfg last, StepDefs.trapCfg reference,
      checked, canonical, congrArg StepDefs.lockdownSt same, checkSeen.trans canonSeen.symm, trivial, rfl, rfl, seen, canonSeen⟩

theorem localMapEntries (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf)
    {entries : List Field} (matched : Field.EntriesMatch entries (.record (mapEntryFields key element)))
    (localEntries : ∀ entry ∈ entries, LocalMemory entry) :
    ∀ entry ∈ entries, MapEntryRules (grow := grow) profile ready (specDispatch ready (host bindings))
      destination inst key element entry := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
    intro entry member
    cases matched with
    | cons headLayout tailLayout =>
      rcases List.mem_cons.mp member with rfl | later
      · have fragment := localEntries entry (by simp)
        cases fragment with
        | leaf leaf =>
          have entryType := headLayout.type_eq
          rcases leaf with handle | ⟨primitive, _, scalar, same⟩
          · cases entry <;> simp [CanonicalHandle, Field.type] at handle entryType
            rename_i channel _ _
            cases channel <;> simp [ListLower.endpointType] at entryType
          · cases same
            cases entryType
        | aggregate parts =>
          cases headLayout with
          | record fields =>
            change Field.FieldsMatch _ [.prim key.toPrimitive, element] at fields
            cases fields with
            | cons keyLayout valueFields =>
              cases valueFields with
              | cons valueLayout remaining =>
                cases remaining
                exact ⟨_, _, rfl, keyLayout, valueLayout,
                  MemoryChildRule.local_memory destination inst (parts _ (by simp)) keyLayout,
                  MemoryChildRule.local_memory destination inst (parts _ (by simp)) valueLayout⟩
      · exact ih tailLayout (fun item present => localEntries item (List.mem_cons_of_mem _ present)) entry later

theorem memoryMapReplay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf) (entries : List Field)
    (index address : Nat) {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (matched : Field.EntriesMatch entries (.record (mapEntryFields key element)))
    (localEntries : ∀ entry ∈ entries, LocalMemory entry)
    (replay : CollectionReplay profile ready bindings older destination inst (.map key element)
      (.record (mapEntryFields key element)) entries index (.memory address) left right check canon checkNext canonNext) :
    CollectionReplayFor profile ready bindings older destination inst (.map key element)
      (.record (mapEntryFields key element)) entries index (.memory address) left right check canon checkNext canonNext
      (fun installed reference _ cursor _ _ => ∃ canonCursor, ReachesKeeping profile ready (specDispatch ready (host bindings))
        (fun store => Core3.Grows installed.store.core store.core) installed reference cursor canonCursor checkNext canonNext) := by
  obtain ⟨checkInstall, canonInstall, continueRun⟩ := replay
  refine ⟨checkInstall, canonInstall, ?_⟩
  intro last seen protectedReturn path covers
  obtain ⟨checkLabels, canonLabels, other, mark, checked, canonical, checkSeen, canonSeen, paired, outside, checkTrail, canonTrail, cut⟩ :=
    continueRun path covers
  refine ⟨checkLabels, canonLabels, other, mark, checked, canonical, checkSeen, canonSeen, paired, outside, checkTrail, canonTrail, ?_⟩
  intro pointer cursor reached atReturn
  exact reaches (memoryMap destination inst key element entries index pointer address checkNext canonNext
    (localMapEntries destination inst key element matched localEntries) (cut pointer cursor reached atReturn))

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.CollectionVisit
