module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Public.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Thms

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Stored.Endpoints.RecordLower
open PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {pointer : FlatValue}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

/-- Compare the actual parked public `givePayload` body for arbitrary
record and tuple nesting with interleaved strings and checked handles.
The public guards provide root placement and string fit; descendants use
compiled offsets and the live writer reached after earlier callbacks. -/
theorem parked_givePayload (call : PayloadRoot.Site grow sig (.memory pointer)) (linked : call.Linked bindings)
    (depth : Nat) (next : call.ReferenceNext) (shape : ParkedShape depth call.field)
    {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (ParkedBody call depth next profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence.parked call linked depth next shape realloc

/-- Both actual parked give bindings compare a compiled list root with
arbitrarily many nested record/tuple entries containing allocating strings
and handles. Its independently reached recheck can refuse before entries;
the descriptor and original reply run only after their respective guards. -/
theorem parked_list {route : GiveEffectRoute} (call : PayloadRoot.Site grow sig route) (linked : call.Linked bindings)
    (element : TypeOf) (entries : List Field) (depth : Nat) (next : call.ReferenceNext)
    (compiledList : call.field = .dynamic (.list element) element entries)
    (shapes : ∀ item ∈ entries, ParkedShape depth item) {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (ParkedListBody call element entries depth next profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence.parkedList
    call linked element entries depth next compiledList shapes realloc

/-- Compare recursively compiled aggregates, arrays, lists, indirect maps,
and selected sums in an actual parked memory payload. Each marked return
discharges the reached range and live reservation. Sum tags take effect
before visiting the selected arm, whose slot uses the full arm layout. -/
theorem parked_list_tree (call : PayloadRoot.Site grow sig (.memory pointer)) (linked : call.Linked bindings)
    (depth : Nat) (next : call.ReferenceNext) (shape : ParkedListTreeShape depth call.field) :
    PayloadRoot.Cut call profile ready bindings (ParkedListTreeBody call depth next profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence.parkedListTree call linked depth next shape

/-- Both public list-root routes run the same recursive memory comparison
for reached entries, including nested lists and indirect maps. -/
theorem parked_recursive_list {route : GiveEffectRoute} (call : PayloadRoot.Site grow sig route) (linked : call.Linked bindings)
    (element : TypeOf) (entries : List Field) (depth : Nat) (next : call.ReferenceNext)
    (compiledList : call.field = .dynamic (.list element) element entries)
    (shapes : ∀ item ∈ entries, ParkedListTreeShape depth item) {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (ParkedRecursiveListBody call element entries depth next profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence.parkedRecursiveValue
    call linked (.list element) element entries depth next compiledList (by cases route <;> rfl) shapes realloc

/-- Flat maps store each compiled key/value record at the slot reached after
the marked allocator return. Unlike indirect maps, their canonical program
reads the width again at entry, then lowers any allocating descendants. -/
theorem parked_recursive_flat_map {schema : TypeOf} (call : PayloadRoot.Site grow sig (.flat schema)) (linked : call.Linked bindings)
    (key : WIT.KeyType) (element : TypeOf) (entries : List Field) (depth : Nat) (next : call.ReferenceNext)
    (compiledMap : call.field = .dynamic (.map key element) (.record (mapEntryFields key element)) entries)
    (shapes : ∀ item ∈ entries, ParkedListTreeShape depth item) {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (ParkedRecursiveFlatMapBody call key element entries depth next profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence.parkedRecursiveValue
    call linked (.map key element) (.record (mapEntryFields key element)) entries depth next compiledMap rfl shapes realloc

/-- An actual parked flat aggregate, fixed array or selected sum visits its
scalar, string, handle and dynamic collection children in order. Sum coercion
uses the words from the reached arm, and a collection descriptor joins the
flat sequence only after the marked return and complete memory traversal.
A typed refusal or trap does not run the next sibling. -/
theorem parked_recursive_flat {schema : TypeOf} (call : PayloadRoot.Site grow sig (.flat schema)) (linked : call.Linked bindings)
    (flatDepth entryDepth : Nat) (next : call.ReferenceNext) (shape : ParkedFlatShape flatDepth entryDepth call.field) :
    PayloadRoot.Cut call profile ready bindings (ParkedFlatBody call flatDepth entryDepth next profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence.parkedFlat
    call linked flatDepth entryDepth next shape

/-- The actual checked preflight supplies the entire active structure and
map pair placement for the parked memory comparison. No per-child comparison
or leaf coverage is a premise. -/
theorem parked_compiled_memory (call : PayloadRoot.Site grow sig (.memory pointer)) (linked : call.Linked bindings)
    (next : call.ReferenceNext) (impl : HostImpl (core3 grow) (HostState sig) := host bindings)
    (embedder : impl.embedder = (host (grow := grow) bindings).embedder := by rfl) :
    ∃ depth, PayloadRoot.Cut call profile ready bindings (ParkedListTreeBody call depth next profile ready bindings) impl :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence.parkedCompiledMemory
    call linked next impl embedder

/-- The same compiler evidence supplies flat aggregate and selected-sum
descent and recursive memory traversal at every reached collection return.
This compares the body through the original reply continuation, not delivery. -/
theorem parked_compiled_flat {schema : TypeOf} (call : PayloadRoot.Site grow sig (.flat schema)) (linked : call.Linked bindings)
    (next : call.ReferenceNext) (impl : HostImpl (core3 grow) (HostState sig) := host bindings)
    (embedder : impl.embedder = (host (grow := grow) bindings).embedder := by rfl) :
    ∃ flatDepth entryDepth, PayloadRoot.Cut call profile ready bindings
      (ParkedFlatBody call flatDepth entryDepth next profile ready bindings) impl :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence.parkedCompiledFlat
    call linked next impl embedder

/-- At a reached successful reply with the original caller on top, both
machines resume that Core thread on the reached store and the same ABI
words. Only the checked route records the completion. The tracked prefix
identifies the original occurrence; it does not predict allocator return. -/
theorem resume_returned_give {route : GiveEffectRoute} (call : PayloadRoot.Site grow sig route)
    (value : route.output.Result) {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {reached reference : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (frame : ChildFrameOver older reached reference check canon) {labels}
    (tracked : ReturnFrame.Occurrence.Prefix profile ready dispatch
      call.checked (.active 0 0) labels reached (.active 0 0))
    (checked : reached.ctl = check.control (call.reply (.ok value)))
    (canonical : reference.ctl = canon.control (call.referenceReply value)) :
    let reply := route.reply call.destination call.start.host.nextTicket (.ok value)
    ∃ left right, (∀ dispatch, Steps profile ready dispatch reached [.tau, .tau, .tau] left) ∧
      (∀ dispatch, Steps profile ready dispatch reference [.tau] right) ∧ left.store = right.store ∧
      left.host = reached.host.record reply.1 ∧ right.host = reference.host ∧
      HostFrame.Related.Paired older left right := by
  obtain ⟨_, caller⟩ := call.reached_caller checked tracked
  exact Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence.resumeReturned
    call value frame caller checked canonical

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence
