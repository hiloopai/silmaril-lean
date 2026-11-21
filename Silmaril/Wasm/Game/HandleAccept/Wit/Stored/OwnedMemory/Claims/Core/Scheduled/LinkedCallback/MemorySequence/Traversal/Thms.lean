module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Traversal.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemoryTraversal

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Stored.Endpoints.RecordLower PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

/-- From the linked memory give, compare the recursive body with canonical
store and rejoin the original Core caller when lowering returns successfully.
Finite classified callback prefixes can suspend, refuse, or trap instead. -/
theorem parked_memory_rejoined {pointer : FlatValue} (call : PayloadRoot.Site grow sig (.memory pointer))
    (linked : call.Linked bindings) (impl : HostImpl (core3 grow) (HostState sig) := host bindings)
    (embedder : impl.embedder = (host (grow := grow) bindings).embedder := by rfl) :
    ∃ depth, PayloadRoot.Cut call profile ready bindings (ParkedRejoinedMemory call depth profile ready bindings) impl :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemoryTraversal.parkedMemoryRejoined call linked impl embedder

/-- The flat give reuses the memory traversal for allocated entries. The
same ABI words reach the original Core caller on a common successful path;
this needs no per-child comparison or assumption that a callback returns. -/
theorem parked_flat_rejoined {schema : Stored.TypeOf} (call : PayloadRoot.Site grow sig (.flat schema))
    (linked : call.Linked bindings) (impl : HostImpl (core3 grow) (HostState sig) := host bindings)
    (embedder : impl.embedder = (host (grow := grow) bindings).embedder := by rfl) :
    ∃ flatDepth entryDepth, PayloadRoot.Cut call profile ready bindings
      (ParkedRejoinedFlat call flatDepth entryDepth profile ready bindings) impl :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemoryTraversal.parkedFlatRejoined call linked impl embedder

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence
