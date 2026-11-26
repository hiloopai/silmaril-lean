module

public import Silmaril.Machine.SQLite.TrackA.Read.Defs
public import Silmaril.Semantics.TrackA.Interaction.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.TrackA.Read.Adapter

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open Silmaril.Semantics.TrackA.Interaction (Signature ITree Coalgebra)

abbrev VfsSignature : Signature := ⟨Request, Response⟩

def exchanges (trace : Trace) : List VfsSignature.Exchange :=
  trace.map fun exchange => ⟨exchange.request, exchange.response⟩

structure Acquire where
  target : PageRead.SlotId
  page : PageRead.Page

structure Acquired where
  result : Except PageRead.FillError Bytes
  cache : PageRead.Cache

abbrev PagerSignature : Signature := ⟨Acquire, fun _ => Acquired⟩
abbrev LeafResult := Read.Result × PageRead.Cache

/-- One VM-to-Pager call and the continuation consuming its typed reply. -/
structure SeekCall where
  request : PagerSignature.Request
  resume : PagerSignature.Response request → LeafResult

def leafCall (request : Acquire) (leaf : File.View → Read.Result) : SeekCall :=
  ⟨request, fun reply =>
    let after := Read.finishAcquire leaf (⟨reply.result, (), reply.cache, []⟩ : PageRead.Outcome Unit)
    (after.result, after.cache)⟩

def stagedCall (request : Acquire) (key : Int64) : SeekCall :=
  leafCall request (fun view => Read.seekLeaf view request.page.number key)

def vmCall (request : Acquire) (key : Int64) : SeekCall :=
  leafCall request (fun view => Read.runLeaf view request.page.number key)

def pagerTree (call : SeekCall) : ITree PagerSignature LeafResult where
  State := Option Acquired
  root := fun _ => none
  unfold
    | none => .vis call.request some
    | some reply => .ret (call.resume reply)

/-- Replace the Pager call with its cache check and any required VFS read.
The VFS reply is accepted by the Pager before the original continuation runs. -/
def lower (call : SeekCall) (cache : PageRead.Cache) : ITree VfsSignature LeafResult where
  State := Option ReadReply
  root := fun _ => none
  unfold state :=
    let target := call.request.target
    let page := call.request.page
    match state with
    | some reply =>
        let result := PageRead.accept page.size reply
        let after := match result with
          | .ok bytes => cache.install target page bytes
          | .error _ => cache
        .ret (call.resume ⟨result, after⟩)
    | none =>
        match PageRead.CacheHit.lookup cache target page with
        | some bytes => .ret (call.resume ⟨.ok bytes, cache⟩)
        | none =>
            match cache target with
            | some .vacant =>
                if page.Admitted then .vis page.request some
                else .ret (call.resume ⟨.error .invalidPage, cache⟩)
            | _ => .ret (call.resume ⟨.error .unavailableSlot, cache⟩)

/-- Handler state carries the actual file and completed exchanges. -/
abbrev Recorded (Backing : Type) := Backing × Trace

def handlePager {Backing : Type} (backing : Handler Backing) (cache : PageRead.Cache) :
    Coalgebra.Handler PagerSignature (Recorded Backing) :=
  fun (file, trace) request =>
    let acquired := PageRead.Acquire.acquire backing file cache request.target request.page
    (⟨acquired.result, acquired.cache⟩, acquired.file, trace ++ acquired.trace)

def handleVfs {Backing : Type} (backing : Handler Backing) :
    Coalgebra.Handler VfsSignature (Recorded Backing) :=
  fun (file, trace) request =>
    let (reply, after) := backing file request
    (reply, after, trace ++ [⟨request, reply⟩])

/-- The interpreted tree reaches its return with the observed file and trace
in the handler state, and its result and cache in the return value. -/
def Returns {S : Signature} {Backing : Type} (tree : ITree S LeafResult)
    (handler : Coalgebra.Handler S (Recorded Backing)) (file : Backing)
    (outcome : Read.Outcome Backing) : Prop :=
  let interpreted := tree.unfold.handle (T := VfsSignature) handler
  ∃ final, interpreted.Silent (tree.root (), file, []) (final, outcome.file, outcome.exchanges) ∧
    interpreted (final, outcome.file, outcome.exchanges) = .ret (outcome.result, outcome.cache)

/-- The open tree can reach a completed return with these request/reply pairs. -/
def Observes {Backing : Type} (tree : ITree VfsSignature LeafResult)
    (outcome : Read.Outcome Backing) : Prop :=
  Silmaril.Semantics.TrackA.Interaction.Trace.finite (exchanges outcome.exchanges)
    (.returned (outcome.result, outcome.cache)) ∈ tree.unfold.observes (tree.root ())

end Silmaril.Machine.SQLite.TrackA.Read.Adapter
