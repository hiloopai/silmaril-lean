module

public import Silmaril.Formats.Blake3Cas.Thms

@[expose] public section

namespace Silmaril.Formats.Blake3Cas.RangeFacts

open Silmaril.Crypto.Blake3
open Silmaril.Semantics.Naming.ByteRange (Slice)

/-- Exactly `[start, stop)` in a reference payload. No assertion about its extent. -/
def ExactAt (whole : Bytes) (start stop : Nat) (bytes : Bytes) : Prop :=
  start + bytes.length = stop ∧ Slice whole start bytes

/-- The true suffix of a reference payload. Starting past EOF is not an empty suffix. -/
def SuffixAt (whole : Bytes) (start : Nat) (bytes : Bytes) : Prop :=
  start ≤ whole.length ∧ whole.drop start = bytes

abbrev Extent (digest : Bytes) (size : Nat) := EOFProof size digest

/-- An extent-free result about any supplied payload with this name, modulo a concrete
compression collision. This does not claim a preimage for an opaque sibling. -/
structure Bounded (digest : Bytes) (start stop : Nat) where
  bytes : Bytes
  exact : start + bytes.length = stop
  against : ∀ {whole}, Named concrete digest whole → ExactAt whole start stop bytes ∨ ConcreteCollision

/-- A bounded range with separate evidence that its end is the object end. -/
structure Suffix (digest : Bytes) (start : Nat) where
  stop : Nat
  bounded : Bounded digest start stop
  extent : Extent digest stop

abbrev Whole (digest : Bytes) := Suffix digest 0

def Suffix.bytes {digest : Bytes} {start : Nat} (suffix : Suffix digest start) : Bytes :=
  suffix.bounded.bytes

/-- A bounded request gives start and count (not an inclusive end). `toEnd` is only
an instruction to the decoder, not a fact about the end of the object. -/
inductive Request where
  | bounded (start count : Nat)
  | toEnd (start : Nat)

def Request.window : Request → Nat → Bao.RangeRequest
  | .bounded start count, _ => ⟨start, count⟩
  | .toEnd start, claim => ⟨start, claim - start⟩

/-- The requested projection of a completed response, still staged at the wire extent. -/
inductive Done (claim : Nat) (digest : Bytes) (request : Request) where
  | body {fields : List Bytes} (body : CompleteBody claim digest fields)
      {range : ExactRange claim digest (request.window claim)}
      (projected : body.range? (request.window claim) = some range)
  | prefix {after : Nat} {initial final : Session claim digest} {input rest : Bytes}
      (trace : Prefix (request.window claim) (request.window claim).start initial input after final rest)
      (atBoundary : Bool) (complete : rangeFinished (request.window claim) after final rest atBoundary = true)

def Done.range {claim : Nat} {digest : Bytes} {request : Request} :
    Done claim digest request → ExactRange claim digest (request.window claim)
  | .body (range := range) .. => range
  | .prefix trace _ complete =>
    let bounds := (rangeFinished_spec.mp complete).2.2.2
    ⟨bounds.2, bounds.1 ▸ trace.coverage⟩

def Done.bytes {claim : Nat} {digest : Bytes} {request : Request} (done : Done claim digest request) : Bytes :=
  done.range.coverage.bytes

/-- EOF evidence can also come from a `Session` before framing finishes, or from
another response at the same digest and extent. It is not a consequence of `Done`. -/
structure Response (digest : Bytes) (request : Request) where
  claim : Nat
  done : Done claim digest request
  eof : Option (Extent digest claim)

def ofBody? {claim : Nat} {digest : Bytes} {fields : List Bytes}
    (body : CompleteBody claim digest fields) (request : Request) : Option (Response digest request) :=
  match projected : body.range? (request.window claim) with
  | none => none
  | some _ => some ⟨claim, .body body projected, body.final.eof⟩

def finishPrefix? {claim after : Nat} {digest input rest : Bytes} {request : Request}
    {initial final : Session claim digest}
    (trace : Prefix (request.window claim) (request.window claim).start initial input after final rest)
    (atBoundary : Bool) : Option (Done claim digest request) :=
  if complete : rangeFinished (request.window claim) after final rest atBoundary = true then
    some (.prefix trace atBoundary complete)
  else none

/-- Match separately obtained EOF evidence to the wire schedule without equating
any two digests or trusting a differently sized header. -/
def Response.doneAt? {digest : Bytes} {request : Request} (response : Response digest request)
    (size : Nat) : Option (Done size digest request) :=
  if same : response.claim = size then some (same ▸ response.done) else none

/-- Use the same request API on the actual strict Bao combined frame. -/
def decodeCombined? (cap : Nat) (digest : Bytes) (request : Request) (wire : Bytes) :
    Option (Response digest request) := do
  let frame ← checkBaoInline? .combined cap digest wire
  ofBody? frame.body request

/-- Resolve an open-ended request using the header for scheduling only. A result may
be sealed as a suffix only with independent authenticated extent. -/
def decodeSlice? (cap : Nat) (digest : Bytes) (request : Request) (wire : Bytes) :
    Option (Response digest request) := do
  let (claim, _) ← Bao.readHeader wire
  let frame ← checkBaoInline? (.slice (request.window claim)) cap digest wire
  ofBody? frame.body request

def decodeOutboard? (cap : Nat) (digest : Bytes) (request : Request) (wire original : Bytes) :
    Option (Response digest request) := do
  let frame ← checkBaoOutboard? cap digest wire original
  ofBody? frame.body request

/-- Iroh selection is in the raw Get request; `request` is a local byte projection.
It must be exactly covered by the checked response, not merely within the header extent. -/
def decodeIroh? (cap : Nat) (digest : Bytes) (request : Request) (get wire : Bytes) :
    Option (Response digest request) := do
  let frame ← checkIrohRawGet? cap digest get wire
  ofBody? frame.frame.body request

end Silmaril.Formats.Blake3Cas.RangeFacts
