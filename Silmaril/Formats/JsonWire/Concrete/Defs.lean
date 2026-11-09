module

public import Silmaril.Formats.Bytes

/-!
# Concrete syntax over bytes

Byte spans, lossless concrete event streams (`Concrete`: the events partition the source and
serialize back to it) and executable format profiles (`Profile`, `restrict`), over
`Silmaril.Formats.Bytes`. Lemmas: `Silmaril.Formats.JsonWire.Concrete.Thms`.
-/
@[expose] public section
namespace Silmaril.Formats.JsonWire

/-- A half-open byte range. Bounds are checked, never silently clamped. -/
structure Span where
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

def Span.bytes? (span : Span) (input : Bytes) : Option Bytes :=
  input.slice? span.start (some span.stop)

structure Located (Kind : Type) where
  kind : Kind
  span : Span
  deriving Repr

/-- Serialize a stream of byte-slice events in event order. -/
def serialize? {Kind : Type} (input : Bytes) : List (Located Kind) → Option Bytes
  | [] => some .empty
  | event :: rest => do
      let head ← event.span.bytes? input
      let tail ← serialize? input rest
      pure (head.append tail)

/-- Events must partition the input in order; repeated or omitted ranges fail. -/
def partitions {Kind : Type} (input : Bytes) (events : List (Located Kind)) : Bool :=
  let rec go (offset : Nat) : List (Located Kind) → Bool
    | [] => offset == input.length
    | e :: es => e.span.start == offset && decide (offset ≤ e.span.stop) &&
        decide (e.span.stop ≤ input.length) && go e.span.stop es
  go 0 events

/-- Concrete syntax retains the exact source and every token, including trivia.
The proof concerns byte reconstruction; grammatical validity is a separate claim. -/
structure Concrete (Ast Kind : Type) where
  source : Bytes
  ast : Ast
  events : List (Located Kind)
  partitioned : partitions source events = true
  lossless : serialize? source events = some source

/-- Certify the slice partition and byte reconstruction of an executable parse. -/
def concrete? {Ast Kind : Type} (source : Bytes) (ast : Ast)
    (events : List (Located Kind)) : Option (Concrete Ast Kind) :=
  if hp : partitions source events = true then
    if hs : serialize? source events = some source then
      some ⟨source, ast, events, hp, hs⟩
    else none
  else none

/-- A profile may restrict both semantic values and their wire spellings.
For example, integer-only JSON constrains values, while deterministic CBOR
also constrains number widths, lengths, and map-key order. -/
structure Profile (Ast : Type) where
  accepts : Bytes → Ast → Bool

def Profile.all {Ast : Type} : Profile Ast := ⟨fun _ _ => true⟩
def Profile.meet {Ast : Type} (p q : Profile Ast) : Profile Ast :=
  ⟨fun b a => p.accepts b a && q.accepts b a⟩
def Profile.value {Ast : Type} (p : Ast → Bool) : Profile Ast := ⟨fun _ => p⟩

/-- A successful parser result, tied to the actual decoder by an equality. -/
def IsSlice {Ast : Type} (decode : Bytes → Option Ast) (bytes : Bytes) : Prop :=
  ∃ ast, decode bytes = some ast

def restrict {Ast : Type} (decode : Bytes → Option Ast) (profile : Profile Ast)
    (bytes : Bytes) : Option Ast := do
  let ast ← decode bytes
  if profile.accepts bytes ast then some ast else none

end Silmaril.Formats.JsonWire
