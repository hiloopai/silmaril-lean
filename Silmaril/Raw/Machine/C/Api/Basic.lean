module

public import Silmaril.Semantics.CPort.Logic.Institution.Bridges.Contracts.Defs
public import Mathlib.Data.BitVec

/-!
# Typed contracts for a C API

An API is a family of operations, each with a C signature and independent
logical request/response types. Logical records may contain byte sequences,
stream states and ownership tokens; they need not be an ABI memory layout.
`arguments` and `result` identify the C values at the boundary. Pointer validity,
state changes, callback protocols and ownership belong in the contract and its
machine representation, not in the scalar signature.

This first profile covers fixed-arity INTEGER-class calls under LP64. Floating
point, aggregates passed by value and varargs require another profile. Signed
values are two's-complement bit patterns; `Scalar.signed` exposes their integer
meaning. Provenance and availability are recorded separately from satisfaction.
-/

@[expose] public section

set_option autoImplicit false

namespace Silmaril.C.Api

/-- The scalar classes supported by the initial LP64 ABI adapter. -/
inductive Scalar where
  | int32 | uint32 | int64 | uint64 | pointer
  deriving DecidableEq, Repr

def Scalar.Value : Scalar → Type
  | .int32 | .uint32 => BitVec 32
  | .int64 | .uint64 | .pointer => BitVec 64

/-- Mathematical interpretation of signed scalar bit patterns. -/
def Scalar.signed : (kind : Scalar) → kind.Value → Int
  | .int32, value => value.toInt
  | .int64, value => value.toInt
  | .uint32, value => value.toNat
  | .uint64, value => value.toNat
  | .pointer, value => value.toNat

/-- A fixed-arity C signature, after typedef and target-profile resolution. -/
structure Signature where
  arguments : List Scalar
  result : Option Scalar
  deriving DecidableEq, Repr

/-- A heterogeneous, signature-indexed tuple of C argument values. -/
inductive Arguments : List Scalar → Type where
  | nil : Arguments []
  | cons {kind : Scalar} {kinds : List Scalar} (head : kind.Value) (tail : Arguments kinds) :
      Arguments (kind :: kinds)

/-- `none` is a C `void` result. -/
def ReturnValue : Option Scalar → Type
  | none => Unit
  | some kind => kind.Value

/-- One semantic operation. The C signature and logical types stay distinct. -/
structure Operation where
  symbol : String
  signature : Signature
  Input : Type
  Output : Type
  arguments : Input → Arguments signature.arguments
  result : Output → ReturnValue signature.result
  pre : Input → Prop
  post : Input → Output → Prop

/-- An API can expose many named operations, each with different logical types. -/
structure Interface where
  OperationId : Type
  operation : OperationId → Operation

/-- Availability selects an explicitly named subset; it is not a proof of any
contract. A full API claim uses all supported operations of its target profile. -/
structure Profile (api : Interface) where
  name : String
  enabled : api.OperationId → Prop

/-- A pinned source location is documentary evidence, not a semantic axiom. -/
structure SourceReference where
  uri : String
  sha256 : String
  anchor : String
  interpretation : String
  deriving Repr

/-- Formal contracts over logical calls use the repository's contract institution. -/
def Operation.contract (operation : Operation) :
    Silmaril.Logic.Institution.Bridges.Contracts.Contract operation.Input operation.Output where
  pre := operation.pre
  post := operation.post

/-- A reusable, representation-independent contract refinement helper. -/
theorem satisfaction_weaken {Input Output : Type}
    {model : Silmaril.Logic.Institution.Bridges.Contracts.Model Input Output}
    {first second : Silmaril.Logic.Institution.Bridges.Contracts.Contract Input Output}
    (correct : Silmaril.Logic.Institution.Bridges.Contracts.Sat model first)
    (domain : ∀ input, second.pre input → first.pre input)
    (post : ∀ input output, second.pre input → first.post input output →
      second.post input output) :
    Silmaril.Logic.Institution.Bridges.Contracts.Sat model second := by
  intro input admitted
  obtain ⟨progress, outcomes⟩ := correct input (domain input admitted)
  exact ⟨progress, fun output returned => post input output admitted (outcomes output returned)⟩

/-- Boundary sanity: the signed status `Z_STREAM_ERROR = -2` is not a large
positive status even though its register representation has many set bits. -/
theorem signed_status_sanity :
    Scalar.signed .int32 (BitVec.ofInt 32 (-2)) = -2 := by decide

end Silmaril.C.Api
