module

public import Silmaril.X86.SystemV.CApi.Defs
public import Silmaril.X86.Spec.EnsuresSysV
public import Silmaril.X86.CallingConvention
public import Silmaril.X86.Ext.Machine

/-! # Fixed Linux x86-64 SysV LP64 boundary

The low 32 bits carry an `int` or `unsigned int`; high register/stack-slot bits
are unspecified. Longs and pointers use all 64 bits. The first six INTEGER
arguments use the standard registers, and later arguments use eight-byte stack
slots after the return address. The model does not claim ISO C pointer
provenance, a struct layout, or a separation-logic soundness theorem.
The underlying machine omits the direction flag and floating-control state, so
full native psABI conformance needs those additional state components.
-/

@[expose] public section

set_option autoImplicit false

namespace Silmaril.X86.SystemV

open Silmaril.X86 (Word Byte MState Reg sysv64)
open Silmaril.X86.SystemV.CApi

/-- The one ABI selected by this adapter. -/
def abi : String := "x86_64-linux-gnu/sysv-amd64-lp64/integer-state-v1"

/-- Encoding is deliberately relational for 32-bit scalars: upper bits are free. -/
def Encodes : (kind : Scalar) → kind.Value → Word → Prop
  | .int32, value, word => word.setWidth 32 = value
  | .uint32, value, word => word.setWidth 32 = value
  | .int64, value, word => word = value
  | .uint64, value, word => word = value
  | .pointer, value, word => word = value

/-- A register or stack slot holding INTEGER argument number `index`. -/
def ArgumentWord (initial : MState) (index : Nat) (word : Word) : Prop :=
  match sysv64.intArgRegs[index]? with
  | some register => initial.core.read register = word
  | none => initial.memory.readBytes
      ((initial.core.read .rsp).toNat + 8 + 8 * (index - 6)) 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [word])

def ArgumentsAt (initial : MState) : {kinds : List Scalar} → Arguments kinds → Nat → Prop
  | _, .nil, _ => True
  | _, .cons (kind := kind) value tail, index =>
      (∃ word, ArgumentWord initial index word ∧ Encodes kind value word) ∧
        ArgumentsAt initial tail (index + 1)

def ResultAt (final : MState) : (kind : Option Scalar) → ReturnValue kind → Prop
  | none, _ => True
  | some kind, value => Encodes kind value (final.core.read .rax)

/-- Call metadata is logical, and is not passed as extra C arguments. -/
structure Call where
  entry : Word
  exit : Word
  initial : MState

/-- Architectural call obligations shared by every operation. -/
structure Entry (signature : Signature) (arguments : Arguments signature.arguments)
    (call : Call) : Prop where
  pc : call.initial.core.rip = call.entry
  arguments : ArgumentsAt call.initial arguments 0
  alignment : (call.initial.core.read .rsp).toNat % 16 = 8
  returnAddress : call.initial.memory.readBytes (call.initial.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [call.exit])
  stackNoWrap : (call.initial.core.read .rsp).toNat + 8 +
    8 * (signature.arguments.length - 6) ≤ 2 ^ 64

/-- Register/return discipline is independent of the API's heap abstraction. -/
structure Return (call : Call) (final : MState) : Prop where
  pc : final.core.rip = call.exit
  stack : final.core.read .rsp = call.initial.core.read .rsp + 8
  calleeSaved : ∀ register ∈ sysv64.calleeSaved,
    final.core.read register = call.initial.core.read register

/-- Aggregate layouts are a separate ABI obligation from argument registers.
A field width is in bytes; a semantic representation must explain the field's
meaning and prove that this recipe matches the selected C target profile. -/
structure FieldLayout where
  name : String
  offset : Nat
  width : Nat
  alignment : Nat
  deriving DecidableEq, Repr

structure AggregateLayout where
  name : String
  size : Nat
  alignment : Nat
  fields : List FieldLayout
  deriving DecidableEq, Repr

/-- Internal layout consistency. This alone is not a proof that a C compiler
uses the recipe: that source/target correspondence is a separate certificate. -/
def AggregateLayout.WellFormed (layout : AggregateLayout) : Prop :=
  0 < layout.alignment ∧ layout.size % layout.alignment = 0 ∧
    (∀ field ∈ layout.fields, 0 < field.width ∧ 0 < field.alignment ∧
      field.offset % field.alignment = 0 ∧ field.offset + field.width ≤ layout.size) ∧
    layout.fields.Pairwise (fun first second =>
      first.offset + first.width ≤ second.offset ∨
        second.offset + second.width ≤ first.offset)

/-- A byte-level footprint, suitable for caller memory, private stack, streams,
allocator metadata, and callback-owned resources. Higher-level separation
reasoning can be connected to this representation separately. -/
abbrev Footprint := Nat → Prop

/-- Explicit caller ownership promises preservation outside the callee's write
footprint. This is a frame property of machine memory, not just return values. -/
def Frame (writes : Footprint) (call : Call) (final : MState) : Prop :=
  call.initial.memory.WritesWithin final.memory writes

/-! ## Native realizations of scalar C operations -/

/-- The convention of this boundary. -/
abbrev convention := Silmaril.X86.sysv64

/-- The observable result and frame of one native scalar call. The argument
representation and entry alignment are stated separately by `SysV.Entry`. -/
structure Result (kind : Option CApi.Scalar)
    (value : CApi.ReturnValue kind) (writes : Footprint)
    (call : Call) (final : Silmaril.X86.MState) : Prop where
  returned : Return call final
  valueAt : ResultAt final kind value
  frame : Frame writes call final

/-- A native implementation of a scalar C API operation. This is a specification:
a compiler or decompilation certificate must separately prove it for its code.
The domain records code loading and source preconditions beyond the ABI. The
implementation receives logical call metadata and must execute to its exit.
-/
def Realizes (signature : CApi.Signature)
    (result : CApi.Arguments signature.arguments →
      CApi.ReturnValue signature.result)
    (writes : CApi.Arguments signature.arguments → Footprint)
    (domain : CApi.Arguments signature.arguments → Call → Prop)
    (execute : Call → Silmaril.X86.MState → Prop) : Prop :=
  ∀ arguments call, Entry signature arguments call →
    domain arguments call → ∃ final, execute call final ∧
      Result signature.result (result arguments) (writes arguments) call final

end Silmaril.X86.SystemV
