module

public import Silmaril.Machine.SystemV.Abi.Native.Defs
public import Silmaril.Machine.C.Api.SysV.Defs

/-! Typed native FFI contracts. These definitions extend the imported integer
machine state with vector/x87 and control-state observations. They supply no
execution semantics for those extra observations: an implementation must connect
its actual execution relation to this state and prove the contract below.
-/

@[expose] public section
namespace Silmaril.Machine.SystemV.Abi.Ffi

open Silmaril.Cerberus.NativeTypes (CType Representation Bytes)
open Silmaril.X86 (MState Reg)

/-- State missing from the imported integer machine is explicit, so its ABI
preservation obligations cannot disappear behind scalar register contracts. -/
structure State where
  machine : MState
  vectors : Nat → BitVec 512
  x87 : Nat → BitVec 80
  direction : Bool
  x87Mode : Bool
  mxcsr : BitVec 32
  x87Control : BitVec 16
  fsBase : BitVec 64

def bytesOfNat (value offset count : Nat) : Bytes :=
  (List.range count).map fun index => UInt8.ofNat (value / 2 ^ (8 * (offset + index)))

/-- Reads only the object's bytes; excess register bits remain unspecified. -/
def locationBytes (state : State) (location : Location) (count : Nat) : Option Bytes :=
  match location with
  | .gp register =>
      if count ≤ 8 then some (bytesOfNat ((state.machine.core.read register).setWidth (8 * count)).toNat 0 count)
      else none
  | .vector index offset =>
      if index < 32 && offset + count ≤ 64 then
        some (bytesOfNat (state.vectors index).toNat offset count)
      else none
  | .x87 index =>
      if index < 8 && count ≤ 10 then some (bytesOfNat (state.x87 index).toNat 0 count)
      else none

def StoredAt (state : State) (address : Nat) (bytes : Bytes) : Prop :=
  address + bytes.length ≤ 2 ^ 64 ∧
    state.machine.memory.readBytes address bytes.length =
      some (bytes.map fun byte => BitVec.ofNat 8 byte.toNat)

/-- NO_CLASS bytes, floating padding and excess register bits remain free. -/
def ChunksAt (state : State) (bytes : Bytes) (chunks : List Chunk) : Prop :=
  ∀ chunk ∈ chunks, chunk.offset + chunk.bytes ≤ bytes.length ∧
    locationBytes state chunk.location chunk.bytes =
      some ((bytes.drop chunk.offset).take chunk.bytes)

structure ObjectSpec where
  type : CType
  object : Object
  representation : Representation type
  size : representation.layout.size = object.size
  alignment : representation.layout.align = object.align
  valid : object.valid = true

def Values : List ObjectSpec → Type
  | [] => PUnit
  | object :: rest => object.representation.Value × Values rest

def ResultValue : Option ObjectSpec → Type
  | none => PUnit
  | some object => object.representation.Value

def ArgumentAt (state : State) (spec : ObjectSpec)
    (value : spec.representation.Value) (argument : Argument) : Prop :=
  argument.object = spec.object ∧ ∃ bytes, spec.representation.encodes value bytes ∧
    match argument.stackOffset with
    | none => ChunksAt state bytes argument.chunks
    | some offset => StoredAt state ((state.machine.core.read .rsp).toNat + 8 + offset) bytes

def ArgumentsAt (state : State) : (specs : List ObjectSpec) → Values specs → List Argument → Prop
  | [], _, [] => True
  | spec :: rest, (value, values), argument :: arguments =>
      ArgumentAt state spec value argument ∧ ArgumentsAt state rest values arguments
  | _, _, _ => False

/-- Actual arguments include variadic arguments after C default promotions.
The declaration and those promotion rules are separate frontend obligations. -/
structure Signature where
  profile : Profile
  arguments : List ObjectSpec
  result : Option ObjectSpec
  namedCount : Nat
  variadic : Bool
  callPlan : CallPlan
  planned : plan profile (arguments.map (·.object)) (result.map (·.object))
    namedCount variadic = .ok callPlan

structure Call where
  entry : BitVec 64
  exit : BitVec 64
  initial : State
  resultStorage : Option Nat

/-- Sret storage must not alias objects visible through other arguments. The
predicate is supplied by the memory/ownership model, not inferred from bytes. -/
def SretAt (signature : Signature) (call : Call) (unaliased : Nat → Nat → Prop) : Prop :=
  match signature.callPlan.result with
  | .indirect size alignment => ∃ address, call.resultStorage = some address ∧
      address < 2 ^ 64 ∧ address + size ≤ 2 ^ 64 ∧ address % alignment = 0 ∧
      (call.initial.machine.core.read .rdi).toNat = address ∧ unaliased address size
  | _ => call.resultStorage = none

structure Entry (signature : Signature) (arguments : Values signature.arguments)
    (call : Call) (unaliased : Nat → Nat → Prop) : Prop where
  pc : call.initial.machine.core.rip = call.entry
  argumentsAt : ArgumentsAt call.initial signature.arguments arguments signature.callPlan.arguments
  alignment : ((call.initial.machine.core.read .rsp).toNat + 8) %
    signature.callPlan.stackAlign = 0
  stackNoWrap : (call.initial.machine.core.read .rsp).toNat + 8 +
    signature.callPlan.stackSize ≤ 2 ^ 64
  returnAddress : call.initial.machine.memory.readBytes
    (call.initial.machine.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [call.exit])
  sret : SretAt signature call unaliased
  direction : call.initial.direction = false
  x87Mode : call.initial.x87Mode = true
  variadicAL : ∀ count, signature.callPlan.variadicAL = some count →
    count ≤ (call.initial.machine.core.read .rax).toNat % 256 ∧
    (call.initial.machine.core.read .rax).toNat % 256 ≤ 8

def ResultAt (signature : Signature) (call : Call) (final : State)
    (value : ResultValue signature.result) : Prop :=
  match signature.result, value with
  | none, _ => signature.callPlan.result = .void
  | some spec, value => ∃ bytes, spec.representation.encodes value bytes ∧
      match signature.callPlan.result with
      | .void => False
      | .direct chunks => ChunksAt final bytes chunks
      | .indirect _ _ => ∃ address, call.resultStorage = some address ∧
          StoredAt final address bytes ∧ (final.machine.core.read .rax).toNat = address

structure Return (call : Call) (final : State) : Prop where
  pc : final.machine.core.rip = call.exit
  stack : final.machine.core.read .rsp = call.initial.machine.core.read .rsp + 8
  calleeSaved : ∀ register ∈ Silmaril.X86.sysv64.calleeSaved,
    final.machine.core.read register = call.initial.machine.core.read register
  direction : final.direction = false
  x87Mode : final.x87Mode = true
  mxcsrControl : final.mxcsr &&& 0xffc0 = call.initial.mxcsr &&& 0xffc0
  x87Control : final.x87Control = call.initial.x87Control
  threadPointer : final.fsBase = call.initial.fsBase

abbrev Footprint := Nat → Prop

def Frame (writes : Footprint) (call : Call) (final : State) : Prop :=
  call.initial.machine.memory.WritesWithin final.machine.memory writes

structure Result (signature : Signature) (value : ResultValue signature.result)
    (writes : Footprint) (call : Call) (final : State) : Prop where
  returned : Return call final
  valueAt : ResultAt signature call final value
  frame : Frame writes call final

/-- A typed native function/callback contract for an actual execution relation.
Existence of a returning run is separate from universal safety/determinism. -/
def Realizes (signature : Signature)
    (result : Values signature.arguments → ResultValue signature.result)
    (writes : Values signature.arguments → Footprint)
    (unaliased : Values signature.arguments → Nat → Nat → Prop)
    (domain : Values signature.arguments → Call → Prop)
    (execute : Call → State → Prop) : Prop :=
  ∀ arguments call, Entry signature arguments call (unaliased arguments) →
    domain arguments call → ∃ final, execute call final ∧
      Result signature (result arguments) (writes arguments) call final

/-- Every admitted execution outcome satisfies the native result contract. The
source-language preconditions, including avoidance of undefined behavior, belong
in `domain`. This property alone makes no termination assertion. -/
def PartialCorrect (signature : Signature)
    (result : Values signature.arguments → ResultValue signature.result)
    (writes : Values signature.arguments → Footprint)
    (unaliased : Values signature.arguments → Nat → Nat → Prop)
    (domain : Values signature.arguments → Call → Prop)
    (execute : Call → State → Prop) : Prop :=
  ∀ arguments call, Entry signature arguments call (unaliased arguments) →
    domain arguments call → ∀ final, execute call final →
      Result signature (result arguments) (writes arguments) call final

/-- Termination is a separate existence obligation for admitted calls. -/
def Terminates (signature : Signature)
    (unaliased : Values signature.arguments → Nat → Nat → Prop)
    (domain : Values signature.arguments → Call → Prop)
    (execute : Call → State → Prop) : Prop :=
  ∀ arguments call, Entry signature arguments call (unaliased arguments) →
    domain arguments call → ∃ final, execute call final

def TotalCorrect (signature : Signature)
    (result : Values signature.arguments → ResultValue signature.result)
    (writes : Values signature.arguments → Footprint)
    (unaliased : Values signature.arguments → Nat → Nat → Prop)
    (domain : Values signature.arguments → Call → Prop)
    (execute : Call → State → Prop) : Prop :=
  PartialCorrect signature result writes unaliased domain execute ∧
    Terminates signature unaliased domain execute

end Silmaril.Machine.SystemV.Abi.Ffi
