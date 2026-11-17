module

public import Silmaril.Machine.Abi.SystemV.Defs

/-!
# The System V AMD64 comorphism on the scalar fragment

C prototypes are fixed-arity lists of **scalars**: 4- and 8-byte integers and pointers
(INTEGER class) and IEEE binary32 and binary64 floating values (`float`, `double`: SSE
class), mixed freely, with at most 127 parameters. A floating value is its bit pattern
(`BitVec 32`, `BitVec 64`); the convention places bytes and says nothing about arithmetic.

The convention reuses the ABI model throughout, as the INTEGER fragment does
(`Machine.Abi.SystemV`):
* the descriptor of a prototype is the raw output of `SystemV.Abi.plan` on the classified
  objects (`Proto.plan`);
* argument placement is `Ffi.Entry` for the planned signature: INTEGER arguments in RDI, RSI,
  RDX, RCX, R8, R9 (`Ffi.ChunksAt` on `.gp`), SSE arguments in the low bytes of XMM0–XMM7
  (`.vector i 0`), each class counted separately, and the rest in 8-byte stack slots above the
  return address in argument order (`Ffi.StoredAt`);
* the return discipline is `Ffi.Return`;
* the result is `Ffi.ResultAt`: an INTEGER result in the low bytes of RAX, an SSE result in
  the low bytes of XMM0 (excess bits unspecified).

`scalarPlan` is the closed form of the planner on this fragment; `Thms.plan_scalarPlan`
proves that `plan` computes it under every vector profile. Long double (X87 class),
`__float128` (SSE + SSEUP), complex types, vectors, aggregates and varargs are outside the
fragment.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.SystemV.Scalar

open Silmaril.Machine.SystemV.Abi
open Silmaril.Cerberus.NativeTypes (CType Representation Bytes)

/-- The scalars of the fragment. -/
inductive Kind where
  | int32 | uint32 | int64 | uint64 | pointer
  /-- IEEE binary32 (`float`). -/
  | float
  /-- IEEE binary64 (`double`). -/
  | double
  deriving DecidableEq, Repr

namespace Kind

/-- Size and alignment in bytes. -/
def bytes : Kind → Nat
  | .int32 | .uint32 | .float => 4
  | .int64 | .uint64 | .pointer | .double => 8

/-- SSE class (floating) rather than INTEGER class. -/
def sse : Kind → Bool
  | .float | .double => true
  | _ => false

def ctype : Kind → CType
  | .int32 => .scalar (.integer .int .signed)
  | .uint32 => .scalar (.integer .int .unsigned)
  | .int64 => .scalar (.integer .long .signed)
  | .uint64 => .scalar (.integer .long .unsigned)
  | .pointer => .pointer .void
  | .float => .scalar (.floating .binary32)
  | .double => .scalar (.floating .binary64)

/-- The classified object: one eightbyte, SSE or INTEGER (psABI §3.2.3). -/
def object (k : Kind) : Object :=
  ⟨k.bytes, k.bytes, [if k.sse then .sse else .integer]⟩

/-- Values are bit patterns of the object's width. -/
abbrev Value (k : Kind) : Type := BitVec (8 * k.bytes)

/-- Little-endian bytes of a value: its object representation. -/
def encode (k : Kind) (v : k.Value) : Bytes :=
  Ffi.bytesOfNat v.toNat 0 k.bytes

def representation (k : Kind) : Representation k.ctype where
  layout := ⟨k.bytes, k.bytes, 8 * k.bytes⟩
  Value := k.Value
  encodes v bytes := bytes = encode k v
  exactSize := by rintro v bytes rfl; simp [encode, Ffi.bytesOfNat]

theorem object_valid (k : Kind) : k.object.valid = true := by cases k <;> decide

/-- The ABI model's object specification of a scalar. -/
def spec (k : Kind) : Ffi.ObjectSpec where
  type := k.ctype
  object := k.object
  representation := k.representation
  size := rfl
  alignment := rfl
  valid := object_valid k

end Kind

/-- A C prototype of the scalar fragment. -/
structure Proto where
  args : List Kind
  result : Option Kind
  arity : args.length ≤ maxArity

/-- The C vocabulary of the fragment: arguments are the ABI model's value tuples. -/
abbrev vocab : Vocab where
  Proto := Proto
  Args p := Ffi.Values (p.args.map Kind.spec)
  Ret p := Ffi.ResultValue (p.result.map Kind.spec)

/-! ## The closed-form plan -/

/-- Registers used so far: INTEGER (`gp`), SSE (`vec`), and 8-byte stack slots (`st`). -/
structure Used where
  gp : Nat
  vec : Nat
  st : Nat
  deriving DecidableEq, Repr

/-- The counters after one more argument. -/
def Used.next (c : Used) (k : Kind) : Used :=
  if k.sse then (if c.vec < 8 then { c with vec := c.vec + 1 } else { c with st := c.st + 1 })
  else (if c.gp < 6 then { c with gp := c.gp + 1 } else { c with st := c.st + 1 })

/-- The placement of an argument: the next INTEGER or SSE register of its class, or else the
next 8-byte stack slot. -/
def scalarArg (k : Kind) (c : Used) : Argument :=
  if k.sse then
    if c.vec < 8 then ⟨k.object, [⟨0, k.bytes, .vector c.vec 0⟩], none⟩
    else ⟨k.object, [], some (8 * c.st)⟩
  else
    if h : c.gp < 6 then
      ⟨k.object, [⟨0, k.bytes, .gp (gpArguments[c.gp]'(by simp [gpArguments]; omega))⟩], none⟩
    else ⟨k.object, [], some (8 * c.st)⟩

def scalarArgs : List Kind → Used → List Argument
  | [], _ => []
  | k :: ks, c => scalarArg k c :: scalarArgs ks (c.next k)

/-- The counters after a list of arguments. -/
def Used.final : List Kind → Used → Used
  | [], c => c
  | k :: ks, c => Used.final ks (c.next k)

/-- An INTEGER result in RAX, an SSE result in XMM0. -/
def scalarReturn : Option Kind → Return
  | none => .void
  | some k => .direct [⟨0, k.bytes, if k.sse then .vector 0 0 else .gp .rax⟩]

/-- The closed form of `SystemV.Abi.plan` on the fragment (`Thms.plan_scalarPlan`). -/
def scalarPlan (args : List Kind) (result : Option Kind) : CallPlan where
  arguments := scalarArgs args ⟨0, 0, 0⟩
  result := scalarReturn result
  stackSize := alignUp (8 * (Used.final args ⟨0, 0, 0⟩).st) 16
  stackAlign := 16
  gpUsed := (Used.final args ⟨0, 0, 0⟩).gp
  vectorUsed := (Used.final args ⟨0, 0, 0⟩).vec
  variadicAL := none

/-- Bytes of stack arguments above the return address. -/
def Proto.stackBytes (p : Proto) : Nat := 8 * (Used.final p.args ⟨0, 0, 0⟩).st

/-! ## The convention -/

/-- The raw planner applied to a prototype. -/
def Proto.plan (profile : Profile) (p : Proto) : Except String CallPlan :=
  Silmaril.Machine.SystemV.Abi.plan profile (p.args.map Kind.object)
    (p.result.map Kind.object) p.args.length false

/-- The planner hypothesis of the convention (proved as `Thms.plan_scalarPlan`). -/
def Planned (profile : Profile) : Prop :=
  ∀ p : Proto, p.plan profile = .ok (scalarPlan p.args p.result)

/-- The typed FFI signature of a prototype. -/
def Proto.ffi (profile : Profile) (planned : Planned profile) (p : Proto) : Ffi.Signature where
  profile := profile
  arguments := p.args.map Kind.spec
  result := p.result.map Kind.spec
  namedCount := p.args.length
  variadic := false
  callPlan := scalarPlan p.args p.result
  planned := by
    rw [← planned p]
    simp [Proto.plan, Function.comp_def, Kind.spec]

/-- Argument placement: `Ffi.Entry` for the planned signature, for some return address. -/
def Proto.Entry (profile : Profile) (planned : Planned profile) (p : Proto)
    (a : vocab.Args p) (s : Ffi.State) : Prop :=
  ∃ exit, Ffi.Entry (p.ffi profile planned) a (callOf s exit) (fun _ _ => True)

/-- The fragment's System V convention, given the planner theorem and an encoding of every
argument tuple. `Thms.sysv` discharges both. -/
def convention (options : Options) (planned : Planned options.profile)
    (inhabited : ∀ (p : Proto) (a : vocab.Args p), ∃ s, p.Entry options.profile planned a s) :
    Convention vocab Ffi.State CallSite where
  tag := options.tag
  desc p := ⟨options.tag, p.plan options.profile⟩
  Entry p a s := p.Entry options.profile planned a s
  Return _ s s' := ∃ exit,
    s.machine.memory.readBytes (s.machine.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit]) ∧
    Ffi.Return (callOf s exit) s'
  ResultAt p s s' r := Ffi.ResultAt (p.ffi options.profile planned) (callOf s 0) s' r
  inhabited := inhabited

end Silmaril.Machine.Abi.SystemV.Scalar
