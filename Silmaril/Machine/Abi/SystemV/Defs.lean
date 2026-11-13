module

public import Silmaril.Machine.Abi.Defs
public import Silmaril.Machine.SystemV.Abi.Ffi.Defs
/-! # The System V AMD64 comorphism on the INTEGER/pointer fragment

C prototypes are the fixed-arity INTEGER-class signatures of `Silmaril.C.Api`
(`int`, `unsigned`, `long`, `unsigned long`, pointers as 64-bit addresses), with
at most 127 parameters (the C17 §5.2.4.1 translation minimum, which also keeps
the outgoing stack area inside the address space).

The convention reuses the ABI model throughout:
* the descriptor of a prototype is the raw output of `SystemV.Abi.plan` on the
  classified argument and result objects (`desc`);
* argument placement is `Ffi.Entry` for the signature planned by `plan`
  (registers via `Ffi.ChunksAt`, stack slots via `Ffi.StoredAt`, alignment,
  return address, direction flag, x87 mode);
* the return discipline is `Ffi.Return` (RIP, RSP + 8, callee-saved GPRs,
  direction flag, x87 mode, MXCSR/x87 control, FS base);
* results are `Ffi.ResultAt` (low bytes of RAX; excess bits unspecified).

`plan_intPlan` (in `Thms`) proves that `plan` returns the closed-form `intPlan`
for every profile, so the planned `Ffi.Signature` is total on the fragment.
Floating, aggregate, varargs and MEMORY-class prototypes are outside this
fragment; pointer provenance is not modelled (addresses only).
-/

@[expose] public section
namespace Silmaril.Machine.Abi.SystemV

open Silmaril.C.Api (Scalar Signature Arguments ReturnValue)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Cerberus.NativeTypes (CType Representation Bytes)

/-- The C17 minimum number of parameters an implementation must accept. -/
def maxArity : Nat := 127

/-- A C prototype of the INTEGER/pointer fragment. -/
structure Proto where
  signature : Signature
  arity : signature.arguments.length ≤ maxArity

/-- The C vocabulary of the fragment; ABI-independent. -/
abbrev vocab : Vocab where
  Proto := Proto
  Args p := Arguments p.signature.arguments
  Ret p := ReturnValue p.signature.result

namespace Kind

def bytes : Scalar → Nat
  | .int32 | .uint32 => 4
  | .int64 | .uint64 | .pointer => 8

/-- The zero-extended 64-bit image of a value. -/
def word : (k : Scalar) → k.Value → BitVec 64
  | .int32, v | .uint32, v => v.setWidth 64
  | .int64, v | .uint64, v | .pointer, v => v

/-- Little-endian bytes of a value: its object representation. -/
def encode (k : Scalar) (v : k.Value) : Bytes :=
  Ffi.bytesOfNat (word k v).toNat 0 (bytes k)

def ctype : Scalar → CType
  | .int32 => .scalar (.integer .int .signed)
  | .uint32 => .scalar (.integer .int .unsigned)
  | .int64 => .scalar (.integer .long .signed)
  | .uint64 => .scalar (.integer .long .unsigned)
  | .pointer => .pointer .void

def object : Scalar → Object
  | .int32 | .uint32 => .integer 4
  | .int64 | .uint64 => .integer 8
  | .pointer => .pointer

def representation (k : Scalar) : Representation (ctype k) where
  layout := ⟨bytes k, bytes k, 8 * bytes k⟩
  Value := k.Value
  encodes v bytes := bytes = encode k v
  exactSize := by rintro v bytes rfl; simp [encode, Ffi.bytesOfNat]

theorem object_size (k : Scalar) : (object k).size = bytes k := by cases k <;> rfl
theorem object_align (k : Scalar) : (object k).align = bytes k := by cases k <;> rfl
theorem object_valid (k : Scalar) : (object k).valid = true := by cases k <;> decide

/-- The the ABI model object specification of a fragment scalar. -/
def spec (k : Scalar) : Ffi.ObjectSpec where
  type := ctype k
  object := object k
  representation := representation k
  size := (object_size k).symm
  alignment := (object_align k).symm
  valid := object_valid k

end Kind

/-- Closed form of `plan` on INTEGER arguments: the `i`-th argument uses the
`i`-th of RDI, RSI, RDX, RCX, R8, R9, and later ones 8-byte stack slots. -/
def intArg (object : Object) (index : Nat) : Argument :=
  match gpArguments[index]? with
  | some register => ⟨object, [⟨0, object.size, .gp register⟩], none⟩
  | none => ⟨object, [], some (8 * (index - 6))⟩

def intArgs : List Object → Nat → List Argument
  | [], _ => []
  | object :: rest, index => intArg object index :: intArgs rest (index + 1)

def intReturn : Option Object → Return
  | none => .void
  | some object => .direct [⟨0, object.size, .gp .rax⟩]

def intPlan (args : List Object) (result : Option Object) : CallPlan where
  arguments := intArgs args 0
  result := intReturn result
  stackSize := alignUp (8 * (args.length - 6)) 16
  stackAlign := 16
  gpUsed := min args.length 6
  vectorUsed := 0
  variadicAL := none

def Proto.objects (p : Proto) : List Object := p.signature.arguments.map Kind.object
def Proto.resultObject (p : Proto) : Option Object := p.signature.result.map Kind.object

/-- The raw the ABI model planner applied to a prototype. -/
def Proto.plan (profile : Profile) (p : Proto) : Except String CallPlan :=
  Silmaril.Machine.SystemV.Abi.plan profile p.objects p.resultObject
    p.signature.arguments.length false

/-- A System V profile. The red zone constrains callee footprints, which this
value-level fragment does not state; it is recorded in the tag. -/
structure Options where
  profile : Profile := {}
  redZone : Bool := true

def Options.tag (options : Options) : Tag :=
  .sysv (match options.profile.vectors with | .sse => 0 | .avx => 1 | .avx512 => 2)
    options.redZone

/-- Machine descriptor: convention tag and the planner's raw output. -/
structure CallSite where
  tag : Tag
  plan : Except String CallPlan

/-- Entry states and their call metadata (RIP is the callee's entry address). -/
def callOf (state : Ffi.State) (exit : BitVec 64) : Ffi.Call :=
  ⟨state.machine.core.rip, exit, state, none⟩

def toValues : {ks : List Scalar} → Arguments ks → Ffi.Values (ks.map Kind.spec)
  | [], .nil => PUnit.unit
  | _ :: _, .cons head tail => (head, toValues tail)

def toResult : (r : Option Scalar) → ReturnValue r → Ffi.ResultValue (r.map Kind.spec)
  | none, _ => PUnit.unit
  | some _, v => v

/-- The planner hypothesis of the convention (proved as `Thms.plan_intPlan`). -/
def Planned (profile : Profile) : Prop :=
  ∀ p : Proto, p.plan profile = .ok (intPlan p.objects p.resultObject)

/-- The the ABI model typed FFI signature of a fragment prototype. -/
def Proto.ffi (profile : Profile) (planned : Planned profile) (p : Proto) : Ffi.Signature where
  profile := profile
  arguments := p.signature.arguments.map Kind.spec
  result := p.signature.result.map Kind.spec
  namedCount := p.signature.arguments.length
  variadic := false
  callPlan := intPlan p.objects p.resultObject
  planned := by
    rw [← planned p]
    simp [Proto.plan, Proto.objects, Proto.resultObject, Function.comp_def, Kind.spec]

/-- Argument placement: `Ffi.Entry` for the planned signature, for some return
address `exit`; the entry RIP is the callee's address, so it is not constrained. -/
def Proto.Entry (profile : Profile) (planned : Planned profile) (p : Proto)
    (a : Arguments p.signature.arguments) (s : Ffi.State) : Prop :=
  ∃ exit, Ffi.Entry (p.ffi profile planned) (toValues a) (callOf s exit) (fun _ _ => True)

/-- The fragment's System V convention, given the planner theorem and an
encoding of every argument tuple. `Thms.sysv` discharges both. -/
def convention (options : Options) (planned : Planned options.profile)
    (inhabited : ∀ (p : Proto) (a : Arguments p.signature.arguments),
      ∃ s, p.Entry options.profile planned a s) :
    Convention vocab Ffi.State CallSite where
  tag := options.tag
  desc p := ⟨options.tag, p.plan options.profile⟩
  Entry p a s := p.Entry options.profile planned a s
  Return _ s s' := ∃ exit,
    s.machine.memory.readBytes (s.machine.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit]) ∧
    Ffi.Return (callOf s exit) s'
  ResultAt p s s' r :=
    Ffi.ResultAt (p.ffi options.profile planned) (callOf s 0) s' (toResult _ r)
  inhabited := inhabited

end Silmaril.Machine.Abi.SystemV
