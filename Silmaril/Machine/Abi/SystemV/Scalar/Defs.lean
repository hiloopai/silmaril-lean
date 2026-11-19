module

public import Silmaril.Machine.Abi.SystemV.Defs

/-!
# The System V AMD64 comorphism on the scalar fragment, with small aggregates by value

C prototypes are fixed-arity lists of **scalars** and **aggregates passed by value**, with at
most 127 parameters:
* scalars: 4- and 8-byte integers and pointers (INTEGER class) and IEEE binary32 and binary64
  floating values (`float`, `double`: SSE class), mixed freely. A floating value is its bit
  pattern (`BitVec 32`, `BitVec 64`); the convention places bytes and says nothing about
  arithmetic;
* aggregates (`Agg`): a struct, union or array object already classified by the psABI
  (§3.2.3, "Classification") into eightbytes (`Eights`): MEMORY, or one or two eightbytes each
  INTEGER or SSE. Its value is its object representation (`Agg.Value`: its `size` bytes,
  padding included). The bytes of padding are **unspecified** in C (C17 6.2.6.1p6) and the
  psABI says nothing of them in registers: the convention carries whatever bytes the caller
  placed, so a spec (`S.pre`, `S.post`) that constrains padding bytes constrains something the
  ABI does not fix, and a spec meant to be about the C value should read only member bytes.
  Its alignment is at most 8 and its size at most `maxAggBytes`. The classification of a C
  struct or union comes from its member layout, in `Machine.Abi.Conformance.SysvScalar`
  (`leavesOf`: nested members flattened to their leaves at absolute offsets), through the ABI
  model's `SystemV.Abi.aggregate`.

The convention reuses the ABI model throughout, as the INTEGER fragment does
(`Machine.Abi.SystemV`):
* the descriptor of a prototype is the raw output of `SystemV.Abi.plan` on the classified
  objects (`Proto.plan`);
* argument placement is `Ffi.Entry` for the planned signature: INTEGER eightbytes in RDI, RSI,
  RDX, RCX, R8, R9 (`Ffi.ChunksAt` on `.gp`), SSE eightbytes in the low bytes of XMM0–XMM7
  (`.vector i 0`), each class counted separately. An argument of class MEMORY, or whose
  eightbytes do not all find a register of their class, goes **whole** to the stack, in 8-byte
  slots above the return address in argument order (`Ffi.StoredAt`), and takes no register;
* a MEMORY result is returned through a hidden pointer (`Return.indirect`): the caller passes
  the address of the result storage in RDI (so the arguments start at RSI) and the callee
  returns it in RAX (`Ffi.SretAt`, `Ffi.ResultAt`); `Proto.call` makes RDI the call's result
  storage;
* the return discipline is `Ffi.Return`;
* the result is `Ffi.ResultAt`: INTEGER eightbytes in RAX then RDX, SSE eightbytes in XMM0
  then XMM1 (low bytes; excess bits unspecified), or the bytes at the hidden pointer.

`scalarPlan` is the closed form of the planner on this fragment; `Thms.plan_scalarPlan`
proves that `plan` computes it under every vector profile. Long double (X87 class),
`__float128` (SSE + SSEUP), `__int128`, complex types, vectors, aggregates with an eightbyte of
another class (X87, SSEUP, NO_CLASS), aggregates aligned to more than 8 bytes and varargs are
outside the fragment.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.SystemV.Scalar

open Silmaril.Machine.SystemV.Abi
open Silmaril.Cerberus.NativeTypes (CType Representation Bytes)
open Silmaril.X86 (Reg)

/-- The class of one eightbyte of the fragment: SSE (`true`) or INTEGER (`false`). -/
def eightClass (sse : Bool) : Class := if sse then .sse else .integer

/-- The classes of an argument or result of the fragment (psABI §3.2.3): MEMORY, or one or two
eightbytes, each INTEGER or SSE (`true`). -/
inductive Eights where
  | memory
  | one (sse : Bool)
  | two (sse₀ sse₁ : Bool)
  deriving DecidableEq, Repr

def Eights.classes : Eights → List Class
  | .memory => [.memory]
  | .one s => [eightClass s]
  | .two s t => [eightClass s, eightClass t]

/-- An eightbyte class of the fragment: SSE (`true`) or INTEGER (`false`). -/
def classSse? : Class → Option Bool
  | .integer => some false
  | .sse => some true
  | _ => none

/-- The classes as `Eights`, if they are in the fragment. -/
def Eights.ofClasses : List Class → Option Eights
  | [.memory] => some .memory
  | [a] => (classSse? a).map .one
  | [a, b] => match classSse? a, classSse? b with
    | some s, some t => some (.two s t)
    | _, _ => none
  | _ => none

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
  ⟨k.bytes, k.bytes, (Eights.one k.sse).classes⟩

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

/-! ## Aggregates -/

/-- The largest aggregate of the fragment, in bytes (with at most 127 arguments, the outgoing
stack area stays inside the address space). -/
def maxAggBytes : Nat := 2 ^ 32

/-- A classified aggregate (struct, union or array object): size and alignment in bytes and the
classes of its eightbytes. `name` is its C spelling. -/
structure Agg where
  name : String
  size : Nat
  align : Nat
  eights : Eights
  deriving DecidableEq, Repr

namespace Agg

def object (a : Agg) : Object := ⟨a.size, a.align, a.eights.classes⟩

/-- In the fragment: a valid object of the ABI model (power-of-two alignment dividing the size,
one class per eightbyte), aligned to at most 8 bytes, of at most `maxAggBytes` bytes. -/
def ok (a : Agg) : Bool := a.object.valid && decide (a.align ≤ 8) && decide (a.size ≤ maxAggBytes)

/-- An aggregate's value is its object representation: `size` bytes, padding included. -/
abbrev Value (a : Agg) : Type := {b : Bytes // b.length = a.size}

/-- The C type of the object representation: `unsigned char[size]` (C17 6.2.6.1p4). -/
def ctype (a : Agg) : CType := .array (.scalar (.integer .char .unsigned)) (some a.size)

def representation (a : Agg) : Representation a.ctype where
  layout := ⟨a.size, a.align, 8 * a.size⟩
  Value := a.Value
  encodes v bytes := bytes = v.1
  exactSize := by rintro v bytes rfl; exact v.2

theorem valid_of_ok {a : Agg} (h : a.ok = true) : a.object.valid = true := by
  simp only [ok, Bool.and_eq_true] at h; exact h.1.1

/-- The ABI model's object specification of an aggregate. -/
def spec (a : Agg) (h : a.ok = true) : Ffi.ObjectSpec where
  type := a.ctype
  object := a.object
  representation := a.representation
  size := rfl
  alignment := rfl
  valid := valid_of_ok h

end Agg

/-- An argument or result of the fragment. -/
inductive Arg where
  | scalar (k : Kind)
  | agg (a : Agg) (ok : a.ok = true)
  deriving DecidableEq

namespace Arg

def size : Arg → Nat
  | .scalar k => k.bytes
  | .agg a _ => a.size

def align : Arg → Nat
  | .scalar k => k.bytes
  | .agg a _ => a.align

def eights : Arg → Eights
  | .scalar k => .one k.sse
  | .agg a _ => a.eights

def object : Arg → Object
  | .scalar k => k.object
  | .agg a _ => a.object

def spec : Arg → Ffi.ObjectSpec
  | .scalar k => k.spec
  | .agg a h => a.spec h

abbrev Value (a : Arg) : Type := a.spec.representation.Value

/-- The object representation of a value. -/
def encode : (a : Arg) → a.Value → Bytes
  | .scalar k, v => k.encode v
  | .agg _ _, v => v.1

@[simp] theorem spec_object (a : Arg) : a.spec.object = a.object := by cases a <;> rfl

theorem object_eq (a : Arg) : a.object = ⟨a.size, a.align, a.eights.classes⟩ := by
  cases a <;> rfl

end Arg

/-- A C prototype of the fragment. -/
structure Proto where
  args : List Arg
  result : Option Arg
  arity : args.length ≤ maxArity
  deriving DecidableEq

/-- The C vocabulary of the fragment: arguments are the ABI model's value tuples. -/
abbrev vocab : Vocab where
  Proto := Proto
  Args p := Ffi.Values (p.args.map Arg.spec)
  Ret p := Ffi.ResultValue (p.result.map Arg.spec)

/-! ## The closed-form plan -/

/-- Registers used so far: INTEGER (`gp`), SSE (`vec`), and 8-byte stack slots (`st`). -/
structure Used where
  gp : Nat
  vec : Nat
  st : Nat
  deriving DecidableEq, Repr

/-- The argument goes to registers: it is not MEMORY class and each of its INTEGER and SSE
eightbytes finds a register of its class (psABI §3.2.3: otherwise the whole argument goes to
the stack). -/
def Arg.fits (a : Arg) (c : Used) : Bool :=
  !memoryClass a.object && decide (c.gp + gpCount a.object ≤ 6) &&
    decide (c.vec + vectorCount a.object ≤ 8)

/-- The counters after one more argument. -/
def Used.next (c : Used) (a : Arg) : Used :=
  if a.fits c then ⟨c.gp + gpCount a.object, c.vec + vectorCount a.object, c.st⟩
  else { c with st := c.st + eightbytes a.size }

/-- The register chunks of an object of `size` bytes whose eightbytes from the `i`-th on have
classes `cs`: INTEGER ones in `regs` from the `g`-th on, SSE ones in the low bytes of the
vector registers from the `v`-th on. -/
def eightChunks (size : Nat) (regs : List Reg) : List Class → Nat → Nat → Nat → List Chunk
  | [], _, _, _ => []
  | .integer :: cs, i, g, v =>
    ⟨8 * i, min 8 (size - 8 * i), .gp (regs.getD g .rax)⟩ ::
      eightChunks size regs cs (i + 1) (g + 1) v
  | .sse :: cs, i, g, v =>
    ⟨8 * i, min 8 (size - 8 * i), .vector v 0⟩ :: eightChunks size regs cs (i + 1) g (v + 1)
  | _ :: cs, i, g, v => eightChunks size regs cs (i + 1) g v

/-- The placement of an argument: its eightbytes in the next INTEGER and SSE registers of their
classes, or else the next 8-byte stack slots, one per eightbyte. -/
def Arg.place (a : Arg) (c : Used) : Argument :=
  if a.fits c then ⟨a.object, eightChunks a.size gpArguments a.object.classes 0 c.gp c.vec, none⟩
  else ⟨a.object, [], some (8 * c.st)⟩

def placeArgs : List Arg → Used → List Argument
  | [], _ => []
  | a :: as, c => a.place c :: placeArgs as (c.next a)

/-- The counters after a list of arguments. -/
def Used.final : List Arg → Used → Used
  | [], c => c
  | a :: as, c => Used.final as (c.next a)

/-- INTEGER eightbytes of a result in RAX then RDX, SSE ones in XMM0 then XMM1; a MEMORY result
through the hidden pointer. -/
def placeReturn : Option Arg → Return
  | none => .void
  | some a => if a.eights = .memory then .indirect a.size a.align
    else .direct (eightChunks a.size gpReturns a.object.classes 0 0 0)

/-- INTEGER registers taken before the arguments: RDI, for the hidden pointer of a MEMORY
result. -/
def gpStart : Return → Nat
  | .indirect .. => 1
  | _ => 0

/-- The counters before the first argument. -/
def start (result : Option Arg) : Used := ⟨gpStart (placeReturn result), 0, 0⟩

/-- The closed form of `SystemV.Abi.plan` on the fragment (`Thms.plan_scalarPlan`). -/
def scalarPlan (args : List Arg) (result : Option Arg) : CallPlan where
  arguments := placeArgs args (start result)
  result := placeReturn result
  stackSize := alignUp (8 * (Used.final args (start result)).st) 16
  stackAlign := 16
  gpUsed := (Used.final args (start result)).gp
  vectorUsed := (Used.final args (start result)).vec
  variadicAL := none

/-- Bytes of stack arguments above the return address. -/
def Proto.stackBytes (p : Proto) : Nat := 8 * (Used.final p.args (start p.result)).st

/-- The result is MEMORY class: it is returned through the hidden pointer in RDI. -/
def Proto.indirect (p : Proto) : Bool := p.result.any (·.eights == .memory)

/-! ## The convention -/

/-- The raw planner applied to a prototype. -/
def Proto.plan (profile : Profile) (p : Proto) : Except String CallPlan :=
  Silmaril.Machine.SystemV.Abi.plan profile (p.args.map Arg.object)
    (p.result.map Arg.object) p.args.length false

/-- The planner hypothesis of the convention (proved as `Thms.plan_scalarPlan`). -/
def Planned (profile : Profile) : Prop :=
  ∀ p : Proto, p.plan profile = .ok (scalarPlan p.args p.result)

/-- The typed FFI signature of a prototype. -/
def Proto.ffi (profile : Profile) (planned : Planned profile) (p : Proto) : Ffi.Signature where
  profile := profile
  arguments := p.args.map Arg.spec
  result := p.result.map Arg.spec
  namedCount := p.args.length
  variadic := false
  callPlan := scalarPlan p.args p.result
  planned := by
    rw [← planned p]
    simp [Proto.plan, Function.comp_def]

/-- The call entered at `s` with return address `exit`: the callee's address is RIP, and the
result storage of a MEMORY result is the hidden pointer in RDI. -/
def Proto.call (p : Proto) (s : Ffi.State) (exit : BitVec 64) : Ffi.Call :=
  ⟨s.machine.core.rip, exit, s,
    if p.indirect then some (s.machine.core.read .rdi).toNat else none⟩

/-- Argument placement: `Ffi.Entry` for the planned signature, for some return address. The
hidden pointer of a MEMORY result is aligned and inside the address space (`Ffi.SretAt`). That
the storage is writable and does not alias the stack, the code or the caller's other objects
is not a register-placement fact (`unaliased` is `True` here); the conformance statement
requires it of admitted calls (`Machine.Abi.Conformance.Stack`, on `AbiDef.owned`). -/
def Proto.Entry (profile : Profile) (planned : Planned profile) (p : Proto)
    (a : vocab.Args p) (s : Ffi.State) : Prop :=
  ∃ exit, Ffi.Entry (p.ffi profile planned) a (p.call s exit) (fun _ _ => True)

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
  ResultAt p s s' r := Ffi.ResultAt (p.ffi options.profile planned) (p.call s 0) s' r
  inhabited := inhabited

end Silmaril.Machine.Abi.SystemV.Scalar
