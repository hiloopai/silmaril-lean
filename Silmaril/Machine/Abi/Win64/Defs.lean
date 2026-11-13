module

public import Silmaril.Machine.Abi.SystemV.Defs
public import Silmaril.X86.CallingConvention
/-! # The Microsoft x64 comorphism on the INTEGER/pointer fragment

This is the calling convention that GCC uses for `__attribute__((ms_abi))`
functions and that Windows x64 uses everywhere. It is a second ABI comorphism
from the *same* C interface institution as System V (`SystemV.vocab`, the
fixed-arity INTEGER/pointer prototypes of at most 127 parameters) to the *same*
machine institution (`Ffi.State`, `CallSite`). Only the convention differs:

* integer and pointer arguments 0–3 go in RCX, RDX, R8, R9 (positionally, so a
  register is consumed even by a later floating argument; the fragment has none);
* the caller reserves 32 bytes of *shadow space* above the return address, so
  argument `i ≥ 4` is the 8-byte slot at `RSP + 8 + 8 * i` on entry (the shadow
  space holds the home slots of arguments 0–3);
* `RSP + 8 ≡ 0 (mod 16)` on entry, the return address is at `[RSP]`;
* the result is in RAX; upper bits of 32-bit values are unspecified, as for
  System V;
* callee-saved: RBX, RBP, RDI, RSI, R12–R15 and the low 128 bits of XMM6–XMM15
  (the upper halves of YMM6–YMM15 are volatile), plus the MXCSR control bits and
  the x87 control word; the direction flag is clear at entry and exit;
* there is no red zone.

Source: Microsoft, "x64 calling convention" and "x64 ABI conventions"
(learn.microsoft.com, cpp/build/x64-calling-convention, x64-software-conventions),
and GCC 13 `ix86_function_arg`/`ix86_compute_frame_layout` for `ms_abi`
(`x86_64_ms_abi_int_parameter_registers`, `x86_64_ms_sysv_extra_clobbered_registers`).

Like the System V fragment, the convention reuses the ABI model's `Ffi` vocabulary:
arguments are `Ffi.ArgumentsAt` against a System V ABI `CallPlan`
(`msPlan`, built by hand here because the ABI model's `plan` is System V specific), and
results are read with `Ffi.ChunksAt` from RAX. The FS base is preserved as in
the System V model: GCC's `ms_abi` code on Linux keeps the thread pointer, and
Windows does not use FS in 64-bit mode.

Out of scope: floating and vector arguments, aggregates (passed by reference
when not 1, 2, 4 or 8 bytes), varargs (which duplicate floating arguments in
GPRs), `__vectorcall`, and frame/unwind-data obligations.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.Win64

open Silmaril.C.Api (Scalar Signature Arguments ReturnValue)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV (Proto CallSite toValues)
open Silmaril.X86 (Reg)
open Silmaril.Machine (CallingConvention)

/-- The integer part of Microsoft x64 as Silmaril calling-convention data
(the sibling of `Silmaril.X86.sysv64`). -/
def ms64 : CallingConvention Reg where
  intArgRegs := [.rcx, .rdx, .r8, .r9]
  intRetRegs := [.rax]
  calleeSaved := [.rbx, .rbp, .rdi, .rsi, .r12, .r13, .r14, .r15]
  stackPointer := .rsp
  stackAlign := 16
  entryResidue := 8
  redZone := 0
  shadowSpace := 32
  stackArgSlot := 8
  returnAddress := .onStack 0
  linkSize := 8

/-- Argument registers, in order. -/
def msArguments : List Reg := [.rcx, .rdx, .r8, .r9]

/-- The `i`-th argument uses the `i`-th of RCX, RDX, R8, R9; later ones use the
8-byte slot at `RSP + 8 + 8 * i` (above the 32-byte shadow space). -/
def msArg (object : Object) (index : Nat) : Argument :=
  match msArguments[index]? with
  | some register => ⟨object, [⟨0, object.size, .gp register⟩], none⟩
  | none => ⟨object, [], some (8 * index)⟩

def msArgs : List Object → Nat → List Argument
  | [], _ => []
  | object :: rest, index => msArg object index :: msArgs rest (index + 1)

/-- The caller's outgoing area: shadow space plus stack arguments, 16-aligned. -/
def outgoingSize (arity : Nat) : Nat := alignUp (8 * max arity 4) 16

/-- The Microsoft x64 call plan of a fragment prototype, in the ABI model's vocabulary. -/
def msPlan (args : List Object) (result : Option Object) : CallPlan where
  arguments := msArgs args 0
  result := Abi.SystemV.intReturn result
  stackSize := outgoingSize args.length
  stackAlign := 16
  gpUsed := min args.length 4
  vectorUsed := 0
  variadicAL := none

def plan (p : Proto) : CallPlan := msPlan p.objects p.resultObject

/-- Register reads of the integer state. -/
abbrev reg (s : Ffi.State) (r : Reg) : BitVec 64 := s.machine.core.read r

/-- Argument placement under Microsoft x64. The entry RIP is the callee address
and the return address is any word; neither is constrained. -/
structure Entry (p : Proto) (a : Arguments p.signature.arguments) (s : Ffi.State) : Prop where
  argumentsAt : Ffi.ArgumentsAt s (p.signature.arguments.map SystemV.Kind.spec) (toValues a)
    (plan p).arguments
  alignment : ((reg s .rsp).toNat + 8) % 16 = 0
  stackNoWrap : (reg s .rsp).toNat + 8 + outgoingSize p.signature.arguments.length ≤ 2 ^ 64
  returnAddress : ∃ exit, s.machine.memory.readBytes (reg s .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [exit])
  direction : s.direction = false
  x87Mode : s.x87Mode = true

/-- The return discipline to a given return address. -/
structure Returns (exit : BitVec 64) (initial final : Ffi.State) : Prop where
  pc : final.machine.core.rip = exit
  stack : reg final .rsp = reg initial .rsp + 8
  calleeSaved : ∀ register ∈ ms64.calleeSaved, reg final register = reg initial register
  vectorsSaved : ∀ index, 6 ≤ index → index < 16 →
    (final.vectors index).setWidth 128 = (initial.vectors index).setWidth 128
  direction : final.direction = false
  x87Mode : final.x87Mode = true
  mxcsrControl : final.mxcsr &&& 0xffc0 = initial.mxcsr &&& 0xffc0
  x87Control : final.x87Control = initial.x87Control
  threadPointer : final.fsBase = initial.fsBase

/-- A return to the address the call pushed. -/
def Return (initial final : Ffi.State) : Prop :=
  ∃ exit, initial.machine.memory.readBytes (reg initial .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [exit]) ∧ Returns exit initial final

/-- A fragment result in the low bytes of RAX (the same rule as System V). -/
def RaxResult : (r : Option Scalar) → ReturnValue r → Ffi.State → Prop
  | none, _, _ => True
  | some k, v, s => ∃ bytes, (SystemV.Kind.spec k).representation.encodes v bytes ∧
      Ffi.ChunksAt s bytes [⟨0, (SystemV.Kind.object k).size, .gp .rax⟩]

/-- The Microsoft x64 convention on the fragment, given an encoding of every
argument tuple (`Thms.win64` discharges it). -/
def convention (inhabited : ∀ (p : Proto) (a : Arguments p.signature.arguments),
    ∃ s, Entry p a s) : Convention SystemV.vocab Ffi.State CallSite where
  tag := .win64
  desc p := ⟨.win64, .ok (plan p)⟩
  Entry := Entry
  Return _ := Return
  ResultAt p _ s' r := RaxResult p.signature.result r s'
  inhabited := inhabited

end Silmaril.Machine.Abi.Win64
