module

public import Silmaril.Machine.Abi.Thunk.Defs
public import Silmaril.Machine.Abi.Win64.Defs
/-! # Bridging contracts between System V and Microsoft x64

A thunk between the two conventions, for prototypes whose arguments all go in
registers under both (`Small`: at most four parameters), is specified by two
state relations:

* `SysvToMs.Enter s s₁` / `SysvToMs.Leave s s₂ s₃`: a System V caller (entry
  state `s`) reaches an `ms_abi` callee (entry `s₁`, final `s₂`) and returns to
  the caller (final `s₃`). The adapter moves RDI, RSI, RDX, RCX to RCX, RDX, R8,
  R9, builds a 16-aligned callee frame with 32 bytes of shadow space and a
  return address, and on the way back restores RSP and jumps to the caller's
  return address. It does not save RSI, RDI or XMM6–15, because the
  Microsoft x64 callee preserves them anyway.
* `MsToSysv.Enter` / `MsToSysv.Leave`: the reverse. The adapter moves RCX, RDX,
  R8, R9 to RDI, RSI, RDX, RCX and must itself restore RSI, RDI and the low
  halves of XMM6–15, which a System V callee may clobber.

Both specifications pass the System V callee-saved registers and the control
state (direction flag, x87 mode, MXCSR, x87 control word, FS base) through
unchanged. A `Thunk` *implements* a specification when its relations are
contained in it. `CrossAbi.Thms` proves that implementing thunks are
simulations (`Convention.Thunk.Simulates`), and hence the composition
theorems. GCC's actual transition sequences are in `CrossAbi.Gcc`.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.CrossAbi

open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV (Proto CallSite vocab)
open Silmaril.Machine.Abi.Win64 (reg)
open Silmaril.Machine.LittleEndian (encodeWords)

/-- Prototypes whose arguments all go in registers under both conventions. -/
def Small (p : Proto) : Prop := p.signature.arguments.length ≤ 4

/-- The caller's return address is at its entry RSP, and the final RIP is it. -/
def ReturnsTo (s s₃ : Ffi.State) : Prop :=
  ∃ exit, s.machine.memory.readBytes (reg s .rsp).toNat 8 = some (encodeWords [exit]) ∧
    s₃.machine.core.rip = exit

/-- The control state of `s'` equals that of `s`. -/
structure SameControl (s s' : Ffi.State) : Prop where
  direction : s'.direction = s.direction
  x87Mode : s'.x87Mode = s.x87Mode
  mxcsr : s'.mxcsr = s.mxcsr
  x87Control : s'.x87Control = s.x87Control
  fsBase : s'.fsBase = s.fsBase

/-- A callee entry frame: aligned, with room for the outgoing area, and a
readable return address. -/
structure CalleeFrame (outgoing : Nat) (s₁ : Ffi.State) : Prop where
  alignment : ((reg s₁ .rsp).toNat + 8) % 16 = 0
  stackNoWrap : (reg s₁ .rsp).toNat + 8 + outgoing ≤ 2 ^ 64
  returnAddress : ∃ exit, s₁.machine.memory.readBytes (reg s₁ .rsp).toNat 8 =
    some (encodeWords [exit])

namespace SysvToMs

structure Enter (s s₁ : Ffi.State) : Prop where
  rcx : reg s₁ .rcx = reg s .rdi
  rdx : reg s₁ .rdx = reg s .rsi
  r8 : reg s₁ .r8 = reg s .rdx
  r9 : reg s₁ .r9 = reg s .rcx
  saved : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, reg s₁ r = reg s r
  frame : CalleeFrame 32 s₁
  control : SameControl s s₁

structure Leave (s s₂ s₃ : Ffi.State) : Prop where
  pc : ReturnsTo s s₃
  stack : reg s₃ .rsp = reg s .rsp + 8
  rax : reg s₃ .rax = reg s₂ .rax
  saved : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, reg s₃ r = reg s₂ r
  control : SameControl s₂ s₃

end SysvToMs

namespace MsToSysv

structure Enter (s s₁ : Ffi.State) : Prop where
  rdi : reg s₁ .rdi = reg s .rcx
  rsi : reg s₁ .rsi = reg s .rdx
  rdx : reg s₁ .rdx = reg s .r8
  rcx : reg s₁ .rcx = reg s .r9
  saved : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, reg s₁ r = reg s r
  frame : CalleeFrame 0 s₁
  control : SameControl s s₁

structure Leave (s s₂ s₃ : Ffi.State) : Prop where
  pc : ReturnsTo s s₃
  stack : reg s₃ .rsp = reg s .rsp + 8
  rax : reg s₃ .rax = reg s₂ .rax
  saved : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, reg s₃ r = reg s₂ r
  rsi : reg s₃ .rsi = reg s .rsi
  rdi : reg s₃ .rdi = reg s .rdi
  vectors : ∀ index, 6 ≤ index → index < 16 →
    (s₃.vectors index).setWidth 128 = (s.vectors index).setWidth 128
  control : SameControl s₂ s₃

end MsToSysv

variable {A B : Convention vocab Ffi.State CallSite} {p : Proto}

/-- A thunk's relations are contained in a bridging specification, on admitted
caller states meeting `room` and well-behaved callee returns meeting `guar`. -/
structure Implements (t : Convention.Thunk A B p)
    (enter : Ffi.State → Ffi.State → Prop)
    (leave : Ffi.State → Ffi.State → Ffi.State → Prop)
    (room : Ffi.State → Prop) (guar : Ffi.State → Ffi.State → Prop) : Prop where
  enter : ∀ a s, A.Entry p a s → room s → ∀ s₁ ∈ t.enter s, enter s s₁
  leave : ∀ a s, A.Entry p a s → room s → ∀ s₁ ∈ t.enter s, ∀ s₂,
    B.Proper p s₁ s₂ → guar s₁ s₂ → ∀ s₃ ∈ t.leave s s₂, leave s s₂ s₃

/-- Progress of a thunk's own code: on admitted caller states it reaches the
callee, and from well-behaved callee returns meeting `guar` it returns. -/
structure Progress (t : Convention.Thunk A B p) (room : Ffi.State → Prop)
    (guar : Ffi.State → Ffi.State → Prop) : Prop where
  enter : ∀ a s, A.Entry p a s → room s → (t.enter s).Nonempty
  leave : ∀ a s, A.Entry p a s → room s → ∀ s₁ ∈ t.enter s, ∀ s₂,
    B.Proper p s₁ s₂ → guar s₁ s₂ → (t.leave s s₂).Nonempty

end Silmaril.Machine.Abi.CrossAbi
