module

public import Silmaril.Machine.Abi.CrossAbi.Defs
public import Silmaril.X86.Ext.Machine
public import Silmaril.X86.Ext.Decode
public import Silmaril.X86.Ext.SymExec
/-! # GCC's System V → `ms_abi` transition sequence

GCC 13.3 compiles a System V function that only forwards its arguments to an
`ms_abi` function (`examples/elf-ladder/11-multi-abi/sysv.c`)

```c
long call_ms(long a, long b, long c, long d) { return ms_mix(a, b, c, d); }
```

at `-O2` to (linked at `0x4013c0` in `build/O2/multi-abi`):

```text
48 83 ec 28      sub  $0x28,%rsp      ; 32 bytes shadow space + 8 alignment
49 89 d0         mov  %rdx,%r8
49 89 c9         mov  %rcx,%r9
48 89 f2         mov  %rsi,%rdx
48 89 f9         mov  %rdi,%rcx
e8 5b ff ff ff   call ms_mix
48 83 c4 28      add  $0x28,%rsp
c3               ret
```

The bytes are `callMsBytes`. `callMsEnter rel` (up to and including the call)
and `callMsLeave` (from the return point) are their Silmaril `Ext` decodings;
`Thms.callMs_decode` checks this by kernel `decide`. `run` executes such
straight-line code with `Ext.exec`. Each instruction is executed at its
canonical length, which equals the consumed length (`Thms.callMs_lengths`).

`callMs` is this code as a `Convention.Thunk`. It needs:

* `CallMs.Room`: 48 bytes of stack below the caller's RSP, with the slot that
  the `call` writes readable and writable;
* `CallMs.Guar`: the callee leaves the caller's return-address slot
  (`[RSP₁ + 48]`, i.e. the caller's `[RSP]`) intact. Value-level contracts do not
  say this; it is a frame property.

The step from `run` to fetching and decoding from memory
(`Silmaril.X86.Ext.stepOpt`) was the open goal `Task.callMsFetch`; it is proved in
round 4 (`Thms.callMsFetch_holds`, with the leave segment `Thms.callMsLeaveFetch_holds`).

## The linked form (round 4)

`callMs` relates the caller to the callee through the decoded list, and its `call`
displacement `rel` is a parameter, so nothing ties the callee to the call target. The
linked form fixes both:

* `callMsLinked A B p exit` runs the code **from memory**: the enter relation is six
  `Ext.stepOpt` retirements fetched at RIP, and the leave relation two `stepAny` steps
  (retirement or return) fetched at the return point.
* `CallMsAt.Room`: `CallMs.Room`, RIP is `callMsAddr` (`0x4013c0`, as linked) and the 26
  bytes `callMsBytes` are loaded executable there (`Ext.Loaded`).
* `CallMsAt.Guar`: `CallMs.Guar`, and the callee returns to the return point
  `callMsAddr + 21` with the 5 bytes of the leave segment still loaded there.
* `Thms.callMs_sound_linked` assumes the callee's contract **only at RIP = `msMixAddr`**
  (`0x401330`, the target of the linked displacement `callMsRel`), and its guarantee only
  there; `Thms.callMsLinked_lands` proves that the fetched code enters the callee there.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.CrossAbi.Gcc

open Silmaril.X86 (Reg Byte MState State)
open Silmaril.X86.Ext (Instr Sz RM)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.Win64 (reg)

/-- Execute straight-line code with `Ext.exec` at canonical lengths. -/
def run : List Instr → MState → Option MState
  | [], m => some m
  | i :: rest, m =>
    match Silmaril.X86.Ext.exec i m.core m.memory with
    | .ok core memory => run rest ⟨core, memory⟩
    | _ => none

/-- Lift a machine-code relation to `Ffi.State`: the extra FFI state is
untouched by integer code. -/
def onMachine (code : List Instr) (s : Ffi.State) : Set Ffi.State :=
  {s' | ∃ m, run code s.machine = some m ∧ s' = { s with machine := m }}

/-- `call_ms` as linked: 26 bytes at `0x4013c0`. -/
def callMsBytes : List Byte :=
  [0x48, 0x83, 0xec, 0x28, 0x49, 0x89, 0xd0, 0x49, 0x89, 0xc9, 0x48, 0x89, 0xf2,
   0x48, 0x89, 0xf9, 0xe8, 0x5b, 0xff, 0xff, 0xff, 0x48, 0x83, 0xc4, 0x28, 0xc3]

/-- The call displacement in the linked `call_ms` (to `ms_mix` at `0x401330`). -/
def callMsRel : BitVec 32 := 0xffffff5b

/-- The register moves before the call. -/
def callMsPre : List Instr :=
  [.aluI8 .q .sub (.reg .rsp) 0x28, .mov .q (.reg .r8) .rdx, .mov .q (.reg .r9) .rcx,
   .mov .q (.reg .rdx) .rsi, .mov .q (.reg .rcx) .rdi]

/-- From the caller's entry to the callee's entry. -/
def callMsEnter (rel : BitVec 32) : List Instr := callMsPre ++ [.call rel]

/-- From the callee's return to the caller's return. -/
def callMsLeave : List Instr := [.aluI8 .q .add (.reg .rsp) 0x28, .ret]

/-- GCC's transition code as a thunk from `A` callers to `B` callees. -/
def callMs (A B : Convention SystemV.vocab Ffi.State SystemV.CallSite) (p : SystemV.Proto)
    (rel : BitVec 32) : Convention.Thunk A B p where
  enter := onMachine (callMsEnter rel)
  leave _ := onMachine callMsLeave

namespace CallMs

/-- Stack the transition code needs below the caller's RSP. -/
structure Room (s : Ffi.State) : Prop where
  low : 48 ≤ (reg s .rsp).toNat
  write : s.machine.memory.Permitted .write ((reg s .rsp).toNat - 48) 8
  read : s.machine.memory.Permitted .read ((reg s .rsp).toNat - 48) 8

/-- The callee preserves the caller's return-address slot. -/
def Guar (s₁ s₂ : Ffi.State) : Prop :=
  s₂.machine.memory.readBytes ((reg s₁ .rsp).toNat + 48) 8 =
    s₁.machine.memory.readBytes ((reg s₁ .rsp).toNat + 48) 8

end CallMs

/-! ## The linked form -/

/-- Where `call_ms` is linked in `examples/elf-ladder/11-multi-abi` (`build/O2/multi-abi`,
committed as `pinned/multi-abi`). -/
def callMsAddr : Silmaril.X86.Word := 0x4013c0

/-- Where `ms_mix` is linked: the target of `callMsRel` from `callMsAddr + 21`. -/
def msMixAddr : Silmaril.X86.Word := 0x401330

/-- The leave segment's bytes, from the return point at offset 21. -/
def callMsLeaveBytes : List Byte := callMsBytes.drop 21

/-- One fetched step that may retire or return (the step function for code ending in `ret`;
`Ext.stepOpt` stops at a `ret` to the designated exit). -/
def stepAny (exit : Silmaril.X86.Word) (m : MState) : Option MState :=
  match Silmaril.X86.Ext.step exit m with
  | .retired next => some next
  | .returned final => some final
  | _ => none

/-- `call_ms` executed from memory: six fetched retirements to the callee, two fetched steps
from the return point back to the caller. `exit` is the `Ext` machine's designated return
address (it plays no role: the enter code has no `ret`, and `stepAny` accepts both outcomes). -/
def callMsLinked (A B : Convention SystemV.vocab Ffi.State SystemV.CallSite) (p : SystemV.Proto)
    (exit : Silmaril.X86.Word) : Convention.Thunk A B p where
  enter s := {s₁ | ∃ m, Silmaril.Machine.Execution.run (Silmaril.X86.Ext.stepOpt exit) 6 s.machine =
    some m ∧ s₁ = { s with machine := m }}
  leave _ s₂ := {s₃ | ∃ m, Silmaril.Machine.Execution.run (stepAny exit) 2 s₂.machine = some m ∧
    s₃ = { s₂ with machine := m }}

namespace CallMsAt

/-- The caller enters `call_ms` at its linked address, with its bytes loaded there. -/
structure Room (s : Ffi.State) : Prop where
  room : CallMs.Room s
  pc : s.machine.core.rip = callMsAddr
  code : Silmaril.X86.Ext.Loaded s.machine.memory callMsAddr callMsBytes

/-- The callee keeps the caller's return slot, returns to the return point, and leaves the
leave segment's bytes loaded there. -/
structure Guar (s₁ s₂ : Ffi.State) : Prop where
  slot : CallMs.Guar s₁ s₂
  pc : s₂.machine.core.rip = callMsAddr + 21
  code : Silmaril.X86.Ext.Loaded s₂.machine.memory (callMsAddr + 21) callMsLeaveBytes

end CallMsAt

end Silmaril.Machine.Abi.CrossAbi.Gcc
