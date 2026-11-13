module

public import Silmaril.Machine.Abi.CrossAbi.Gcc.Defs
public import Silmaril.Machine.Abi.CrossAbi.Thms
import Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc
import Silmaril.Proofs.Machine.Abi.CrossAbi.GccFetch
/-! # GCC's `call_ms` is a verified System V → `ms_abi` thunk

* `callMs_decode`, `callMs_lengths`: the linked bytes of `call_ms` decode, under
  Silmaril's `Ext` decoder, to `callMsEnter` followed by `callMsLeave`, and every
  instruction is consumed at its canonical length (kernel `decide`).
* `callMs_implements`, `callMs_progress`: under `Ext.exec`, the code implements
  the bridging specification `SysvToMs` and progresses, given the stack room
  `CallMs.Room` and the callee frame guarantee `CallMs.Guar`.
* `callMs_sound`: the composition theorem for the **decoded list**. For every prototype
  with at most four parameters, every strict C contract `c` and every `ms_abi` callee
  relation that satisfies the Microsoft x64 translation of `c` and keeps the caller's return
  slot, the decoded transition code (`run` of `callMsEnter rel`/`callMsLeave`) wrapped around
  the callee satisfies the System V translation of `c` (on caller states with 48 bytes of
  usable stack). This is a relational composition of a decoded instruction list with an
  **abstract** callee relation: `rel` is universally quantified and `Win64.Entry` leaves the
  entry RIP free, so **the call target is not tied to the callee** here.
* `callMs_sound_linked` (round 4): the same composition for the code **fetched from memory**
  (`callMsLinked`: `Ext.stepOpt`/`stepAny` on the loaded bytes) at its linked address
  `callMsAddr` with the linked displacement `callMsRel`, and a callee whose contract and
  guarantee are assumed **only at RIP = `msMixAddr`**, the call target
  (`callMsLinked_lands`). The callee is still a relation on states (not code loaded at
  `msMixAddr`); `CallMsAt.Guar` asks it to return to the return point with the leave bytes
  still loaded. `Ladder.Pinned.multiAbi_callMs` shows `callMsBytes` are the bytes the
  committed rung-11 executable loads at `callMsAddr`. `callMsAt_room_inhabited`: a
  concrete state meets `CallMsAt.Room` (the System V entry obligations are not part of
  that witness).

Former open goals, **proved in round 4**:

* `Task.callMsFetch` (`callMsFetch_holds`): running `callMsEnter callMsRel` with `run`
  agrees with fetching and decoding it from memory (`Ext.stepOpt`, 6 retirements) when the
  26 bytes are loaded executable at RIP.
* `Task.callMsLeaveFetch` (`callMsLeaveFetch_holds`): the same for the leave segment
  (`add $0x28,%rsp; ret`, 2 `stepAny` steps) from the return point.

Open goals (`Task`):

* `Task.msCallsSysvBridge`: GCC's reverse transition `ms_calls_sysv` (push RDI/RSI,
  moves, `sub $8`, call, `add $8`, pop, pop, ret) implements `MsToSysv` under a
  room assumption and a guarantee that the System V callee keeps the two saved
  slots, the return slot **and XMM6–XMM15**. GCC omits the XMM6–15 saves under
  `-mgeneral-regs-only`, so the guarantee is a real extra assumption on the
  callee, not part of the System V contract.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.CrossAbi.Gcc

open Silmaril.Logic.Institution.Bridges
open Silmaril.X86 (Reg Byte MState)
open Silmaril.X86.Ext (Instr)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV (Proto vocab sysv Options)
open Silmaril.Machine.Abi.Win64 (win64 reg)
open Silmaril.Machine.Abi.Convention (Thunk Strict Guarantees)

theorem callMs_decode :
    Silmaril.X86.Ext.decodeAll 40 callMsBytes = some (callMsEnter callMsRel ++ callMsLeave) := by
  decide

theorem callMs_lengths :
    Silmaril.X86.Ext.decodeLengths 40 callMsBytes =
      some ((callMsEnter callMsRel ++ callMsLeave).map Silmaril.X86.Ext.Instr.length) := by
  decide

variable {p : Proto}

theorem callMs_implements (options : Options) (rel : BitVec 32) :
    Implements (callMs (sysv options) win64 p rel) SysvToMs.Enter SysvToMs.Leave
      CallMs.Room CallMs.Guar :=
  Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc.implements options

theorem callMs_progress (options : Options) (rel : BitVec 32) :
    Progress (callMs (sysv options) win64 p rel) CallMs.Room CallMs.Guar :=
  Silmaril.Proofs.Machine.Abi.CrossAbi.Gcc.progress options

/-- **Composition theorem for GCC's System V → `ms_abi` transition.** -/
theorem callMs_sound (options : Options) (rel : BitVec 32) (small : Small p)
    {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))} (strict : Strict c)
    {model : Contracts.Model Ffi.State Ffi.State}
    (callee : Contracts.Sat model (win64.translate p c))
    (keeps : Guarantees win64 p c model CallMs.Guar) :
    Contracts.Sat ((callMs (sysv options) win64 p rel).wrap model)
      (within ((sysv options).translate p c) CallMs.Room) :=
  sysv_of_ms options small (callMs_implements options rel) (callMs_progress options rel)
    strict callee keeps

/-- `run` of the `call_ms` enter segment agrees with fetch/decode/execute from memory when
the 26 bytes are loaded executable at RIP (6 retirements, ending with the `call`).
Round 2: open; **round 4: proved** (`callMsFetch_holds`). -/
def Task.callMsFetch : Prop :=
  ∀ (m : MState) (exit : Silmaril.X86.Word),
    m.core.rip.toNat + 26 ≤ 2 ^ 64 →
    m.memory.fetchBytes m.core.rip.toNat 26 = some callMsBytes →
      Silmaril.Machine.Execution.run (Silmaril.X86.Ext.stepOpt exit) 6 m =
        run (callMsEnter callMsRel) m

theorem callMsFetch_holds : Task.callMsFetch := fun _ exit _ fetched =>
  Silmaril.Proofs.Machine.Abi.CrossAbi.GccFetch.fetch_enter exit fetched

/-- The leave segment (`add $0x28,%rsp; ret`) from the return point: two fetched steps
(the `ret` may retire or return to `exit`) agree with `run callMsLeave`.
**Proved** (`callMsLeaveFetch_holds`). -/
def Task.callMsLeaveFetch : Prop :=
  ∀ (m : MState) (exit : Silmaril.X86.Word),
    m.memory.fetchBytes m.core.rip.toNat 5 = some callMsLeaveBytes →
      Silmaril.Machine.Execution.run (stepAny exit) 2 m = run callMsLeave m

theorem callMsLeaveFetch_holds : Task.callMsLeaveFetch := fun _ exit fetched =>
  Silmaril.Proofs.Machine.Abi.CrossAbi.GccFetch.fetch_leave exit fetched

/-! ## The linked form -/

/-- The fetched code enters the callee at `msMixAddr`. -/
theorem callMsLinked_lands (options : Options) (exit : Silmaril.X86.Word) {s s₁ : Ffi.State}
    (room : CallMsAt.Room s) (entered : s₁ ∈ (callMsLinked (sysv options) win64 p exit).enter s) :
    s₁.machine.core.rip = msMixAddr :=
  Silmaril.Proofs.Machine.Abi.CrossAbi.GccFetch.lands_linked options exit room entered

theorem callMsLinked_implements (options : Options) (exit : Silmaril.X86.Word) :
    Implements (callMsLinked (sysv options) win64 p exit) SysvToMs.Enter SysvToMs.Leave
      CallMsAt.Room CallMsAt.Guar :=
  Silmaril.Proofs.Machine.Abi.CrossAbi.GccFetch.implements_linked options exit

theorem callMsLinked_progress (options : Options) (exit : Silmaril.X86.Word) :
    Progress (callMsLinked (sysv options) win64 p exit) CallMsAt.Room CallMsAt.Guar :=
  Silmaril.Proofs.Machine.Abi.CrossAbi.GccFetch.progress_linked options exit

/-- **Composition theorem for GCC's `call_ms` as linked, run from memory.** On System V
caller states at `callMsAddr` with `callMsBytes` loaded there and 48 bytes of stack
(`CallMsAt.Room`), fetching and executing the code around any callee relation that meets the
Microsoft x64 translation of a strict C contract `c` **when entered at `msMixAddr`** (and
there provides `CallMsAt.Guar`) satisfies the System V translation of `c`. -/
theorem callMs_sound_linked (options : Options) (exit : Silmaril.X86.Word) (small : Small p)
    {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))} (strict : Strict c)
    {model : Contracts.Model Ffi.State Ffi.State}
    (callee : Contracts.Sat model
      (Silmaril.Machine.Abi.within (win64.translate p c) fun s₁ => s₁.machine.core.rip = msMixAddr))
    (keeps : ∀ a s₁, win64.Entry p a s₁ → s₁.machine.core.rip = msMixAddr → c.pre a →
      ∀ s₂ ∈ model s₁, CallMsAt.Guar s₁ s₂) :
    Contracts.Sat ((callMsLinked (sysv options) win64 p exit).wrap model)
      (within ((sysv options).translate p c) CallMsAt.Room) :=
  Silmaril.Proofs.Machine.Abi.CrossAbi.GccFetch.sound_at
    (sysvToMs_simulates options small (callMsLinked_implements options exit)
      (callMsLinked_progress options exit))
    (fun _ _ _ room _ entered => callMsLinked_lands options exit room entered)
    strict callee keeps

/-- `CallMsAt.Room` is not vacuous: a concrete state (`rsp = 0x8ff8`, one RWX region
`[0x8000, 0x402000)` with `callMsBytes` at `callMsAddr`) meets it. This says nothing about
the System V entry obligations or `c.pre`, which `callMs_sound_linked` also assumes. -/
theorem callMsAt_room_inhabited : ∃ s, CallMsAt.Room s :=
  ⟨_, Silmaril.Proofs.Machine.Abi.CrossAbi.GccFetch.room_inhabited⟩

/-- `ms_calls_sysv` as linked: 30 bytes at `0x401380`. -/
def msCallsSysvBytes : List Byte :=
  [0x57, 0x48, 0x89, 0xcf, 0x4c, 0x89, 0xc9, 0x56, 0x48, 0x89, 0xd6, 0x4c, 0x89, 0xc2,
   0x48, 0x83, 0xec, 0x08, 0xe8, 0x09, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x08,
   0x5e, 0x5f, 0xc3]

def msCallsSysvEnter (rel : BitVec 32) : List Instr :=
  [.push .rdi, .mov .q (.reg .rdi) .rcx, .mov .q (.reg .rcx) .r9, .push .rsi,
   .mov .q (.reg .rsi) .rdx, .mov .q (.reg .rdx) .r8, .aluI8 .q .sub (.reg .rsp) 0x08,
   .call rel]

def msCallsSysvLeave : List Instr := [.aluI8 .q .add (.reg .rsp) 0x08, .pop .rsi, .pop .rdi, .ret]

theorem msCallsSysv_decode :
    Silmaril.X86.Ext.decodeAll 40 msCallsSysvBytes =
      some (msCallsSysvEnter 0x00000009 ++ msCallsSysvLeave) := by
  decide

/-- GCC's reverse transition as a thunk. -/
def msCallsSysv (A B : Convention SystemV.vocab Ffi.State SystemV.CallSite) (p : Proto)
    (rel : BitVec 32) : Thunk A B p where
  enter := onMachine (msCallsSysvEnter rel)
  leave _ := onMachine msCallsSysvLeave

/-- Stack room for the reverse transition: three 8-byte pushes below RSP. -/
structure MsCallsSysv.Room (s : Ffi.State) : Prop where
  low : 32 ≤ (reg s .rsp).toNat
  write : s.machine.memory.Permitted .write ((reg s .rsp).toNat - 32) 32
  read : s.machine.memory.Permitted .read ((reg s .rsp).toNat - 32) 32

/-- The System V callee keeps the saved RSI/RDI slots, the return slot and the
low halves of XMM6–XMM15 (which GCC does not save under `-mgeneral-regs-only`). -/
structure MsCallsSysv.Guar (s₁ s₂ : Ffi.State) : Prop where
  slots : s₂.machine.memory.readBytes ((reg s₁ .rsp).toNat + 16) 24 =
    s₁.machine.memory.readBytes ((reg s₁ .rsp).toNat + 16) 24
  vectors : ∀ index, 6 ≤ index → index < 16 →
    (s₂.vectors index).setWidth 128 = (s₁.vectors index).setWidth 128

/-- Open goal: GCC's `ms_calls_sysv` transition implements `MsToSysv` and
progresses under these assumptions. With `ms_of_sysv`, it would give the
composition theorem for the reverse direction. -/
def Task.msCallsSysvBridge : Prop :=
  ∀ (options : Options) (p : Proto) (rel : BitVec 32),
    Implements (msCallsSysv win64 (sysv options) p rel) MsToSysv.Enter MsToSysv.Leave
      MsCallsSysv.Room MsCallsSysv.Guar ∧
    Progress (msCallsSysv win64 (sysv options) p rel) MsCallsSysv.Room MsCallsSysv.Guar

/-- The reverse composition theorem, conditional on `Task.msCallsSysvBridge`. -/
theorem msCallsSysv_sound (task : Task.msCallsSysvBridge) (options : Options) (rel : BitVec 32)
    (small : Small p)
    {c : Contracts.Contract (vocab.Args p) (Option (vocab.Ret p))} (strict : Strict c)
    {model : Contracts.Model Ffi.State Ffi.State}
    (callee : Contracts.Sat model ((sysv options).translate p c))
    (keeps : Guarantees (sysv options) p c model MsCallsSysv.Guar) :
    Contracts.Sat ((msCallsSysv win64 (sysv options) p rel).wrap model)
      (within (win64.translate p c) MsCallsSysv.Room) :=
  ms_of_sysv options small (task options p rel).1 (task options p rel).2 strict callee keeps

end Silmaril.Machine.Abi.CrossAbi.Gcc
