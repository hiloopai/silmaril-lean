module

public import Silmaril.X86.SegVC
public import Silmaril.X86.Ext8.Basic

/-!
# The open x86 machine

`Silmaril.X86.Ext.step exit` and `Silmaril.X86.Ext8.step exit` single out the `ret` that pops
the designated return address `exit`: that step is reported as `returned` and is not a
retirement, so a run of `stepOpt exit` stops there. A caller and its callee use different
designated exits, so their runs disagree about which `ret` ends a run (the "`exit`-sentinel
problem"). The **open machine** has no designated exit: every `ret` is an ordinary pop and
jump. That a function has returned is a property of a state (`Returned`: `rip` is the
return address and `rsp` is the entry value plus eight), not of the step.

* `step`: one step of the `Ext8` variant (the `X86.Ext` forms and the 8-bit forms), whatever
  instruction retires, including every `ret`;
* `decode`: the listing decoder of `Ext8` restricted to slices where the machine's fetch
  reaches the decoded form. It is a copy of `decode8` of public silmaril-lean
  (`Silmaril/Apps/Sha256sum/X86Sys/SegVC8.lean`, rev `35a6f60`) without its `syscall` clause,
  which only the Linux process machine needs;
* `Returned`: the returned predicate.

The `SegVC.Isa` instance (`Open.isa`) and the transport lemmas are in `Open/Thms.lean`.
This is a model of the handwritten `X86.Ext`/`Ext8` semantics, not of hardware.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Open

open Silmaril.X86 (State MState Word Byte maxInstrLength)
open Silmaril.Process (Memory)

/-- A successful execution as a machine state. -/
def ofResult : Silmaril.X86.Ext.Result → Option MState
  | .ok core memory => some ⟨core, memory⟩
  | _ => none

/-- **One step of the open machine.** Fetch as `Ext8` does (an `X86.Ext` form first, then a
new 8-bit form), execute, and retire. A `ret` is an ordinary step: it pops the return
address into `rip`, whatever that address is. -/
def step (m : MState) : Option MState :=
  match Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat with
  | .inl (.decoded i _) => ofResult (Silmaril.X86.Ext.exec i m.core m.memory)
  | .inr (i, n) =>
    ofResult (Silmaril.X86.Ext8.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n))
  | .inl _ => none

/-- The listing decoder: `Ext8.decode`, accepting a new form only where the machine's fetch
reaches it (the length decoder finishes inside the slice, and the form is 2 to 15 bytes
long). Checked on each listing by `decide`. -/
def decode (bytes : List Byte) : Option (Silmaril.X86.Ext8.Instr × Nat) :=
  match Silmaril.X86.Ext8.decode bytes with
  | some (.base i, n) => some (.base i, n)
  | some (.new i, n) =>
    match Silmaril.X86.Ext.parseRaw bytes with
    | .eof => none
    | _ => if 2 ≤ n ∧ n ≤ maxInstrLength then some (.new i, n) else none
  | none => none

/-- The return address at the top of the stack of a core and memory (`0` if unreadable). -/
def retOf (core : State) (memory : Memory) : Word :=
  ((memory.readBytes (core.read .rsp).toNat 8).bind Silmaril.X86.wordOfBytes?).getD 0

/-- A function entered with stack pointer `sp0` and return address `ret` has returned. -/
def Returned (sp0 ret : Word) (m : MState) : Prop :=
  m.core.rip = ret ∧ m.core.read .rsp = sp0 + 8#64

end Silmaril.Machine.X86.Open
