module

public import Silmaril.X86.SegVC
public import Silmaril.X86.Ext8.Basic

/-!
# The open x86 machine over `Ext8`

`Silmaril.X86.Ext.step exit` and `Silmaril.X86.Ext8.step exit` single out the `ret` that pops
the designated return address `exit`: that step is reported as `returned` and is not a
retirement, so a run of `stepOpt exit` stops there. A caller and its callee use different
designated exits, so their runs disagree about which `ret` ends a run. The **open machine**
has no designated exit: every `ret` is an ordinary pop and jump. That a function has
returned is a property of a state (`Returned`: `rip` is the return address and `rsp` is the
entry value plus eight), not of the step.

* `step`: one step of `Ext8` (the `X86.Ext` forms and the 8-bit forms), whatever
  instruction retires, including every `ret`;
* `decode`: the listing decoder of `Ext8`, restricted to slices where the machine's fetch
  reaches the decoded form;
* `Returned`: the returned predicate.

The `SegVC.Isa` instance `Open.isa` and the agreement with `Ext8.step exit` are in
`Open/Thms.lean`. `Open9` (`Silmaril.X86.Open9`) extends this machine with the `Ext9` forms
and is the default machine for new contracts (`docs/x86.md`). This is a model of the
handwritten `X86.Ext`/`Ext8` semantics, not of hardware.
-/

@[expose] public section

namespace Silmaril.X86.Open

open Silmaril.X86 (State MState Word Byte maxInstrLength)
open Silmaril.Process (Memory)

/-- A successful execution as a machine state. -/
def ofResult : Ext.Result → Option MState
  | .ok core memory => some ⟨core, memory⟩
  | _ => none

/-- **One step of the open machine.** Fetch as `Ext8` does (an `X86.Ext` form first, then a
new 8-bit form), execute, and retire. A `ret` is an ordinary step: it pops the return
address into `rip`, whatever that address is. -/
def step (m : MState) : Option MState :=
  match Ext8.fetch m.memory m.core.rip.toNat with
  | .inl (.decoded i _) => ofResult (Ext.exec i m.core m.memory)
  | .inr (i, n) => ofResult (Ext8.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n))
  | .inl _ => none

/-- The listing decoder: `Ext8.decode`, accepting a new form only where the machine's fetch
reaches it (the `Ext` length decoder finishes inside the slice, and the form is 2 to 15 bytes
long). Checked on each listing by `decide`. -/
def decode (bytes : List Byte) : Option (Ext8.Instr × Nat) :=
  match Ext8.decode bytes with
  | some (.base i, n) => some (.base i, n)
  | some (.new i, n) =>
    match Ext.parseRaw bytes with
    | .eof => none
    | _ => if 2 ≤ n ∧ n ≤ maxInstrLength then some (.new i, n) else none
  | none => none

/-- A function entered with stack pointer `sp0` and return address `ret` has returned. -/
def Returned (sp0 ret : Word) (m : MState) : Prop :=
  m.core.rip = ret ∧ m.core.read .rsp = sp0 + 8#64

end Silmaril.X86.Open
