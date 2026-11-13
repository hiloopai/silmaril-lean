module

public import Silmaril.Machine.X86.Open.Defs
public import Silmaril.Machine.X86.Ext9.Defs

/-!
# The open x86 machine over `Ext9`

`Open.step` (the open machine: every `ret` is an ordinary pop and jump) over the `Ext9`
variant: on bytes that `Ext8` cannot decode (`Ext8.fetch` is `undecodable`), fetch and
execute a new `Ext9` form; otherwise, exactly `Open.step`. So every open step is an `Open9`
step (`step_of_open` in `Open9/Thms.lean`), and every `FnContract Open.isa` is a
`FnContract Open9.isa` (`FnContract.toOpen9`).

* `step`: the machine;
* `decode`: the listing decoder. `Open.decode` first; a new form only where the machine's
  fetch reaches it: `Ext.decode` rejects the slice, the length decoder of `Ext` and the
  parser of `Ext8`'s new forms finish inside it (`rawNotEof`, `newBad`: their rejection
  persists whatever bytes follow), and the form is 1 to 15 bytes long. Checked on each
  listing by `decide`.

The `SegVC.Isa` instance `Open9.isa` and its law are in `Open9/Thms.lean`. This is a model of
the handwritten `X86.Ext`/`Ext8`/`Ext9` semantics, not of hardware.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Open9

open Silmaril.X86 (State MState Word Byte maxInstrLength fetchWindow)
open Silmaril.Process (Memory)

/-- **One step of the open machine over `Ext9`.** -/
def step (m : MState) : Option MState :=
  match Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat with
  | .inl .undecodable =>
    match Ext9.fetchNew m.memory m.core.rip.toNat with
    | some (some (i, n)) =>
      Open.ofResult (Ext9.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n))
    | _ => none
  | _ => Open.step m

/-- The parser of `Ext8`'s new forms rejects (and so rejects every extension). -/
def newBad (bytes : List Byte) : Bool :=
  match Silmaril.X86.Ext8.pNew bytes with
  | .bad => true
  | _ => false

/-- The length decoder of `Ext` does not run out of input. -/
def rawNotEof (bytes : List Byte) : Bool :=
  match Silmaril.X86.Ext.parseRaw bytes with
  | .eof => false
  | _ => true

/-- The listing decoder. -/
def decode (bytes : List Byte) : Option (Ext9.Instr × Nat) :=
  match Open.decode bytes with
  | some (i, n) => some (.ext8 i, n)
  | none =>
    match Ext9.decodeNew bytes with
    | some (i, n) =>
      if Silmaril.X86.Ext.decode bytes = none ∧ newBad bytes = true ∧ rawNotEof bytes = true ∧
          0 < n ∧ n ≤ maxInstrLength then some (.new i, n)
      else none
    | none => none

end Silmaril.Machine.X86.Open9
