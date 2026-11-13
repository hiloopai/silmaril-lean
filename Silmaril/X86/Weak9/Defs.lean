module

public import Silmaril.X86.Atomic9.Defs
public import Silmaril.X86.Str9.Defs
public import Silmaril.X86.MemEvent.Defs

/-!
# `Weak9`: `Atomic9` with the weakly ordered stores (`movnti`, string stores)

The XL memory
model (`Silmaril.X86.MemoryModel.Xl`) orders non-temporal stores and the stores of string
instructions more weakly than ordinary write-back stores, but no decoder had them: `Atomic9`
has neither `movnti` nor any string form, and `Str9` (`movsb`, `rep movsq`, `rep stosq`) is a
sibling machine of `Atomic9`, not combined with it. `Weak9` is `Atomic9` extended by

| Form | Bytes | `Weak9` |
| --- | --- | --- |
| `movnti m32, r32` / `movnti m64, r64` | `REX? 0F C3 /r` (memory operand) | `weak (.movnti ..)` |
| `rep stosb` | `F3 AA` | `weak .repStosb` |
| `movsb`, `rep movsq`, `rep stosq` | `Str9`'s encodings | `str ..` (Str9's semantics) |

`step` is `Atomic9.step`'s fetch chain (`Ext8`, then `Ext9`'s new forms, then the atomic forms)
followed, on bytes all of them reject, by the forms above (`movnti`/`rep stosb` first, then
`Str9`'s). Listings use `decode`, which accepts a new form only where the machine's fetch
reaches it (each rejection is a parser `.bad`, which no following byte can turn into a form).

## Semantics, and the documented choices

* `movnti` is, sequentially, exactly `mov m, r`: a little-endian store of the source register
  (SDM Vol. 2, MOVNTI). The non-temporal hint has no sequential effect; it matters only to a
  memory model, which reads it from the flavour the litmus extractor attaches.
* `rep stosb` follows `Str9`'s **one element per step** discipline: with `rcx = 0` it only
  advances RIP; otherwise it stores `al` at `rdi`, adds one to `rdi`, subtracts one from `rcx`,
  and leaves RIP on the instruction unless the new `rcx` is `0`. DF is assumed clear (System V).
  A store that is not permitted faults (`dataFault`) before any register changes.
* Only these exact encodings: no segment override, no `66`/`F2` prefix on `movnti`, no REX on
  `rep stosb`, and the register form of `movnti` (`#UD`) is rejected.

This is a handwritten model of the SDM, like `Str9` and `Atomic9`; it is not differentially
tested in this module (the litmus hardware runs executed these bytes, which is evidence
about orderings, not about this model).
-/

@[expose] public section

namespace Silmaril.X86.Weak9

open Silmaril.X86 (State MState Word Byte Reg maxInstrLength fetchWindow)
open Silmaril.X86.Ext (Mem Sz Result retire loadN storeN Rex Opc Pfx ModrmPart ByteParser pHead)
open Silmaril.Process (Memory)
open MemEvent (Event)

/-! ## Instructions -/

/-- The weakly ordered forms that are not `Str9`'s. -/
inductive Weak where
  /-- `movnti m, r` (`REX? 0F C3 /r`). -/
  | movnti (sz : Sz) (dst : Ext.Mem) (src : Reg)
  /-- `rep stosb` (`F3 AA`). -/
  | repStosb
  deriving DecidableEq, Repr

/-- The instructions of the machine. -/
inductive Instr where
  | atomic (i : Atomic9.Instr)
  | weak (i : Weak)
  | str (i : Str9.Str)
  deriving DecidableEq, Repr

/-! ## Decoding -/

/-- The parser of the forms of `Weak`. -/
def pWeak : ByteParser Weak :=
  ByteParser.bind pHead fun h =>
    if h.1 = true then ByteParser.fail
    else
      match h.2.1 with
      | .none =>
        if h.2.2.2 = .two 0xC3#8 then
          ByteParser.bind Silmaril.X86.Ext8.pM fun mp =>
            ByteParser.map (fun m => .movnti (Sz.ofW (h.2.2.1.getD Rex.zero).w) m
              (Ext9.regOf h.2.2.1 mp)) (Atomic9.memP h.2.2.1 mp)
        else ByteParser.fail
      | .rep =>
        if h.2.2.1 = none ∧ h.2.2.2 = .one 0xAA#8 then ByteParser.pure .repStosb
        else ByteParser.fail
      | _ => ByteParser.fail

/-- Decode a form of `Weak`; the form and the number of bytes consumed. -/
def decodeWeak (bytes : List Byte) : Option (Weak × Nat) :=
  match pWeak bytes with
  | .ok i rest => some (i, bytes.length - rest.length)
  | _ => none

/-- The atomic-form parser rejects (so rejects every extension). -/
def atomicBad (bytes : List Byte) : Bool :=
  match Atomic9.pNew bytes with
  | .bad => true
  | _ => false

/-- The `Weak` parser rejects (so rejects every extension). -/
def weakBad (bytes : List Byte) : Bool :=
  match pWeak bytes with
  | .bad => true
  | _ => false

/-- The listing decoder of a `Weak` form: everything `Atomic9.step` tries before it rejects the
slice (as in `Atomic9.decodeL`, plus the atomic parser), and `decodeWeak` reads a form of 1 to
15 bytes. -/
def decodeLW (bytes : List Byte) : Option (Weak × Nat) :=
  match decodeWeak bytes with
  | some (i, n) =>
    if Silmaril.X86.Ext.decode bytes = none ∧ Open9.newBad bytes = true ∧
        Open9.rawNotEof bytes = true ∧ Sse9.ext9Bad bytes = true ∧ atomicBad bytes = true ∧
        0 < n ∧ n ≤ maxInstrLength then
      some (i, n)
    else none
  | none => none

/-- The listing decoder of a `Str9` form inside `Weak9`: `Str9`'s listing decoder, and the
atomic and `Weak` parsers reject the slice. -/
def decodeLS (bytes : List Byte) : Option (Str9.Str × Nat) :=
  match Str9.decodeL bytes with
  | some (i, n) => if atomicBad bytes = true ∧ weakBad bytes = true then some (i, n) else none
  | none => none

/-- **The listing decoder of the machine**: `Atomic9.decode`, then a `Weak` form, then a
`Str9` form. -/
def decode (bytes : List Byte) : Option (Instr × Nat) :=
  match Atomic9.decode bytes with
  | some (i, n) => some (.atomic i, n)
  | none =>
    match decodeLW bytes with
    | some (i, n) => some (.weak i, n)
    | none => (decodeLS bytes).map fun (i, n) => (.str i, n)

/-! ## Semantics -/

/-- One element of `rep stosb` (`rcx ≠ 0`): store `al` at `rdi`, advance `rdi`, decrease
`rcx`, and leave RIP on the instruction unless `rcx` reaches `0`. -/
def stosbElem (s : State) (memory : Memory) (next : Word) : Result :=
  match storeN memory (s.read .rdi) 1 (s.read .rax) with
  | none => .dataFault
  | some memory' =>
    let c := s.read .rcx - 1
    let t := (s.write .rdi (s.read .rdi + 1)).write .rcx c
    .ok { t with rip := if c = 0 then next else s.rip } memory'

/-- **Execute a `Weak` form**, given the address of the next instruction. -/
def execWeak (i : Weak) (s : State) (memory : Memory) (next : Word) : Result :=
  match i with
  | .movnti sz dst src =>
    retire next ((storeN memory (dst.addr s next) sz.bytes ((sz.read s src).setWidth 64)).map
      fun m' => (s, m'))
  | .repStosb =>
    if s.read .rcx = 0 then .ok { s with rip := next } memory else stosbElem s memory next

/-- Execute an instruction of the machine with its consumed byte length. -/
def exec (i : Instr) (s : State) (memory : Memory) (length : Nat) : Result :=
  match i with
  | .atomic i => Atomic9.exec i s memory length
  | .weak i => execWeak i s memory (s.rip + BitVec.ofNat 64 length)
  | .str i => Str9.execStr i s memory (s.rip + BitVec.ofNat 64 length)

/-! ## Fetch and step -/

/-- Fetch a `Weak` form: `none` if not decodable as one; `some none` if not fetchable. -/
def fetchWeak (memory : Memory) (address : Nat) : Option (Option (Weak × Nat)) :=
  (decodeWeak (fetchWindow memory maxInstrLength address)).map fun (i, n) =>
    if memory.Permitted .execute address n then some (i, n) else none

/-- **One step**: `Atomic9`'s fetch chain, then a `Weak` form, then a `Str9` form. -/
def step (m : MState) : Option MState :=
  match Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat with
  | .inl .undecodable =>
    match Ext9.fetchNew m.memory m.core.rip.toNat with
    | some (some (i, n)) =>
      Open.ofResult (Ext9.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n))
    | some none => none
    | none =>
      match Atomic9.fetchNew m.memory m.core.rip.toNat with
      | some (some (i, n)) =>
        Open.ofResult (Atomic9.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n))
      | some none => none
      | none =>
        match fetchWeak m.memory m.core.rip.toNat with
        | some (some (i, n)) =>
          Open.ofResult (execWeak i m.core m.memory (m.core.rip + BitVec.ofNat 64 n))
        | some none => none
        | none =>
          match Str9.fetchStr m.memory m.core.rip.toNat with
          | some (some (i, n)) =>
            Open.ofResult (Str9.execStr i m.core m.memory (m.core.rip + BitVec.ofNat 64 n))
          | _ => none
  | _ => Open.step m

/-! ## Memory events

The access list of one step (`MemEvent.Event`), for the new forms: one event per element of
a `rep` form (the element the step performs; none when `rcx = 0`). Which stores are weakly
ordered is not an event attribute; the litmus extractor attaches it as a flavour. -/

/-- The accesses of one step of a string form. -/
def strAccesses (i : Str9.Str) (s : State) : List Event :=
  match i with
  | .movsb => [⟨.load, (s.read .rsi).toNat, 1, false⟩, ⟨.store, (s.read .rdi).toNat, 1, false⟩]
  | .repMovsq =>
    if s.read .rcx = 0 then []
    else [⟨.load, (s.read .rsi).toNat, 8, false⟩, ⟨.store, (s.read .rdi).toNat, 8, false⟩]
  | .repStosq => if s.read .rcx = 0 then [] else [⟨.store, (s.read .rdi).toNat, 8, false⟩]

/-- The accesses of one step of a `Weak` form. -/
def weakAccesses (i : Weak) (s : State) (next : Word) : List Event :=
  match i with
  | .movnti sz dst _ => [⟨.store, (dst.addr s next).toNat, sz.bytes, false⟩]
  | .repStosb => if s.read .rcx = 0 then [] else [⟨.store, (s.read .rdi).toNat, 1, false⟩]

/-- The accesses of one step of the machine. -/
def accesses (i : Instr) (s : State) (len : Nat) : List Event :=
  match i with
  | .atomic i => MemEvent.atomic9Accesses i s len
  | .weak i => weakAccesses i s (s.rip + BitVec.ofNat 64 len)
  | .str i => strAccesses i s

end Silmaril.X86.Weak9
