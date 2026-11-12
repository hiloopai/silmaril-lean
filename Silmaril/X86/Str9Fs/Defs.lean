module

public import Silmaril.X86.Str9.Defs
public import Silmaril.X86.Atomic9.Defs

/-!
# `Str9Fs`: `Str9` with FS-relative memory operands and sequential atomics

silmaril's `Str9` is the machine of the simple executables and of much of glibc, but two
families of instructions stop it on glibc code (they are the first undecoded instruction of
many glibc functions):

* **FS-relative operands with a base register**, `mov %eax, %fs:(%rdx)` (`64 89 02`): the
  thread-local `errno` write after every failing system call, and other TLS accesses through
  a GOT-loaded offset. `Ext` reads the FS override only on base-less operands (the
  stack-protector canary `%fs:0x28`); the `Ext9` new forms refuse it;
* **`lock`-prefixed read-modify-write**, `xchg`, `xadd`, `cmpxchg` (glibc's locks): silmaril's
  `Atomic9` defines them (decoder and sequential semantics) but has no machine over `Str9`.

`Str9Fs` adds both as a **sibling extension at the end of `Str9`'s fetch chain**: `step` is
`Str9.step` on every state where `Ext8`, `Ext9` or a string form is fetched (so every `Str9`
step is a step, `Thms.extendsStr9`), and only on bytes all of them reject does it try an
atomic form (`Atomic9.decodeNew`, unchanged) and then an FS form (`decodeFs`).

**FS forms.** After a `64` prefix (no other legacy prefix, an optional REX), the opcodes
`89`, `8B`, `85`, `REX.W 63` (`movsxd`), `C7 /0`, `F7 /0` (`test imm32`, an `Ext9` form),
`80 /7` (`cmpb imm8`), `81 /d`, `83 /d`, `01 09 21 29 31 39 /r`, `03 0B 23 2B 33 3B /r`,
`FF /0`, `FF /1`, with a **memory** operand whose base is a register or absent (never RIP).
Each is read as the `Ext9` instruction `i` it is without the prefix, with its memory operand
replaced by `fs:[0]` (`Mem.fsAt 0`), together with the operand `m` itself. Its meaning
(`execFs`) is `Ext9.exec i` on the core whose `fsBase` is the linear address
`fsBase + m.addr` (the SDM's FS segment base plus effective address), with `fsBase` put back
afterwards. This is exact for these forms: they read `fsBase` only through the `fs:` operand
and never write it, and the encoded length is passed to `Ext9.exec`, so `rip` moves past the
real bytes. Byte stores, 16-bit forms, RIP-relative `fs:` and `lock` together with `fs` are
not read (glibc 2.39 does not use them).

**Atomics** are exactly `Atomic9`'s, sequentially (see its documentation): `lock op m`,
`xadd`, `cmpxchg` (a failing compare writes the old value back), `xchg`, `bts`, fences and
`pause`.

The semantics is a handwritten model of the SDM; it is not proved to match hardware.
-/

@[expose] public section

namespace Silmaril.X86.Str9Fs

open Silmaril.X86 (Reg Word State Byte MState AluOp fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Mem RM Sz Result Rex Opc Pfx ModrmPart ByteParser pHead pImm32)
open Silmaril.X86.Ext8 (pM optP aluOfDigit)
open Silmaril.Process (Memory)

/-! ## Instructions -/

/-- The new forms: an `Atomic9` form, or an `Ext9` instruction whose memory operand `fs:[0]`
stands for the FS-relative operand `fs:m`. -/
inductive New where
  | atomic (i : Silmaril.X86.Atomic9.New)
  | fs (i : Silmaril.X86.Ext9.Instr) (m : Ext.Mem)
  deriving DecidableEq, Repr

/-- The instructions of the machine. -/
inductive Instr where
  | str9 (i : Silmaril.X86.Str9.Instr)
  | new (i : New)
  deriving DecidableEq, Repr

/-! ## Decoding the FS forms -/

/-- The placeholder operand `fs:[0]`. -/
def fs0 : Ext.Mem := Ext.Mem.fsAt 0

/-- A memory operand with a register base or none (not RIP-relative), or reject. -/
def fsMemP (rex : Option Rex) (mp : ModrmPart) : ByteParser Ext.Mem :=
  match Silmaril.X86.Ext9.rmOf rex mp with
  | .mem m => if m.base = .rip then ByteParser.fail else ByteParser.pure m
  | .reg _ => ByteParser.fail

/-- An `Ext` instruction as an `Ext9` instruction. -/
def ext (i : Silmaril.X86.Ext.Instr) : Silmaril.X86.Ext9.Instr := .ext8 (.base i)

/-- The body of an FS form after REX and opcode. -/
def pFsBody (rex : Option Rex) : Opc → ByteParser New
  | .one b =>
    let sz := Sz.ofW (rex.getD Rex.zero).w
    let lo := b.toNat % 8
    let digit : BitVec 3 := BitVec.ofNat 3 (b.toNat / 8)
    ByteParser.bind pM fun mp =>
      let r := Silmaril.X86.Ext9.regOf rex mp
      ByteParser.bind (fsMemP rex mp) fun m =>
        if b = 0x89#8 then ByteParser.pure (.fs (ext (.mov sz (.mem fs0) r)) m)
        else if b = 0x8B#8 then ByteParser.pure (.fs (ext (.load sz r fs0)) m)
        else if b = 0x85#8 then ByteParser.pure (.fs (ext (.test sz (.mem fs0) r)) m)
        else if b = 0x63#8 ∧ (rex.getD Rex.zero).w = true then
          ByteParser.pure (.fs (ext (.movsxd r (.mem fs0))) m)
        else if b = 0xC7#8 ∧ mp.1.reg = 0#3 then
          ByteParser.map (fun v => .fs (ext (.movI sz (.mem fs0) v)) m) pImm32
        else if b = 0xF7#8 ∧ mp.1.reg = 0#3 then
          ByteParser.map (fun v => .fs (.new (.testI sz (.mem fs0) v)) m) pImm32
        else if b = 0x80#8 ∧ mp.1.reg = 7#3 then
          ByteParser.map (fun v => .fs (ext (.cmpI8 (.mem fs0) v)) m) ByteParser.byte
        else if b = 0x81#8 then
          ByteParser.bind (optP (aluOfDigit mp.1.reg)) fun op =>
            ByteParser.map (fun v => .fs (ext (.aluI sz op (.mem fs0) v)) m) pImm32
        else if b = 0x83#8 then
          ByteParser.bind (optP (aluOfDigit mp.1.reg)) fun op =>
            ByteParser.map (fun v => .fs (ext (.aluI8 sz op (.mem fs0) v)) m) ByteParser.byte
        else if b = 0xFF#8 ∧ (mp.1.reg = 0#3 ∨ mp.1.reg = 1#3) then
          ByteParser.pure (.fs (ext (.incdec sz (mp.1.reg = 1#3) (.mem fs0))) m)
        else if b.toNat < 0x40 ∧ lo = 1 then
          ByteParser.map (fun op => .fs (ext (.alu sz op (.mem fs0) r)) m) (optP (aluOfDigit digit))
        else if b.toNat < 0x40 ∧ lo = 3 then
          ByteParser.map (fun op => .fs (ext (.aluR sz op r (.mem fs0))) m) (optP (aluOfDigit digit))
        else ByteParser.fail
  | .two _ => ByteParser.fail

/-- The parser of an FS form: `pHead` read a `64`, no legacy prefix. -/
def pFs : ByteParser New :=
  ByteParser.bind pHead fun h =>
    if h.1 = true ∧ h.2.1 = .none then pFsBody h.2.2.1 h.2.2.2 else ByteParser.fail

/-- Decode a new form: an atomic form, else an FS form. -/
def decodeNew (bytes : List Byte) : Option (New × Nat) :=
  match Silmaril.X86.Atomic9.decodeNew bytes with
  | some (i, n) => some (.atomic i, n)
  | none =>
    match pFs bytes with
    | .ok i rest => some (i, bytes.length - rest.length)
    | _ => none

/-- The string-form decoder of `Str9` cannot read anything that starts with these bytes. -/
def strBad : List Byte → Bool
  | [] => false
  | [b] => b != 0xA4#8 && b != 0xF3#8
  | [b, c] => b != 0xA4#8 && !(b == 0xF3#8 && c == 0x48#8)
  | b :: c :: d :: _ => b != 0xA4#8 && !(b == 0xF3#8 && c == 0x48#8 && (d == 0xA5#8 || d == 0xAB#8))

/-- The listing decoder of a new form: every decoder of `Str9` rejects the slice in a way
that no following byte can change (`Ext` rejects it, the `Ext8`/`Ext9` new-form parsers
fail, the `Ext` length decoder does not run out, no string form starts here), and
`decodeNew` reads a form of 1 to 15 bytes. Checked on each listing by `decide`. -/
def decodeL (bytes : List Byte) : Option (New × Nat) :=
  match decodeNew bytes with
  | some (i, n) =>
    if Silmaril.X86.Ext.decode bytes = none ∧ Silmaril.X86.Open9.newBad bytes = true ∧
        Silmaril.X86.Open9.rawNotEof bytes = true ∧ Silmaril.X86.Str9.ext9Bad bytes = true ∧
        strBad bytes = true ∧ 0 < n ∧ n ≤ maxInstrLength then
      some (i, n)
    else none
  | none => none

/-- The listing decoder of the machine: `Str9.decode` first, then a new form. -/
def decode (bytes : List Byte) : Option (Instr × Nat) :=
  match Silmaril.X86.Str9.decode bytes with
  | some (i, n) => some (.str9 i, n)
  | none => (decodeL bytes).map fun (i, n) => (.new i, n)

/-! ## Semantics -/

/-- **An FS form**: `Ext9.exec i` with `fsBase` set to the linear address `fsBase + m.addr`
(so the placeholder `fs:[0]` addresses it), then `fsBase` restored. -/
def execFs (i : Silmaril.X86.Ext9.Instr) (m : Ext.Mem) (s : State) (memory : Memory)
    (length : Nat) : Result :=
  let next := s.rip + BitVec.ofNat 64 length
  match Silmaril.X86.Ext9.exec i { s with fsBase := s.fsBase + m.addr s next } memory length with
  | .ok c memory' => .ok { c with fsBase := s.fsBase } memory'
  | r => r

/-- Execute a new form with its encoded length. -/
def execNew (i : New) (s : State) (memory : Memory) (length : Nat) : Result :=
  match i with
  | .atomic i => Silmaril.X86.Atomic9.execNew i s memory (s.rip + BitVec.ofNat 64 length)
  | .fs i m => execFs i m s memory length

/-- The executor of the machine (the `SegVC` shape: the encoded length). -/
def exec (i : Instr) (s : State) (memory : Memory) (length : Nat) : Result :=
  match i with
  | .str9 i => Silmaril.X86.Str9.exec i s memory length
  | .new i => execNew i s memory length

/-! ## Fetch and step -/

/-- Fetch a new form: `decodeNew` reads the fetch window, and its bytes are executable. -/
def fetchNew (memory : Memory) (address : Nat) : Option (Option (New × Nat)) :=
  (decodeNew (fetchWindow memory maxInstrLength address)).map fun (i, n) =>
    if memory.Permitted .execute address n then some (i, n) else none

/-- **One step**: `Str9.step`, and on bytes that `Ext8`, `Ext9` and the string forms all
reject, a new form. -/
def step (m : MState) : Option MState :=
  match Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat with
  | .inl .undecodable =>
    match Silmaril.X86.Ext9.fetchNew m.memory m.core.rip.toNat with
    | some (some (i, n)) =>
      Silmaril.X86.Open.ofResult
        (Silmaril.X86.Ext9.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n))
    | some none => none
    | none =>
      match Silmaril.X86.Str9.fetchStr m.memory m.core.rip.toNat with
      | some (some (i, n)) =>
        Silmaril.X86.Open.ofResult
          (Silmaril.X86.Str9.execStr i m.core m.memory (m.core.rip + BitVec.ofNat 64 n))
      | some none => none
      | none =>
        match fetchNew m.memory m.core.rip.toNat with
        | some (some (i, n)) => Silmaril.X86.Open.ofResult (execNew i m.core m.memory n)
        | _ => none
  | _ => Silmaril.X86.Open.step m

end Silmaril.X86.Str9Fs
