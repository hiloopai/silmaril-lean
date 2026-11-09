module

public import Silmaril.X86.Open9.Defs
public import Silmaril.X86.Float.Instr

/-!
# `Sse9`: the open `Ext9` machine with XMM registers and an SSE data-movement subset

A census of the lifter's rejections found SSE moves the largest rejected class
on SQLite and the system binaries, and they gate whole functions. `Ext9`/`Open9` have no
vector state, and `Silmaril.X86.MState` cannot be extended, so the XMM file is added **beside**
the open machine:

* `XState` is an `Open9` state (`m : MState`) and sixteen 128-bit XMM registers. MXCSR, the
  upper halves of YMM/ZMM, x87 and MMX are not modelled (no instruction here reads or writes
  them; the 128-bit legacy SSE forms leave YMM/ZMM bits 255:128 unchanged, SDM Vol. 2).
* `step` is `Open9.step` on `m` with the XMM file unchanged, and on bytes that `Ext8` and
  `Ext9` both reject, the SSE forms below. This is a **conservative extension**
  (`Thms.lean`): every `Open9` step is a step with the XMM file as a frame
  (`step_of_open9`), every step is such a step or an SSE step (`step_cases`), and so every
  `Open9` run lifts (`reaches_of_open9`). No integer behaviour changes.
* `isa : SegVC.Isa XState` has the `Ext9` instructions (its law is `Open9`'s); the SSE forms
  have their own listing law (`step_of_listed_sse`).

## The SSE subset (Intel SDM Vol. 2; legacy SSE/SSE2 encodings, no VEX)

| Form | Bytes | `Instr` |
| --- | --- | --- |
| `movups xmm, xmm/m128` / `movups xmm/m128, xmm` | `0F 10 /r`, `0F 11 /r` | `load .ups`, `store .ups` |
| `movaps` (load / store) | `0F 28 /r`, `0F 29 /r` | `load .aps`, `store .aps` |
| `movdqu` (load / store) | `F3 0F 6F /r`, `F3 0F 7F /r` | `load .dqu`, `store .dqu` |
| `movdqa` (load / store) | `66 0F 6F /r`, `66 0F 7F /r` | `load .dqa`, `store .dqa` |
| `movd xmm, r/m32`, `movq xmm, r/m64` | `66 REX.W? 0F 6E /r` | `movToX` |
| `movd r/m32, xmm`, `movq r/m64, xmm` | `66 REX.W? 0F 7E /r` | `movFromX` |
| `movq xmm, xmm/m64` | `F3 0F 7E /r` | `movqLoad` |
| `movq xmm/m64, xmm` | `66 0F D6 /r` | `movqStore` |
| `pxor xmm, xmm/m128` | `66 0F EF /r` | `pxor` |
| `xorps xmm, xmm/m128` | `0F 57 /r` | `xorps` |
| `punpcklqdq xmm, xmm/m128` | `66 0F 6C /r` | `punpcklqdq` |
| `punpckldq xmm, xmm/m128` | `66 0F 62 /r` | `punpckldq` |

REX.R and REX.B extend the XMM register numbers; REX.W is accepted only on `0F 6E`/`0F 7E`
(where it selects `movq`) and is rejected elsewhere (the SDM ignores it there; rejecting is
the conservative choice). The FS override, `F2`, and every other opcode are rejected.

## Semantics, and the documented choices

* Moves copy 128 bits; `movd`/`movq` into an XMM register zero-extend to 128 bits; `movq`
  `F3 0F 7E` and `66 0F D6` with a register destination zero the upper 64 bits; `movd` into a
  32-bit GPR zero-extends to 64 bits (`Ext.Sz.write`). No instruction here changes RFLAGS,
  MXCSR or raises a SIMD floating-point exception (the moves and the bitwise/unpack forms
  have "SIMD Floating-Point Exceptions: None").
* **Alignment.** `movaps`/`movdqa` and the legacy-SSE `pxor`/`xorps`/`punpckl*` with a
  memory operand need a 16-byte-aligned address, else `#GP(0)` (SDM Vol. 2, "Exceptions":
  "If a memory operand is not aligned on a 16-byte boundary"). The model reports
  `alignFault` (no step). `movups`, `movdqu` and the 32/64-bit moves have no alignment check.
* **Memory accesses** are byte-checked like `Ext`'s: a 128-bit access is permitted as a whole
  (`readBytes`/`writeBytes` of 16 bytes) or faults (`dataFault`). For `punpckl*` with a memory
  operand the model reads all 16 bytes; hardware may read only the low 8, so a run that the
  model faults could succeed on hardware (an under-approximation: no step, never a wrong
  one).
* Values are little-endian (`le128`).

This is a handwritten local model, written from the SDM, differentially tested against the
host CPU outside this repository, not proved to correspond to hardware.
-/

@[expose] public section

namespace Silmaril.X86.Sse9

open Silmaril.X86 (Reg Word State Byte MState XReg fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Mem RM Sz Rex Opc Pfx ModrmPart ByteParser pHead readRM writeRM loadN
  storeN)
open Silmaril.X86.Ext8 (pM)
open Silmaril.Process (Memory)

/-! ## State -/

/-- A 128-bit XMM value. -/
abbrev Xmm := BitVec 128

/-- The sixteen XMM registers. -/
abbrev XFile := Silmaril.Machine.RegisterFile XReg Xmm

/-- The state of the machine: an `Open9` state and the XMM registers. -/
structure XState where
  m : MState
  xmm : XFile

/-! ## Instructions -/

/-- An XMM `r/m` operand: an XMM register or memory. -/
inductive XRM where
  | reg (x : XReg)
  | mem (m : Silmaril.X86.Ext.Mem)
  deriving DecidableEq, Repr

/-- The four 128-bit moves. -/
inductive Move where
  | ups | aps | dqu | dqa
  deriving DecidableEq, Repr

/-- `movaps` and `movdqa` need a 16-byte-aligned memory operand. -/
def Move.aligned : Move → Bool
  | .aps | .dqa => true
  | .ups | .dqu => false

/-- The SSE data-movement subset. -/
inductive Instr where
  /-- `movups`/`movaps`/`movdqu`/`movdqa xmm, xmm/m128`. -/
  | load (k : Move) (dst : XReg) (src : XRM)
  /-- `movups`/`movaps`/`movdqu`/`movdqa xmm/m128, xmm`. -/
  | store (k : Move) (dst : XRM) (src : XReg)
  /-- `movd xmm, r/m32` (`sz = .d`), `movq xmm, r/m64` (`sz = .q`). -/
  | movToX (sz : Sz) (dst : XReg) (src : RM)
  /-- `movd r/m32, xmm`, `movq r/m64, xmm`. -/
  | movFromX (sz : Sz) (dst : RM) (src : XReg)
  /-- `movq xmm, xmm/m64` (`F3 0F 7E`). -/
  | movqLoad (dst : XReg) (src : XRM)
  /-- `movq xmm/m64, xmm` (`66 0F D6`). -/
  | movqStore (dst : XRM) (src : XReg)
  /-- `pxor xmm, xmm/m128`. -/
  | pxor (dst : XReg) (src : XRM)
  /-- `xorps xmm, xmm/m128`. -/
  | xorps (dst : XReg) (src : XRM)
  /-- `punpcklqdq xmm, xmm/m128`. -/
  | punpcklqdq (dst : XReg) (src : XRM)
  /-- `punpckldq xmm, xmm/m128`. -/
  | punpckldq (dst : XReg) (src : XRM)
  deriving DecidableEq, Repr

/-! ## Decoding -/

/-- The XMM register with the same number as a general-purpose register. -/
def xOf (r : Reg) : XReg := XReg.ofBitVec r.toBitVec

/-- The XMM register of the ModRM `reg` field. -/
def xregOf (rex : Option Rex) (mp : ModrmPart) : XReg := xOf (Ext9.regOf rex mp)

/-- The XMM `r/m` operand of a ModRM part (no FS override). -/
def xrmOf (rex : Option Rex) (mp : ModrmPart) : XRM :=
  match Ext9.rmOf rex mp with
  | .reg r => .reg (xOf r)
  | .mem m => .mem m

/-- The body of an SSE form, after the head: the legacy prefix, REX and the `0F`-escaped
opcode byte. -/
def pBody (pfx : Pfx) (rex : Option Rex) (b : Byte) : ByteParser Instr :=
  let w := (rex.getD Rex.zero).w
  match pfx with
  | .none =>
    if w = true then ByteParser.fail
    else if b = 0x10#8 then ByteParser.map (fun mp => .load .ups (xregOf rex mp) (xrmOf rex mp)) pM
    else if b = 0x11#8 then ByteParser.map (fun mp => .store .ups (xrmOf rex mp) (xregOf rex mp)) pM
    else if b = 0x28#8 then ByteParser.map (fun mp => .load .aps (xregOf rex mp) (xrmOf rex mp)) pM
    else if b = 0x29#8 then ByteParser.map (fun mp => .store .aps (xrmOf rex mp) (xregOf rex mp)) pM
    else if b = 0x57#8 then ByteParser.map (fun mp => .xorps (xregOf rex mp) (xrmOf rex mp)) pM
    else ByteParser.fail
  | .rep =>
    if w = true then ByteParser.fail
    else if b = 0x6F#8 then ByteParser.map (fun mp => .load .dqu (xregOf rex mp) (xrmOf rex mp)) pM
    else if b = 0x7F#8 then ByteParser.map (fun mp => .store .dqu (xrmOf rex mp) (xregOf rex mp)) pM
    else if b = 0x7E#8 then ByteParser.map (fun mp => .movqLoad (xregOf rex mp) (xrmOf rex mp)) pM
    else ByteParser.fail
  | .opsize =>
    if b = 0x6E#8 then
      ByteParser.map (fun mp => .movToX (Sz.ofW w) (xregOf rex mp) (Ext9.rmOf rex mp)) pM
    else if b = 0x7E#8 then
      ByteParser.map (fun mp => .movFromX (Sz.ofW w) (Ext9.rmOf rex mp) (xregOf rex mp)) pM
    else if w = true then ByteParser.fail
    else if b = 0x6F#8 then ByteParser.map (fun mp => .load .dqa (xregOf rex mp) (xrmOf rex mp)) pM
    else if b = 0x7F#8 then ByteParser.map (fun mp => .store .dqa (xrmOf rex mp) (xregOf rex mp)) pM
    else if b = 0xD6#8 then ByteParser.map (fun mp => .movqStore (xrmOf rex mp) (xregOf rex mp)) pM
    else if b = 0xEF#8 then ByteParser.map (fun mp => .pxor (xregOf rex mp) (xrmOf rex mp)) pM
    else if b = 0x6C#8 then
      ByteParser.map (fun mp => .punpcklqdq (xregOf rex mp) (xrmOf rex mp)) pM
    else if b = 0x62#8 then
      ByteParser.map (fun mp => .punpckldq (xregOf rex mp) (xrmOf rex mp)) pM
    else ByteParser.fail
  | .nopPad _ => ByteParser.fail

/-- The parser of an SSE form: no FS override, a `0F`-escaped opcode. -/
def pSse : ByteParser Instr :=
  ByteParser.bind pHead fun h =>
    if h.1 = true then ByteParser.fail
    else
      match h.2.2.2 with
      | .two b => pBody h.2.1 h.2.2.1 b
      | .one _ => ByteParser.fail

/-- Decode an SSE form; the instruction and the number of bytes consumed. -/
def decodeSse (bytes : List Byte) : Option (Instr × Nat) :=
  match pSse bytes with
  | .ok i rest => some (i, bytes.length - rest.length)
  | _ => none

/-! ## Semantics -/

/-- The 16 little-endian bytes of a 128-bit value. -/
def le128 (v : Xmm) : List Byte := List.ofFn fun i : Fin 16 => v.extractLsb' (8 * i.val) 8

/-- A 128-bit little-endian load. -/
def load128 (memory : Memory) (a : Word) : Option Xmm :=
  (memory.readBytes a.toNat 16).map fun bs => BitVec.ofNat 128 (Silmaril.X86.Ext.leValue bs)

/-- A 128-bit little-endian store. -/
def store128 (memory : Memory) (a : Word) (v : Xmm) : Option Memory :=
  memory.writeBytes a.toNat (le128 v)

/-- The outcome of an SSE instruction. -/
inductive XResult where
  /-- Retired with this core (RIP included), XMM file and memory. -/
  | ok (core : State) (xmm : XFile) (memory : Memory)
  /-- A data access was not permitted or not backed. -/
  | dataFault
  /-- `#GP(0)`: a misaligned 16-byte operand of an aligned form. -/
  | alignFault

/-- The successor state of a retired instruction, if any. -/
def XResult.toOption : XResult → Option XState
  | .ok c x m => some ⟨⟨c, m⟩, x⟩
  | _ => none

/-- A memory operand of an aligned form is not 16-byte aligned. -/
def misaligned (src : XRM) (s : State) (next : Word) : Bool :=
  match src with
  | .reg _ => false
  | .mem m => (m.addr s next).toNat % 16 != 0

/-- Read a 128-bit `xmm/m128` operand. -/
def readX (src : XRM) (s : State) (x : XFile) (memory : Memory) (next : Word) : Option Xmm :=
  match src with
  | .reg r => some (x r)
  | .mem m => load128 memory (m.addr s next)

/-- Read an aligned 128-bit operand and combine it with the destination register. -/
def binop (f : Xmm → Xmm → Xmm) (dst : XReg) (src : XRM) (s : State) (x : XFile)
    (memory : Memory) (next : Word) : XResult :=
  if misaligned src s next then .alignFault
  else
    match readX src s x memory next with
    | none => .dataFault
    | some v => .ok { s with rip := next } (Silmaril.Machine.RegisterFile.write x dst (f (x dst) v))
        memory

/-- `punpckldq`: interleave the low doublewords, destination first. -/
def unpackLoDq (d v : Xmm) : Xmm :=
  (v.extractLsb' 32 32 ++ d.extractLsb' 32 32 ++ v.extractLsb' 0 32 ++ d.extractLsb' 0 32 :
    BitVec 128)

/-- `punpcklqdq`: the low quadword of the source above the low quadword of the destination. -/
def unpackLoQdq (d v : Xmm) : Xmm := (v.setWidth 64 ++ d.setWidth 64 : BitVec 128)

/-- **Execute an SSE instruction**, given the address of the next instruction. -/
def exec (i : Instr) (s : State) (x : XFile) (memory : Memory) (next : Word) : XResult :=
  let wr := Silmaril.Machine.RegisterFile.write x
  match i with
  | .load k dst src =>
    if k.aligned && misaligned src s next then .alignFault
    else
      match readX src s x memory next with
      | none => .dataFault
      | some v => .ok { s with rip := next } (wr dst v) memory
  | .store k dst src =>
    match dst with
    | .reg r => .ok { s with rip := next } (wr r (x src)) memory
    | .mem m =>
      if k.aligned && misaligned (.mem m) s next then .alignFault
      else
        match store128 memory (m.addr s next) (x src) with
        | none => .dataFault
        | some memory' => .ok { s with rip := next } x memory'
  | .movToX sz dst src =>
    match readRM sz src s memory next with
    | none => .dataFault
    | some v => .ok { s with rip := next } (wr dst (v.setWidth 128)) memory
  | .movFromX sz dst src =>
    match writeRM sz dst ((x src).setWidth sz.bits) s memory next with
    | none => .dataFault
    | some (t, memory') => .ok { t with rip := next } x memory'
  | .movqLoad dst src =>
    match src with
    | .reg r => .ok { s with rip := next } (wr dst (((x r).setWidth 64).setWidth 128)) memory
    | .mem m =>
      match loadN memory (m.addr s next) 8 with
      | none => .dataFault
      | some v => .ok { s with rip := next } (wr dst (v.setWidth 128)) memory
  | .movqStore dst src =>
    match dst with
    | .reg r => .ok { s with rip := next } (wr r (((x src).setWidth 64).setWidth 128)) memory
    | .mem m =>
      match storeN memory (m.addr s next) 8 ((x src).setWidth 64) with
      | none => .dataFault
      | some memory' => .ok { s with rip := next } x memory'
  | .pxor dst src => binop (· ^^^ ·) dst src s x memory next
  | .xorps dst src => binop (· ^^^ ·) dst src s x memory next
  | .punpcklqdq dst src => binop unpackLoQdq dst src s x memory next
  | .punpckldq dst src => binop unpackLoDq dst src s x memory next

/-! ## Fetch and step -/

/-- Fetch an SSE form: `decodeSse` reads the fetch window and the bytes it consumed are
executable. `none` if not decodable as an SSE form; `some none` if not fetchable. -/
def fetchSse (memory : Memory) (address : Nat) : Option (Option (Instr × Nat)) :=
  (decodeSse (fetchWindow memory maxInstrLength address)).map fun (i, n) =>
    if memory.Permitted .execute address n then some (i, n) else none

/-- **One step**: `Open9.step` with the XMM file unchanged; on bytes that neither `Ext8` nor
`Ext9` decodes, an SSE form. -/
def step (x : XState) : Option XState :=
  match Silmaril.X86.Ext8.fetch x.m.memory x.m.core.rip.toNat with
  | .inl .undecodable =>
    match Ext9.fetchNew x.m.memory x.m.core.rip.toNat with
    | some (some (i, n)) =>
      (Open.ofResult (Ext9.execNew i x.m.core x.m.memory
        (x.m.core.rip + BitVec.ofNat 64 n))).map fun m' => ⟨m', x.xmm⟩
    | some none => none
    | none =>
      match fetchSse x.m.memory x.m.core.rip.toNat with
      | some (some (i, n)) =>
        (exec i x.m.core x.xmm x.m.memory (x.m.core.rip + BitVec.ofNat 64 n)).toOption
      | _ => none
  | _ => (Open.step x.m).map fun m' => ⟨m', x.xmm⟩

/-! ## The listing decoder of the SSE forms -/

/-- `Ext9`'s new-form parser rejects (and so rejects every extension). -/
def ext9Bad (bytes : List Byte) : Bool :=
  match Ext9.pNew bytes with
  | .bad => true
  | _ => false

/-- The listing decoder of an SSE form: `Ext` rejects the slice, the parsers of `Ext8`'s and
`Ext9`'s new forms reject it, the `Ext` length decoder finishes inside it, and `decodeSse`
reads a form of 1 to 15 bytes. Checked on each listing by `decide`. -/
def decodeL (bytes : List Byte) : Option (Instr × Nat) :=
  match decodeSse bytes with
  | some (i, n) =>
    if Silmaril.X86.Ext.decode bytes = none ∧ Open9.newBad bytes = true ∧
        Open9.rawNotEof bytes = true ∧ ext9Bad bytes = true ∧ 0 < n ∧ n ≤ maxInstrLength then
      some (i, n)
    else none
  | none => none

end Silmaril.X86.Sse9
