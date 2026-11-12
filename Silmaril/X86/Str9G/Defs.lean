module

public import Silmaril.X86.Str9FsX.Defs

/-!
# `Str9G`: `Str9FsX` with a time-stamp oracle, CET-off shadow-stack hints and SSE2 integer forms

Three additions close the `__libc_start_main` closure of glibc 2.39 and the `sse2`
string variants.

**State.** `GState` holds an `Sse9.XState` (`x`) and two ghost components:

* `tsc : Nat → Word`, a **time-stamp oracle**. `rdtsc` returns `tsc 0` and the state keeps
  `fun k => tsc (k + 1)`. A statement about every state therefore holds for every sequence
  of counter values. That is the nondeterminism of `rdtsc` (glibc's adaptive mutex spin reads
  it), and the step stays a function, so `SegVC` and the `Isa.Extends` lenses still apply.
  Two alternatives were rejected:
  - a relational step leaves `SegVC.Isa` and silmaril's deterministic transfer theorems;
  - an opaque function of the state is deterministic, so a proof could rely on two reads
    being equal.
* `cetOff : Bool`, the **explicit CET assumption**. With user shadow stacks disabled,
  `rdsspq` sits in the hint-NOP space and executes as a no-op: the destination is unchanged
  (SDM Vol. 1 §17). That is how glibc 2.39 runs unless a shadow stack is
  enabled. With `cetOff = true` the model takes that step; with `cetOff = false` it has
  **no** step there, because the shadow stack is not modelled. A statement that needs to get
  past `_setjmp` assumes `cetOff = true` of its entry state. `incsspq` is decoded but has
  **no step** in either case: on a processor without CET (an i7-8700, for
  example) it raises `#UD`, and glibc executes it only when the shadow-stack pointer read by
  `rdsspq` is non-zero, which with CET off it never is.

**SSE2 integer forms** (legacy encodings, `66 0F …` unless noted), in `Sse9`'s style and on
its XMM file:

* byte-wise `pcmpeqb` (`74`), `pminub` (`DA`), `psubb` (`F8`), and bit-wise `por` (`EB`) and
  `pand` (`DB`);
* `pmovmskb r32, xmm` (`D7`, register operand), `psrldq`/`pslldq xmm, imm8` (`73 /3`, `73 /7`),
  `punpcklbw` (`60`), `punpcklwd` (`61`), `pshufd` (`70 ib`);
* `movhps`/`movhpd`, `movlps`/`movlpd xmm, m64` (`[66] 0F 16`, `[66] 0F 12`, memory operand);
* `movss xmm, xmm/m32` (`F3 0F 10`) and `movsd xmm, xmm/m64` (`F2 0F 10`).

One integer form: `lea` with the address-size prefix (`67 [REX] 8D /r`). The address is
computed in 32 bits, which is the low 32 bits of the 64-bit sum (an `rip`-relative operand
uses `eip`, whose low 32 bits are those of `rip`), and the result is zero-extended into the
destination for either operand size. `__strrchr_sse2` uses `lea -1(%ecx), %edx`.

The packed forms with a memory operand need 16-byte alignment (`#GP`), as `Sse9.binop`
checks. The 32/64-bit loads have no alignment check. A load into the low or high half keeps
the other half. `movss`/`movsd` from memory zero the rest; from a register they merge the
low element.

`rdtsc` (`0F 31`) and the CET forms change the ghost state, so like the SSE forms they are
not `SegVC` instructions: `Thms.step_of_fetch_g` is their law.

The semantics is a handwritten model of the SDM; it is not proved or tested to match
hardware.
-/

@[expose] public section

namespace Silmaril.X86.Str9G

open Silmaril.X86 (Reg Word State Byte MState XReg fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Mem RM Sz Rex Opc Pfx ModrmPart ByteParser pHead loadN)
open Silmaril.X86.Ext8 (pM)
open Silmaril.X86.Sse9 (XState XFile Xmm XRM xregOf xrmOf)
open Silmaril.Process (Memory)

/-! ## State -/

/-- **The state**: an `Sse9` state, the time-stamp oracle and the CET assumption. -/
structure GState where
  x : XState
  tsc : Nat → Word
  cetOff : Bool

/-! ## Instructions -/

/-- The SSE2 integer forms. -/
inductive Sse2 where
  | pcmpeqb (d : XReg) (s : Sse9.XRM)
  | pminub (d : XReg) (s : Sse9.XRM)
  | psubb (d : XReg) (s : Sse9.XRM)
  | por (d : XReg) (s : Sse9.XRM)
  | pand (d : XReg) (s : Sse9.XRM)
  | punpcklbw (d : XReg) (s : Sse9.XRM)
  | punpcklwd (d : XReg) (s : Sse9.XRM)
  | pshufd (d : XReg) (s : Sse9.XRM) (imm : BitVec 8)
  /-- `pmovmskb r32, xmm`. -/
  | pmovmskb (r : Reg) (s : XReg)
  /-- `psrldq` (`left = false`) and `pslldq` by `imm` bytes. -/
  | pshiftdq (left : Bool) (d : XReg) (imm : BitVec 8)
  /-- `movhps`/`movhpd` (`high`) or `movlps`/`movlpd xmm, m64`. -/
  | movHalf (high : Bool) (d : XReg) (m : Ext.Mem)
  /-- `movss` (`dbl = false`) / `movsd` (`dbl = true`) `xmm, xmm/m`. -/
  | movScalar (dbl : Bool) (d : XReg) (s : Sse9.XRM)
  deriving DecidableEq, Repr

/-- The new forms of the layer. -/
inductive New where
  | sse2 (i : Sse2)
  /-- `rdtsc`. -/
  | rdtsc
  /-- `rdsspq r64` (`inc = false`), `incsspq r64` (`inc = true`). -/
  | cet (inc : Bool) (r : Reg)
  /-- `lea` with the address-size prefix (`67 [REX] 8D /r`, memory operand): the low 32 bits
  of the address, zero-extended into the 64-bit register. -/
  | lea32 (d : Reg) (m : Ext.Mem)
  deriving DecidableEq, Repr

/-! ## Decoding -/

/-- The register operand of a ModRM part (`mod = 11`), or reject. -/
def regP (rex : Option Rex) (mp : ModrmPart) : ByteParser Reg :=
  if mp.1.mod = 3#2 then ByteParser.pure (Silmaril.X86.Ext.mkReg (rex.getD Rex.zero).b mp.1.rm)
  else ByteParser.fail

/-- A memory operand, or reject. -/
def memP (rex : Option Rex) (mp : ModrmPart) : ByteParser Ext.Mem :=
  match Silmaril.X86.Ext9.rmOf rex mp with
  | .mem m => ByteParser.pure m
  | .reg _ => ByteParser.fail

/-- A packed `xmm, xmm/m128` form. -/
def packed (f : XReg → Sse9.XRM → Sse2) (rex : Option Rex) : ByteParser New :=
  ByteParser.map (fun mp => .sse2 (f (xregOf rex mp) (xrmOf rex mp))) pM

/-- After an `F2` (which the head parser reads as a one-byte opcode): `0F 10 /r`,
`movsd xmm, xmm/m64`. -/
def pF2Rest : ByteParser New :=
  ByteParser.bind pHead fun h =>
    if h.1 = false ∧ h.2.1 = .none ∧ h.2.2.2 = .two 0x10#8 ∧
        (h.2.2.1.getD Rex.zero).w = false then
      ByteParser.map (fun mp => .sse2 (.movScalar true (xregOf h.2.2.1 mp) (xrmOf h.2.2.1 mp))) pM
    else ByteParser.fail

/-- After a `67` (which the head parser reads as a one-byte opcode): `[REX] 8D /r` with a
memory operand, `lea r, m` with a 32-bit address. -/
def p67Rest : ByteParser New :=
  ByteParser.bind pHead fun h =>
    if h.1 = false ∧ h.2.1 = .none ∧ h.2.2.2 = .one 0x8D#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun m => .lea32 (Silmaril.X86.Ext9.regOf h.2.2.1 mp) m) (memP h.2.2.1 mp)
    else ByteParser.fail

/-- The body of a form after the head: legacy prefix, REX, opcode. -/
def pBody (pfx : Pfx) (rex : Option Rex) : Opc → ByteParser New
  | .two b =>
    let w := (rex.getD Rex.zero).w
    match pfx with
    | .opsize =>
      if w = true then ByteParser.fail
      else if b = 0x74#8 then packed .pcmpeqb rex
      else if b = 0xDA#8 then packed .pminub rex
      else if b = 0xF8#8 then packed .psubb rex
      else if b = 0xEB#8 then packed .por rex
      else if b = 0xDB#8 then packed .pand rex
      else if b = 0x60#8 then packed .punpcklbw rex
      else if b = 0x61#8 then packed .punpcklwd rex
      else if b = 0x70#8 then
        ByteParser.bind pM fun mp =>
          ByteParser.map (fun v => .sse2 (.pshufd (xregOf rex mp) (xrmOf rex mp) v)) ByteParser.byte
      else if b = 0xD7#8 then
        ByteParser.bind pM fun mp =>
          ByteParser.map (fun r => .sse2 (.pmovmskb (Silmaril.X86.Ext9.regOf rex mp)
            (Silmaril.X86.Sse9.xOf r))) (regP rex mp)
      else if b = 0x73#8 then
        ByteParser.bind pM fun mp =>
          if mp.1.reg = 3#3 ∨ mp.1.reg = 7#3 then
            ByteParser.bind (regP rex mp) fun r =>
              ByteParser.map (fun v => .sse2 (.pshiftdq (mp.1.reg = 7#3) (Silmaril.X86.Sse9.xOf r) v))
                ByteParser.byte
          else ByteParser.fail
      else if b = 0x16#8 ∨ b = 0x12#8 then
        ByteParser.bind pM fun mp =>
          ByteParser.map (fun m => .sse2 (.movHalf (b = 0x16#8) (xregOf rex mp) m)) (memP rex mp)
      else ByteParser.fail
    | .none =>
      if b = 0x31#8 ∧ rex = none then ByteParser.pure .rdtsc
      else if w = true then ByteParser.fail
      else if b = 0x16#8 ∨ b = 0x12#8 then
        ByteParser.bind pM fun mp =>
          ByteParser.map (fun m => .sse2 (.movHalf (b = 0x16#8) (xregOf rex mp) m)) (memP rex mp)
      else ByteParser.fail
    | .rep =>
      if b = 0x10#8 ∧ w = false then
        ByteParser.map (fun mp => .sse2 (.movScalar false (xregOf rex mp) (xrmOf rex mp))) pM
      else if b = 0x1E#8 ∧ w = true then
        ByteParser.bind pM fun mp =>
          if mp.1.reg = 1#3 then ByteParser.map (fun r => .cet false r) (regP rex mp)
          else ByteParser.fail
      else if b = 0xAE#8 ∧ w = true then
        ByteParser.bind pM fun mp =>
          if mp.1.reg = 5#3 then ByteParser.map (fun r => .cet true r) (regP rex mp)
          else ByteParser.fail
      else ByteParser.fail
    | .nopPad _ => ByteParser.fail
  | .one b =>
    if b = 0xF2#8 ∧ pfx = .none ∧ rex = none then pF2Rest
    else if b = 0x67#8 ∧ pfx = .none ∧ rex = none then p67Rest
    else ByteParser.fail

/-- The parser of the layer's forms: no FS override. -/
def pNew : ByteParser New :=
  ByteParser.bind pHead fun h => if h.1 = true then ByteParser.fail else pBody h.2.1 h.2.2.1 h.2.2.2

/-- Decode a form of the layer. -/
def decodeNew (w : List Byte) : Option (New × Nat) :=
  match pNew w with
  | .ok i rest => some (i, w.length - rest.length)
  | _ => none

/-- `rep stosd` cannot start here. -/
def stosdBad (w : List Byte) : Bool := 2 ≤ w.length && (Silmaril.X86.Str9FsX.decodeStosd w).isNone

/-- The listing decoder of the layer's forms: every lower decoder rejects the slice in a way
no following byte changes, and `decodeNew` reads a form of 2 to 15 bytes. -/
def decodeL (w : List Byte) : Option (New × Nat) :=
  match decodeNew w with
  | some (i, n) =>
    if Silmaril.X86.Ext.decode w = none ∧ Silmaril.X86.Open9.newBad w = true ∧
        Silmaril.X86.Open9.rawNotEof w = true ∧ Silmaril.X86.Str9.ext9Bad w = true ∧
        Silmaril.X86.Str9Fs.strBad w = true ∧ Silmaril.X86.Str9FsX.atomicBad w = true ∧
        Silmaril.X86.Str9FsX.fsBad w = true ∧ Silmaril.X86.Str9FsX.sseBad w = true ∧
        stosdBad w = true ∧ 2 ≤ n ∧ n ≤ maxInstrLength then some (i, n) else none
  | none => none

/-! ## Semantics -/

/-- Byte `i` of a 128-bit value. -/
def byteOf (v : Sse9.Xmm) (i : Nat) : BitVec 8 := v.extractLsb' (8 * i) 8

/-- The 128-bit value with bytes `f 0, …, f 15`. -/
def ofBytes (f : Nat → BitVec 8) : Sse9.Xmm :=
  BitVec.ofNat 128 ((List.range 16).map fun i => (f i).toNat * 2 ^ (8 * i)).sum

/-- A byte-wise operation. -/
def bytewise (f : BitVec 8 → BitVec 8 → BitVec 8) (d v : Sse9.Xmm) : Sse9.Xmm :=
  ofBytes fun i => f (byteOf d i) (byteOf v i)

/-- `pcmpeqb`: `FF` where the bytes are equal, `00` elsewhere. -/
def cmpeqb (d v : Sse9.Xmm) : Sse9.Xmm := bytewise (fun a b => if a = b then 0xFF else 0) d v

/-- `pminub`: the unsigned byte minimum. -/
def minub (d v : Sse9.Xmm) : Sse9.Xmm := bytewise (fun a b => if a.toNat ≤ b.toNat then a else b) d v

/-- `pmovmskb`: bit `i` is the top bit of byte `i`. -/
def movmskb (v : Sse9.Xmm) : Word :=
  BitVec.ofNat 64 ((List.range 16).map fun i => if (byteOf v i).msb then 2 ^ i else 0).sum

/-- `punpcklbw`: interleave the low bytes, destination first. -/
def unpackLoBw (d v : Sse9.Xmm) : Sse9.Xmm :=
  ofBytes fun j => if j % 2 = 0 then byteOf d (j / 2) else byteOf v (j / 2)

/-- `punpcklwd`: interleave the low words, destination first. -/
def unpackLoWd (d v : Sse9.Xmm) : Sse9.Xmm :=
  ofBytes fun j =>
    let w := j / 2
    byteOf (if w % 2 = 0 then d else v) (2 * (w / 2) + j % 2)

/-- `pshufd`: doubleword `i` of the result is doubleword `imm[2i+1:2i]` of the source. -/
def shufd (v : Sse9.Xmm) (imm : BitVec 8) : Sse9.Xmm :=
  ofBytes fun j => byteOf v (4 * ((imm.toNat >>> (2 * (j / 4))) % 4) + j % 4)

/-- An XMM-only result. -/
def xmmOnly (g : GState) (next : Word) (xs : XFile) (memory : Memory) : Option GState :=
  some { g with x := ⟨⟨{ g.x.m.core with rip := next }, memory⟩, xs⟩ }

/-- An integer-register result with the XMM file and memory kept. -/
def xmmOnly' (g : GState) (c : State) : Option GState :=
  some { g with x := ⟨⟨c, g.x.m.memory⟩, g.x.xmm⟩ }

/-- The successor of an `Sse9`-style result. -/
def ofX (g : GState) : Silmaril.X86.Sse9.XResult → Option GState
  | .ok c xs m => some { g with x := ⟨⟨c, m⟩, xs⟩ }
  | _ => none

/-- Execute an SSE2 form. -/
def execSse2 (i : Sse2) (g : GState) (next : Word) : Option GState :=
  let s := g.x.m.core
  let x := g.x.xmm
  let memory := g.x.m.memory
  let wr := Silmaril.Machine.RegisterFile.write x
  match i with
  | .pcmpeqb d src => ofX g (Silmaril.X86.Sse9.binop cmpeqb d src s x memory next)
  | .pminub d src => ofX g (Silmaril.X86.Sse9.binop minub d src s x memory next)
  | .psubb d src => ofX g (Silmaril.X86.Sse9.binop (bytewise (· - ·)) d src s x memory next)
  | .por d src => ofX g (Silmaril.X86.Sse9.binop (· ||| ·) d src s x memory next)
  | .pand d src => ofX g (Silmaril.X86.Sse9.binop (· &&& ·) d src s x memory next)
  | .punpcklbw d src => ofX g (Silmaril.X86.Sse9.binop unpackLoBw d src s x memory next)
  | .punpcklwd d src => ofX g (Silmaril.X86.Sse9.binop unpackLoWd d src s x memory next)
  | .pshufd d src imm => ofX g (Silmaril.X86.Sse9.binop (fun _ v => shufd v imm) d src s x memory next)
  | .pmovmskb r src =>
    some { g with x := ⟨⟨{ s.write r (movmskb (x src)) with rip := next }, memory⟩, x⟩ }
  | .pshiftdq left d imm =>
    let k := 8 * min imm.toNat 16
    xmmOnly g next (wr d (if left then x d <<< k else x d >>> k)) memory
  | .movHalf high d m =>
    match loadN memory (m.addr s next) 8 with
    | none => none
    | some v =>
      let lo := v.setWidth 64
      let cur := x d
      xmmOnly g next
        (wr d (if high then (lo ++ cur.setWidth 64 : BitVec 128)
          else (cur.extractLsb' 64 64 ++ lo : BitVec 128))) memory
  | .movScalar dbl d src =>
    let k := if dbl then 8 else 4
    match src with
    | .reg r =>
      let lo := (x r).setWidth (8 * k)
      let cur := x d
      xmmOnly g next (wr d ((cur >>> (8 * k) <<< (8 * k)) ||| lo.setWidth 128)) memory
    | .mem m =>
      match loadN memory (m.addr s next) k with
      | none => none
      | some v => xmmOnly g next (wr d ((v.setWidth (8 * k)).setWidth 128)) memory

/-- Execute a form of the layer, given the address of the next instruction. -/
def execNew (i : New) (g : GState) (next : Word) : Option GState :=
  match i with
  | .sse2 i => execSse2 i g next
  | .rdtsc =>
    let t := g.tsc 0
    let c := ((g.x.m.core.write .rax (t.setWidth 32 |>.setWidth 64)).write .rdx
      ((t >>> 32).setWidth 32 |>.setWidth 64))
    some (GState.mk ⟨⟨{ c with rip := next }, g.x.m.memory⟩, g.x.xmm⟩ (fun k => g.tsc (k + 1))
      g.cetOff)
  | .cet false _ => if g.cetOff then xmmOnly g next g.x.xmm g.x.m.memory else none
  | .cet true _ => none
  | .lea32 d m =>
    let s := g.x.m.core
    xmmOnly' g { s.write d (((m.addr s next).setWidth 32).setWidth 64) with rip := next }

/-! ## Fetch and step -/

/-- Fetch a form of the layer. -/
def fetchNew (memory : Memory) (address : Nat) : Option (Option (New × Nat)) :=
  (decodeNew (fetchWindow memory maxInstrLength address)).map fun (i, n) =>
    if memory.Permitted .execute address n then some (i, n) else none

/-- Lift an `XState` successor. -/
def lift (g : GState) (y : Option XState) : Option GState := y.map fun x => { g with x := x }

/-- **One step**: `Str9FsX.step` on `x` with the ghost state kept, and on bytes that every
`Str9FsX` decoder rejects, a form of this layer. -/
def step (g : GState) : Option GState :=
  let x := g.x
  match Silmaril.X86.Ext8.fetch x.m.memory x.m.core.rip.toNat with
  | .inl .undecodable =>
    match Silmaril.X86.Ext9.fetchNew x.m.memory x.m.core.rip.toNat with
    | some (some _) => lift g (Silmaril.X86.Str9FsX.step x)
    | some none => none
    | none =>
      match Silmaril.X86.Str9.fetchStr x.m.memory x.m.core.rip.toNat with
      | some (some _) => lift g (Silmaril.X86.Str9FsX.step x)
      | some none => none
      | none =>
        match Silmaril.X86.Str9Fs.fetchNew x.m.memory x.m.core.rip.toNat with
        | some (some _) => lift g (Silmaril.X86.Str9FsX.step x)
        | some none => none
        | none =>
          match Silmaril.X86.Sse9.fetchSse x.m.memory x.m.core.rip.toNat with
          | some (some _) => lift g (Silmaril.X86.Str9FsX.step x)
          | some none => none
          | none =>
            match Silmaril.X86.Str9FsX.fetchStosd x.m.memory x.m.core.rip.toNat with
            | some (some _) => lift g (Silmaril.X86.Str9FsX.step x)
            | some none => none
            | none =>
              match fetchNew x.m.memory x.m.core.rip.toNat with
              | some (some (i, n)) => execNew i g (x.m.core.rip + BitVec.ofNat 64 n)
              | _ => none
  | _ => lift g (Silmaril.X86.Str9FsX.step x)

end Silmaril.X86.Str9G
