module

public import Silmaril.X86.Str9G.Defs

/-!
# `Str9V`: `Str9G` with the YMM upper halves, VEX (AVX/AVX2/BMI) forms and copy hints

The forms that glibc's IFUNC resolvers select on an AVX2 machine (`__memset_avx2_unaligned_erms`,
`__memmove_avx_unaligned_erms`, `__strlen_avx2`, …) and that `__memmove_sse2_unaligned` needs
for large copies.

**State.** `VState` is a `Str9G.GState` (`g`) and the upper 128 bits of each YMM register
(`hi`). `ymm r = hi r ++ g.x.xmm r`. A legacy SSE instruction (any lower layer's step) keeps
`hi` (SDM Vol. 1 §14.1.3). A VEX.128 instruction writing `xmm r` zeroes `hi r`. A VEX.256
instruction writes both halves. `vzeroupper` zeroes every `hi`.

**Legacy additions** (no VEX):
* `rep movsb` (`F3 A4`), one byte per step, forward (the direction flag is not modelled; it is
  clear under the System V ABI), like `Str9`'s `rep movsq`;
* `prefetcht0/1/2/nta m8` (`0F 18 /0–/3`), a no-op (a hint; never faults);
* `movntdq m128, xmm` (`66 0F E7`), an aligned 16-byte store (the non-temporal hint has no
  effect in this sequential model);
* `movbe r, m` / `movbe m, r` (`0F 38 F0/F1`, 32 or 64 bit), a byte-swapped load or store.

**VEX forms** (`C4`/`C5` prefixes; map `0F` unless noted):
* moves: `vmovd/vmovq xmm, r/m` (`66 6E`), `vmovd/vmovq r/m, xmm` (`66 7E`), `vmovq xmm, xmm/m64`
  (`F3 7E`), `vmovq xmm/m64, xmm` (`66 D6`), `vmovdqa` (`66 6F/7F`), `vmovdqu` (`F3 6F/7F`),
  `vmovntdq` (`66 E7`);
* packed integer, three-operand, 128 or 256 bit: `vpaddb` (`FC`), `vpand` (`DB`), `vpandn` (`DF`),
  `vpor` (`EB`), `vpxor` (`EF`), `vpcmpeqb` (`74`), `vpcmpeqd` (`76`), `vpcmpgtb` (`64`),
  `vpminub` (`DA`), `vpminud` (map `0F38`, `3B`);
* `vpmovmskb r32, xmm/ymm` (`D7`), `vpbroadcastb`/`vpbroadcastd` (map `0F38`, `78`/`58`),
  `vzeroupper` (`77`);
* BMI (map `0F38`, general registers): `bzhi` (`F5`), `shlx`/`shrx`/`sarx` (`66`/`F2`/`F3 F7`),
  `blsmsk` (`F3 /2`).

VEX forms with a memory operand need no alignment, except `vmovdqa` and `vmovntdq`
(16 or 32 bytes, `#GP`).

The semantics is a handwritten model of the SDM; it is not proved to match hardware.
-/

@[expose] public section

namespace Silmaril.X86.Str9V

open Silmaril.X86 (Reg Word State Byte MState XReg fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Mem RM Sz Rex Opc Pfx ModrmPart ByteParser pHead loadN storeN)
open Silmaril.X86.Ext8 (pM)
open Silmaril.X86.Sse9 (XState XFile Xmm XRM xregOf xrmOf)
open Silmaril.Process (Memory)
open Silmaril.X86.Str9G (GState)

/-! ## State -/

/-- **The state**: a `Str9G` state and the upper halves of the YMM registers. -/
structure VState where
  g : GState
  hi : XReg → Sse9.Xmm

/-! ## Instructions -/

/-- The packed integer operations (on each 128-bit lane). -/
inductive VBin where
  | addb | and | andn | or | xor | cmpeqb | cmpeqd | cmpgtb | minub | minud
  deriving DecidableEq, Repr

/-- The BMI shifts and `bzhi`. -/
inductive Bmi where
  | bzhi | shlx | shrx | sarx
  deriving DecidableEq, Repr

/-- The narrow unary forms. -/
inductive Un where
  | inc | dec | not
  deriving DecidableEq, Repr

/-- The forms of the layer. -/
inductive Instr where
  | repMovsb
  | repStosb
  /-- `inc`/`dec r8` (`FE /0`, `/1`, register operand, no high-byte register). -/
  | un8 (op : Un) (r : Reg)
  /-- `inc`/`dec`/`not r16` (`66 FF /0`, `/1`, `66 F7 /2`, register operand). -/
  | un16 (op : Un) (r : Reg)
  /-- `bts r, r` (`0F AB`, register operands). -/
  | btsR (q : Bool) (d s : Reg)
  /-- `lea r32/r64, m` with the 32-bit address-size prefix (`67 8D`). -/
  | lea32 (d : Reg) (m : Ext.Mem)
  | prefetch
  | movntdq (m : Ext.Mem) (s : XReg)
  /-- `movbe r, m` (`load`) or `movbe m, r`. -/
  | movbe (load : Bool) (sz : Sz) (r : Reg) (m : Ext.Mem)
  /-- `vmovd`/`vmovq xmm, r/m` (`q` for 64 bit). -/
  | vmovToX (q : Bool) (d : XReg) (src : RM)
  /-- `vmovd`/`vmovq r/m, xmm`. -/
  | vmovFromX (q : Bool) (dst : RM) (s : XReg)
  /-- `vmovq xmm, xmm/m64`. -/
  | vmovqLoad (d : XReg) (src : Sse9.XRM)
  /-- `vmovq xmm/m64, xmm`. -/
  | vmovqStore (dst : Sse9.XRM) (s : XReg)
  /-- `vmovdqa`/`vmovdqu` load, 128 (`wide = false`) or 256 bit. -/
  | vload (aligned wide : Bool) (d : XReg) (src : Sse9.XRM)
  /-- `vmovdqa`/`vmovdqu`/`vmovntdq` store. -/
  | vstore (aligned wide : Bool) (dst : Sse9.XRM) (s : XReg)
  /-- `d ← v op src`. -/
  | vbin (op : VBin) (wide : Bool) (d v : XReg) (src : Sse9.XRM)
  | vpmovmskb (wide : Bool) (r : Reg) (s : XReg)
  /-- `vpbroadcastb` (`dw = false`) / `vpbroadcastd`. -/
  | vbcast (dw wide : Bool) (d : XReg) (src : Sse9.XRM)
  | vzeroupper
  /-- `bzhi`/`shlx`/`shrx`/`sarx d, src, v`. -/
  | bmi (op : Bmi) (q : Bool) (d : Reg) (src : RM) (v : Reg)
  /-- `blsmsk v, src`. -/
  | blsmsk (q : Bool) (v : Reg) (src : RM)
  deriving DecidableEq, Repr

/-! ## Decoding -/

/-- The fields of a VEX prefix (`r`, `x`, `b` already un-inverted; `vvvv` the register). -/
structure Vex where
  r : Bool
  x : Bool
  b : Bool
  w : Bool
  map : BitVec 5
  v : BitVec 4
  l : Bool
  pp : BitVec 2
  deriving DecidableEq, Repr

/-- The REX the ModRM helpers read. -/
def Vex.rex (v : Vex) : Option Rex := some ⟨v.w, v.r, v.x, v.b⟩

/-- A memory operand, or reject. -/
def memP (rex : Option Rex) (mp : ModrmPart) : ByteParser Ext.Mem :=
  match Silmaril.X86.Ext9.rmOf rex mp with
  | .mem m => ByteParser.pure m
  | .reg _ => ByteParser.fail

/-- A register operand (`mod = 11`), or reject. -/
def regP (rex : Option Rex) (mp : ModrmPart) : ByteParser Reg :=
  if mp.1.mod = 3#2 then ByteParser.pure (Silmaril.X86.Ext.mkReg (rex.getD Rex.zero).b mp.1.rm)
  else ByteParser.fail

/-- The packed binary operation of an opcode of map `0F`, prefix `66`. -/
def binOf (op : Byte) : Option VBin :=
  if op = 0xFC#8 then some .addb else if op = 0xDB#8 then some .and
  else if op = 0xDF#8 then some .andn else if op = 0xEB#8 then some .or
  else if op = 0xEF#8 then some .xor else if op = 0x74#8 then some .cmpeqb
  else if op = 0x76#8 then some .cmpeqd else if op = 0x64#8 then some .cmpgtb
  else if op = 0xDA#8 then some .minub else none

/-- The body of a VEX form: opcode and ModRM. -/
def vexBody (v : Vex) (op : Byte) : ByteParser Instr :=
  ByteParser.bind pM fun mp =>
  let rex := v.rex
  let d := xregOf rex mp
  let s := xrmOf rex mp
  let vreg : XReg := XReg.ofBitVec v.v
  let noV := v.v = 0#4
  if v.map = 1#5 then
    if v.pp = 1#2 then
      match binOf op with
      | some b => ByteParser.pure (.vbin b v.l d vreg s)
      | none =>
        if op = 0x6E#8 ∧ v.l = false ∧ noV then
          ByteParser.pure (.vmovToX v.w d (Silmaril.X86.Ext9.rmOf rex mp))
        else if op = 0x7E#8 ∧ v.l = false ∧ noV then
          ByteParser.pure (.vmovFromX v.w (Silmaril.X86.Ext9.rmOf rex mp) d)
        else if op = 0xD6#8 ∧ v.l = false ∧ noV then ByteParser.pure (.vmovqStore s d)
        else if op = 0x6F#8 ∧ noV then ByteParser.pure (.vload true v.l d s)
        else if op = 0x7F#8 ∧ noV then ByteParser.pure (.vstore true v.l s d)
        else if op = 0xE7#8 ∧ noV then
          ByteParser.map (fun m => .vstore true v.l (.mem m) d) (memP rex mp)
        else if op = 0xD7#8 ∧ noV then
          ByteParser.map (fun r => .vpmovmskb v.l (Silmaril.X86.Ext9.regOf rex mp)
            (Silmaril.X86.Sse9.xOf r)) (regP rex mp)
        else ByteParser.fail
    else if v.pp = 2#2 then
      if op = 0x6F#8 ∧ noV then ByteParser.pure (.vload false v.l d s)
      else if op = 0x7F#8 ∧ noV then ByteParser.pure (.vstore false v.l s d)
      else if op = 0x7E#8 ∧ v.l = false ∧ noV then ByteParser.pure (.vmovqLoad d s)
      else ByteParser.fail
    else ByteParser.fail
  else if v.map = 2#5 then
    let gd := Silmaril.X86.Ext9.regOf rex mp
    let gs := Silmaril.X86.Ext9.rmOf rex mp
    let gv : Reg := Reg.ofBitVec v.v
    if v.pp = 1#2 ∧ op = 0x78#8 ∧ noV ∧ v.w = false then ByteParser.pure (.vbcast false v.l d s)
    else if v.pp = 1#2 ∧ op = 0x58#8 ∧ noV ∧ v.w = false then ByteParser.pure (.vbcast true v.l d s)
    else if v.pp = 1#2 ∧ op = 0x3B#8 then ByteParser.pure (.vbin .minud v.l d vreg s)
    else if v.l = false ∧ op = 0xF5#8 ∧ v.pp = 0#2 then ByteParser.pure (.bmi .bzhi v.w gd gs gv)
    else if v.l = false ∧ op = 0xF7#8 ∧ v.pp = 1#2 then ByteParser.pure (.bmi .shlx v.w gd gs gv)
    else if v.l = false ∧ op = 0xF7#8 ∧ v.pp = 3#2 then ByteParser.pure (.bmi .shrx v.w gd gs gv)
    else if v.l = false ∧ op = 0xF7#8 ∧ v.pp = 2#2 then ByteParser.pure (.bmi .sarx v.w gd gs gv)
    else if v.l = false ∧ op = 0xF3#8 ∧ v.pp = 0#2 ∧ mp.1.reg = 2#3 then
      ByteParser.pure (.blsmsk v.w gv gs)
    else ByteParser.fail
  else ByteParser.fail

/-- `vzeroupper` (`C5 F8 77`) has no ModRM. -/
def isVzu (v : Vex) (op : Byte) : Bool :=
  v.map = 1#5 && v.pp = 0#2 && v.l = false && v.v = 0#4 && op = 0x77#8

/-- A VEX form after its prefix fields. -/
def vexRest (v : Vex) : ByteParser Instr :=
  ByteParser.bind ByteParser.byte fun op =>
    if isVzu v op then ByteParser.pure .vzeroupper else vexBody v op

/-- The legacy forms of the layer, after the head. -/
def pLegacy (pfx : Pfx) (rex : Option Rex) : Opc → ByteParser Instr
  | .one b =>
    if b = 0xA4#8 ∧ pfx = .rep ∧ rex = none then ByteParser.pure .repMovsb
    else if b = 0xAA#8 ∧ pfx = .rep ∧ rex = none then ByteParser.pure .repStosb
    else if b = 0xFE#8 ∧ pfx = .none then
      ByteParser.bind pM fun mp =>
        if (mp.1.reg = 0#3 ∨ mp.1.reg = 1#3) ∧ (rex.isSome ∨ mp.1.rm.toNat < 4) then
          ByteParser.map (fun r => .un8 (if mp.1.reg = 0#3 then .inc else .dec) r) (regP rex mp)
        else ByteParser.fail
    else if b = 0xFF#8 ∧ pfx = .opsize ∧ (rex.getD Rex.zero).w = false then
      ByteParser.bind pM fun mp =>
        if mp.1.reg = 0#3 ∨ mp.1.reg = 1#3 then
          ByteParser.map (fun r => .un16 (if mp.1.reg = 0#3 then .inc else .dec) r) (regP rex mp)
        else ByteParser.fail
    else if b = 0xF7#8 ∧ pfx = .opsize ∧ (rex.getD Rex.zero).w = false then
      ByteParser.bind pM fun mp =>
        if mp.1.reg = 2#3 then ByteParser.map (fun r => .un16 .not r) (regP rex mp)
        else ByteParser.fail
    else ByteParser.fail
  | .two b =>
    if b = 0x18#8 ∧ pfx = .none then
      ByteParser.bind pM fun mp =>
        if mp.1.reg.toNat < 4 then ByteParser.map (fun _ => .prefetch) (memP rex mp)
        else ByteParser.fail
    else if b = 0xE7#8 ∧ pfx = .opsize ∧ (rex.getD Rex.zero).w = false then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun m => .movntdq m (xregOf rex mp)) (memP rex mp)
    else if b = 0xAB#8 ∧ pfx = .none then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun r => .btsR (rex.getD Rex.zero).w r (Silmaril.X86.Ext9.regOf rex mp))
          (regP rex mp)
    else if b = 0x38#8 ∧ pfx = .none then
      ByteParser.bind ByteParser.byte fun op =>
        if op = 0xF0#8 ∨ op = 0xF1#8 then
          ByteParser.bind pM fun mp =>
            ByteParser.map (fun m => .movbe (op = 0xF0#8) (Sz.ofW (rex.getD Rex.zero).w)
              (Silmaril.X86.Ext9.regOf rex mp) m) (memP rex mp)
        else ByteParser.fail
    else ByteParser.fail

/-- The two-byte VEX prefix's fields. -/
def vex2 (b1 : Byte) : Vex :=
  ⟨!b1.getLsbD 7, false, false, false, 1#5, ~~~(b1.extractLsb' 3 4), b1.getLsbD 2, b1.extractLsb' 0 2⟩

/-- The three-byte VEX prefix's fields. -/
def vex3 (b1 b2 : Byte) : Vex :=
  ⟨!b1.getLsbD 7, !b1.getLsbD 6, !b1.getLsbD 5, b2.getLsbD 7, b1.extractLsb' 0 5,
    ~~~(b2.extractLsb' 3 4), b2.getLsbD 2, b2.extractLsb' 0 2⟩

/-- `lea` with the 32-bit address-size prefix, after the `67`. -/
def pLea32 : ByteParser Instr :=
  ByteParser.bind pHead fun h =>
    if h.1 = false ∧ h.2.1 = .none ∧ h.2.2.2 = .one 0x8D#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun m => .lea32 (Silmaril.X86.Ext9.regOf h.2.2.1 mp) m) (memP h.2.2.1 mp)
    else ByteParser.fail

/-- The parser of the layer's forms: a VEX form (`C5`, `C4`), a `67`-prefixed `lea`, or a
legacy form (no FS override). -/
def pNew : ByteParser Instr :=
  ByteParser.bind ByteParser.byte fun b0 =>
    if b0 = 0xC5#8 then ByteParser.bind ByteParser.byte fun b1 => vexRest (vex2 b1)
    else if b0 = 0xC4#8 then
      ByteParser.bind ByteParser.byte fun b1 => ByteParser.bind ByteParser.byte fun b2 =>
        vexRest (vex3 b1 b2)
    else if b0 = 0x67#8 then pLea32
    else if b0 = 0x64#8 then ByteParser.fail
    else ByteParser.bind (Silmaril.X86.Ext.pAfterSeg false b0) fun h =>
      if h.1 = true then ByteParser.fail else pLegacy h.2.1 h.2.2.1 h.2.2.2

/-- Decode a form of the layer. -/
def decodeNew (w : List Byte) : Option (Instr × Nat) :=
  match pNew w with
  | .ok i rest => some (i, w.length - rest.length)
  | _ => none

/-- `Str9G`'s own parser rejects the slice (stable under appending). -/
def gBad (w : List Byte) : Bool :=
  match Silmaril.X86.Str9G.pNew w with
  | .bad => true
  | _ => false

/-- The listing decoder of the layer's forms: every lower decoder rejects the slice in a way
no following byte changes, and `decodeNew` reads a form of 2 to 15 bytes. -/
def decodeL (w : List Byte) : Option (Instr × Nat) :=
  match decodeNew w with
  | some (i, n) =>
    if Silmaril.X86.Ext.decode w = none ∧ Silmaril.X86.Open9.newBad w = true ∧
        Silmaril.X86.Open9.rawNotEof w = true ∧ Silmaril.X86.Str9.ext9Bad w = true ∧
        Silmaril.X86.Str9Fs.strBad w = true ∧ Silmaril.X86.Str9FsX.atomicBad w = true ∧
        Silmaril.X86.Str9FsX.fsBad w = true ∧ Silmaril.X86.Str9FsX.sseBad w = true ∧
        Silmaril.X86.Str9G.stosdBad w = true ∧ gBad w = true ∧ 2 ≤ n ∧ n ≤ maxInstrLength
    then some (i, n) else none
  | none => none

/-! ## Semantics -/

open Silmaril.X86.Str9G (byteOf ofBytes bytewise cmpeqb minub movmskb)

/-- Dword `i` of a 128-bit value. -/
def dwOf (v : Sse9.Xmm) (i : Nat) : BitVec 32 := v.extractLsb' (32 * i) 32

/-- The 128-bit value with dwords `f 0, …, f 3`. -/
def ofDws (f : Nat → BitVec 32) : Sse9.Xmm :=
  BitVec.ofNat 128 ((List.range 4).map fun i => (f i).toNat * 2 ^ (32 * i)).sum

/-- One 128-bit lane of a packed operation. -/
def lane (op : VBin) (a b : Sse9.Xmm) : Sse9.Xmm :=
  match op with
  | .addb => bytewise (· + ·) a b
  | .and => a &&& b
  | .andn => (~~~a) &&& b
  | .or => a ||| b
  | .xor => a ^^^ b
  | .cmpeqb => cmpeqb a b
  | .cmpeqd => ofDws fun i => if dwOf a i = dwOf b i then 0xFFFFFFFF#32 else 0#32
  | .cmpgtb => bytewise (fun x y => if y.toInt < x.toInt then 0xFF#8 else 0#8) a b
  | .minub => minub a b
  | .minud => ofDws fun i => if (dwOf a i).toNat ≤ (dwOf b i).toNat then dwOf a i else dwOf b i

/-- The little-endian value of `n` bytes at `a`. -/
def loadV (memory : Memory) (a : Word) (n : Nat) : Option (BitVec (8 * n)) :=
  (memory.readBytes a.toNat n).map fun bs => BitVec.ofNat (8 * n) (Silmaril.X86.Ext.leValue bs)

/-- The little-endian bytes of a value. -/
def leN (n : Nat) (v : BitVec (8 * n)) : List Byte :=
  List.ofFn fun i : Fin n => v.extractLsb' (8 * i.val) 8

/-- A 128/256-bit operand: `(lo, hi)`. -/
def readV (wide : Bool) (src : Sse9.XRM) (v : VState) (next : Word) : Option (Sse9.Xmm × Sse9.Xmm) :=
  match src with
  | .reg r => some (v.g.x.xmm r, if wide then v.hi r else 0)
  | .mem m =>
    if wide then
      (loadV v.g.x.m.memory (m.addr v.g.x.m.core next) 32).map fun x =>
        (x.extractLsb' 0 128, x.extractLsb' 128 128)
    else (loadV v.g.x.m.memory (m.addr v.g.x.m.core next) 16).map fun x => (x.extractLsb' 0 128, 0)

/-- Write a vector register: `lo`, and `hi` (zero for a VEX.128 form). -/
def writeV (v : VState) (next : Word) (d : XReg) (lo hi : Sse9.Xmm) (memory : Memory) : VState :=
  ⟨{ v.g with x := ⟨⟨{ v.g.x.m.core with rip := next }, memory⟩,
      Silmaril.Machine.RegisterFile.write v.g.x.xmm d lo⟩ },
    Silmaril.Machine.RegisterFile.write v.hi d hi⟩

/-- A new core and memory, the vector registers kept. -/
def coreV (v : VState) (c : State) (memory : Memory) : VState :=
  ⟨{ v.g with x := ⟨⟨c, memory⟩, v.g.x.xmm⟩ }, v.hi⟩

/-- The address is a multiple of `n`. -/
def alignedAt (a : Word) (n : Nat) : Bool := a.toNat % n == 0

/-- The flags of `bzhi`: ZF and SF of the result, CF when the index is past the width. -/
def bzhiFlags {n : Nat} (r : BitVec n) (cf : Bool) : Silmaril.X86.Flags :=
  ⟨some cf, none, none, some (r == 0#n), some r.msb, some false⟩

/-- Execute a form of the layer, given the address of the next instruction. -/
def execV (i : Instr) (v : VState) (next : Word) : Option VState :=
  let s := v.g.x.m.core
  let memory := v.g.x.m.memory
  let x := v.g.x.xmm
  match i with
  | .repMovsb =>
    if s.read .rcx = 0 then some (coreV v { s with rip := next } memory)
    else
      match loadN memory (s.read .rsi) 1 with
      | none => none
      | some b =>
        match storeN memory (s.read .rdi) 1 b with
        | none => none
        | some memory' =>
          let t := ((s.write .rsi (s.read .rsi + 1)).write .rdi (s.read .rdi + 1)).write .rcx
            (s.read .rcx - 1)
          some (coreV v { t with rip := if s.read .rcx - 1 = 0 then next else s.rip } memory')
  | .repStosb =>
    if s.read .rcx = 0 then some (coreV v { s with rip := next } memory)
    else
      match storeN memory (s.read .rdi) 1 ((s.read .rax).setWidth 8 |>.setWidth 64) with
      | none => none
      | some memory' =>
        let t := (s.write .rdi (s.read .rdi + 1)).write .rcx (s.read .rcx - 1)
        some (coreV v { t with rip := if s.read .rcx - 1 = 0 then next else s.rip } memory')
  | .un8 op r =>
    let a := (s.read r).setWidth 8
    let res : BitVec 8 := match op with | .inc => a + 1 | .dec => a - 1 | .not => ~~~a
    let f := match op with
      | .inc => Silmaril.X86.Ext.incFlagsN a s.flags
      | .dec => Silmaril.X86.Ext.decFlagsN a s.flags
      | .not => s.flags
    some (coreV v { Silmaril.X86.Ext.writeByte s r res with rip := next, flags := f } memory)
  | .un16 op r =>
    let a := (s.read r).setWidth 16
    let res : BitVec 16 := match op with | .inc => a + 1 | .dec => a - 1 | .not => ~~~a
    let f := match op with
      | .inc => Silmaril.X86.Ext.incFlagsN a s.flags
      | .dec => Silmaril.X86.Ext.decFlagsN a s.flags
      | .not => s.flags
    let t := s.write r ((s.read r &&& ~~~(0xFFFF#64)) ||| res.setWidth 64)
    some (coreV v { t with rip := next, flags := f } memory)
  | .btsR q d src =>
    let w := if q then 64 else 32
    let idx := (s.read src).toNat % w
    let a := s.read d
    let bit := a.getLsbD idx
    let r : Word := a ||| (1#64 <<< idx)
    let r' : Word := if q then r else (r.setWidth 32).setWidth 64
    let f : Silmaril.X86.Flags :=
      ⟨some bit, none, none, s.flags.zero, none, none⟩
    some (coreV v { s.write d r' with rip := next, flags := f } memory)
  | .lea32 d m =>
    some (coreV v { s.write d (((m.addr s next).setWidth 32).setWidth 64) with rip := next } memory)
  | .prefetch => some (coreV v { s with rip := next } memory)
  | .movntdq m r =>
    let a := m.addr s next
    if alignedAt a 16 then
      (memory.writeBytes a.toNat (Silmaril.X86.Sse9.le128 (x r))).map fun mem' =>
        coreV v { s with rip := next } mem'
    else none
  | .movbe load sz r m =>
    let a := m.addr s next
    if load then
      (loadN memory a sz.bytes).map fun w =>
        let val : Word := if sz = .q then Silmaril.X86.Ext.byteSwap64 w
          else (Silmaril.X86.Ext.byteSwap32 (w.setWidth 32)).setWidth 64
        coreV v { s.write r val with rip := next } memory
    else
      let val : Word := if sz = .q then Silmaril.X86.Ext.byteSwap64 (s.read r)
        else (Silmaril.X86.Ext.byteSwap32 ((s.read r).setWidth 32)).setWidth 64
      (storeN memory a sz.bytes val).map fun mem' => coreV v { s with rip := next } mem'
  | .vmovToX q d src =>
    let sz : Sz := if q then .q else .d
    (Silmaril.X86.Ext.readRM sz src s memory next).map fun val =>
      writeV v next d (val.setWidth 128) 0 memory
  | .vmovFromX q dst r =>
    let sz : Sz := if q then .q else .d
    (Silmaril.X86.Ext.writeRM sz dst ((x r).setWidth sz.bits) s memory next).map fun (t, mem') =>
      coreV v { t with rip := next } mem'
  | .vmovqLoad d src =>
    match src with
    | .reg r => some (writeV v next d (((x r).setWidth 64).setWidth 128) 0 memory)
    | .mem m => (loadN memory (m.addr s next) 8).map fun val =>
        writeV v next d (val.setWidth 128) 0 memory
  | .vmovqStore dst r =>
    match dst with
    | .reg d => some (writeV v next d (((x r).setWidth 64).setWidth 128) 0 memory)
    | .mem m => (storeN memory (m.addr s next) 8 ((x r).setWidth 64)).map fun mem' =>
        coreV v { s with rip := next } mem'
  | .vload aligned wide d src =>
    let ok := match src with
      | .reg _ => true
      | .mem m => !aligned || alignedAt (m.addr s next) (if wide then 32 else 16)
    if ok then (readV wide src v next).map fun (lo, hi) => writeV v next d lo hi memory else none
  | .vstore aligned wide dst r =>
    match dst with
    | .reg d => some (writeV v next d (x r) (if wide then v.hi r else 0) memory)
    | .mem m =>
      let a := m.addr s next
      if !aligned || alignedAt a (if wide then 32 else 16) then
        let bytes := Silmaril.X86.Sse9.le128 (x r) ++
          (if wide then Silmaril.X86.Sse9.le128 (v.hi r) else [])
        (memory.writeBytes a.toNat bytes).map fun mem' => coreV v { s with rip := next } mem'
      else none
  | .vbin op wide d a src =>
    (readV wide src v next).map fun (lo, hi) =>
      writeV v next d (lane op (x a) lo) (if wide then lane op (v.hi a) hi else 0) memory
  | .vpmovmskb wide r src =>
    let m := if wide then movmskb (x src) ||| (movmskb (v.hi src) <<< 16) else movmskb (x src)
    some (coreV v { s.write r m with rip := next } memory)
  | .vbcast dw wide d src =>
    let k := if dw then 4 else 1
    let val : Option (BitVec 32) := match src with
      | .reg r => some ((x r).setWidth 32)
      | .mem m => (loadN memory (m.addr s next) k).map fun w => w.setWidth 32
    val.map fun e =>
      let b : Sse9.Xmm := if dw then ofDws fun _ => e else ofBytes fun _ => e.setWidth 8
      writeV v next d b (if wide then b else 0) memory
  | .vzeroupper =>
    some ⟨{ v.g with x := ⟨⟨{ s with rip := next }, memory⟩, x⟩ }, fun _ => 0⟩
  | .bmi op q d src vr =>
    let sz : Sz := if q then .q else .d
    (Silmaril.X86.Ext.readRM sz src s memory next).map fun a =>
      let w := sz.bits
      let c := sz.read s vr
      match op with
      | .bzhi =>
        let n := (c.setWidth 8).toNat
        let r : BitVec sz.bits := if n < w then a &&& (BitVec.allOnes w >>> (w - n)) else a
        coreV v { sz.write s d r with rip := next, flags := bzhiFlags r (decide (w ≤ n)) } memory
      | .shlx => coreV v { sz.write s d (a <<< (c.toNat % w)) with rip := next } memory
      | .shrx => coreV v { sz.write s d (a >>> (c.toNat % w)) with rip := next } memory
      | .sarx => coreV v { sz.write s d (a.sshiftRight (c.toNat % w)) with rip := next } memory
  | .blsmsk q vr src =>
    let sz : Sz := if q then .q else .d
    (Silmaril.X86.Ext.readRM sz src s memory next).map fun a =>
      let r := a ^^^ (a - 1)
      let f : Silmaril.X86.Flags := ⟨some (a == 0), none, none, some false, some r.msb, some false⟩
      coreV v { sz.write s vr r with rip := next, flags := f } memory

/-! ## Fetch and step -/

/-- Fetch a form of the layer. -/
def fetchNew (memory : Memory) (address : Nat) : Option (Option (Instr × Nat)) :=
  (decodeNew (fetchWindow memory maxInstrLength address)).map fun (i, n) =>
    if memory.Permitted .execute address n then some (i, n) else none

/-- Some lower layer claims the bytes at `rip` (decodes them, or faults fetching them). -/
def lowerClaims (g : GState) : Bool :=
  let mem := g.x.m.memory
  let a := g.x.m.core.rip.toNat
  match Silmaril.X86.Ext8.fetch mem a with
  | .inl .undecodable =>
    (Silmaril.X86.Ext9.fetchNew mem a).isSome || (Silmaril.X86.Str9.fetchStr mem a).isSome ||
      (Silmaril.X86.Str9Fs.fetchNew mem a).isSome || (Silmaril.X86.Sse9.fetchSse mem a).isSome ||
      (Silmaril.X86.Str9FsX.fetchStosd mem a).isSome ||
      (Silmaril.X86.Str9G.fetchNew mem a).isSome
  | _ => true

/-- **One step**: `Str9G.step` with the upper halves kept, where a lower layer claims the
bytes; otherwise a form of this layer. -/
def step (v : VState) : Option VState :=
  if lowerClaims v.g then (Silmaril.X86.Str9G.step v.g).map fun g => ⟨g, v.hi⟩
  else
    match fetchNew v.g.x.m.memory v.g.x.m.core.rip.toNat with
    | some (some (i, n)) => execV i v (v.g.x.m.core.rip + BitVec.ofNat 64 n)
    | _ => none

end Silmaril.X86.Str9V
