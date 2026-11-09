module

public import Silmaril.X86.Open9.Defs
public import Silmaril.X86.Sse9.Defs

/-!
# `Atomic9`: the open `Ext9` machine with sequential atomics, fences and `pause`

`Ext9`/`Open9` have no `lock` prefix, no `xchg`, `xadd`, `cmpxchg`, no fences and no `pause`
(gcc's `__atomic_thread_fence(__ATOMIC_SEQ_CST)` is `lock or qword ptr [rsp],0`, common in
optimised code). `Atomic9` adds them,
the way `Sse9` adds the SSE moves: a **sibling over `Open9`**, not stacked on `Sse9`.

* `step` is `Open9.step`, and on bytes that `Ext8` and `Ext9` both reject, an atomic form.
  It is meant as a **conservative extension**: every `Open9` step is a step, so every
  open/`Open9` contract carries over (not proved here).
* `decode` is the listing decoder: `Open9.decode` first, then `decodeL`, which accepts an
  atomic form only where the machine's fetch reaches it (checked on each listing by `decide`).
* `tag` is the ordering/atomicity tag that the memory-event interface (`Silmaril.X86.MemEvent`)
  and a TSO machine consume. Sequentially it has no effect.
* The opcodes are disjoint from `Sse9`'s (`F0` prefix, `86/87`, `0F B0/B1/C1`, `0F BA /5`,
  `0F AE F0/E8/F8`, `F3 90` against `0F 10/11/28/29/57/62/6C/6E/6F/7E/7F/D6/EF`).

## The forms (Intel SDM Vol. 2)

| Form | Bytes | `New` |
| --- | --- | --- |
| `lock add/or/and/sub/xor m32/64, r` | `F0 REX? 01 09 21 29 31 /r` (memory) | `lockAlu` |
| `lock add/or/and/sub/xor m32/64, imm` | `F0 REX? 81 /d id`, `F0 REX? 83 /d ib` | `lockAluI` |
| `lock add/or/and/sub/xor m8, imm8` | `F0 REX? 80 /d ib` (no REX.W) | `lockAlu8I` |
| `lock inc/dec m32/64` | `F0 REX? FF /0`, `/1` | `lockIncDec` |
| `lock bts m32/64, imm8` | `F0 REX? 0F BA /5 ib` | `lockBts` |
| `[lock] xadd r/m32/64, r` | `[F0] REX? 0F C1 /r` | `xadd` |
| `[lock] cmpxchg r/m32/64, r` | `[F0] REX? 0F B1 /r` | `cmpxchg` |
| `[lock] cmpxchg r/m8, r8` | `[F0] REX? 0F B0 /r` (no REX.W) | `cmpxchg8` |
| `[lock] xchg r/m32/64, r` | `[F0] REX? 87 /r` | `xchg` |
| `[lock] xchg r/m8, r8` | `[F0] REX? 86 /r` (no REX.W) | `xchg8` |
| `xchg r32/64, eax/rax` (short form) | `REX? 91`-`97`, `REX.B 90` | `xchg sz (.reg r) .rax` |
| `mfence`, `lfence`, `sfence` | `0F AE F0`, `0F AE E8`, `0F AE F8` | `fence` |
| `pause` | `F3 90` | `pause` |

With `F0`, a register destination is rejected (it raises `#UD`), and so is `lock cmp`
(`/7`). Rejected (`none`), never misread: the FS override, `66` (16-bit atomics), `F2`, a
repeated `F0`, REX.W on the byte forms, `F0` on the short `xchg`, and every other ModRM digit.
`66 90` (`xchg ax,ax`, the padding `nop`), `90` and `48 90` (without REX.B) are not read
here: `90` and `66 90` are `Ext` forms and are unchanged.

## Sequential semantics, and the documented choices

* `lock op m, …`: exactly the unlocked ALU semantics (`Ext.aluStep`: load, op, flags,
  store). Under SC this is atomic by construction. `lock inc/dec` keeps CF.
* `xadd`: `TEMP := SRC + DEST; SRC := DEST; DEST := TEMP` (in that order, so `xadd r, r` with
  one register leaves the sum), flags as `add`.
* `cmpxchg`: compare the accumulator with `DEST` (flags as `cmp acc, DEST`). If equal,
  `DEST := SRC`. Otherwise the accumulator gets `DEST` (a 32-bit accumulator write
  zero-extends) and **a memory destination is written back with its old value** (SDM: "the
  processor never produces a locked read without also producing a locked write"; so a
  read-only destination faults even when the comparison fails). A register destination is
  not written on failure (as observed on hardware).
* `xchg`: swap. With a memory operand it is implicitly locked (`tag.locked = true`). The short
  form `90+r` is `xchg r, rax`; at 32 bits both registers are zero-extended (only `90` itself,
  `xchg eax, eax`, is special-cased by hardware as `nop`, and it is not read here).
* `bts`: `CF := bit (imm mod size)` of the destination, then the bit is set. OF, SF, AF and PF
  are undefined (SDM), and so is ZF (Intel: unaffected; AMD: undefined; vendor-neutral, as
  for `Ext9`'s `bt`).
* `mfence`, `lfence`, `sfence`, `pause`: they only advance `rip`. Their ordering meaning comes
  only with a TSO model.
* Alignment: a locked access that splits a cache line is legal on x86 (slow; a kernel with
  `split_lock_detect=fatal` raises `SIGBUS`). The model accepts it.

This is a handwritten local model written from the SDM with `Ext`'s helpers, differentially
tested against x86-64 hosts outside this repository, not proved to match hardware.

This module gives the definitions. The conservative-extension, listing and decoder theorems
of the machine are not part of this library yet.
-/

@[expose] public section

namespace Silmaril.X86.Atomic9

open Silmaril.X86 (Reg Word State Flags AluOp Byte MState fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Mem RM Sz Result retire readRM writeRM Rex Opc Pfx ModrmPart PResult
  ByteParser pHead pImm32 aluStep loadN storeN)
open Silmaril.X86.Ext8 (pM optP aluOfDigit RM8 BReg rm8Of reg8Of)
open Silmaril.Process (Memory)

/-! ## Instructions -/

/-- The three fences. -/
inductive FenceKind where
  | mfence | lfence | sfence
  deriving DecidableEq, Repr

/-- The atomic forms. Immediates of the `imm8` forms are stored sign-extended to 32 bits. -/
inductive New where
  /-- `lock op m, r` (`F0 01 09 21 29 31 /r`). -/
  | lockAlu (sz : Sz) (op : AluOp) (dst : Ext.Mem) (src : Reg)
  /-- `lock op m, imm` (`F0 81 /d id`, `F0 83 /d ib`). -/
  | lockAluI (sz : Sz) (op : AluOp) (dst : Ext.Mem) (imm : BitVec 32)
  /-- `lock op m8, imm8` (`F0 80 /d ib`). -/
  | lockAlu8I (op : AluOp) (dst : Ext.Mem) (imm : BitVec 8)
  /-- `lock inc m` (`F0 FF /0`), `lock dec m` (`F0 FF /1`) when `dec`. -/
  | lockIncDec (sz : Sz) (dec : Bool) (dst : Ext.Mem)
  /-- `lock bts m, imm8` (`F0 0F BA /5 ib`). -/
  | lockBts (sz : Sz) (dst : Ext.Mem) (bit : BitVec 8)
  /-- `[lock] xadd r/m, r` (`[F0] 0F C1 /r`). -/
  | xadd (sz : Sz) (locked : Bool) (dst : RM) (src : Reg)
  /-- `[lock] cmpxchg r/m, r` (`[F0] 0F B1 /r`). -/
  | cmpxchg (sz : Sz) (locked : Bool) (dst : RM) (src : Reg)
  /-- `[lock] cmpxchg r/m8, r8` (`[F0] 0F B0 /r`). -/
  | cmpxchg8 (locked : Bool) (dst : RM8) (src : BReg)
  /-- `[lock] xchg r/m, r` (`[F0] 87 /r`). -/
  | xchg (sz : Sz) (dst : RM) (src : Reg)
  /-- `[lock] xchg r/m8, r8` (`[F0] 86 /r`). -/
  | xchg8 (dst : RM8) (src : BReg)
  /-- `mfence`, `lfence`, `sfence` (`0F AE F0/E8/F8`). -/
  | fence (k : FenceKind)
  /-- `pause` (`F3 90`). -/
  | pause
  deriving DecidableEq, Repr

/-- Instructions of the machine: those of `Ext9`, and the atomic forms. -/
inductive Instr where
  | open9 (i : Ext9.Instr)
  | new (i : New)
  deriving DecidableEq, Repr

/-! ## Tags -/

/-- The ordering/atomicity tag of an atomic form, consumed by a memory-event interface and a
future TSO machine. `locked`: the `LOCK` prefix, or `xchg` with a memory operand (SDM Vol. 3A
§9.1.2.1). `fence`: an explicit fence (a locked operation also acts as a full fence under
TSO, which the consumer derives from `locked`). -/
structure Tag where
  locked : Bool
  fence : Option FenceKind
  deriving DecidableEq, Repr

/-- `r/m` is a memory operand. -/
def RM.isMem : RM → Bool
  | .mem _ => true
  | .reg _ => false

/-- `r/m8` is a memory operand. -/
def RM8.isMem : RM8 → Bool
  | .mem _ => true
  | .reg _ => false

/-- The tag of an atomic form. -/
def tag : New → Tag
  | .lockAlu .. | .lockAluI .. | .lockAlu8I .. | .lockIncDec .. | .lockBts .. => ⟨true, none⟩
  | .xadd _ l _ _ | .cmpxchg _ l _ _ | .cmpxchg8 l _ _ => ⟨l, none⟩
  | .xchg _ dst _ => ⟨RM.isMem dst, none⟩
  | .xchg8 dst _ => ⟨RM8.isMem dst, none⟩
  | .fence k => ⟨false, some k⟩
  | .pause => ⟨false, none⟩

/-! ## Decoding -/

/-- A memory `r/m` operand, or reject. -/
def memP (rex : Option Rex) (mp : ModrmPart) : ByteParser Ext.Mem :=
  match Ext9.rmOf rex mp with
  | .mem m => ByteParser.pure m
  | .reg _ => ByteParser.fail

/-- A memory operand under `lock`; any `r/m` operand without it. -/
def rmP (locked : Bool) (rex : Option Rex) (mp : ModrmPart) : ByteParser RM :=
  if locked then ByteParser.map RM.mem (memP rex mp) else ByteParser.pure (Ext9.rmOf rex mp)

/-- A memory byte operand under `lock`; any `r/m8` operand without it. -/
def rm8P (locked : Bool) (rex : Option Rex) (mp : ModrmPart) : ByteParser RM8 :=
  if locked then
    match rm8Of rex mp with
    | .mem m => ByteParser.pure (.mem m)
    | .reg _ => ByteParser.fail
  else ByteParser.pure (rm8Of rex mp)

/-- The ALU operation of a locked group-1 digit: `cmp` (`/7`) is not lockable. -/
def lockOp (d : BitVec 3) : Option AluOp :=
  match aluOfDigit d with
  | some .cmp => none
  | o => o

/-- The body of an atomic form after REX and opcode; `locked` when an `F0` came first. -/
def pBody (locked : Bool) (rex : Option Rex) : Opc → ByteParser New
  | .one b =>
    let w := (rex.getD Rex.zero).w
    let sz := Sz.ofW w
    let lo := b.toNat % 8
    let digit : BitVec 3 := BitVec.ofNat 3 (b.toNat / 8)
    if locked ∧ b.toNat < 0x40 ∧ lo = 1 then
      ByteParser.bind (optP (lockOp digit)) fun op =>
        ByteParser.bind pM fun mp =>
          ByteParser.map (fun m => .lockAlu sz op m (Ext9.regOf rex mp)) (memP rex mp)
    else if locked ∧ b = 0x81#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.bind (optP (lockOp mp.1.reg)) fun op =>
          ByteParser.bind (memP rex mp) fun m =>
            ByteParser.map (fun v => .lockAluI sz op m v) pImm32
    else if locked ∧ b = 0x83#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.bind (optP (lockOp mp.1.reg)) fun op =>
          ByteParser.bind (memP rex mp) fun m =>
            ByteParser.map (fun v => .lockAluI sz op m v) Ext9.pIb32
    else if locked ∧ b = 0x80#8 ∧ w = false then
      ByteParser.bind pM fun mp =>
        ByteParser.bind (optP (lockOp mp.1.reg)) fun op =>
          ByteParser.bind (memP rex mp) fun m =>
            ByteParser.map (fun v => .lockAlu8I op m v) ByteParser.byte
    else if locked ∧ b = 0xFF#8 then
      ByteParser.bind pM fun mp =>
        if mp.1.reg = 0#3 ∨ mp.1.reg = 1#3 then
          ByteParser.map (fun m => .lockIncDec sz (mp.1.reg = 1#3) m) (memP rex mp)
        else ByteParser.fail
    else if b = 0x87#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun d => .xchg sz d (Ext9.regOf rex mp)) (rmP locked rex mp)
    else if b = 0x86#8 ∧ w = false then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun d => .xchg8 d (reg8Of rex mp)) (rm8P locked rex mp)
    else if locked = false ∧
        ((0x91 ≤ b.toNat ∧ b.toNat ≤ 0x97) ∨ (b = 0x90#8 ∧ (rex.getD Rex.zero).b = true)) then
      ByteParser.pure
        (.xchg sz (.reg (Silmaril.X86.Ext.mkReg (rex.getD Rex.zero).b (b.extractLsb' 0 3))) .rax)
    else ByteParser.fail
  | .two b =>
    let w := (rex.getD Rex.zero).w
    let sz := Sz.ofW w
    if b = 0xC1#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun d => .xadd sz locked d (Ext9.regOf rex mp)) (rmP locked rex mp)
    else if b = 0xB1#8 then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun d => .cmpxchg sz locked d (Ext9.regOf rex mp)) (rmP locked rex mp)
    else if b = 0xB0#8 ∧ w = false then
      ByteParser.bind pM fun mp =>
        ByteParser.map (fun d => .cmpxchg8 locked d (reg8Of rex mp)) (rm8P locked rex mp)
    else if locked ∧ b = 0xBA#8 then
      ByteParser.bind pM fun mp =>
        if mp.1.reg = 5#3 then
          ByteParser.bind (memP rex mp) fun m =>
            ByteParser.map (fun v => .lockBts sz m v) ByteParser.byte
        else ByteParser.fail
    else if locked = false ∧ rex = none ∧ b = 0xAE#8 then
      ByteParser.bind ByteParser.byte fun c =>
        if c = 0xF0#8 then ByteParser.pure (.fence .mfence)
        else if c = 0xE8#8 then ByteParser.pure (.fence .lfence)
        else if c = 0xF8#8 then ByteParser.pure (.fence .sfence)
        else ByteParser.fail
    else ByteParser.fail

/-- After an `F0`: a second head with no FS override and no legacy prefix, then the body. -/
def pLocked : ByteParser New :=
  ByteParser.bind pHead fun h =>
    if h.1 = false ∧ h.2.1 = .none ∧ h.2.2.2 ≠ .one 0xF0#8 then pBody true h.2.2.1 h.2.2.2
    else ByteParser.fail

/-- The parser of an atomic form. `pHead` reads a leading `F0` as a one-byte opcode with no
prefix and no REX; the locked body follows it. `F3 90` is `pause`. -/
def pNew : ByteParser New :=
  ByteParser.bind pHead fun h =>
    if h.1 = true then ByteParser.fail
    else
      match h.2.1 with
      | .none =>
        if h.2.2.1 = none ∧ h.2.2.2 = .one 0xF0#8 then pLocked
        else pBody false h.2.2.1 h.2.2.2
      | .rep =>
        if h.2.2.1 = none ∧ h.2.2.2 = .one 0x90#8 then ByteParser.pure .pause
        else ByteParser.fail
      | _ => ByteParser.fail

/-- Decode an atomic form; the instruction and the number of bytes consumed. -/
def decodeNew (bytes : List Byte) : Option (New × Nat) :=
  match pNew bytes with
  | .ok i rest => some (i, bytes.length - rest.length)
  | _ => none

/-- The listing decoder of an atomic form: `Ext` rejects the slice, the parsers of `Ext8`'s
and `Ext9`'s new forms reject it, the `Ext` length decoder finishes inside it, and
`decodeNew` reads a form of 1 to 15 bytes. Checked on each listing by `decide`. -/
def decodeL (bytes : List Byte) : Option (New × Nat) :=
  match decodeNew bytes with
  | some (i, n) =>
    if Silmaril.X86.Ext.decode bytes = none ∧ Open9.newBad bytes = true ∧
        Open9.rawNotEof bytes = true ∧ Sse9.ext9Bad bytes = true ∧ 0 < n ∧
        n ≤ maxInstrLength then
      some (i, n)
    else none
  | none => none

/-- The listing decoder of the machine: `Open9.decode` first, then an atomic form. -/
def decode (bytes : List Byte) : Option (Instr × Nat) :=
  match Open9.decode bytes with
  | some (i, n) => some (.open9 i, n)
  | none => (decodeL bytes).map fun (i, n) => (.new i, n)

/-! ## Semantics -/

/-- The flags of `bts`: CF is the tested bit, the rest undefined. -/
def btsFlags (cf : Bool) : Flags := ⟨some cf, none, none, none, none, none⟩

/-- `xadd`: `TEMP := SRC + DEST; SRC := DEST; DEST := TEMP`, flags as `add`. -/
def xaddStep (sz : Sz) (dst : RM) (src : Reg) (s : State) (memory : Memory) (next : Word) :
    Option (State × Memory) :=
  match readRM sz dst s memory next with
  | none => none
  | some x =>
    let y := sz.read s src
    let fl := Silmaril.X86.Ext.addFlagsN x y
    match dst with
    | .reg r => some ({ sz.write (sz.write s src x) r (x + y) with flags := fl }, memory)
    | .mem m =>
      (storeN memory (m.addr s next) sz.bytes ((x + y).setWidth 64)).map fun mem' =>
        ({ sz.write s src x with flags := fl }, mem')

/-- `cmpxchg`: flags of `cmp acc, DEST`; on equality `DEST := SRC`; otherwise
`acc := DEST`, and a memory destination is rewritten with its old value. -/
def cmpxchgStep (sz : Sz) (dst : RM) (src : Reg) (s : State) (memory : Memory) (next : Word) :
    Option (State × Memory) :=
  match readRM sz dst s memory next with
  | none => none
  | some x =>
    let a := sz.read s .rax
    let fl := Silmaril.X86.Ext.subFlagsN a x
    if a = x then
      (writeRM sz dst (sz.read s src) s memory next).map fun r => ({ r.1 with flags := fl }, r.2)
    else
      match dst with
      | .reg _ => some ({ sz.write s .rax x with flags := fl }, memory)
      | .mem m =>
        (storeN memory (m.addr s next) sz.bytes (x.setWidth 64)).map fun mem' =>
          ({ sz.write s .rax x with flags := fl }, mem')

/-- `cmpxchg r/m8, r8` with accumulator `AL`. -/
def cmpxchg8Step (dst : RM8) (src : BReg) (s : State) (memory : Memory) (next : Word) :
    Option (State × Memory) :=
  match dst.read s memory next with
  | none => none
  | some x =>
    let a := (BReg.low .rax).read s
    let fl := Silmaril.X86.Ext.subFlagsN a x
    if a = x then
      (dst.write (src.read s) s memory next).map fun r => ({ r.1 with flags := fl }, r.2)
    else
      match dst with
      | .reg _ => some ({ (BReg.low .rax).write s x with flags := fl }, memory)
      | .mem m =>
        (storeN memory (m.addr s next) 1 (x.setWidth 64)).map fun mem' =>
          ({ (BReg.low .rax).write s x with flags := fl }, mem')

/-- `xchg r/m, r`: swap (the destination is written first, then the register). -/
def xchgStep (sz : Sz) (dst : RM) (src : Reg) (s : State) (memory : Memory) (next : Word) :
    Option (State × Memory) :=
  match readRM sz dst s memory next with
  | none => none
  | some x =>
    (writeRM sz dst (sz.read s src) s memory next).map fun r => (sz.write r.1 src x, r.2)

/-- `xchg r/m8, r8`. -/
def xchg8Step (dst : RM8) (src : BReg) (s : State) (memory : Memory) (next : Word) :
    Option (State × Memory) :=
  match dst.read s memory next with
  | none => none
  | some x => (dst.write (src.read s) s memory next).map fun r => (src.write r.1 x, r.2)

/-- `lock inc/dec m`: as `Ext`'s `incdec`, CF kept. -/
def incDecStep (sz : Sz) (dec : Bool) (dst : Ext.Mem) (s : State) (memory : Memory) (next : Word) :
    Option (State × Memory) :=
  match readRM sz (.mem dst) s memory next with
  | none => none
  | some x =>
    (writeRM sz (.mem dst) (if dec then x - 1#sz.bits else x + 1#sz.bits) s memory next).map
      fun r => ({ r.1 with flags := if dec then Silmaril.X86.Ext.decFlagsN x s.flags
        else Silmaril.X86.Ext.incFlagsN x s.flags }, r.2)

/-- `lock bts m, imm8`: CF := the bit `imm mod size`, then set it. -/
def btsStep (sz : Sz) (dst : Ext.Mem) (bit : BitVec 8) (s : State) (memory : Memory) (next : Word) :
    Option (State × Memory) :=
  match readRM sz (.mem dst) s memory next with
  | none => none
  | some x =>
    let k := bit.toNat % sz.bits
    (writeRM sz (.mem dst) (x ||| (1#sz.bits <<< k)) s memory next).map fun r =>
      ({ r.1 with flags := btsFlags (x.getLsbD k) }, r.2)

/-- **Execute an atomic form**, given the address of the next instruction. -/
def execNew (i : New) (s : State) (memory : Memory) (next : Word) : Result :=
  match i with
  | .lockAlu sz op dst src => retire next (aluStep sz op (.mem dst) (sz.read s src) s memory next)
  | .lockAluI sz op dst imm =>
    retire next (aluStep sz op (.mem dst) (imm.signExtend sz.bits) s memory next)
  | .lockAlu8I op dst imm => retire next (Silmaril.X86.Ext8.alu8 op (.mem dst) imm s memory next)
  | .lockIncDec sz dec dst => retire next (incDecStep sz dec dst s memory next)
  | .lockBts sz dst bit => retire next (btsStep sz dst bit s memory next)
  | .xadd sz _ dst src => retire next (xaddStep sz dst src s memory next)
  | .cmpxchg sz _ dst src => retire next (cmpxchgStep sz dst src s memory next)
  | .cmpxchg8 _ dst src => retire next (cmpxchg8Step dst src s memory next)
  | .xchg sz dst src => retire next (xchgStep sz dst src s memory next)
  | .xchg8 dst src => retire next (xchg8Step dst src s memory next)
  | .fence _ => retire next (some (s, memory))
  | .pause => retire next (some (s, memory))

/-- Execute an instruction of the machine with its consumed byte length. -/
def exec (i : Instr) (s : State) (memory : Memory) (length : Nat) : Result :=
  match i with
  | .open9 i => Ext9.exec i s memory length
  | .new i => execNew i s memory (s.rip + BitVec.ofNat 64 length)

/-! ## Fetch and step -/

/-- Fetch an atomic form: `decodeNew` reads the fetch window and the bytes it consumed are
executable. `none` if not decodable as an atomic form; `some none` if not fetchable. -/
def fetchNew (memory : Memory) (address : Nat) : Option (Option (New × Nat)) :=
  (decodeNew (fetchWindow memory maxInstrLength address)).map fun (i, n) =>
    if memory.Permitted .execute address n then some (i, n) else none

/-- **One step**: `Open9.step`; on bytes that neither `Ext8` nor `Ext9` decodes, an atomic
form. -/
def step (m : MState) : Option MState :=
  match Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat with
  | .inl .undecodable =>
    match Ext9.fetchNew m.memory m.core.rip.toNat with
    | some (some (i, n)) =>
      Open.ofResult (Ext9.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n))
    | some none => none
    | none =>
      match fetchNew m.memory m.core.rip.toNat with
      | some (some (i, n)) =>
        Open.ofResult (execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n))
      | _ => none
  | _ => Open.step m

/-! ## Opcode tables (for the disjointness checks) -/

/-- The `Sse9` opcode bytes after `0F` (`Silmaril/X86/Sse9/Defs.lean`, `pBody`). -/
def sse9Opcodes : List Byte :=
  [0x10, 0x11, 0x28, 0x29, 0x57, 0x62, 0x6C, 0x6E, 0x6F, 0x7E, 0x7F, 0xD6, 0xEF]

/-- The atomic opcode heads (one representative encoding per opcode). -/
def atomicHeads : List (List Byte) :=
  [[0xF0, 0x01], [0xF0, 0x09], [0xF0, 0x21], [0xF0, 0x29], [0xF0, 0x31], [0xF0, 0x81],
    [0xF0, 0x83], [0xF0, 0x80], [0xF0, 0xFF], [0xF0, 0x0F, 0xBA], [0x87], [0x86],
    [0x0F, 0xC1], [0x0F, 0xB1], [0x0F, 0xB0], [0x0F, 0xAE], [0xF3, 0x90]]

end Silmaril.X86.Atomic9
