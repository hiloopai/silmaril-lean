module

public import Silmaril.X86.Ext.Machine

/-!
# `Ext8`: the 8-bit ALU variant of the extended x86-64 model

`X86.Ext` has 32- and 64-bit ALU forms and a few byte forms (`test8`, `testI8`,
`cmpI8`, `setcc`, `movx`, byte stores). `Ext8` is a **variant** that leaves every
definition and theorem of `X86.Ext` untouched and adds the remaining byte forms
that gcc emits for character code, as written in the Intel SDM (Vol. 2):

| Form | Bytes |
| --- | --- |
| `op r/m8, r8` (ADD OR AND SUB XOR CMP) | `REX? 00 08 20 28 30 38 /r` |
| `op r8, r/m8` | `REX? 02 0A 22 2A 32 3A /r` |
| `op al, imm8` | `04 0C 24 2C 34 3C ib` |
| `op r/m8, imm8` | `REX? 80 /0 /1 /4 /5 /6 /7 ib` |
| `test r/m8, r8` | `REX? 84 /r` |
| `shl`/`shr`/`sar r/m8` by 1, CL, imm8 | `REX? D0 / D2 / C0 /4 /5 /7 (ib)` |
| `mov r/m8, r8`; `mov r8, r/m8` | `REX? 88 /r`; `REX? 8A /r` |
| `movzx`/`movsx r32/r64, r/m8` | `REX? 0F B6 / 0F BE /r` |
| `setcc r/m8` | `REX? 0F 90+cc /0` |

with all byte registers, **including the legacy high-byte registers** AH, CH, DH,
BH (register fields 4-7 without a REX prefix; with any REX prefix the same fields
name SPL, BPL, SIL, DIL). ADC and SBB (`/2`, `/3`), 8-bit rotates, the `66` and
`F3` prefixes, REX.W on the 8-bit forms and the FS override are rejected
(`none`), never misread.

## How the variant is put together

`Instr` is `base (i : Ext.Instr)` or `new (i : New)`. `decode` tries `Ext.decode`
first and only falls back to `decodeNew` when `Ext.decode` fails, so

* `decode_of_ext`: wherever `Ext.decode` decodes, `decode` returns the same
  instruction (wrapped in `base`) with the same length;
* `exec_base`: `exec (.base i)` is `Ext.exec i`;
* `fetch_of_ext`, `step_of_ext`: the same for fetch and the machine step, so every
  retirement, return and fault of `Ext.step` other than `undecodable` is the same
  outcome of `Ext8.step` (`step_eq_of_ne_undecodable`), and every `Ext.Returns`
  run is an `Ext8.Returns` run (`returns_of_ext`).

The new forms overlap `Ext` (for example `84 /r` with low-byte registers): the
overlap is harmless because `Ext` is tried first, and the `New` semantics agree
with `Ext` there anyway (they are written from the same SDM text).

`decodeNew` is a direct ModRM decoder (it does not require canonical encodings);
it reuses `Ext`'s length decoder pieces (`pHead`, `pModrm`) and memory-operand
decoder `decodeMem`. This is a handwritten local model, checked by native
difftests (`scripts/x86/ext8-difftest.py`), not derived from Sail or ACL2.

## Flags (SDM)

* ADD/SUB/CMP/AND/OR/XOR/TEST at 8 bits: `AluOp.flagsN`, `logicFlagsN` at width 8.
* SHL/SHR/SAR r/m8: the count is masked to 5 bits (`& 1FH`), so it may exceed
  the operand width. For `c < 8` the flags are `ShiftOp.flags`. For `8 ≤ c`,
  SHL/SHR leave CF undefined (SDM: "CF is undefined for SHL and SHR where the
  count is greater than or equal to the size of the destination"), SAR sets CF to
  the sign bit (the last bit shifted out), OF and AF are undefined, and SF, ZF, PF
  follow the result. A zero masked count leaves the flags unchanged.
-/

@[expose] public section

namespace Silmaril.X86.Ext8

open Silmaril.X86 (Reg Word State Flags AluOp Byte MState fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Mem Sz Cond ShiftOp Count Result retire loadN storeN writeByte
  Rex Opc Pfx ModRM ModrmPart PResult mkReg decodeMem pHead pModrm)
open Silmaril.Process (Memory)

/-! ## Byte registers -/

/-- A byte register: the low byte of any of the sixteen registers, or a legacy
high byte (`high r` for `r` one of RAX, RCX, RDX, RBX: AH, CH, DH, BH). -/
inductive BReg where
  | low (r : Reg)
  | high (r : Reg)
  deriving DecidableEq, Repr

/-- The byte register named by a three-bit field with REX extension `ext`. With a
REX prefix fields 4-7 are SPL, BPL, SIL, DIL; without one they are AH, CH, DH, BH. -/
def BReg.ofField (rex : Option Rex) (ext : Bool) (f : BitVec 3) : BReg :=
  match rex with
  | some _ => .low (mkReg ext f)
  | none => if f.toNat < 4 then .low (mkReg false f) else .high (mkReg false (f - 4#3))

def BReg.read (s : State) : BReg → BitVec 8
  | .low r => (s.read r).setWidth 8
  | .high r => (s.read r).extractLsb' 8 8

/-- Write a byte register: only its eight bits change. -/
def BReg.write (s : State) : BReg → BitVec 8 → State
  | .low r, v => writeByte s r v
  | .high r, v => s.write r ((s.read r &&& ~~~(0xFF00#64)) ||| (v.setWidth 64 <<< 8))

/-- A byte `r/m` operand. -/
inductive RM8 where
  | reg (b : BReg)
  | mem (m : Mem)
  deriving DecidableEq, Repr

def RM8.read (op : RM8) (s : State) (memory : Memory) (next : Word) : Option (BitVec 8) :=
  match op with
  | .reg b => some (b.read s)
  | .mem m => (loadN memory (m.addr s next) 1).map fun v => v.setWidth 8

def RM8.write (op : RM8) (v : BitVec 8) (s : State) (memory : Memory) (next : Word) :
    Option (State × Memory) :=
  match op with
  | .reg b => some (b.write s v, memory)
  | .mem m => (storeN memory (m.addr s next) 1 (v.setWidth 64)).map fun after => (s, after)

/-! ## Instructions -/

/-- The byte forms added by the variant. -/
inductive New where
  /-- `op r/m8, r8` (`00 08 20 28 30 38 /r`). -/
  | alu (op : AluOp) (dst : RM8) (src : BReg)
  /-- `op r8, r/m8` (`02 0A 22 2A 32 3A /r`). -/
  | aluR (op : AluOp) (dst : BReg) (src : RM8)
  /-- `op al, imm8` (`04 0C 24 2C 34 3C ib`). -/
  | aluA (op : AluOp) (imm : BitVec 8)
  /-- `op r/m8, imm8` (`80 /digit ib`). -/
  | aluI (op : AluOp) (dst : RM8) (imm : BitVec 8)
  /-- `test r/m8, r8` (`84 /r`). -/
  | test (dst : RM8) (src : BReg)
  /-- `shl`/`shr`/`sar r/m8` (`D0`, `D2`, `C0 ib`). -/
  | shift (op : ShiftOp) (dst : RM8) (count : Count)
  /-- `mov r/m8, r8` (`88 /r`). -/
  | mov (dst : RM8) (src : BReg)
  /-- `mov r8, r/m8` (`8A /r`). -/
  | movR (dst : BReg) (src : RM8)
  /-- `movzx`/`movsx r32/r64, r/m8` (`0F B6`, `0F BE`). -/
  | movx (sx : Bool) (sz : Sz) (dst : Reg) (src : RM8)
  /-- `setcc r/m8` (`0F 90+cc /0`). -/
  | setcc (c : Cond) (dst : RM8)
  deriving DecidableEq, Repr

/-- Instructions of the variant: those of `X86.Ext`, and the new byte forms. -/
inductive Instr where
  | base (i : Ext.Instr)
  | new (i : New)
  deriving DecidableEq, Repr

/-! ## Decoding the new forms -/

/-- The ALU operation of group-1 digit `d` (`/0 /1 /4 /5 /6 /7`); ADC and SBB
(`/2`, `/3`) are not modeled. -/
def aluOfDigit (d : BitVec 3) : Option AluOp :=
  match d.toNat with
  | 0 => some .add | 1 => some .or | 4 => some .and | 5 => some .sub
  | 6 => some .xor | 7 => some .cmp | _ => none

/-- The shift of digit `d` (`/4 /5 /7`); 8-bit rotates are not modeled. -/
def shiftOfDigit (d : BitVec 3) : Option ShiftOp :=
  match d.toNat with
  | 4 => some .shl | 5 => some .shr | 7 => some .sar | _ => none

/-- The `r/m8` operand of a ModRM part. -/
def rm8Of (rex : Option Rex) (mp : ModrmPart) : RM8 :=
  let r := rex.getD Rex.zero
  if mp.1.mod = 3#2 then .reg (BReg.ofField rex r.b mp.1.rm)
  else .mem (decodeMem false r.x r.b mp.1 mp.2.1 mp.2.2)

/-- The byte register of the ModRM `reg` field. -/
def reg8Of (rex : Option Rex) (mp : ModrmPart) : BReg :=
  BReg.ofField rex (rex.getD Rex.zero).r mp.1.reg

/-- Read a ModRM part and continue. -/
def withModrm (rest : List Byte) (k : ModrmPart → List Byte → Option (New × List Byte)) :
    Option (New × List Byte) :=
  match pModrm true rest with
  | .ok (some mp) rest' => k mp rest'
  | _ => none

/-- Read an imm8 and continue. -/
def withImm8 (rest : List Byte) (k : BitVec 8 → List Byte → Option (New × List Byte)) :
    Option (New × List Byte) :=
  match rest with
  | v :: rest' => k v rest'
  | [] => none

/-- Decode the opcode and operands of a new form, after the head. -/
def decodeBody (rex : Option Rex) : Opc → List Byte → Option (New × List Byte)
  | .one b, rest =>
    let lo := b.toNat % 8
    let digit : BitVec 3 := BitVec.ofNat 3 (b.toNat / 8)
    if b.toNat < 0x40 ∧ lo = 0 then
      (aluOfDigit digit).bind fun op =>
        withModrm rest fun mp r => some (.alu op (rm8Of rex mp) (reg8Of rex mp), r)
    else if b.toNat < 0x40 ∧ lo = 2 then
      (aluOfDigit digit).bind fun op =>
        withModrm rest fun mp r => some (.aluR op (reg8Of rex mp) (rm8Of rex mp), r)
    else if b.toNat < 0x40 ∧ lo = 4 then
      (aluOfDigit digit).bind fun op =>
        withImm8 rest fun v r => some (.aluA op v, r)
    else if b = 0x80#8 then
      withModrm rest fun mp r =>
        (aluOfDigit mp.1.reg).bind fun op =>
          withImm8 r fun v r' => some (.aluI op (rm8Of rex mp) v, r')
    else if b = 0x84#8 then
      withModrm rest fun mp r => some (.test (rm8Of rex mp) (reg8Of rex mp), r)
    else if b = 0x88#8 then
      withModrm rest fun mp r => some (.mov (rm8Of rex mp) (reg8Of rex mp), r)
    else if b = 0x8A#8 then
      withModrm rest fun mp r => some (.movR (reg8Of rex mp) (rm8Of rex mp), r)
    else if b = 0xC0#8 then
      withModrm rest fun mp r =>
        (shiftOfDigit mp.1.reg).bind fun op =>
          withImm8 r fun v r' => some (.shift op (rm8Of rex mp) (.imm v), r')
    else if b = 0xD0#8 then
      withModrm rest fun mp r =>
        (shiftOfDigit mp.1.reg).map fun op => (.shift op (rm8Of rex mp) .one, r)
    else if b = 0xD2#8 then
      withModrm rest fun mp r =>
        (shiftOfDigit mp.1.reg).map fun op => (.shift op (rm8Of rex mp) .cl, r)
    else none
  | .two b, rest =>
    let x := rex.getD Rex.zero
    if b = 0xB6#8 ∨ b = 0xBE#8 then
      withModrm rest fun mp r =>
        some (.movx (b = 0xBE#8) (Sz.ofW x.w) (mkReg x.r mp.1.reg) (rm8Of rex mp), r)
    else if b.toNat / 16 = 9 then
      withModrm rest fun mp r =>
        if mp.1.reg = 0#3 then
          some (.setcc (Cond.ofCode (BitVec.ofNat 4 (b.toNat % 16))) (rm8Of rex mp), r)
        else none
    else none

/-- Whether the instruction's REX.W bit is meaningful (only for MOVZX/MOVSX). -/
def allowsW : Opc → Bool
  | .two b => b = 0xB6#8 ∨ b = 0xBE#8
  | .one _ => false

/-- Decode a new form: no FS override, no legacy prefix, and no REX.W except on
MOVZX/MOVSX. Returns the instruction and the number of bytes consumed. -/
def decodeNew (bytes : List Byte) : Option (New × Nat) :=
  match pHead bytes with
  | .ok (fs, pfx, rex, opc) rest =>
    if fs = true ∨ pfx ≠ .none ∨ ((rex.getD Rex.zero).w = true ∧ allowsW opc = false) then none
    else (decodeBody rex opc rest).map fun (i, r) => (i, bytes.length - r.length)
  | _ => none

/-- The variant's decoder: `Ext.decode` first, then the new forms. -/
def decode (bytes : List Byte) : Option (Instr × Nat) :=
  match Ext.decode bytes with
  | some (i, n) => some (.base i, n)
  | none => (decodeNew bytes).map fun (i, n) => (.new i, n)

/-- **Decoder agreement**: wherever `Ext` decodes, so does the variant, to the
same instruction and length. -/
theorem decode_of_ext {bytes : List Byte} {i : Ext.Instr} {n : Nat}
    (h : Ext.decode bytes = some (i, n)) : decode bytes = some (.base i, n) := by
  simp [decode, h]

/-- The variant's decoder returns a `base` instruction exactly when `Ext` decodes. -/
theorem decode_base_iff {bytes : List Byte} {i : Ext.Instr} {n : Nat} :
    decode bytes = some (.base i, n) ↔ Ext.decode bytes = some (i, n) := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · rename_i i' n' he
      simp only [Option.some.injEq, Prod.mk.injEq, Instr.base.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact he
    · simp at h
  · exact decode_of_ext

/-! ## Semantics of the new forms -/

/-- The flags after an 8-bit SHL/SHR/SAR of `x` by the masked count `c < 32`. -/
def shift8Flags (op : ShiftOp) (x : BitVec 8) (c : Nat) (old : Flags) : Flags :=
  if c < 8 then op.flags x c old
  else
    let r := op.result x c
    ⟨if op = .sar then some x.msb else none, some (Ext.parityN r), none,
      some (Ext.isZeroN r), some r.msb, none⟩

/-- An 8-bit two-operand ALU step. CMP writes nothing. -/
def alu8 (op : AluOp) (dst : RM8) (y : BitVec 8) (s : State) (memory : Memory) (next : Word) :
    Option (State × Memory) :=
  match dst.read s memory next with
  | none => none
  | some x =>
    if op = .cmp then some ({ s with flags := Ext.AluOp.flagsN op x y }, memory)
    else (dst.write (Ext.AluOp.resultN op x y) s memory next).map fun r =>
      ({ r.1 with flags := Ext.AluOp.flagsN op x y }, r.2)

/-- Execute a new form, given the address of the next instruction. -/
def execNew (i : New) (s : State) (memory : Memory) (next : Word) : Result :=
  match i with
  | .alu op dst src => retire next (alu8 op dst (src.read s) s memory next)
  | .aluR op dst src =>
    match src.read s memory next with
    | none => .dataFault
    | some y => retire next (alu8 op (.reg dst) y s memory next)
  | .aluA op imm => retire next (alu8 op (.reg (.low .rax)) imm s memory next)
  | .aluI op dst imm => retire next (alu8 op dst imm s memory next)
  | .test dst src =>
    retire next ((dst.read s memory next).map fun x =>
      ({ s with flags := Ext.logicFlagsN (x &&& src.read s) }, memory))
  | .shift op dst count =>
    let c := (count.raw s).toNat % 32
    match dst.read s memory next with
    | none => .dataFault
    | some x =>
      if c = 0 then retire next (some (s, memory))
      else retire next ((dst.write (op.result x c) s memory next).map fun r =>
        ({ r.1 with flags := shift8Flags op x c s.flags }, r.2))
  | .mov dst src => retire next (dst.write (src.read s) s memory next)
  | .movR dst src =>
    retire next ((src.read s memory next).map fun v => (dst.write s v, memory))
  | .movx sx sz dst src =>
    retire next ((src.read s memory next).map fun v =>
      (sz.write s dst (if sx then v.signExtend sz.bits else v.setWidth sz.bits), memory))
  | .setcc c dst =>
    match c.eval s.flags with
    | none => .undefinedCondition c
    | some b => retire next (dst.write (if b then 1#8 else 0#8) s memory next)

/-- Execute a variant instruction with its consumed byte length. -/
def exec (i : Instr) (s : State) (memory : Memory) (length : Nat) : Result :=
  match i with
  | .base i => Ext.exec i s memory length
  | .new i => execNew i s memory (s.rip + BitVec.ofNat 64 length)

/-- **Execution agreement**: on `Ext` instructions the variant is `Ext.exec`. -/
@[simp] theorem exec_base (i : Ext.Instr) (s : State) (memory : Memory) (length : Nat) :
    exec (.base i) s memory length = Ext.exec i s memory length := rfl

/-! ## Fetch and step -/

/-- Fetch at an address: `Ext.fetch`, falling back to the new forms on bytes that
`Ext` cannot decode. -/
def fetch (memory : Memory) (address : Nat) : Ext.Fetch ⊕ (New × Nat) :=
  match Ext.fetch memory address with
  | .undecodable =>
    match decodeNew (fetchWindow memory maxInstrLength address) with
    | some (i, n) =>
      if memory.Permitted .execute address n then .inr (i, n) else .inl .truncated
    | none => .inl .undecodable
  | f => .inl f

theorem fetch_of_ne_undecodable {memory : Memory} {address : Nat}
    (h : Ext.fetch memory address ≠ .undecodable) :
    fetch memory address = .inl (Ext.fetch memory address) := by
  unfold fetch
  split
  · rename_i e; exact absurd e h
  · rfl

/-- The outcome of one variant step. -/
inductive Outcome where
  | ext (o : Ext.Outcome)
  /-- A new form retired. -/
  | retired (next : MState)
  /-- A new form faulted on data or depended on an undefined flag. -/
  | newFault (r : Result)

/-- Fetch, decode and execute one instruction. -/
def step (exit : Word) (m : MState) : Outcome :=
  match fetch m.memory m.core.rip.toNat with
  | .inl .undecodable => .ext .undecodable
  | .inl .truncated => .ext .fetchFault
  | .inl (.decoded _ _) => .ext (Ext.step exit m)
  | .inr (i, n) =>
    match execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n) with
    | .ok core memory => .retired ⟨core, memory⟩
    | r => .newFault r

/-- **Step agreement**: whenever `Ext.step` does anything but report undecodable
bytes, the variant's step is that outcome. -/
theorem step_eq_of_ne_undecodable {exit : Word} {m : MState}
    (h : Ext.step exit m ≠ .undecodable) : step exit m = .ext (Ext.step exit m) := by
  have hf : Ext.fetch m.memory m.core.rip.toNat ≠ .undecodable := by
    intro e; apply h; simp [Ext.step, e]
  unfold step
  rw [fetch_of_ne_undecodable hf]
  cases e : Ext.fetch m.memory m.core.rip.toNat with
  | undecodable => exact absurd e hf
  | truncated => simp [Ext.step, e]
  | decoded i n => rfl

/-- Retirement only. -/
def stepOpt (exit : Word) (m : MState) : Option MState :=
  match step exit m with
  | .ext (.retired next) => some next
  | .retired next => some next
  | _ => none

def Returns (exit : Word) (initial final : MState) : Prop :=
  ∃ n mid, Machine.Execution.run (stepOpt exit) n initial = some mid ∧
    step exit mid = .ext (.returned final)

theorem stepOpt_of_ext {exit : Word} {m next : MState} (h : Ext.stepOpt exit m = some next) :
    stepOpt exit m = some next := by
  have hs : Ext.step exit m = .retired next := Ext.stepOpt_eq_some_iff.mp h
  have := step_eq_of_ne_undecodable (exit := exit) (m := m) (by rw [hs]; simp)
  simp [stepOpt, this, hs]

theorem run_of_ext {exit : Word} : ∀ (n : Nat) {initial mid : MState},
    Machine.Execution.run (Ext.stepOpt exit) n initial = some mid →
    Machine.Execution.run (stepOpt exit) n initial = some mid
  | 0, _, _, h => h
  | n + 1, initial, mid, h => by
    simp only [Machine.Execution.run] at h ⊢
    cases e : Ext.stepOpt exit initial with
    | none => simp [e] at h
    | some next =>
      rw [e] at h
      simp only [Option.bind_some] at h
      rw [stepOpt_of_ext e]
      exact run_of_ext n h

/-- **Run agreement**: every `Ext.Returns` run is an `Ext8.Returns` run, so
contracts proved for `Ext` (for example `sha256_compress`) transfer. -/
theorem returns_of_ext {exit : Word} {initial final : MState}
    (h : Ext.Returns exit initial final) : Returns exit initial final := by
  obtain ⟨n, mid, hrun, hstep⟩ := h
  refine ⟨n, mid, run_of_ext n hrun, ?_⟩
  rw [step_eq_of_ne_undecodable (by rw [hstep]; simp), hstep]

/-! ## Decoding examples from `sha256sum-min`

Each is the exact encoding at the given address of the binary
(`sha256sum-min`, SHA-256 `22fa6345…`); `Ext.decode` rejects every one. -/

example : Ext.decode [0x08, 0xCA] = none := by decide
example : decode [0x08, 0xCA] = some (.new (.alu .or (.reg (.low .rdx)) (.low .rcx)), 2) := by
  decide
/-- `movzbl %ah,%ebx` at `0x4030e6`: the legacy high byte. -/
example : decode [0x0F, 0xB6, 0xDC] =
    some (.new (.movx false .d .rbx (.reg (.high .rax))), 3) := by decide
example : decode [0x34, 0x01] = some (.new (.aluA .xor 1), 2) := by decide
example : decode [0xC0, 0xE9, 0x03] = some (.new (.shift .shr (.reg (.low .rcx)) (.imm 3)), 3) := by
  decide
example : decode [0x40, 0x08, 0xD6] = some (.new (.alu .or (.reg (.low .rsi)) (.low .rdx)), 3) := by
  decide
example : decode [0x44, 0x38, 0xD5] = some (.new (.alu .cmp (.reg (.low .rbp)) (.low .r10)), 3) := by
  decide
example : decode [0x3A, 0x54, 0x06, 0x02] =
    some (.new (.aluR .cmp (.low .rdx) (.mem (Mem.ofReg .rsi (some ⟨.rax, 0, by decide⟩) 2))),
      4) := by decide
/-- ADC, 8-bit rotates and REX.W on an 8-bit ALU form are rejected. -/
example : decode [0x10, 0xCA] = none ∧ decode [0xC0, 0xC1, 0x03] = none ∧
    decode [0x48, 0x08, 0xCA] = none := by decide

end Silmaril.X86.Ext8
