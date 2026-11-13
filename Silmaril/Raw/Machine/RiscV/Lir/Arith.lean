module

public import Silmaril.Machine.RiscV.Lir.Exec.Defs
/-!
# Register-only instruction selection

Selection for Lir constants, moves, unary and binary operators into register-only
`Ext.Compute` sequences, with one value theorem per operator.

Every sequence writes only its destination and the scratch registers `t0 t1 t2`
(`*_frame`). Multi-instruction sequences compute into scratch registers and
write the destination last, so the destination may equal an operand.

## 32-bit operators

Lir's 32-bit operators return zero-extended results. The RV64 `*W`
instructions return sign-extended results, so each 32-bit operator is followed
by `slli 32; srli 32`. 32-bit comparisons first extend their operands (sign
extension with `ADDIW` for signed and equality comparisons, zero extension for
unsigned ones) and then use the 64-bit comparison sequence.

## Bit counting

`clz`, `ctz`, `popcnt` and their 32-bit forms have no single RV64 instruction
without the Zbb extension, which is not modeled; `selUnopBasic` returns `none`
for them and `Silmaril.RiscV.Lir.Bits` selects them as unrolled sums.
-/

@[expose] public section

namespace Silmaril.RiscV.Backend

open Silmaril.RiscV.Ext (Compute)
open Machine.Lir (Unop Binop Cond)

/-! ## Reading registers after register-only steps -/

theorem State.read_setPc (s : State) (p : Word) (r : Reg) :
    ({ s with pc := p } : State).read r = s.read r := rfl

theorem State.read_write_eq (s : State) (r q : Reg) (v : Word) :
    (s.write r v).read q = if q = r ∧ r ≠ 0#5 then v else s.read q := by
  by_cases h : q = r
  · subst h
    by_cases hz : q = 0#5
    · subst hz; simp
    · simp [hz]
  · simp [h, State.read_write_other _ _ _ _ h]

@[simp] theorem read_compute_step (c : Compute) (s : State) (q : Reg) :
    (Compute.step c s).read q = if q = c.dest ∧ c.dest ≠ 0#5 then c.value s else s.read q := by
  simp only [Compute.step, State.read_setPc, State.read_write_eq]

@[simp] theorem read_base_step (i : RiscV.Instr) (s : State) (q : Reg) :
    (RiscV.step i s).read q = if q = i.dest ∧ i.dest ≠ 0#5 then i.value s else s.read q := by
  simp only [RiscV.step, State.read_setPc, State.read_write_eq]

/-- Registers outside the destinations of a register-only block keep their value. -/
theorem run_frame {cs : List Compute} {d : Reg} (h : ∀ c ∈ cs, c.dest = d ∨ Scratch c.dest)
    (s : State) (r : Reg) (hr : r ≠ d) (hs : ¬ Scratch r) :
    (Machine.Block.run Compute.step cs s).read r = s.read r := by
  apply Ext.run_read_frame
  intro c hc e
  rcases h c hc with h' | h'
  · exact hr (e.trans h')
  · exact hs (e ▸ h')

/-! ## Constants -/

/-- `v` is the sign extension of its low 12 bits. -/
def fits12 (v : Word) : Bool := (v.setWidth 12).signExtend 64 == v

/-- What remains to materialise after the sign-extended low 12 bits. -/
def liHi (v : Word) : Word := (v - (v.setWidth 12).signExtend 64) >>> 12

theorem low12_toNat (v : Word) : ((v.setWidth 12).signExtend 64).toNat =
    v.toNat % 4096 + if 2048 ≤ v.toNat % 4096 then 2 ^ 64 - 2 ^ 12 else 0 := by
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp [BitVec.toNat_setWidth]; omega

theorem liHi_bound {v : Word} (hv : fits12 v = false) :
    (liHi v).toNat ≤ (v.toNat + 2048) / 4096 := by
  have hlo := low12_toNat v
  have hfit : ¬ (2 ^ 64 - 2048 ≤ v.toNat) ∨ v.toNat % 4096 < 2048 := by
    by_contra hc
    simp only [not_or, not_not, not_lt] at hc
    apply Bool.false_ne_true
    rw [← hv, fits12, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [hlo]
    simp only [show 2048 ≤ v.toNat % 4096 from hc.2, ↓reduceIte]
    have := v.isLt
    omega
  rw [liHi, BitVec.toNat_ushiftRight, BitVec.toNat_sub, hlo, Nat.shiftRight_eq_div_pow]
  have := v.isLt
  split <;> simp only [Nat.reducePow] at * <;> omega

theorem fits12_of_small {v : Word} (h : v.toNat < 2048) : fits12 v = true := by
  rw [fits12, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [low12_toNat]
  have : v.toNat % 4096 = v.toNat := Nat.mod_eq_of_lt (by omega)
  rw [this, ite_false_of (by omega)]
  rfl

/-- Materialise a constant in `d` with `ADDI`, `SLLI`, `ADDI`, peeling 12 bits
per round for at most `n` rounds. -/
def liN (d : Reg) : Nat → Word → List Compute
  | 0, v => [.base (.imm .add d 0#5 (v.setWidth 12))]
  | n + 1, v =>
    if fits12 v then [.base (.imm .add d 0#5 (v.setWidth 12))]
    else liN d n (liHi v) ++ [.base (.shift .sll d d 12#6), .base (.imm .add d d (v.setWidth 12))]

/-- Materialise a 64-bit constant in `d`: one `ADDI` for a 12-bit signed
constant, otherwise the upper bits recursively followed by `SLLI 12` and `ADDI`
(at most 11 instructions). -/
def li (d : Reg) (v : Word) : List Compute := liN d 5 v

theorem liN_ne_nil (d : Reg) : ∀ n v, liN d n v ≠ []
  | 0, _ => by simp [liN]
  | n + 1, v => by unfold liN; split <;> simp

theorem li_ne_nil (d : Reg) (v : Word) : li d v ≠ [] := liN_ne_nil d 5 v

theorem liN_dest (d : Reg) : ∀ n v, ∀ c ∈ liN d n v, c.dest = d
  | 0, _ => by simp [liN, Compute.dest, RiscV.Instr.dest]
  | n + 1, v => by
    unfold liN
    split
    · simp [Compute.dest, RiscV.Instr.dest]
    · intro c hc
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · exact liN_dest d n _ c hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> rfl

theorem li_dest (d : Reg) (v : Word) : ∀ c ∈ li d v, c.dest = d := liN_dest d 5 v

theorem shift_reassemble (v : Word) :
    ((v - (v.setWidth 12).signExtend 64) >>> 12) <<< 12 + (v.setWidth 12).signExtend 64 = v := by
  apply BitVec.eq_of_toNat_eq
  have hlo := low12_toNat v
  have := v.isLt
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_sub, hlo,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  split <;> simp only [Nat.reducePow] at * <;> omega

theorem liN_value (d : Reg) (hd : d ≠ 0#5) :
    ∀ n (v : Word) (s : State), v.toNat ≤ 2 ^ (4 + 12 * n) →
      (Machine.Block.run Compute.step (liN d n v) s).read d = v
  | 0, v, s, hv => by
    have hf := fits12_of_small (v := v) (by simp at hv; omega)
    simp only [liN, Machine.Block.run_singleton, read_compute_step, Compute.dest, RiscV.Instr.dest,
      ne_eq, hd, not_false_eq_true, and_self, ↓reduceIte, Compute.value, RiscV.Instr.value,
      RiscV.ImmOp.eval, State.read_zero, BitVec.zero_add]
    simpa [fits12] using hf
  | n + 1, v, s, hv => by
    unfold liN
    split
    · rename_i hf
      simp only [Machine.Block.run_singleton, read_compute_step, Compute.dest, RiscV.Instr.dest,
        ne_eq, hd, not_false_eq_true, and_self, ↓reduceIte, Compute.value, RiscV.Instr.value,
        RiscV.ImmOp.eval, State.read_zero, BitVec.zero_add]
      simpa [fits12] using hf
    · rename_i hf
      have hb := liHi_bound (v := v) (by simpa using hf)
      have hX : 2 ^ (4 + 12 * (n + 1)) = 4096 * 2 ^ (4 + 12 * n) := by
        rw [show 4 + 12 * (n + 1) = 12 + (4 + 12 * n) by omega, Nat.pow_add]
      have ih := liN_value d hd n (liHi v)
      rw [Machine.Block.run_append]
      simp only [Machine.Block.run_cons, Machine.Block.run_nil, read_compute_step, Compute.dest,
        RiscV.Instr.dest, ne_eq, hd, not_false_eq_true, and_self, ↓reduceIte, Compute.value,
        RiscV.Instr.value, RiscV.ImmOp.eval, RiscV.ShiftOp.eval]
      rw [ih _ (by rw [hX] at hv; generalize 2 ^ (4 + 12 * n) = X at *; omega)]
      exact shift_reassemble v

theorem li_value (d : Reg) (hd : d ≠ 0#5) (v : Word) (s : State) :
    (Machine.Block.run Compute.step (li d v) s).read d = v :=
  liN_value d hd 5 v s (by have := v.isLt; simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]; omega)

/-! ## Bit-vector facts used by the selection proofs -/

theorem boolWord_eq (b : Bool) : boolWord b = Machine.Lir.ofBool b := by
  cases b <;> rfl

theorem mulHigh_eq (x y : Word) : Ext.mulHigh x y = Machine.Lir.mulHigh true x y := by
  apply BitVec.eq_of_toNat_eq
  simp [Ext.mulHigh, Machine.Lir.mulHigh, BitVec.extractLsb', BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

theorem mulHighU_eq (x y : Word) : Ext.mulHighU x y = Machine.Lir.mulHigh false x y := by
  apply BitVec.eq_of_toNat_eq
  simp [Ext.mulHighU, Machine.Lir.mulHigh, BitVec.extractLsb', BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

theorem setWidth6_toNat (y : Word) : (y.setWidth 6).toNat = y.toNat % 64 := by
  simp [BitVec.toNat_setWidth]

theorem setWidth5_toNat (y : Word) : (y.setWidth 5).toNat = y.toNat % 32 := by
  simp [BitVec.toNat_setWidth]

theorem neg_setWidth6 (y : Word) : ((0#64 - y).setWidth 6).toNat = (64 - y.toNat % 64) % 64 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub]
  have := y.isLt
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero, Nat.reducePow] at *
  omega

theorem neg_setWidth5 (y : Word) : ((0#64 - y).setWidth 5).toNat = (32 - y.toNat % 32) % 32 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub]
  have := y.isLt
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero, Nat.reducePow] at *
  omega

theorem ushiftRight_width {w : Nat} (x : BitVec w) : x >>> w = 0#w := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_eq_div_pow]
  exact x.isLt

theorem shiftLeft_width {w : Nat} (x : BitVec w) : x <<< w = 0#w := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem rotl_eq {w : Nat} (x : BitVec w) (k : Nat) (hk : k < w) :
    x <<< k ||| x >>> ((w - k) % w) = x.rotateLeft k := by
  rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt hk]
  by_cases h : k = 0
  · subst h; simp [ushiftRight_width]
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem rotr_eq {w : Nat} (x : BitVec w) (k : Nat) (hk : k < w) :
    x >>> k ||| x <<< ((w - k) % w) = x.rotateRight k := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hk]
  by_cases h : k = 0
  · subst h; simp
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem zext_shifts (v : Word) (k : Nat) (hk : k ≤ 64) :
    (v <<< (64 - k)) >>> (64 - k) = (v.setWidth k).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h1 : i < k
  · simp [h1, hi]; intro; omega
  · simp [h1]; intro; omega

theorem sext_shifts (v : Word) (k : Nat) (hk0 : 0 < k) (hk : k ≤ 64) :
    (v <<< (64 - k)).sshiftRight (64 - k) = (v.setWidth k).signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_setWidth, BitVec.msb_eq_getLsbD_last]
  have e1 : ¬ (64 ≤ i) := by omega
  by_cases h1 : i < k
  · have : 64 - k + i < 64 := by omega
    have e2 : ¬ (64 - k + i < 64 - k) := by omega
    have e3 : 64 - k + i - (64 - k) = i := by omega
    simp [h1, hi, this, e1, e2, e3]
  · have : ¬ (64 - k + i < 64) := by omega
    have e2 : 63 - (64 - k) = k - 1 := by omega
    have e3 : ¬ (63 < 64 - k) := by omega
    have e4 : k - 1 < k := by omega
    simp [h1, hi, this, e1, e2, e3, e4]

theorem andi_255 (x : Word) : x &&& (255#12).signExtend 64 = (x.setWidth 8).setWidth 64 := by
  have : (255#12).signExtend 64 = 255#64 := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := Nat.and_two_pow_sub_one_eq_mod x.toNat 8
  have h2 := x.isLt
  simp only [Nat.reducePow] at *
  rw [show 255 % 18446744073709551616 = 255 from rfl, this]
  omega

theorem andi_255' (x : Word) : x &&& 255#64 = (x.setWidth 8).setWidth 64 := by
  have := andi_255 x
  rwa [show (255#12).signExtend 64 = 255#64 from by decide] at this

theorem low32_or (x y : Word) : Ext.low32 (x ||| y) = Ext.low32 x ||| Ext.low32 y := by
  simp [Ext.low32, BitVec.setWidth_or]

/-- The zero extension of the low 32 bits, as `slli 32; srli 32` computes it. -/
theorem zext32_eq (v : Word) : (v <<< 32) >>> 32 = Machine.Lir.of32 (Ext.low32 v) := by
  have := zext_shifts v 32 (by decide)
  simpa [Machine.Lir.of32, Ext.low32] using this

theorem slt_eq (x y : Word) : x.slt y = decide (x.toInt < y.toInt) := by
  rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, decide_eq_true_iff]

theorem ult_eq (x y : Word) : x.ult y = decide (x.toNat < y.toNat) := by
  rw [Bool.eq_iff_iff, BitVec.ult_iff_toNat_lt, decide_eq_true_iff]

theorem one_signExtend : (1#12).signExtend 64 = 1#64 := by decide

theorem not_decide_lt {α : Type} [LinearOrder α] (a b : α) :
    (!decide (a < b)) = decide (b ≤ a) := by
  rw [← decide_not]; simp only [not_lt]

theorem ofBool_xor_one (b : Bool) : Machine.Lir.ofBool b ^^^ 1#64 = Machine.Lir.ofBool (!b) := by
  cases b <;> decide

theorem ult_one (v : Word) : v.ult ((1#12).signExtend 64) = (v == 0#64) := by
  rw [one_signExtend, Bool.eq_iff_iff, BitVec.ult_iff_toNat_lt, beq_iff_eq]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have : (1#64).toNat = 1 := rfl
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega
  · rintro rfl; decide

theorem ult_one' (v : Word) : v.ult 1#64 = (v == 0#64) := by
  have := ult_one v
  rwa [one_signExtend] at this

theorem zero_ult (v : Word) : (0#64).ult v = (v != 0#64) := by
  rw [Bool.eq_iff_iff, BitVec.ult_iff_toNat_lt, bne_iff_ne]
  constructor
  · rintro h rfl; simp at h
  · intro h
    have : v.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega

theorem xor_beq_zero (x y : Word) : ((x ^^^ y) == 0#64) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, BitVec.xor_eq_zero_iff]

theorem xor_bne_zero (x y : Word) : ((x ^^^ y) != 0#64) = (x != y) := by
  simp only [bne, xor_beq_zero]

theorem sext32_toInt (v : BitVec 32) : (Ext.sext32 v).toInt = v.toInt :=
  BitVec.toInt_signExtend_of_le (by decide)

theorem sext32_inj {a b : BitVec 32} : Ext.sext32 a = Ext.sext32 b ↔ a = b := by
  constructor
  · intro h; have := congrArg Ext.low32 h; simpa using this
  · rintro rfl; rfl

theorem of32_toNat (v : BitVec 32) : (Machine.Lir.of32 v).toNat = v.toNat := by
  have := v.isLt
  simp [Machine.Lir.of32, BitVec.toNat_setWidth]
  omega

/-! ## Selection -/

/-- `d := zext32 t0`. -/
def zextTail (d : Reg) : List Compute :=
  [.base (.shift .sll t0 t0 32#6), .base (.shift .srl d t0 32#6)]

/-- 64-bit comparison into `d`, using `t0` as a temporary. -/
def selCmp : Cond → Reg → Reg → Reg → List Compute
  | .eq, d, x, y => [.base (.reg .xor t0 x y), .base (.imm .sltu d t0 1#12)]
  | .ne, d, x, y => [.base (.reg .xor t0 x y), .base (.reg .sltu d 0#5 t0)]
  | .lts, d, x, y => [.base (.reg .slt d x y)]
  | .ltu, d, x, y => [.base (.reg .sltu d x y)]
  | .gts, d, x, y => [.base (.reg .slt d y x)]
  | .gtu, d, x, y => [.base (.reg .sltu d y x)]
  | .les, d, x, y => [.base (.reg .slt t0 y x), .base (.imm .xor d t0 1#12)]
  | .leu, d, x, y => [.base (.reg .sltu t0 y x), .base (.imm .xor d t0 1#12)]
  | .ges, d, x, y => [.base (.reg .slt t0 x y), .base (.imm .xor d t0 1#12)]
  | .geu, d, x, y => [.base (.reg .sltu t0 x y), .base (.imm .xor d t0 1#12)]

def Cond.unsigned : Cond → Bool
  | .ltu | .leu | .gtu | .geu => true
  | _ => false

/-- Extend the low 32 bits of `x` and `y` into `t1` and `t2`: zero extension
for unsigned comparisons, sign extension otherwise. -/
def extOperands (c : Cond) (x y : Reg) : List Compute :=
  if Cond.unsigned c then
    [.base (.shift .sll t1 x 32#6), .base (.shift .srl t1 t1 32#6),
      .base (.shift .sll t2 y 32#6), .base (.shift .srl t2 t2 32#6)]
  else [.addiw t1 x 0#12, .addiw t2 y 0#12]

def selBinop : Binop → Reg → Reg → Reg → List Compute
  | .add, d, x, y => [.base (.reg .add d x y)]
  | .sub, d, x, y => [.base (.reg .sub d x y)]
  | .mul, d, x, y => [.mulDiv .mul d x y]
  | .mulhs, d, x, y => [.mulDiv .mulh d x y]
  | .mulhu, d, x, y => [.mulDiv .mulhu d x y]
  | .and, d, x, y => [.base (.reg .and d x y)]
  | .or, d, x, y => [.base (.reg .or d x y)]
  | .xor, d, x, y => [.base (.reg .xor d x y)]
  | .shl, d, x, y => [.base (.reg .sll d x y)]
  | .shrs, d, x, y => [.base (.reg .sra d x y)]
  | .shru, d, x, y => [.base (.reg .srl d x y)]
  | .rotl, d, x, y =>
    [.base (.reg .sll t0 x y), .base (.reg .sub t1 0#5 y), .base (.reg .srl t1 x t1),
      .base (.reg .or d t0 t1)]
  | .rotr, d, x, y =>
    [.base (.reg .srl t0 x y), .base (.reg .sub t1 0#5 y), .base (.reg .sll t1 x t1),
      .base (.reg .or d t0 t1)]
  | .shl32, d, x, y => .regW .sll t0 x y :: zextTail d
  | .shrs32, d, x, y => .regW .sra t0 x y :: zextTail d
  | .shru32, d, x, y => .regW .srl t0 x y :: zextTail d
  | .rotl32, d, x, y =>
    [.regW .sll t0 x y, .base (.reg .sub t1 0#5 y), .regW .srl t1 x t1,
      .base (.reg .or t0 t0 t1)] ++ zextTail d
  | .rotr32, d, x, y =>
    [.regW .srl t0 x y, .base (.reg .sub t1 0#5 y), .regW .sll t1 x t1,
      .base (.reg .or t0 t0 t1)] ++ zextTail d
  | .divs, d, x, y => [.mulDiv .div d x y]
  | .divu, d, x, y => [.mulDiv .divu d x y]
  | .rems, d, x, y => [.mulDiv .rem d x y]
  | .remu, d, x, y => [.mulDiv .remu d x y]
  | .divs32, d, x, y => .mulDivW .divw t0 x y :: zextTail d
  | .divu32, d, x, y => .mulDivW .divuw t0 x y :: zextTail d
  | .rems32, d, x, y => .mulDivW .remw t0 x y :: zextTail d
  | .remu32, d, x, y => .mulDivW .remuw t0 x y :: zextTail d
  | .cmp c, d, x, y => selCmp c d x y
  | .cmp32 c, d, x, y => extOperands c x y ++ selCmp c d t1 t2

/-- Unary operators other than the bit-counting ones (`Silmaril.RiscV.Lir.Bits`). -/
def selUnopBasic : Unop → Reg → Reg → Option (List Compute)
  | .sext8, d, x => some [.base (.shift .sll t0 x 56#6), .base (.shift .sra d t0 56#6)]
  | .sext16, d, x => some [.base (.shift .sll t0 x 48#6), .base (.shift .sra d t0 48#6)]
  | .sext32, d, x => some [.addiw d x 0#12]
  | .zext8, d, x => some [.base (.imm .and d x 255#12)]
  | .zext16, d, x => some [.base (.shift .sll t0 x 48#6), .base (.shift .srl d t0 48#6)]
  | .zext32, d, x => some [.base (.shift .sll t0 x 32#6), .base (.shift .srl d t0 32#6)]
  | .eqz, d, x => some [.base (.imm .sltu d x 1#12)]
  | .clz, _, _ | .ctz, _, _ | .popcnt, _, _ | .clz32, _, _ | .ctz32, _, _ | .popcnt32, _, _ =>
    none

def selMove (d x : Reg) : List Compute := [.base (.imm .add d x 0#12)]

/-! ## Write sets -/

/-- Destinations of a selected block: the target register or a scratch register. -/
def DestsIn (cs : List Compute) (d : Reg) : Prop := ∀ c ∈ cs, c.dest = d ∨ Scratch c.dest

theorem selCmp_dests (c : Cond) (d x y : Reg) : DestsIn (selCmp c d x y) d := by
  cases c <;> simp [DestsIn, selCmp, Compute.dest, RiscV.Instr.dest, Scratch]

theorem selBinop_dests (op : Binop) (d x y : Reg) : DestsIn (selBinop op d x y) d := by
  cases op with
  | cmp c => exact selCmp_dests c d x y
  | cmp32 c =>
    intro i hi
    rw [selBinop, List.mem_append] at hi
    rcases hi with hi | hi
    · right
      unfold extOperands at hi
      split at hi <;> simp at hi <;> rcases hi with rfl | rfl | rfl | rfl <;>
        simp [Compute.dest, RiscV.Instr.dest, Scratch]
    · exact selCmp_dests c d t1 t2 i hi
  | _ => simp [DestsIn, selBinop, zextTail, Compute.dest, RiscV.Instr.dest, Scratch]

theorem selUnopBasic_dests {op : Unop} {d x : Reg} {cs : List Compute}
    (h : selUnopBasic op d x = some cs) : DestsIn cs d := by
  cases op <;> simp [selUnopBasic] at h <;> subst h <;>
    simp [DestsIn, Compute.dest, RiscV.Instr.dest, Scratch]

theorem selMove_dests (d x : Reg) : DestsIn (selMove d x) d := by
  simp [DestsIn, selMove, Compute.dest, RiscV.Instr.dest]

theorem li_dests (d : Reg) (v : Word) : DestsIn (li d v) d :=
  fun c hc => .inl (li_dest d v c hc)

theorem selBinop_ne_nil (op : Binop) (d x y : Reg) : selBinop op d x y ≠ [] := by
  cases op with
  | cmp c => cases c <;> simp [selBinop, selCmp]
  | cmp32 c => simp [selBinop, extOperands]; split <;> simp
  | _ => simp [selBinop, zextTail]

theorem selUnopBasic_ne_nil {op : Unop} {d x : Reg} {cs : List Compute}
    (h : selUnopBasic op d x = some cs) : cs ≠ [] := by
  cases op <;> simp [selUnopBasic] at h <;> subst h <;> simp

/-! ## Values -/

section Values

variable {d x y : Reg}

theorem ne_scratch {r : Reg} (h : ¬ Scratch r) : r ≠ t0 ∧ r ≠ t1 ∧ r ≠ t2 :=
  ⟨fun e => h (.inl e), fun e => h (.inr (.inl e)), fun e => h (.inr (.inr e))⟩

theorem selMove_value (hd : d ≠ 0#5) (s : State) :
    (Machine.Block.run Compute.step (selMove d x) s).read d = s.read x := by
  simp [selMove, RiscV.Instr.dest, hd, RiscV.Instr.value, RiscV.ImmOp.eval]

theorem zextTail_value (hd : d ≠ 0#5) (s : State) :
    (Machine.Block.run Compute.step (zextTail d) s).read d =
      Machine.Lir.of32 (Ext.low32 (s.read t0)) := by
  simp [zextTail, RiscV.Instr.dest, hd, RiscV.Instr.value, RiscV.ShiftOp.eval, zext32_eq]

theorem selCmp_value (c : Cond) (hd : d ≠ 0#5) (s : State) :
    (Machine.Block.run Compute.step (selCmp c d x y) s).read d =
      Machine.Lir.ofBool (c.eval (s.read x) (s.read y)) := by
  cases c
  case eq =>
    simp only [selCmp, Machine.Block.run_cons, Machine.Block.run_nil, Ext.Compute.step_base,
      read_base_step, RiscV.Instr.dest, RiscV.Instr.value, RiscV.ImmOp.eval, RiscV.RegOp.eval,
      ne_eq, hd, t0_ne_zero, not_false_eq_true, and_self, ↓reduceIte, ult_one,
      xor_beq_zero, boolWord_eq, Cond.eval]
  case ne =>
    simp only [selCmp, Machine.Block.run_cons, Machine.Block.run_nil, Ext.Compute.step_base,
      read_base_step, RiscV.Instr.dest, RiscV.Instr.value, RiscV.RegOp.eval,
      ne_eq, hd, t0_ne_zero, not_false_eq_true, and_self, ↓reduceIte, zero_ult,
      xor_bne_zero, boolWord_eq, Cond.eval, State.read_zero]
  all_goals
    simp [selCmp, hd, RiscV.Instr.dest, RiscV.Instr.value, RiscV.RegOp.eval, RiscV.ImmOp.eval,
      Cond.eval, boolWord_eq, slt_eq, ult_eq, one_signExtend, ofBool_xor_one, not_decide_lt]

theorem lo32_eq (v : Word) : Machine.Lir.lo32 v = Ext.low32 v := rfl

theorem neg_setWidth6' (y : Word) : ((-y).setWidth 6).toNat = (64 - y.toNat % 64) % 64 := by
  rw [← BitVec.zero_sub]; exact neg_setWidth6 y

theorem neg_setWidth5' (y : Word) : ((-y).setWidth 5).toNat = (32 - y.toNat % 32) % 32 := by
  rw [← BitVec.zero_sub]; exact neg_setWidth5 y

theorem zero_signExtend32 : (0#12).signExtend 32 = 0#32 := by decide
theorem zero_signExtend64 : (0#12).signExtend 64 = 0#64 := by decide

theorem divOp_some {w : Nat} {sg rm : Bool} {a b z : BitVec w}
    (h : Machine.Lir.divOp sg rm a b = some z) :
    b ≠ 0#w ∧ z = if sg then (if rm then a.srem b else a.sdiv b) else (if rm then a % b else a / b) := by
  unfold Machine.Lir.divOp at h
  split at h
  · cases h
  · rename_i hb
    refine ⟨hb, ?_⟩
    split at h
    · split at h
      · cases h
      · cases h; rename_i hs _; simp [hs]
    · cases h; rename_i hs; simp [hs]

theorem sext32_beq (a b : BitVec 32) : (Ext.sext32 a == Ext.sext32 b) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, sext32_inj]

theorem cond_sext (c : Cond) (hc : Cond.unsigned c = false) (a b : BitVec 32) :
    c.eval (Ext.sext32 a) (Ext.sext32 b) = c.eval a b := by
  cases c <;> simp [Cond.unsigned] at hc <;> simp [Cond.eval, sext32_toInt, sext32_beq, bne]

theorem cond_zext (c : Cond) (hc : Cond.unsigned c = true) (a b : BitVec 32) :
    c.eval (Machine.Lir.of32 a) (Machine.Lir.of32 b) = c.eval a b := by
  cases c <;> simp [Cond.unsigned] at hc <;> simp [Cond.eval, of32_toNat]

theorem extOperands_values (c : Cond) (hy : ¬ Scratch y) (s : State) :
    let s' := Machine.Block.run Compute.step (extOperands c x y) s
    c.eval (s'.read t1) (s'.read t2) = c.eval (Ext.low32 (s.read x)) (Ext.low32 (s.read y)) := by
  obtain ⟨hy0, hy1, hy2⟩ := ne_scratch hy
  intro s'
  unfold s' extOperands
  cases hc : Cond.unsigned c
  · simp only [Bool.false_eq_true, ↓reduceIte, Machine.Block.run_cons, Machine.Block.run_nil,
      read_compute_step, Compute.dest, ne_eq, t1_ne_zero, t2_ne_zero, not_false_eq_true, and_true,
      t1_ne_t2, ↓reduceIte, Compute.value, hy1, zero_signExtend32,
      BitVec.add_zero]
    exact cond_sext c hc _ _
  · simp only [↓reduceIte, Machine.Block.run_cons, Machine.Block.run_nil, Ext.Compute.step_base,
      read_base_step, RiscV.Instr.dest, ne_eq, t1_ne_zero, t2_ne_zero, not_false_eq_true, and_true,
      t1_ne_t2, and_self, ↓reduceIte, RiscV.Instr.value, RiscV.ShiftOp.eval,
      hy1]
    have e := zext32_eq
    simp only [BitVec.toNat_ofNat] at e ⊢
    rw [e, e]
    exact cond_zext c hc _ _

theorem selBinop_value (op : Binop) (hd : d ≠ 0#5) (hx : ¬ Scratch x) (hy : ¬ Scratch y)
    (s : State) {z : Word} (h : op.eval (s.read x) (s.read y) = some z) :
    (Machine.Block.run Compute.step (selBinop op d x y) s).read d = z := by
  obtain ⟨hx0, hx1, hx2⟩ := ne_scratch hx
  obtain ⟨hy0, hy1, hy2⟩ := ne_scratch hy
  cases op
  case cmp c =>
    simp only [Binop.eval, Option.some.injEq] at h
    subst h
    exact selCmp_value c hd s
  case cmp32 c =>
    simp only [Binop.eval, Option.some.injEq] at h
    subst h
    rw [selBinop, Machine.Block.run_append, selCmp_value c hd, extOperands_values c hy]
    rfl
  case divs | divu | rems | remu =>
    simp only [Binop.eval] at h
    obtain ⟨hb, rfl⟩ := divOp_some h
    simp [selBinop, hd, Compute.dest, Compute.value, Ext.MulOp.eval, Ext.divS_of_ne_zero _ hb,
      Ext.divU_of_ne_zero _ hb, Ext.remS_of_ne_zero _ hb, Ext.remU_eq_umod]
  case divs32 | divu32 | rems32 | remu32 =>
    simp only [Binop.eval, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    obtain ⟨hb, rfl⟩ := divOp_some hq
    rw [lo32_eq] at hb
    rw [selBinop, Machine.Block.run_cons, zextTail_value hd]
    simp [Compute.dest, Compute.value, Ext.MulWOp.eval, lo32_eq, Ext.divS_of_ne_zero _ hb,
      Ext.divU_of_ne_zero _ hb, Ext.remS_of_ne_zero _ hb, Ext.remU_eq_umod]
  case shl32 | shrs32 | shru32 =>
    simp only [Binop.eval, Option.some.injEq] at h
    subst h
    rw [selBinop, Machine.Block.run_cons, zextTail_value hd]
    simp [Compute.dest, Compute.value, Ext.RegWOp.eval, Ext.evalShiftW, lo32_eq]
  case rotl32 =>
    simp only [Binop.eval, Option.some.injEq] at h
    subst h
    rw [selBinop, Machine.Block.run_append, zextTail_value hd]
    simp [hx0, hx1, hy0, Compute.dest, Compute.value, RiscV.Instr.dest, RiscV.Instr.value,
      RiscV.RegOp.eval, Ext.RegWOp.eval, Ext.evalShiftW, lo32_eq, low32_or]
    rw [rotl_eq _ _ (by omega)]; simp
  case rotr32 =>
    simp only [Binop.eval, Option.some.injEq] at h
    subst h
    rw [selBinop, Machine.Block.run_append, zextTail_value hd]
    simp [hx0, hx1, hy0, Compute.dest, Compute.value, RiscV.Instr.dest, RiscV.Instr.value,
      RiscV.RegOp.eval, Ext.RegWOp.eval, Ext.evalShiftW, lo32_eq, low32_or]
    rw [rotr_eq _ _ (by omega)]; simp
  case rotl =>
    simp only [Binop.eval, Option.some.injEq] at h
    subst h
    simp [selBinop, hd, hx0, hx1, hy0, RiscV.Instr.dest, RiscV.Instr.value,
      RiscV.RegOp.eval, RiscV.ShiftOp.eval]
    rw [rotl_eq _ _ (by omega)]; simp
  case rotr =>
    simp only [Binop.eval, Option.some.injEq] at h
    subst h
    simp [selBinop, hd, hx0, hx1, hy0, RiscV.Instr.dest, RiscV.Instr.value,
      RiscV.RegOp.eval, RiscV.ShiftOp.eval]
    rw [rotr_eq _ _ (by omega)]; simp
  all_goals
    simp only [Binop.eval, Option.some.injEq] at h
    subst h
    simp [selBinop, hd, RiscV.Instr.dest, RiscV.Instr.value, RiscV.RegOp.eval, RiscV.ShiftOp.eval,
      Compute.dest, Compute.value, Ext.MulOp.eval, mulHigh_eq, mulHighU_eq]

theorem selUnopBasic_value {op : Unop} {cs : List Compute} (hsel : selUnopBasic op d x = some cs)
    (hd : d ≠ 0#5) (s : State) :
    (Machine.Block.run Compute.step cs s).read d = op.eval (s.read x) := by
  cases op <;> simp only [selUnopBasic, Option.some.injEq, reduceCtorEq] at hsel <;> subst hsel
  case sext8 =>
    have := sext_shifts (s.read x) 8 (by decide) (by decide)
    simp only [Nat.reduceSub] at this
    simp [hd, RiscV.Instr.dest, RiscV.Instr.value, RiscV.ShiftOp.eval, Unop.eval, this]
  case sext16 =>
    have := sext_shifts (s.read x) 16 (by decide) (by decide)
    simp only [Nat.reduceSub] at this
    simp [hd, RiscV.Instr.dest, RiscV.Instr.value, RiscV.ShiftOp.eval, Unop.eval, this]
  case zext16 =>
    have := zext_shifts (s.read x) 16 (by decide)
    simp only [Nat.reduceSub] at this
    simp [hd, RiscV.Instr.dest, RiscV.Instr.value, RiscV.ShiftOp.eval, Unop.eval, this]
  case zext32 =>
    simp [hd, RiscV.Instr.dest, RiscV.Instr.value, RiscV.ShiftOp.eval, Unop.eval, zext32_eq,
      lo32_eq]
  case zext8 =>
    simp [hd, RiscV.Instr.dest, RiscV.Instr.value, RiscV.ImmOp.eval, Unop.eval, andi_255']
  case eqz =>
    simp [hd, RiscV.Instr.dest, RiscV.Instr.value, RiscV.ImmOp.eval, Unop.eval, ult_one',
      boolWord_eq]
  case sext32 =>
    simp [hd, Compute.dest, Compute.value, Unop.eval, zero_signExtend32, Ext.sext32, Ext.low32]

end Values

end Silmaril.RiscV.Backend
