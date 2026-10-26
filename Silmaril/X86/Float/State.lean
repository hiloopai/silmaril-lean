module

public import Silmaril.X86.Float.Instr
public import Silmaril.X86.Encoding
public import Silmaril.Numeric.Float
import Std.Tactic.BVDecide

/-!
# XMM registers and MXCSR for the scalar SSE subset

A handwritten local model of the user-visible SSE state of 64-bit mode, written
from the Intel 64 and IA-32 Architectures Software Developer's Manual (SDM),
Volume 1, §10.2 ("SSE extensions" execution environment). It is a specification
from documents: nothing here is derived from, or proved to correspond with, the
Sail, ACL2 or any hardware description.

* `State` wraps the integer state `X86.State` (general-purpose registers, RIP and
  the six arithmetic flags) with the sixteen 128-bit XMM registers (SDM Vol. 1,
  §10.2.2) and MXCSR. The upper halves of YMM/ZMM registers (AVX) are not
  modeled. The SDM specifies that the 128-bit legacy SSE forms leave them
  unchanged (Vol. 2, the "Description" of each instruction page: "the upper
  bits (MAXVL-1:128) of the corresponding destination register remain
  unchanged"), so a model that later adds them must keep them in the frame of
  every instruction here.
* `MXCSR` is the 32-bit control/status register (SDM Vol. 1, §10.2.3,
  Figure 10-3): sticky exception flags IE, DE, ZE, OE, UE, PE (bits 0–5), DAZ
  (bit 6), exception masks IM, DM, ZM, OM, UM, PM (bits 7–12), the rounding
  control RC (bits 13–14) and FZ (bit 15). Bits 31–16 are reserved;
  `MXCSR.WellFormed` says they are zero. The model assumes a processor whose
  MXCSR_MASK is `0000FFFFH`, i.e. one that supports DAZ (SDM Vol. 1, §11.6.6
  "Guidelines for Writing to the MXCSR Register");
  on processors without DAZ, bit 6 is also reserved.
* `MXCSR.reset` is the power-up and reset value `1F80H` (SDM Vol. 1, §10.2.3):
  all exceptions masked, all flags clear, round to nearest, DAZ and FZ off.

The result-affecting fields are passed to the shared floating-point layer
through `MXCSR.control` and `MXCSR.profile`, which instantiate
`Silmaril.Numeric.Float.Profile.x86SSE`. Floating-point arithmetic is never
computed in this directory: every value, IEEE flag and subnormal-operand
indication comes from that profile.

`MXCSR.control` enables flush-to-zero only when FZ is set *and* underflow is
masked (UM = 1). SDM Vol. 1, §10.2.3.3 states that FZ takes effect only for a
masked underflow; with underflow unmasked, the underflow exception is raised
instead (`Semantics.lean` turns it into a fault). `control_eq_ofBits` shows that
`control` is the shared decoder `MXCSRControl.ofBits` of the raw bits, which
gates FZ on UM in the same way.

The file also provides the lane operations on 128-bit registers and the
little-endian byte images of 32-, 64- and 128-bit values used by the memory
forms.
-/

@[expose] public section

namespace Silmaril.X86.Float

open Silmaril.Numeric.Float (Bits MXCSRControl Profile x86RoundingControl)

/-! ## Scalar formats and lanes -/

/-- The IEEE interchange format of a scalar precision: binary32 for SS forms and
binary64 for SD forms (SDM Vol. 1, §4.2.2). -/
def Precision.fmt : Precision → _root_.Float.Model.Format
  | .single => .binary32
  | .double => .binary64

/-- The width in bits of a scalar lane. -/
def Precision.width : Precision → Nat
  | .single => 32
  | .double => 64

/-- The width in bytes of a scalar memory operand (`m32` or `m64`). -/
def Precision.bytes : Precision → Nat
  | .single => 4
  | .double => 8

/-- The other precision; `cvtPrec p` converts from `p` to `p.other`. -/
def Precision.other : Precision → Precision
  | .single => .double
  | .double => .single

@[simp] theorem Precision.other_other (p : Precision) : p.other.other = p := by cases p <;> rfl

theorem Precision.width_le (p : Precision) : p.width ≤ 128 := by cases p <;> decide

/-- The low scalar lane of a 128-bit register. -/
def lane : (p : Precision) → BitVec 128 → Bits p.fmt
  | .single, v => v.extractLsb' 0 32
  | .double, v => v.extractLsb' 0 64

/-- Replace the low lane and keep bits 127:width, as scalar arithmetic,
register-to-register MOVSS/MOVSD, CVTSI2SS/SD, CVTSS2SD/CVTSD2SS, SQRTSS/SD,
ROUNDSS/SD and CMPSS/SD do on their destination (SDM Vol. 2 instruction
pages, operation sections: "DEST[MAXVL-1:32] (Unmodified)" for the legacy SSE
forms). -/
def setLane : (p : Precision) → BitVec 128 → Bits p.fmt → BitVec 128
  | .single, v, x => (v.extractLsb' 32 96 ++ (x : BitVec 32) : BitVec 128)
  | .double, v, x => (v.extractLsb' 64 64 ++ (x : BitVec 64) : BitVec 128)

/-- A 128-bit value whose low lane is `x` and whose other bits are zero, as
written by a MOVSS/MOVSD load (SDM Vol. 2B, MOVSS/MOVSD: "DEST[127:32] ← 0"
respectively "DEST[127:64] ← 0" for the memory source forms). -/
def zeroLane : (p : Precision) → Bits p.fmt → BitVec 128
  | .single, x => (x : BitVec 32).setWidth 128
  | .double, x => (x : BitVec 64).setWidth 128

private theorem setLane32_lane (v : BitVec 128) (x : BitVec 32) :
    (v.extractLsb' 32 96 ++ x : BitVec 128).extractLsb' 0 32 = x := by bv_decide

private theorem setLane64_lane (v : BitVec 128) (x : BitVec 64) :
    (v.extractLsb' 64 64 ++ x : BitVec 128).extractLsb' 0 64 = x := by bv_decide

private theorem zeroLane32_lane (x : BitVec 32) : (x.setWidth 128).extractLsb' 0 32 = x := by
  bv_decide

private theorem zeroLane64_lane (x : BitVec 64) : (x.setWidth 128).extractLsb' 0 64 = x := by
  bv_decide

@[simp] theorem lane_setLane (p : Precision) (v : BitVec 128) (x : Bits p.fmt) :
    lane p (setLane p v x) = x := by
  cases p
  · exact setLane32_lane v x
  · exact setLane64_lane v x

@[simp] theorem lane_zeroLane (p : Precision) (x : Bits p.fmt) : lane p (zeroLane p x) = x := by
  cases p
  · exact zeroLane32_lane x
  · exact zeroLane64_lane x

private theorem getLsbD_append_extract {w : Nat} (v : BitVec 128) (x : BitVec w) (hw : w ≤ 128)
    (i : Nat) :
    (v.extractLsb' w (128 - w) ++ x).getLsbD i =
      if i < w then x.getLsbD i else v.getLsbD i := by
  rw [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split
  · rfl
  · by_cases h : i < 128
    · simp only [show i - w < 128 - w by omega, decide_true, Bool.true_and]
      rw [show w + (i - w) = i by omega]
    · simp only [show ¬ i - w < 128 - w by omega, decide_false, Bool.false_and]
      exact (BitVec.getLsbD_of_ge v i (by omega)).symm

private theorem getLsbD_setWidth_128 {w : Nat} (x : BitVec w) (hw : w ≤ 128) (i : Nat) :
    (x.setWidth 128).getLsbD i = if i < w then x.getLsbD i else false := by
  rw [BitVec.getLsbD_setWidth]
  split
  · simp only [show i < 128 by omega, decide_true, Bool.true_and]
  · simp [BitVec.getLsbD_of_ge x i (by omega)]

/-- `setLane` agrees with the new lane below the lane width and with the old
value at and above it, bit for bit. -/
theorem getLsbD_setLane (p : Precision) (v : BitVec 128) (x : Bits p.fmt) (i : Nat) :
    (setLane p v x).getLsbD i = if i < p.width then x.getLsbD i else v.getLsbD i := by
  cases p
  · exact getLsbD_append_extract v (x : BitVec 32) (by decide) i
  · exact getLsbD_append_extract v (x : BitVec 64) (by decide) i

/-- `setLane` keeps every bit at or above the lane width. -/
theorem getLsbD_setLane_upper (p : Precision) (v : BitVec 128) (x : Bits p.fmt) {i : Nat}
    (hi : p.width ≤ i) : (setLane p v x).getLsbD i = v.getLsbD i := by
  rw [getLsbD_setLane]
  simp only [show ¬ i < p.width by omega, ↓reduceIte]

/-- `zeroLane` clears every bit at or above the lane width. -/
theorem getLsbD_zeroLane_upper (p : Precision) (x : Bits p.fmt) {i : Nat}
    (hi : p.width ≤ i) : (zeroLane p x).getLsbD i = false := by
  cases p <;> simp only [Precision.width] at hi
  · have h := getLsbD_setWidth_128 (w := 32) x (by decide) i
    simp only [show ¬ i < 32 by omega, ↓reduceIte] at h
    exact h
  · have h := getLsbD_setWidth_128 (w := 64) x (by decide) i
    simp only [show ¬ i < 64 by omega, ↓reduceIte] at h
    exact h

/-! ## Little-endian byte images -/

/-- The four bytes of a 32-bit value, least significant first. -/
def le32 (v : BitVec 32) : List Byte :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8]

/-- The value of exactly four little-endian bytes. -/
def ofLe32? : List Byte → Option (BitVec 32)
  | [b0, b1, b2, b3] => some (b3 ++ b2 ++ b1 ++ b0)
  | _ => none

/-- The eight bytes of a 64-bit value, least significant first. -/
def le64 (v : BitVec 64) : List Byte :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
    v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8]

/-- The value of exactly eight little-endian bytes. -/
def ofLe64? : List Byte → Option (BitVec 64)
  | [b0, b1, b2, b3, b4, b5, b6, b7] => some (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)
  | _ => none

/-- The value of exactly sixteen little-endian bytes. -/
def ofLe128? (bytes : List Byte) : Option (BitVec 128) :=
  match ofLe64? (bytes.take 8), ofLe64? (bytes.drop 8) with
  | some lo, some hi => some (hi ++ lo)
  | _, _ => none

@[simp] theorem length_le32 (v : BitVec 32) : (le32 v).length = 4 := rfl
@[simp] theorem length_le64 (v : BitVec 64) : (le64 v).length = 8 := rfl

@[simp] theorem ofLe32?_le32 (v : BitVec 32) : ofLe32? (le32 v) = some v := by
  simp only [le32, ofLe32?, Option.some.injEq]
  bv_decide

@[simp] theorem ofLe64?_le64 (v : BitVec 64) : ofLe64? (le64 v) = some v := by
  simp only [le64, ofLe64?, Option.some.injEq]
  bv_decide

theorem ofLe32?_isSome {bytes : List Byte} (h : bytes.length = 4) :
    ∃ v, ofLe32? bytes = some v := by
  match bytes, h with
  | [_, _, _, _], _ => exact ⟨_, rfl⟩

theorem ofLe64?_isSome {bytes : List Byte} (h : bytes.length = 8) :
    ∃ v, ofLe64? bytes = some v := by
  match bytes, h with
  | [_, _, _, _, _, _, _, _], _ => exact ⟨_, rfl⟩

theorem ofLe128?_isSome {bytes : List Byte} (h : bytes.length = 16) :
    ∃ v, ofLe128? bytes = some v := by
  obtain ⟨lo, hlo⟩ := ofLe64?_isSome (bytes := bytes.take 8) (by simp [h])
  obtain ⟨hi, hhi⟩ := ofLe64?_isSome (bytes := bytes.drop 8) (by simp [h])
  exact ⟨hi ++ lo, by simp [ofLe128?, hlo, hhi]⟩

/-- The byte image of a scalar lane (`m32` or `m64`). -/
def encodeLane : (p : Precision) → Bits p.fmt → List Byte
  | .single, x => le32 x
  | .double, x => le64 x

/-- The scalar lane held by exactly `p.bytes` little-endian bytes. -/
def decodeLane? : (p : Precision) → List Byte → Option (Bits p.fmt)
  | .single, bytes => ofLe32? bytes
  | .double, bytes => ofLe64? bytes

@[simp] theorem length_encodeLane (p : Precision) (x : Bits p.fmt) :
    (encodeLane p x).length = p.bytes := by
  cases p <;> rfl

@[simp] theorem decodeLane?_encodeLane (p : Precision) (x : Bits p.fmt) :
    decodeLane? p (encodeLane p x) = some x := by
  cases p
  · exact ofLe32?_le32 x
  · exact ofLe64?_le64 x

theorem decodeLane?_isSome (p : Precision) {bytes : List Byte} (h : bytes.length = p.bytes) :
    ∃ x, decodeLane? p bytes = some x := by
  cases p
  · exact ofLe32?_isSome h
  · exact ofLe64?_isSome h

/-! ## MXCSR -/

/-- The six SIMD floating-point exceptions of SDM Vol. 1, §11.5.1, in MXCSR
flag order: invalid operation (#I), denormal operand (#D), divide-by-zero (#Z),
numeric overflow (#O), numeric underflow (#U) and inexact result or precision
(#P). Used both as a set of detected exceptions and as a set of flags. -/
structure Exceptions where
  invalid : Bool := false
  denormal : Bool := false
  divideByZero : Bool := false
  overflow : Bool := false
  underflow : Bool := false
  precision : Bool := false
  deriving DecidableEq, Repr

namespace Exceptions

/-- Union of two exception sets. -/
def union (a b : Exceptions) : Exceptions where
  invalid := a.invalid || b.invalid
  denormal := a.denormal || b.denormal
  divideByZero := a.divideByZero || b.divideByZero
  overflow := a.overflow || b.overflow
  underflow := a.underflow || b.underflow
  precision := a.precision || b.precision

/-- The set as MXCSR flag bits 5:0 (PE UE OE ZE DE IE, most significant first). -/
def toBits (e : Exceptions) : BitVec 32 :=
  0#26 ++ BitVec.ofBool e.precision ++ BitVec.ofBool e.underflow ++ BitVec.ofBool e.overflow ++
    BitVec.ofBool e.divideByZero ++ BitVec.ofBool e.denormal ++ BitVec.ofBool e.invalid

private theorem toBits_low (e : Exceptions) :
    e.toBits.getLsbD 0 = e.invalid ∧ e.toBits.getLsbD 1 = e.denormal ∧
      e.toBits.getLsbD 2 = e.divideByZero ∧ e.toBits.getLsbD 3 = e.overflow ∧
      e.toBits.getLsbD 4 = e.underflow ∧ e.toBits.getLsbD 5 = e.precision := by
  simp (config := { decide := true }) only [toBits, BitVec.getLsbD_append, BitVec.getLsbD_ofBool,
    Bool.true_and, and_self, ite_true, ite_false, decide_true, decide_false, Bool.false_and]

@[simp] theorem toBits_getLsbD_0 (e : Exceptions) : e.toBits.getLsbD 0 = e.invalid :=
  (toBits_low e).1
@[simp] theorem toBits_getLsbD_1 (e : Exceptions) : e.toBits.getLsbD 1 = e.denormal :=
  (toBits_low e).2.1
@[simp] theorem toBits_getLsbD_2 (e : Exceptions) : e.toBits.getLsbD 2 = e.divideByZero :=
  (toBits_low e).2.2.1
@[simp] theorem toBits_getLsbD_3 (e : Exceptions) : e.toBits.getLsbD 3 = e.overflow :=
  (toBits_low e).2.2.2.1
@[simp] theorem toBits_getLsbD_4 (e : Exceptions) : e.toBits.getLsbD 4 = e.underflow :=
  (toBits_low e).2.2.2.2.1
@[simp] theorem toBits_getLsbD_5 (e : Exceptions) : e.toBits.getLsbD 5 = e.precision :=
  (toBits_low e).2.2.2.2.2

/-- Only bits 5:0 of `toBits` can be set. -/
theorem toBits_getLsbD_of_ge (e : Exceptions) {i : Nat} (hi : 6 ≤ i) :
    e.toBits.getLsbD i = false := by
  simp only [toBits, BitVec.getLsbD_append, BitVec.getLsbD_ofBool, BitVec.getLsbD_zero]
  repeat' split
  all_goals first | omega | simp_all

theorem toBits_union (a b : Exceptions) : (a.union b).toBits = a.toBits ||| b.toBits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or]
  by_cases h : 6 ≤ i
  · simp only [toBits_getLsbD_of_ge _ h, Bool.or_false]
  · have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [toBits_getLsbD_0, toBits_getLsbD_1, toBits_getLsbD_2, toBits_getLsbD_3,
        toBits_getLsbD_4, toBits_getLsbD_5, union]

@[simp] theorem union_empty (a : Exceptions) : a.union {} = a := by
  cases a; simp [union]

@[simp] theorem empty_union (a : Exceptions) : Exceptions.union {} a = a := by
  cases a; simp [union]

end Exceptions

/-- The MXCSR register (SDM Vol. 1, §10.2.3, Figure 10-3). -/
structure MXCSR where
  bits : BitVec 32
  deriving DecidableEq, Repr

namespace MXCSR

variable (m : MXCSR)

/-- IE, bit 0: invalid-operation flag. -/
def ie : Bool := m.bits.getLsbD 0
/-- DE, bit 1: denormal-operand flag. -/
def de : Bool := m.bits.getLsbD 1
/-- ZE, bit 2: divide-by-zero flag. -/
def ze : Bool := m.bits.getLsbD 2
/-- OE, bit 3: overflow flag. -/
def oe : Bool := m.bits.getLsbD 3
/-- UE, bit 4: underflow flag. -/
def ue : Bool := m.bits.getLsbD 4
/-- PE, bit 5: precision flag. -/
def pe : Bool := m.bits.getLsbD 5
/-- DAZ, bit 6: denormals are zeros (SDM Vol. 1, §10.2.3.4). -/
def daz : Bool := m.bits.getLsbD 6
/-- IM, bit 7: invalid-operation mask. -/
def im : Bool := m.bits.getLsbD 7
/-- DM, bit 8: denormal-operand mask. -/
def dm : Bool := m.bits.getLsbD 8
/-- ZM, bit 9: divide-by-zero mask. -/
def zm : Bool := m.bits.getLsbD 9
/-- OM, bit 10: overflow mask. -/
def om : Bool := m.bits.getLsbD 10
/-- UM, bit 11: underflow mask. -/
def um : Bool := m.bits.getLsbD 11
/-- PM, bit 12: precision mask. -/
def pm : Bool := m.bits.getLsbD 12
/-- RC, bits 14:13: rounding control (SDM Vol. 1, §10.2.3.2 and Table 4-8). -/
def rc : BitVec 2 := m.bits.extractLsb' 13 2
/-- FZ, bit 15: flush to zero (SDM Vol. 1, §10.2.3.3). -/
def fz : Bool := m.bits.getLsbD 15

/-- The sticky flags as an exception set. -/
def flags : Exceptions := ⟨m.ie, m.de, m.ze, m.oe, m.ue, m.pe⟩

/-- Reserved bits 31:16 are zero. Loading a value that violates this with
LDMXCSR raises #GP (SDM Vol. 2A, LDMXCSR). -/
def WellFormed : Prop := m.bits.extractLsb' 16 16 = 0#16

instance : Decidable m.WellFormed := inferInstanceAs (Decidable (_ = _))

/-- The power-up and reset value `1F80H` (SDM Vol. 1, §10.2.3). -/
def reset : MXCSR := ⟨0x1F80#32⟩

/-- Record detected exceptions in the sticky flags: MXCSR flags are set by
the instruction that detects the condition and are never cleared by it (SDM
Vol. 1, §10.2.3.1). -/
def record (e : Exceptions) : MXCSR := ⟨m.bits ||| e.toBits⟩

/-- Whether some exception of the set has its mask bit clear. -/
def unmasked (e : Exceptions) : Bool :=
  (e.invalid && !m.im) || (e.denormal && !m.dm) || (e.divideByZero && !m.zm) ||
    (e.overflow && !m.om) || (e.underflow && !m.um) || (e.precision && !m.pm)

/-- All six exceptions are masked. -/
def AllMasked : Prop := (m.im && m.dm && m.zm && m.om && m.um && m.pm) = true

instance : Decidable m.AllMasked := inferInstanceAs (Decidable (_ = _))

/-- The result-affecting controls passed to the shared profile. Flush-to-zero
applies only while underflow is masked (SDM Vol. 1, §10.2.3.3). -/
def control : MXCSRControl where
  denormalsAreZeros := m.daz
  flushToZero := m.fz && m.um
  rounding := x86RoundingControl m.rc

/-- The floating-point profile of this MXCSR value. -/
def profile : Profile := Profile.x86SSE m.control

/-- The dynamic rounding direction selected by RC. -/
def rounding : Numeric.Ieee754.RoundingMode := x86RoundingControl m.rc

@[simp] theorem control_rounding : m.control.rounding = m.rounding := rfl
@[simp] theorem profile_flushInputs : m.profile.flushInputs = m.daz := rfl

/-- `control` is the shared decoding of the raw bits. -/
theorem control_eq_ofBits : m.control = MXCSRControl.ofBits m.bits := rfl

/-! ### The reset value -/

theorem reset_wellFormed : reset.WellFormed := by decide

@[simp] theorem reset_flags : reset.flags = {} := by decide
theorem reset_allMasked : reset.AllMasked := by decide
@[simp] theorem reset_daz : reset.daz = false := by decide
@[simp] theorem reset_fz : reset.fz = false := by decide
@[simp] theorem reset_rc : reset.rc = 0#2 := by decide
@[simp] theorem reset_um : reset.um = true := by decide

/-- At reset the profile is the default x86 SSE profile: round to nearest even,
no DAZ, no FZ. -/
theorem reset_control : reset.control = {} := by decide

theorem reset_profile : reset.profile = Profile.x86SSE {} := by
  rw [profile, reset_control]

theorem reset_rounding : reset.rounding = .nearestTiesToEven := by decide

/-! ### Recording exceptions -/

section Record

variable (e : Exceptions)

@[simp] theorem record_ie : (m.record e).ie = (m.ie || e.invalid) := by
  simp only [record, ie, BitVec.getLsbD_or, Exceptions.toBits_getLsbD_0]
@[simp] theorem record_de : (m.record e).de = (m.de || e.denormal) := by
  simp only [record, de, BitVec.getLsbD_or, Exceptions.toBits_getLsbD_1]
@[simp] theorem record_ze : (m.record e).ze = (m.ze || e.divideByZero) := by
  simp only [record, ze, BitVec.getLsbD_or, Exceptions.toBits_getLsbD_2]
@[simp] theorem record_oe : (m.record e).oe = (m.oe || e.overflow) := by
  simp only [record, oe, BitVec.getLsbD_or, Exceptions.toBits_getLsbD_3]
@[simp] theorem record_ue : (m.record e).ue = (m.ue || e.underflow) := by
  simp only [record, ue, BitVec.getLsbD_or, Exceptions.toBits_getLsbD_4]
@[simp] theorem record_pe : (m.record e).pe = (m.pe || e.precision) := by
  simp only [record, pe, BitVec.getLsbD_or, Exceptions.toBits_getLsbD_5]

/-- Recording only sets flag bits 5:0; every other bit is unchanged. -/
theorem record_getLsbD_of_ge {i : Nat} (hi : 6 ≤ i) :
    (m.record e).bits.getLsbD i = m.bits.getLsbD i := by
  simp only [record, BitVec.getLsbD_or, e.toBits_getLsbD_of_ge hi, Bool.or_false]

@[simp] theorem record_daz : (m.record e).daz = m.daz := record_getLsbD_of_ge m e (by decide)
@[simp] theorem record_im : (m.record e).im = m.im := record_getLsbD_of_ge m e (by decide)
@[simp] theorem record_dm : (m.record e).dm = m.dm := record_getLsbD_of_ge m e (by decide)
@[simp] theorem record_zm : (m.record e).zm = m.zm := record_getLsbD_of_ge m e (by decide)
@[simp] theorem record_om : (m.record e).om = m.om := record_getLsbD_of_ge m e (by decide)
@[simp] theorem record_um : (m.record e).um = m.um := record_getLsbD_of_ge m e (by decide)
@[simp] theorem record_pm : (m.record e).pm = m.pm := record_getLsbD_of_ge m e (by decide)
@[simp] theorem record_fz : (m.record e).fz = m.fz := record_getLsbD_of_ge m e (by decide)

@[simp] theorem record_rc : (m.record e).rc = m.rc := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [rc, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  exact record_getLsbD_of_ge m e (by omega)

@[simp] theorem record_control : (m.record e).control = m.control := by
  simp [control]

@[simp] theorem record_profile : (m.record e).profile = m.profile := by
  simp [profile]

@[simp] theorem record_rounding : (m.record e).rounding = m.rounding := by
  simp [rounding]

@[simp] theorem record_unmasked (e' : Exceptions) : (m.record e).unmasked e' = m.unmasked e' := by
  simp [unmasked]

theorem record_allMasked : (m.record e).AllMasked ↔ m.AllMasked := by
  simp [AllMasked]

/-- The sticky flags after recording are the union. -/
@[simp] theorem record_flags : (m.record e).flags = m.flags.union e := by
  simp [flags, Exceptions.union]

theorem record_wellFormed (h : m.WellFormed) : (m.record e).WellFormed := by
  unfold WellFormed at h ⊢
  rw [← h]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  exact record_getLsbD_of_ge m e (by omega)

@[simp] theorem record_empty : m.record {} = m := by
  cases m
  simp only [record, MXCSR.mk.injEq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or]
  by_cases h : 6 ≤ i
  · rw [Exceptions.toBits_getLsbD_of_ge _ h, Bool.or_false]
  · have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Exceptions.toBits_getLsbD_0, Exceptions.toBits_getLsbD_1,
        Exceptions.toBits_getLsbD_2, Exceptions.toBits_getLsbD_3, Exceptions.toBits_getLsbD_4,
        Exceptions.toBits_getLsbD_5, Bool.or_false]

theorem record_record (e' : Exceptions) : (m.record e).record e' = m.record (e.union e') := by
  simp only [record, Exceptions.toBits_union, BitVec.or_assoc]

end Record

/-- No exception is unmasked when all are masked. -/
theorem unmasked_eq_false_of_allMasked {m : MXCSR} (h : m.AllMasked) (e : Exceptions) :
    m.unmasked e = false := by
  simp only [AllMasked, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨him, hdm⟩, hzm⟩, hom⟩, hum⟩, hpm⟩ := h
  simp [unmasked, him, hdm, hzm, hom, hum, hpm]

end MXCSR

/-! ## Architectural state -/

/-- The integer state, the sixteen XMM registers and MXCSR. -/
structure State where
  core : X86.State
  xmm : Machine.RegisterFile XReg (BitVec 128)
  mxcsr : MXCSR

namespace State

variable (s : State)

/-- A full 128-bit XMM register read. -/
def readX (r : XReg) : BitVec 128 := s.xmm r

/-- A full 128-bit XMM register write. -/
def writeX (r : XReg) (v : BitVec 128) : State :=
  { s with xmm := Machine.RegisterFile.write s.xmm r v }

/-- A full 64-bit general-purpose register write. -/
def writeGpr (r : Reg) (v : Word) : State := { s with core := s.core.write r v }

@[simp] theorem readX_writeX_same (r : XReg) (v : BitVec 128) : (s.writeX r v).readX r = v := by
  simp [readX, writeX]

@[simp] theorem readX_writeX_other {r q : XReg} (v : BitVec 128) (h : q ≠ r) :
    (s.writeX r v).readX q = s.readX q := by
  simp [readX, writeX, h]

@[simp] theorem writeX_core (r : XReg) (v : BitVec 128) : (s.writeX r v).core = s.core := rfl
@[simp] theorem writeX_mxcsr (r : XReg) (v : BitVec 128) : (s.writeX r v).mxcsr = s.mxcsr := rfl
@[simp] theorem writeGpr_xmm (r : Reg) (v : Word) : (s.writeGpr r v).xmm = s.xmm := rfl
@[simp] theorem writeGpr_mxcsr (r : Reg) (v : Word) : (s.writeGpr r v).mxcsr = s.mxcsr := rfl
@[simp] theorem writeGpr_core (r : Reg) (v : Word) : (s.writeGpr r v).core = s.core.write r v :=
  rfl

@[simp] theorem readX_writeGpr (r : Reg) (v : Word) (q : XReg) :
    (s.writeGpr r v).readX q = s.readX q := rfl

end State

end Silmaril.X86.Float
