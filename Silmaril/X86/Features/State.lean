module

public import Silmaril.X86.Float.State

/-!
# The extended architectural state

`State` extends the integer user-mode state `X86.State` (general-purpose
registers, RIP, the six arithmetic flags and the FS base) with the vector,
mask, SIMD-control and x87 state user-mode code can observe:

* `zmm`: the 32 vector registers ZMM0–ZMM31 (SDM Vol. 1, §15.1). XMMi and YMMi
  are the low 128 and 256 bits of ZMMi (`xmm`, `ymm`). Registers 16–31 exist only
  with AVX-512 and are reachable only through EVEX encodings.
* `k`: the eight 64-bit opmask registers k0–k7 (SDM Vol. 1, §15.1.3).
* `mxcsr`: MXCSR, reusing `Float.MXCSR` (bits, fields, `profile`).
* `x87`: the x87 FPU state (SDM Vol. 1, §8.1): the eight 80-bit physical data
  registers R0–R7, the status word (with TOP in bits 13:11), the control word
  and the full 16-bit tag word. The last-instruction and last-data pointers
  (FIP, FDP, FOP) are not modelled.

## Writes to vector registers

The SDM distinguishes legacy-SSE and VEX/EVEX writes of a register narrower
than the maximum vector length (SDM Vol. 1, §14.1.3 and §15.5):

* a legacy-SSE instruction writing XMMi leaves bits MAXVL-1:128 unchanged
  (`writeXmmLegacy`, `zmm_writeXmmLegacy_upper`);
* a VEX.128 or EVEX.128 write zeroes bits MAXVL-1:128 (`writeXmmVex`), and a
  VEX.256/EVEX.256 write zeroes bits MAXVL-1:256 (`writeYmmVex`).

The model fixes MAXVL = 512, i.e. it describes a processor with AVX-512 state.
On processors without AVX-512 the bits above 255 do not exist; since no
instruction there can read them, a program verified on this state behaves the
same on a processor with a smaller register file.

## The scalar SSE view

`toFloat` projects to the scalar-SSE state `Float.State` (core, XMM0–XMM15 and
MXCSR) and `withFloat` writes such a state back as a legacy-SSE instruction
would: XMM0–XMM15 take the new low 128 bits, every upper bit and every other
component is kept (`toFloat_withFloat`, `withFloat_toFloat`).
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86.Float (MXCSR)

/-! ## Bit-vector slicing lemmas -/

theorem extractLsb'_zero_append {n m : Nat} (u : BitVec n) (v : BitVec m) :
    (u ++ v).extractLsb' 0 m = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_append, hi]

theorem extractLsb'_append_high {n m : Nat} (u : BitVec n) (v : BitVec m) :
    (u ++ v).extractLsb' m n = u := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_append, hi]

theorem extractLsb'_zero_setWidth {n m : Nat} (h : n ≤ m) (v : BitVec n) :
    (v.setWidth m).extractLsb' 0 n = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_setWidth, hi]; omega

theorem extractLsb'_setWidth_high {n m k : Nat} (v : BitVec n) :
    (v.setWidth m).extractLsb' n k = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']

theorem extractLsb'_append_extractLsb' {n m : Nat} (w : BitVec (n + m)) :
    w.extractLsb' m n ++ w.extractLsb' 0 m = w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split
  · simp [*]
  · simp only [show i - m < n by omega, decide_true, Bool.true_and]; congr 1; omega

theorem getLsbD_append_low {n m : Nat} (u : BitVec n) (v : BitVec m) (k : Nat) (hk : k < m) :
    (u ++ v).getLsbD k = v.getLsbD k := by
  simp [BitVec.getLsbD_append, hk]

theorem getLsbD_append_high {n m : Nat} (u : BitVec n) (v : BitVec m) (k : Nat) (hk : m ≤ k) :
    (u ++ v).getLsbD k = u.getLsbD (k - m) := by
  simp [BitVec.getLsbD_append]; omega

/-- A vector register number, 0–31. -/
abbrev VReg := Fin 32

/-- An opmask register number, 0–7. -/
abbrev KReg := Fin 8

/-- The vector register holding an SSE register. -/
def _root_.Silmaril.X86.XReg.toV (r : XReg) : VReg := ⟨r.toBitVec.toNat, by omega⟩

theorem _root_.Silmaril.X86.XReg.toV_injective : Function.Injective XReg.toV := by
  intro r q h
  apply XReg.toBitVec_injective
  apply BitVec.eq_of_toNat_eq
  simpa [XReg.toV] using congrArg Fin.val h

theorem _root_.Silmaril.X86.XReg.toV_lt (r : XReg) : r.toV.val < 16 := by
  simp only [XReg.toV]; omega

/-! ## x87 -/

/-- The x87 FPU state. `regs` is indexed by physical register; ST(i) is
`regs (TOP + i)`. -/
structure X87 where
  regs : Fin 8 → BitVec 80
  status : BitVec 16
  control : BitVec 16
  tag : BitVec 16

namespace X87

/-- TOP, status word bits 13:11. -/
def top (x : X87) : BitVec 3 := x.status.extractLsb' 11 3

/-- The physical register of ST(i). -/
def phys (x : X87) (i : Fin 8) : Fin 8 := ⟨(x.top.toNat + i.val) % 8, Nat.mod_lt _ (by decide)⟩

/-- ST(i). -/
def st (x : X87) (i : Fin 8) : BitVec 80 := x.regs (x.phys i)

/-- Replace TOP, keeping the other status bits. -/
def setTop (x : X87) (t : BitVec 3) : X87 :=
  { x with status := (x.status.extractLsb' 14 2 ++ t ++ x.status.extractLsb' 0 11 : BitVec 16) }

theorem top_setTop (x : X87) (t : BitVec 3) : (x.setTop t).top = t := by
  simp only [top, setTop]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [getLsbD_append_high _ _ _ (by omega)]
  simp only [show 11 + i - 11 = i by omega]
  rw [getLsbD_append_low _ _ _ hi]

/-- The state after FNINIT (SDM Vol. 1, §8.1.10, Table 8-1): control word
`037FH`, status word 0, every tag empty; the data registers are unchanged. -/
def init (x : X87) : X87 := { x with status := 0, control := 0x037F, tag := 0xFFFF }

/-- The power-up state with zeroed data registers. -/
def reset : X87 := init ⟨fun _ => 0, 0, 0, 0⟩

/-- Precision control, control word bits 9:8 (00 single, 10 double, 11 extended). -/
def precisionControl (x : X87) : BitVec 2 := x.control.extractLsb' 8 2

/-- Rounding control, control word bits 11:10. -/
def roundingControl (x : X87) : BitVec 2 := x.control.extractLsb' 10 2

end X87

/-! ## The extended state -/

/-- The extended architectural state of one user-mode thread. -/
structure State where
  core : X86.State
  zmm : Machine.RegisterFile VReg (BitVec 512)
  k : Machine.RegisterFile KReg (BitVec 64)
  mxcsr : MXCSR
  x87 : X87

namespace State

variable (s : State)

/-- The power-up vector state over an integer state: zero vector and mask
registers, MXCSR `1F80H`, x87 after FNINIT. -/
def ofCore (core : X86.State) : State :=
  ⟨core, fun _ => 0, fun _ => 0, MXCSR.reset, X87.reset⟩

/-- RIP. -/
def rip : X86.Word := s.core.rip

/-- Set RIP. -/
def setRip (rip : X86.Word) : State := { s with core := { s.core with rip } }

/-- Advance RIP by an instruction length. -/
def advance (length : Nat) : State := s.setRip (s.rip + BitVec.ofNat 64 length)

/-- Replace the integer state. -/
def setCore (core : X86.State) : State := { s with core }

/-! ### Register views -/

/-- XMMi: bits 127:0 of ZMMi. -/
def xmm (i : VReg) : BitVec 128 := (s.zmm i).extractLsb' 0 128

/-- YMMi: bits 255:0 of ZMMi. -/
def ymm (i : VReg) : BitVec 256 := (s.zmm i).extractLsb' 0 256

/-- Bits 511:128 of ZMMi, kept by legacy-SSE writes. -/
def upper128 (i : VReg) : BitVec 384 := (s.zmm i).extractLsb' 128 384

/-- Write a whole ZMM register. -/
def writeZmm (i : VReg) (v : BitVec 512) : State :=
  { s with zmm := Machine.RegisterFile.write s.zmm i v }

/-- A legacy-SSE write of XMMi: bits 511:128 are kept. -/
def writeXmmLegacy (i : VReg) (v : BitVec 128) : State :=
  s.writeZmm i (s.upper128 i ++ v)

/-- A VEX.128/EVEX.128 write of XMMi: bits 511:128 are zeroed. -/
def writeXmmVex (i : VReg) (v : BitVec 128) : State := s.writeZmm i (v.setWidth 512)

/-- A VEX.256/EVEX.256 write of YMMi: bits 511:256 are zeroed. -/
def writeYmmVex (i : VReg) (v : BitVec 256) : State := s.writeZmm i (v.setWidth 512)

/-- Write an opmask register. -/
def writeK (i : KReg) (v : BitVec 64) : State := { s with k := Machine.RegisterFile.write s.k i v }

/-- Write MXCSR. -/
def setMxcsr (m : MXCSR) : State := { s with mxcsr := m }

/-- Write the x87 state. -/
def setX87 (x : X87) : State := { s with x87 := x }

/-! ### Frame lemmas -/

@[simp] theorem writeZmm_zmm_same (i : VReg) (v : BitVec 512) : (s.writeZmm i v).zmm i = v := by
  simp [writeZmm]

@[simp] theorem writeZmm_zmm_other {i j : VReg} (v : BitVec 512) (h : j ≠ i) :
    (s.writeZmm i v).zmm j = s.zmm j := by
  simp [writeZmm, h]

@[simp] theorem writeZmm_core (i : VReg) (v : BitVec 512) : (s.writeZmm i v).core = s.core := rfl
@[simp] theorem writeZmm_k (i : VReg) (v : BitVec 512) : (s.writeZmm i v).k = s.k := rfl
@[simp] theorem writeZmm_mxcsr (i : VReg) (v : BitVec 512) : (s.writeZmm i v).mxcsr = s.mxcsr := rfl
@[simp] theorem writeZmm_x87 (i : VReg) (v : BitVec 512) : (s.writeZmm i v).x87 = s.x87 := rfl

@[simp] theorem writeK_core (i : KReg) (v : BitVec 64) : (s.writeK i v).core = s.core := rfl
@[simp] theorem writeK_zmm (i : KReg) (v : BitVec 64) : (s.writeK i v).zmm = s.zmm := rfl
@[simp] theorem writeK_k_same (i : KReg) (v : BitVec 64) : (s.writeK i v).k i = v := by
  simp [writeK]
@[simp] theorem writeK_k_other {i j : KReg} (v : BitVec 64) (h : j ≠ i) :
    (s.writeK i v).k j = s.k j := by
  simp [writeK, h]

@[simp] theorem setRip_rip (r : X86.Word) : (s.setRip r).rip = r := rfl
@[simp] theorem setRip_zmm (r : X86.Word) : (s.setRip r).zmm = s.zmm := rfl
@[simp] theorem setRip_k (r : X86.Word) : (s.setRip r).k = s.k := rfl
@[simp] theorem setRip_mxcsr (r : X86.Word) : (s.setRip r).mxcsr = s.mxcsr := rfl
@[simp] theorem setRip_x87 (r : X86.Word) : (s.setRip r).x87 = s.x87 := rfl
@[simp] theorem setRip_regs (r : X86.Word) : (s.setRip r).core.regs = s.core.regs := rfl
@[simp] theorem setRip_flags (r : X86.Word) : (s.setRip r).core.flags = s.core.flags := rfl

@[simp] theorem advance_rip (n : Nat) : (s.advance n).rip = s.rip + BitVec.ofNat 64 n := rfl
@[simp] theorem advance_zmm (n : Nat) : (s.advance n).zmm = s.zmm := rfl
@[simp] theorem advance_k (n : Nat) : (s.advance n).k = s.k := rfl
@[simp] theorem advance_mxcsr (n : Nat) : (s.advance n).mxcsr = s.mxcsr := rfl
@[simp] theorem advance_x87 (n : Nat) : (s.advance n).x87 = s.x87 := rfl

private theorem extract_low_append (u : BitVec 384) (v : BitVec 128) :
    (u ++ v : BitVec 512).extractLsb' 0 128 = v := extractLsb'_zero_append u v

private theorem extract_high_append (u : BitVec 384) (v : BitVec 128) :
    (u ++ v : BitVec 512).extractLsb' 128 384 = u := extractLsb'_append_high u v

private theorem extract_low_setWidth (v : BitVec 128) :
    (v.setWidth 512).extractLsb' 0 128 = v := extractLsb'_zero_setWidth (by decide) v

private theorem extract_high_setWidth (v : BitVec 128) :
    (v.setWidth 512).extractLsb' 128 384 = 0 := extractLsb'_setWidth_high v

private theorem extract_ymm_setWidth (v : BitVec 256) :
    (v.setWidth 512).extractLsb' 0 256 = v := extractLsb'_zero_setWidth (by decide) v

private theorem extract_ymm_high_setWidth (v : BitVec 256) :
    (v.setWidth 512).extractLsb' 256 256 = 0 := extractLsb'_setWidth_high v

private theorem extract_ymm_append (w : BitVec 512) (v : BitVec 128) :
    ((w.extractLsb' 128 384 ++ v : BitVec 512).extractLsb' 0 256).extractLsb' 128 128 =
      (w.extractLsb' 0 256).extractLsb' 128 128 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb']
  simp only [show i < 128 from hi, decide_true, Bool.true_and, show 128 + i < 256 by omega]
  rw [getLsbD_append_high _ v _ (by omega)]
  simp [BitVec.getLsbD_extractLsb']
  omega

private theorem extract_split (w : BitVec 512) :
    w.extractLsb' 128 384 ++ w.extractLsb' 0 128 = w :=
  extractLsb'_append_extractLsb' (n := 384) (m := 128) w

@[simp] theorem xmm_writeXmmLegacy_same (i : VReg) (v : BitVec 128) :
    (s.writeXmmLegacy i v).xmm i = v := by
  simp [writeXmmLegacy, xmm, extract_low_append]

/-- A legacy-SSE write keeps bits 511:128. -/
@[simp] theorem upper128_writeXmmLegacy_same (i : VReg) (v : BitVec 128) :
    (s.writeXmmLegacy i v).upper128 i = s.upper128 i := by
  simp [writeXmmLegacy, upper128, extract_high_append]

/-- A legacy-SSE write keeps bits 255:128 of the YMM view. -/
theorem ymm_high_writeXmmLegacy_same (i : VReg) (v : BitVec 128) :
    ((s.writeXmmLegacy i v).ymm i).extractLsb' 128 128 = (s.ymm i).extractLsb' 128 128 := by
  simp only [ymm, writeXmmLegacy, writeZmm_zmm_same, upper128]
  exact extract_ymm_append (s.zmm i) v

/-- Equivalently: the whole register is the old upper part over the new low part. -/
theorem zmm_writeXmmLegacy_same (i : VReg) (v : BitVec 128) :
    (s.writeXmmLegacy i v).zmm i = s.upper128 i ++ v := by
  simp [writeXmmLegacy]

@[simp] theorem xmm_writeXmmVex_same (i : VReg) (v : BitVec 128) :
    (s.writeXmmVex i v).xmm i = v := by
  simp [writeXmmVex, xmm, extract_low_setWidth]

/-- A VEX/EVEX.128 write zeroes bits 511:128. -/
@[simp] theorem upper128_writeXmmVex_same (i : VReg) (v : BitVec 128) :
    (s.writeXmmVex i v).upper128 i = 0 := by
  simp [writeXmmVex, upper128, extract_high_setWidth]

@[simp] theorem ymm_writeYmmVex_same (i : VReg) (v : BitVec 256) :
    (s.writeYmmVex i v).ymm i = v := by
  simp [writeYmmVex, ymm, extract_ymm_setWidth]

/-- A VEX/EVEX.256 write zeroes bits 511:256. -/
theorem zmm_high_writeYmmVex_same (i : VReg) (v : BitVec 256) :
    ((s.writeYmmVex i v).zmm i).extractLsb' 256 256 = 0 := by
  simp [writeYmmVex, extract_ymm_high_setWidth]

@[simp] theorem writeXmmLegacy_zmm_other {i j : VReg} (v : BitVec 128) (h : j ≠ i) :
    (s.writeXmmLegacy i v).zmm j = s.zmm j := by
  simp [writeXmmLegacy, h]

@[simp] theorem writeXmmVex_zmm_other {i j : VReg} (v : BitVec 128) (h : j ≠ i) :
    (s.writeXmmVex i v).zmm j = s.zmm j := by
  simp [writeXmmVex, h]

@[simp] theorem writeYmmVex_zmm_other {i j : VReg} (v : BitVec 256) (h : j ≠ i) :
    (s.writeYmmVex i v).zmm j = s.zmm j := by
  simp [writeYmmVex, h]

/-! ### The scalar SSE view -/

/-- The scalar-SSE state seen by `Float.Instr.exec`. -/
def toFloat : Float.State := ⟨s.core, fun r => s.xmm r.toV, s.mxcsr⟩

/-- Write back a scalar-SSE state as legacy SSE does: XMM0–15 take the new low
bits, bits 511:128, ZMM16–31, the opmasks and x87 are kept. -/
def withFloat (t : Float.State) : State :=
  { s with
    core := t.core
    mxcsr := t.mxcsr
    zmm := fun j =>
      if j.val < 16 then s.upper128 j ++ t.xmm (XReg.ofBitVec (BitVec.ofNat 4 j.val))
      else s.zmm j }

private theorem toV_ofBitVec (j : VReg) (h : j.val < 16) :
    (XReg.ofBitVec (BitVec.ofNat 4 j.val)).toV = j := by
  apply Fin.ext
  simp only [XReg.toV, XReg.toBitVec_ofBitVec, BitVec.toNat_ofNat]
  omega

@[simp] theorem toFloat_withFloat (t : Float.State) : (s.withFloat t).toFloat = t := by
  obtain ⟨core, xmmF, mxcsr⟩ := t
  simp only [toFloat, withFloat, xmm, Float.State.mk.injEq, true_and, and_true]
  funext r
  simp only [XReg.toV_lt r, ↓reduceIte]
  have : XReg.ofBitVec (BitVec.ofNat 4 r.toV.val) = r := by
    simp [XReg.toV]
  rw [this, extract_low_append]

@[simp] theorem withFloat_toFloat : s.withFloat s.toFloat = s := by
  obtain ⟨core, zmm, k, mxcsr, x87⟩ := s
  simp only [withFloat, toFloat, State.mk.injEq, true_and, and_true]
  funext j
  split
  · rename_i h
    simp only [xmm, upper128]
    rw [toV_ofBitVec j h]
    exact extract_split _
  · rfl

/-- `withFloat` keeps bits 511:128 of every register. -/
theorem zmm_withFloat (t : Float.State) (j : VReg) :
    (s.withFloat t).zmm j =
      if j.val < 16 then s.upper128 j ++ t.xmm (XReg.ofBitVec (BitVec.ofNat 4 j.val))
      else s.zmm j := rfl

@[simp] theorem upper128_withFloat (t : Float.State) (j : VReg) :
    (s.withFloat t).upper128 j = s.upper128 j := by
  show ((s.withFloat t).zmm j).extractLsb' 128 384 = s.upper128 j
  rw [zmm_withFloat]
  by_cases h : j.val < 16
  · simp only [h, ↓reduceIte]; exact extract_high_append _ _
  · simp only [h, ↓reduceIte]; rfl

@[simp] theorem withFloat_k (t : Float.State) : (s.withFloat t).k = s.k := rfl
@[simp] theorem withFloat_x87 (t : Float.State) : (s.withFloat t).x87 = s.x87 := rfl
@[simp] theorem withFloat_core (t : Float.State) : (s.withFloat t).core = t.core := rfl
@[simp] theorem withFloat_mxcsr (t : Float.State) : (s.withFloat t).mxcsr = t.mxcsr := rfl
@[simp] theorem toFloat_core : s.toFloat.core = s.core := rfl
@[simp] theorem toFloat_mxcsr : s.toFloat.mxcsr = s.mxcsr := rfl

/-- ZMM16–31 are untouched by a scalar-SSE write-back. -/
theorem withFloat_zmm_high (t : Float.State) {j : VReg} (h : 16 ≤ j.val) :
    (s.withFloat t).zmm j = s.zmm j := by
  rw [zmm_withFloat]
  simp only [show ¬ j.val < 16 by omega, ↓reduceIte]

end State

end Silmaril.X86.Features
