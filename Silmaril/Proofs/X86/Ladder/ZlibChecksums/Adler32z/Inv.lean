module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Frame
public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Arith
public import Silmaril.X86.BlockCert9.Thms
import Mathlib.Tactic.Ring

/-!
# `adler32_z`: cut-point invariants and the facts the segment VCs consume

Cut points (loop heads): `0x80` (the `NMAX` chunk loop, `DO16` body), `0x205` (the short
byte loop, `len < 16`), `0x2e3` (the `DO16` loop of the last partial chunk), `0x3e0` (the
byte tail). Stops: the four `ret`s (`0x1f6`, `0x274`, `0x2b2`, `0x462`), before the `ret`
executes; `Total.lean` adds that step.

The frame (`Fr`) after the prologue: `rsp = sp`, the memory is the entry memory changed only
in the area (`FM`), and the six pushed registers are at `sp + 8 i` (`Saved`). Spill slots
are stated as `loadN` facts at the exact addresses `seg_vc9` produces (`sp + c` with `c` a
literal).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN HoldsLE Stored leBytes)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86
open Silmaril.X86.Ladder.ZlibChecksums
open Silmaril.X86.Stencils.TableFold (bytesAt byteAt)
open Silmaril.X86.Stencils.ByteLoop (Readable Writable Apart arg1 arg2)
open Silmaril.X86.Stencils.AccumFold (rawFold rawStep modFold red)

namespace Ctx

variable (c : Ctx)

/-- The incoming checksum. -/
def a : Nat := (c.m0.core.read .rdi).toNat
/-- Byte `i` of the buffer, zero-extended. -/
def b (i : Nat) : Word := (c.bs.getD i 0).setWidth 64
/-- The reduced and raw sums of this call. -/
def S (k : Nat) : Nat × Nat := Adler32z.S c.bs c.a k
def R (k j : Nat) : Nat × Nat := Adler32z.R c.bs c.a k j
/-- The result. -/
def res : Word := if c.p.toNat = 0 then 1 else BitVec.ofNat 64 (adler32 c.a c.bs)

end Ctx

/-- The six registers pushed by the prologue, at `sp + 8 i` (`rbx` lowest). -/
structure Saved (c : Ctx) (mem : Memory) : Prop where
  rbx : mem.readBytes c.sp.toNat 8 = some (encodeWords [c.m0.core.read .rbx])
  rbp : mem.readBytes (c.sp + 8#64).toNat 8 = some (encodeWords [c.m0.core.read .rbp])
  r12 : mem.readBytes (c.sp + 16#64).toNat 8 = some (encodeWords [c.m0.core.read .r12])
  r13 : mem.readBytes (c.sp + 24#64).toNat 8 = some (encodeWords [c.m0.core.read .r13])
  r14 : mem.readBytes (c.sp + 32#64).toNat 8 = some (encodeWords [c.m0.core.read .r14])
  r15 : mem.readBytes (c.sp + 40#64).toNat 8 = some (encodeWords [c.m0.core.read .r15])

/-- The frame of every cut point. -/
structure Fr (c : Ctx) (s : MState) : Prop where
  pre : c.Pre
  sp : s.core.read .rsp = c.sp
  mem : FM c s.memory
  saved : Saved c s.memory
  nz : c.p.toNat ≠ 0

/-! ## Addresses -/

section Addr

variable {c : Ctx}

theorem sp_toNat (hP : c.Pre) : c.sp.toNat = c.lo + 48 := by
  have := hP.room; have := c.r0.isLt
  simp only [Ctx.sp, Ctx.lo, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem sp_add_toNat (hP : c.Pre) {k : Nat} (hk : k ≤ 40) :
    (c.sp + BitVec.ofNat 64 k).toNat = c.lo + 48 + k := by
  have := hP.room; have := c.r0.isLt
  simp only [Ctx.sp, Ctx.lo, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem sp_sub_toNat (hP : c.Pre) {k : Nat} (hk : 2 ^ 64 - 48 ≤ k) (hk' : k < 2 ^ 64) :
    (c.sp + BitVec.ofNat 64 k).toNat = c.lo + 48 + k - 2 ^ 64 := by
  have := hP.room; have := c.r0.isLt
  simp only [Ctx.sp, Ctx.lo, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem slot0 (hP : c.Pre) : (c.sp + 18446744073709551568#64).toNat = c.lo + 0 := by
  rw [sp_sub_toNat hP (by decide) (by decide)]; omega
theorem slot8 (hP : c.Pre) : (c.sp + 18446744073709551576#64).toNat = c.lo + 8 := by
  rw [sp_sub_toNat hP (by decide) (by decide)]; omega
theorem slot16 (hP : c.Pre) : (c.sp + 18446744073709551584#64).toNat = c.lo + 16 := by
  rw [sp_sub_toNat hP (by decide) (by decide)]; omega
theorem slot24 (hP : c.Pre) : (c.sp + 18446744073709551592#64).toNat = c.lo + 24 := by
  rw [sp_sub_toNat hP (by decide) (by decide)]; omega
theorem slot32 (hP : c.Pre) : (c.sp + 18446744073709551600#64).toNat = c.lo + 32 := by
  rw [sp_sub_toNat hP (by decide) (by decide)]; omega
theorem slot40 (hP : c.Pre) : (c.sp + 18446744073709551608#64).toNat = c.lo + 40 := by
  rw [sp_sub_toNat hP (by decide) (by decide)]; omega

end Addr

/-! ## Stores into the frame -/

section Store

variable {c : Ctx}

theorem Saved.store {mem after : Memory} (hP : c.Pre) (h : Saved c mem) {A v : Word}
    (hst : storeN mem A 8 v = some after) (hA : A.toNat + 8 ≤ c.lo + 48) : Saved c after := by
  have hS := Stored.of_storeN hst
  have k := fun (B : Nat) (hB : c.lo + 48 ≤ B) =>
    hS.readWith_disjoint .read B 8 (Or.inr (by simp; omega))
  have e0 := sp_toNat hP
  have e1 := sp_add_toNat hP (k := 8) (by decide)
  have e2 := sp_add_toNat hP (k := 16) (by decide)
  have e3 := sp_add_toNat hP (k := 24) (by decide)
  have e4 := sp_add_toNat hP (k := 32) (by decide)
  have e5 := sp_add_toNat hP (k := 40) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := h.rbx; simp only [Memory.readBytes] at this ⊢; rw [k _ (by omega)]; exact this
  · have := h.rbp; simp only [Memory.readBytes] at this ⊢; rw [k _ (by simp at e1 ⊢; omega)]; exact this
  · have := h.r12; simp only [Memory.readBytes] at this ⊢; rw [k _ (by simp at e2 ⊢; omega)]; exact this
  · have := h.r13; simp only [Memory.readBytes] at this ⊢; rw [k _ (by simp at e3 ⊢; omega)]; exact this
  · have := h.r14; simp only [Memory.readBytes] at this ⊢; rw [k _ (by simp at e4 ⊢; omega)]; exact this
  · have := h.r15; simp only [Memory.readBytes] at this ⊢; rw [k _ (by simp at e5 ⊢; omega)]; exact this

/-- **A spill store** at `lo + o` (`o < 48`): everything a VC needs about the new memory. -/
theorem spill {mem after : Memory} (hP : c.Pre) (hF : FM c mem) (hS : Saved c mem) {A v : Word}
    {o : Nat} (hA : A.toNat = c.lo + o) (ho : o + 8 ≤ 48)
    (hst : storeN mem A 8 v = some after) :
    FM c after ∧ Saved c after ∧ Loaded after c.base adler32zCode ∧ loadN after A 8 = some v ∧
      (∀ B j, B.toNat + j ≤ A.toNat ∨ A.toNat + 8 ≤ B.toNat → loadN after B j = loadN mem B j) := by
  have hF' := hF.store hst hA (by omega)
  refine ⟨hF', hS.store hP hst (by omega), hF'.loaded hP, ?_, fun B j hd =>
    Silmaril.X86.Ext.loadN_storeN_disjoint hst hd⟩
  exact Silmaril.X86.Ext.loadN_storeN_eight hst (by rw [hA]; exact (hF.permitted hP (by omega)).2)

/-- A spill store in a VC: the write permission, then everything about the new memory. -/
theorem store_go {mem : Memory} {P : Memory → Prop} (hP : c.Pre) (hF : FM c mem)
    (hS : Saved c mem) {A v : Word} {o : Nat} (hA : A.toNat = c.lo + o) (ho : o + 8 ≤ 48)
    (h : ∀ after, FM c after → Saved c after → Loaded after c.base adler32zCode →
      loadN after A 8 = some v →
      (∀ B j, B.toNat + j ≤ A.toNat ∨ A.toNat + 8 ≤ B.toNat → loadN after B j = loadN mem B j) →
      P after) :
    mem.Permitted .write A.toNat 8 ∧ ∀ after, storeN mem A 8 v = some after → P after := by
  refine ⟨by rw [hA]; exact (hF.permitted hP (by omega)).1, fun after hst => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := spill hP hF hS hA ho hst
  exact h after h1 h2 h3 h4 h5

/-- A slot fact survives a store into another slot. -/
theorem keep {mem after : Memory} {A B v : Word} {oa ob : Nat}
    (hD : ∀ B j, B.toNat + j ≤ A.toNat ∨ A.toNat + 8 ≤ B.toNat → loadN after B j = loadN mem B j)
    (hA : A.toNat = c.lo + oa) (hB : B.toNat = c.lo + ob) (hd : ob + 8 ≤ oa ∨ oa + 8 ≤ ob)
    (h : loadN mem B 8 = some v) : loadN after B 8 = some v := by
  rw [hD B 8 (by rw [hA, hB]; omega)]; exact h

theorem spill_perm {mem : Memory} (hP : c.Pre) (hF : FM c mem) {A : Word} {o : Nat}
    (hA : A.toNat = c.lo + o) (ho : o + 8 ≤ 96) : mem.Permitted .write A.toNat 8 := by
  rw [hA]; exact (hF.permitted hP ho).1

end Store

/-! ## The buffer -/

section Buf

variable {c : Ctx}

theorem bs_length : c.bs.length = c.n := by
  simp [Ctx.bs, buf, bytesAt, Ctx.n, arg2]

theorem p_fit (hP : c.Pre) (hz : c.p.toNat ≠ 0) {i : Nat} (hi : i < c.n) : c.p.toNat + i < 2 ^ 64 :=
  ((hP.buf hz).1 i hi).1

/-- A buffer byte, read in any frame memory. -/
theorem load_buf {mem : Memory} (hP : c.Pre) (hF : FM c mem) (hz : c.p.toNat ≠ 0) {i : Nat}
    (hi : i < c.n) : loadN mem (c.p + BitVec.ofNat 64 i) 1 = some (c.b i) := by
  obtain ⟨hR, hA⟩ := hP.buf hz
  obtain ⟨hlim, hperm, hsome⟩ := hR i hi
  have haddr : (c.p + BitVec.ofNat 64 i).toNat = c.p.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : i < 2 ^ 64 := by simp [Silmaril.Process.addressLimit] at hlim; omega
    rw [Nat.mod_eq_of_lt this]; exact Nat.mod_eq_of_lt (by simpa [Silmaril.Process.addressLimit] using hlim)
  unfold loadN
  rw [haddr, hF.readBytes_eq (by simp only [Apart] at hA; omega)]
  obtain ⟨byte, hb⟩ := Option.isSome_iff_exists.mp hsome
  have hrd : c.m0.memory.readBytes (c.p.toNat + i) 1 = some [byte] := by
    simp only [Memory.readBytes, Memory.readWith, Memory.checkSpan_iff]
    have hl2 : c.p.toNat + i < 2 ^ 64 := by simpa [Silmaril.Process.addressLimit] using hlim
    rw [ite_eq_left ⟨by simp [Silmaril.Process.addressLimit]; omega,
      by simp [Silmaril.Process.addressLimit]; omega, fun o ho => by
        rw [show o = 0 by omega]; simpa using hperm⟩]
    have hb' : c.m0.memory.bytes[c.p.toNat + i]? = some byte := hb
    simp [Memory.readBacking, hb']
  rw [hrd]
  simp only [Option.map_some, Option.some.injEq, Silmaril.X86.Ext.leValue, Nat.mul_zero, Nat.add_zero]
  have hbi : c.bs.getD i 0 = byte := by
    have hl : i < c.bs.length := by rw [bs_length]; exact hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
    have hb' : c.m0.memory.bytes[c.p.toNat + i]? = some byte := hb
    simp only [Ctx.p] at hb'
    simp [Ctx.bs, buf, bytesAt, byteAt, arg1, hb']
  simp only [Ctx.b, hbi]
  apply BitVec.eq_of_toNat_eq; simp

/-- The buffer bytes from a register holding `p + pos`. -/
theorem load_buf_off {mem : Memory} (hP : c.Pre) (hF : FM c mem) (hz : c.p.toNat ≠ 0) {X : Word}
    {pos : Nat} (hX : X = c.p + BitVec.ofNat 64 pos) :
    ∀ k, pos + k < c.n → loadN mem (X + BitVec.ofNat 64 k) 1 = some (c.b (pos + k)) := by
  intro k hk
  rw [hX, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact load_buf hP hF hz hk

/-- A loaded byte through `movzbl`. -/
theorem zx_b (c : Ctx) (i : Nat) :
    ((((c.b i).setWidth 8).setWidth 32).setWidth 64 : Word) = c.b i := by
  simp only [Ctx.b]; apply BitVec.eq_of_toNat_eq; simp

end Buf

/-! ## Steps -/

theorem Fr.with {c : Ctx} {s t : MState} (h : Fr c s) (hm : t.memory = s.memory)
    (hsp : t.core.read .rsp = c.sp) : Fr c t :=
  ⟨h.pre, hsp, hm ▸ h.mem, hm ▸ h.saved, h.nz⟩

theorem Fr.withMem {c : Ctx} {s t : MState} (h : Fr c s) (hF : FM c t.memory)
    (hS : Saved c t.memory) (hsp : t.core.read .rsp = c.sp) : Fr c t :=
  ⟨h.pre, hsp, hF, hS, h.nz⟩

theorem b_eq (c : Ctx) (i : Nat) : c.b i = BitVec.ofNat 64 (c.bs.getD i 0).toNat := by
  simp only [Ctx.b]; apply BitVec.eq_of_toNat_eq; simp

/-- One raw step, at `BitVec 64`. -/
theorem R_succW (c : Ctx) {k j : Nat} (h : k + j < c.n) :
    BitVec.ofNat 64 (c.R k (j + 1)).1 = BitVec.ofNat 64 (c.R k j).1 + c.b (k + j) ∧
    BitVec.ofNat 64 (c.R k (j + 1)).2 =
      BitVec.ofNat 64 (c.R k j).2 + (BitVec.ofNat 64 (c.R k j).1 + c.b (k + j)) := by
  have hR := R_succ c.bs c.a k j (by rw [bs_length]; exact h)
  simp only [Ctx.R, hR, rawStep, b_eq, BitVec.ofNat_add, BitVec.add_assoc, and_self]

theorem p_sub (c : Ctx) {i : Nat} (hi : i < 2 ^ 64) : (c.p + BitVec.ofNat 64 i - c.p).toNat = i := by
  rw [show c.p + BitVec.ofNat 64 i - c.p = BitVec.ofNat 64 i by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi]

theorem p_add_inj {c : Ctx} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : c.p + BitVec.ofNat 64 i = c.p + BitVec.ofNat 64 j) : i = j := by
  have := congrArg (fun x => (x - c.p).toNat) h
  simp only [p_sub c hi, p_sub c hj] at this; exact this

theorem n_lt (c : Ctx) : c.n < 2 ^ 64 := (c.m0.core.read .rdx).isLt

theorem sp_48 (c : Ctx) : c.sp + 48#64 = c.r0 := by simp [Ctx.sp]

/-- A reduced raw sum, at `BitVec 64`. -/
theorem modR (x : Nat) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 ((BitVec.ofNat 64 x).toNat % 65521) = BitVec.ofNat 64 (x % 65521) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- The raw sums of the last chunk, reduced, are the final sums. -/
theorem R_final (c : Ctx) {k : Nat} (hk : k ≤ c.n) :
    (c.R k (c.n - k)).1 % 65521 = (c.S c.n).1 ∧ (c.R k (c.n - k)).2 % 65521 = (c.S c.n).2 := by
  have := red_R c.bs c.a k (c.n - k)
  rw [show k + (c.n - k) = c.n by omega] at this
  simp only [red, BASE] at this
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- Packing the final sums is the result. -/
theorem pack_res (c : Ctx) (hz : c.p.toNat ≠ 0) :
    (BitVec.ofNat 64 (c.S c.n).2 <<< 16) ||| BitVec.ofNat 64 (c.S c.n).1 = c.res := by
  have h := S_lt c.bs c.a c.n
  simp only [Ctx.S] at h ⊢
  simp only [Ctx.res, hz, ↓reduceIte]
  rw [adler32, ← S_full, bs_length]
  simp only [adlerPack, BASE] at h ⊢
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  have h1 : (Adler32z.S c.bs c.a c.n).1 < 65536 := by omega
  have h2 : (Adler32z.S c.bs c.a c.n).2 < 65536 := by omega
  rw [Nat.mod_eq_of_lt (by omega : (Adler32z.S c.bs c.a c.n).1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (Adler32z.S c.bs c.a c.n).2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (Adler32z.S c.bs c.a c.n).2 <<< 16 < 2 ^ 64)]
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have e := Nat.two_pow_add_eq_or_of_lt (show (Adler32z.S c.bs c.a c.n).1 < 2 ^ 16 by omega)
    (Adler32z.S c.bs c.a c.n).2
  conv_lhs => rw [Nat.mul_comm]
  rw [← e]; omega

/-- One `DO16` block, at `BitVec 64`. -/
theorem R16W (c : Ctx) {k j : Nat} (h : k + j + 16 ≤ c.n) :
    BitVec.ofNat 64 (c.R k (j + 16)).1 = BitVec.ofNat 64 (c.R k j).1 + c.b (k + j) + c.b (k + j + 1) + c.b (k + j + 2) + c.b (k + j + 3) + c.b (k + j + 4) + c.b (k + j + 5) + c.b (k + j + 6) + c.b (k + j + 7) + c.b (k + j + 8) + c.b (k + j + 9) + c.b (k + j + 10) + c.b (k + j + 11) + c.b (k + j + 12) + c.b (k + j + 13) + c.b (k + j + 14) + c.b (k + j + 15) ∧
    BitVec.ofNat 64 (c.R k (j + 16)).2 = BitVec.ofNat 64 (c.R k j).2 + 16 * BitVec.ofNat 64 (c.R k j).1 + 16 * c.b (k + j) + 15 * c.b (k + j + 1) + 14 * c.b (k + j + 2) + 13 * c.b (k + j + 3) + 12 * c.b (k + j + 4) + 11 * c.b (k + j + 5) + 10 * c.b (k + j + 6) + 9 * c.b (k + j + 7) + 8 * c.b (k + j + 8) + 7 * c.b (k + j + 9) + 6 * c.b (k + j + 10) + 5 * c.b (k + j + 11) + 4 * c.b (k + j + 12) + 3 * c.b (k + j + 13) + 2 * c.b (k + j + 14) + 1 * c.b (k + j + 15) := by
  have e0 := R_succW c (k := k) (j := j) (by omega)
  have e1 := R_succW c (k := k) (j := j + 1) (by omega)
  have e2 := R_succW c (k := k) (j := j + 2) (by omega)
  have e3 := R_succW c (k := k) (j := j + 3) (by omega)
  have e4 := R_succW c (k := k) (j := j + 4) (by omega)
  have e5 := R_succW c (k := k) (j := j + 5) (by omega)
  have e6 := R_succW c (k := k) (j := j + 6) (by omega)
  have e7 := R_succW c (k := k) (j := j + 7) (by omega)
  have e8 := R_succW c (k := k) (j := j + 8) (by omega)
  have e9 := R_succW c (k := k) (j := j + 9) (by omega)
  have e10 := R_succW c (k := k) (j := j + 10) (by omega)
  have e11 := R_succW c (k := k) (j := j + 11) (by omega)
  have e12 := R_succW c (k := k) (j := j + 12) (by omega)
  have e13 := R_succW c (k := k) (j := j + 13) (by omega)
  have e14 := R_succW c (k := k) (j := j + 14) (by omega)
  have e15 := R_succW c (k := k) (j := j + 15) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 ⊢
  rw [e15.2, e15.1, e14.2, e14.1, e13.2, e13.1, e12.2, e12.1, e11.2, e11.1, e10.2, e10.1,
    e9.2, e9.1, e8.2, e8.1, e7.2, e7.1, e6.2, e6.1, e5.2, e5.1, e4.2, e4.1, e3.2, e3.1,
    e2.2, e2.1, e1.2, e1.1, e0.2, e0.1]
  constructor <;> ring

/-- The tail end pointer `0x3db` computes after the `DO16` loop of the last chunk. -/
theorem rdx_eq (p : BitVec 64) (n k q : Nat) (hk : k ≤ n) :
  p + (BitVec.ofNat 64 (k + 16 * (q + 1)) + (BitVec.ofNat 64 (n - k) + ((0#64 - BitVec.ofNat 64 q) <<< 4 + 18446744073709551600#64))) = p + BitVec.ofNat 64 n := by
  have e1 : (18446744073709551600#64 : BitVec 64) = -16 := by decide
  have e2 : ∀ x : BitVec 64, x <<< 4 = x * 16 := fun x => by
    rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl
  have e3 : BitVec.ofNat 64 (n - k) = BitVec.ofNat 64 n - BitVec.ofNat 64 k := by
    rw [show n = (n - k) + k from by omega, BitVec.ofNat_add]; simp
  rw [e1, e2, e3, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_add]
  have h16 : (16#64 : BitVec 64) = 16 := rfl
  have h1 : (1#64 : BitVec 64) = 1 := rfl
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h16, h1, h0]
  ring

/-! ## The prologue -/

/-- A push into the frame: the write permission, then the pushed slot and the rest. -/
theorem push_go {c : Ctx} {mem : Memory} {P : Memory → Prop} (hP : c.Pre) (hF : FM c mem)
    {A v : Word} {o : Nat} (hA : A.toNat = c.lo + o) (ho : o + 8 ≤ 96)
    (h : ∀ after, FM c after → Loaded after c.base adler32zCode →
      after.readBytes A.toNat 8 = some (encodeWords [v]) →
      (∀ B, B + 8 ≤ A.toNat ∨ A.toNat + 8 ≤ B → after.readBytes B 8 = mem.readBytes B 8) →
      P after) :
    mem.Permitted .write A.toNat 8 ∧ ∀ after, Silmaril.X86.Ext.storeN mem A 8 v = some after →
      P after := by
  refine ⟨by rw [hA]; exact (hF.permitted hP ho).1, fun after hst => ?_⟩
  have hF' := hF.store hst hA ho
  have hS := Stored.of_storeN hst
  refine h after hF' (hF'.loaded hP) ?_ fun B hB => ?_
  · have := FM.holds_self hP hF hst hA ho
    simpa [HoldsLE, Silmaril.X86.Ext.leBytes_eight] using this
  · have := hS.readWith_disjoint .read B 8 (by simpa using hB)
    simpa [Memory.readBytes] using this

theorem readBytes_keep {mem after : Memory} {A v : Word} {B : Nat}
    (hst : Silmaril.X86.Ext.storeN mem A 8 v = some after)
    (hd : B + 8 ≤ A.toNat ∨ A.toNat + 8 ≤ B) : after.readBytes B 8 = mem.readBytes B 8 := by
  have := (Stored.of_storeN hst).readWith_disjoint .read B 8 (by simpa using hd)
  simpa [Memory.readBytes] using this

theorem sp6 (c : Ctx) :
    c.m0.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 - 8#64 = c.sp := by
  simp only [Ctx.sp, Ctx.r0]; bv_omega

theorem push_toNat {c : Ctx} (hP : c.Pre) {k : Nat} (hk : k ≤ 96) :
    (c.m0.core.read .rsp - BitVec.ofNat 64 k).toNat = c.lo + (96 - k) := by
  have := hP.room; have := c.r0.isLt
  simp only [Ctx.lo, Ctx.r0] at *
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem sub8 (x : Word) (k : Nat) : x - BitVec.ofNat 64 k - 8#64 = x - BitVec.ofNat 64 (k + 8) := by
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]

/-- `movzwl %di, %r15d`: the low half of the incoming value is `s1`. -/
theorem start1 (c : Ctx) (hP : c.Pre) :
    ((((c.m0.core.read .rdi).setWidth 16).setWidth 32).setWidth 64 : Word) =
      BitVec.ofNat 64 (c.S 0).1 := by
  have hok := hP.ok.1
  simp only [Ctx.S, Adler32z.S, List.take_zero, modFold, List.foldl_nil, adlerStart, red,
    Ctx.a] at hok ⊢
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BASE] at hok ⊢
  omega

/-- `shr $16, %rax; movzwl %ax, %eax`: the high half is `s2`. -/
theorem start2 (c : Ctx) (hP : c.Pre) :
    (((((c.m0.core.read .rdi) >>> 16).setWidth 16).setWidth 32).setWidth 64 : Word) =
      BitVec.ofNat 64 (c.S 0).2 := by
  have hok := hP.ok.2.1
  simp only [Ctx.S, Adler32z.S, List.take_zero, modFold, List.foldl_nil, adlerStart, red,
    Ctx.a] at hok ⊢
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, BASE,
    Nat.shiftRight_eq_div_pow] at hok ⊢
  omega

/-! ## The `len = 1` path -/

theorem cs_le {v : Nat} (hv : v < 2 ^ 64) (h : (BitVec.ofNat 64 v).ule 65520#64 = true) :
    BitVec.ofNat 64 v = BitVec.ofNat 64 (v % 65521) := by
  have h' : (BitVec.ofNat 64 v).toNat ≤ (65520#64).toNat := by simpa [BitVec.ule] using h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] at h'
  rw [Nat.mod_eq_of_lt (by simp at h'; omega)]

theorem cs_gt {v : Nat} (hv : v < 2 * 65521) (h : (BitVec.ofNat 64 v).ule 65520#64 = false) :
    BitVec.ofNat 64 v - 65521#64 = BitVec.ofNat 64 (v % 65521) := by
  have h' : ¬ (BitVec.ofNat 64 v).toNat ≤ (65520#64).toNat := by simpa [BitVec.ule] using h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
  simp at h'
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem S1_eq (c : Ctx) (h : 0 < c.n) :
    (c.S 1).1 = ((c.S 0).1 + (c.bs.getD 0 0).toNat) % 65521 ∧
    (c.S 1).2 = ((c.S 0).2 + (c.S 1).1) % 65521 := by
  have hl : 0 < c.bs.length := by rw [bs_length]; exact h
  have : c.bs.take 1 = [c.bs.getD 0 0] := by
    cases hb : c.bs with
    | nil => rw [hb] at hl; simp at hl
    | cons x xs => simp
  simp only [Ctx.S, Adler32z.S, this, List.take_zero, modFold, List.foldl_cons, List.foldl_nil,
    Silmaril.X86.Stencils.AccumFold.modStep, BASE, and_self]

/-- The `s2` increment of one `DO16` block of the last-chunk loop (`0x2e3`), in the shape the
machine computes it (spills included), is the raw-sum update. -/
theorem do16C_s2 (q r r1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) (hr1 : r1 = r + x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15) :
    q + (x0 + (r + (x1 + (x0 + (r + (x2 + (x1 + (x0 + (r + (x3 + (x2 + (x1 + (x0 + (r + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x9 + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x10 + (x9 + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x11 + (x10 + (x9 + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x12 + (x11 + (x10 + (x9 + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x13 + (x12 + (x11 + (x10 + (x9 + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x14 + (x13 + (x12 + (x11 + (x10 + (x9 + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + r1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) =
      q + 16 * r + 16 * x0 + 15 * x1 + 14 * x2 + 13 * x3 + 12 * x4 + 11 * x5 + 10 * x6 + 9 * x7 + 8 * x8 + 7 * x9 + 6 * x10 + 5 * x11 + 4 * x12 + 3 * x13 + 2 * x14 + 1 * x15 := by
  subst hr1; ring

/-- `and $0xf, %esi; je`: the remainder is a multiple of 16. -/
theorem and15 (x : Nat) (hx : x < 2 ^ 32) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 x) &&& 15#32 = 0#32) ↔ x % 16 = 0 := by
  have e : (BitVec.setWidth 32 (BitVec.ofNat 64 x) &&& 15#32).toNat = x % 16 := by
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega), Nat.mod_eq_of_lt hx]
    rw [show (15 : Nat) % 2 ^ 32 = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  constructor
  · intro h; rw [← e, h]; rfl
  · intro h; apply BitVec.eq_of_toNat_eq; rw [e, h]; rfl

/-- `lea -0x10(%rsi),%rax; shr $4,%rax` and `lea 1(%rax),%rax; shl $4,%rax` (`0x2bd`). -/
theorem qm_eq (n : Nat) (h16 : 16 ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n + 18446744073709551600#64) >>> 4 = BitVec.ofNat 64 ((n - 16) / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega
theorem q1_eq (n : Nat) (_h16 : 16 ≤ n) (_hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 ((n - 16) / 16) + 1#64) <<< 4 = BitVec.ofNat 64 (16 * ((n - 16) / 16 + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- The `s2` increment of one `DO16` block of the chunk loop (`0x80`), in the shape the machine
computes it (spills included), is the raw-sum update. -/
theorem do16A_s2 (q r r1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) (hr1 : r1 = r + x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15) :
    q + (x0 + (r + (x1 + (x0 + (r + (x2 + (x1 + (x0 + (r + (x3 + (x2 + (x1 + (x0 + (r + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x9 + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x10 + (x9 + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x11 + (x10 + (x9 + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x12 + (x11 + (x10 + (x9 + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x13 + (x12 + (x11 + (x10 + (x9 + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + (x14 + (x13 + (x12 + (x11 + (x10 + (x9 + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + (x0 + (r + r1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) =
      q + 16 * r + 16 * x0 + 15 * x1 + 14 * x2 + 13 * x3 + 12 * x4 + 11 * x5 + 10 * x6 + 9 * x7 + 8 * x8 + 7 * x9 + 6 * x10 + 5 * x11 + 4 * x12 + 3 * x13 + 2 * x14 + 1 * x15 := by
  subst hr1; ring

set_option maxRecDepth 100000 in
/-- `do16C_s2` at the slot: the `s2` spill after one last-chunk `DO16` block. (A separate lemma
so that the kernel checks this step outside `vcC`'s proof term.) -/
theorem slotC {c : Ctx} {k t : Nat} {mem : Memory} {A : Word} (hpos : k + 16 * t + 16 ≤ c.n)
    (h : loadN mem A 8 = some ((BitVec.ofNat 64 (c.R k (16 * t)).2) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + ((c.b (k + 16 * t + 1)) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + ((c.b (k + 16 * t + 2)) + ((c.b (k + 16 * t + 1)) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + ((c.b (k + 16 * t + 3)) + ((c.b (k + 16 * t + 2)) + ((c.b (k + 16 * t + 1)) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + ((c.b (k + 16 * t + 4)) + ((c.b (k + 16 * t + 3)) + ((c.b (k + 16 * t + 2)) + ((c.b (k + 16 * t + 1)) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + ((c.b (k + 16 * t + 5)) + ((c.b (k + 16 * t + 4)) + ((c.b (k + 16 * t + 3)) + ((c.b (k + 16 * t + 2)) + ((c.b (k + 16 * t + 1)) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + ((c.b (k + 16 * t + 6)) + ((c.b (k + 16 * t + 5)) + ((c.b (k + 16 * t + 4)) + ((c.b (k + 16 * t + 3)) + ((c.b (k + 16 * t + 2)) + ((c.b (k + 16 * t + 1)) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + ((c.b (k + 16 * t + 7)) + ((c.b (k + 16 * t + 6)) + ((c.b (k + 16 * t + 5)) + ((c.b (k + 16 * t + 4)) + ((c.b (k + 16 * t + 3)) + ((c.b (k + 16 * t + 2)) + ((c.b (k + 16 * t + 1)) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + ((c.b (k + 16 * t + 8)) + ((c.b (k + 16 * t + 7)) + ((c.b (k + 16 * t + 6)) + ((c.b (k + 16 * t + 5)) + ((c.b (k + 16 * t + 4)) + ((c.b (k + 16 * t + 3)) + ((c.b (k + 16 * t + 2)) + ((c.b (k + 16 * t + 1)) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + ((c.b (k + 16 * t + 9)) + ((c.b (k + 16 * t + 8)) + ((c.b (k + 16 * t + 7)) + ((c.b (k + 16 * t + 6)) + ((c.b (k + 16 * t + 5)) + ((c.b (k + 16 * t + 4)) + ((c.b (k + 16 * t + 3)) + ((c.b (k + 16 * t + 2)) + ((c.b (k + 16 * t + 1)) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + ((c.b (k + 16 * t + 10)) + ((c.b (k + 16 * t + 9)) + ((c.b (k + 16 * t + 8)) + ((c.b (k + 16 * t + 7)) + ((c.b (k + 16 * t + 6)) + ((c.b (k + 16 * t + 5)) + ((c.b (k + 16 * t + 4)) + ((c.b (k + 16 * t + 3)) + ((c.b (k + 16 * t + 2)) + ((c.b (k + 16 * t + 1)) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + ((c.b (k + 16 * t + 11)) + ((c.b (k + 16 * t + 10)) + ((c.b (k + 16 * t + 9)) + ((c.b (k + 16 * t + 8)) + ((c.b (k + 16 * t + 7)) + ((c.b (k + 16 * t + 6)) + ((c.b (k + 16 * t + 5)) + ((c.b (k + 16 * t + 4)) + ((c.b (k + 16 * t + 3)) + ((c.b (k + 16 * t + 2)) + ((c.b (k + 16 * t + 1)) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + ((c.b (k + 16 * t + 12)) + ((c.b (k + 16 * t + 11)) + ((c.b (k + 16 * t + 10)) + ((c.b (k + 16 * t + 9)) + ((c.b (k + 16 * t + 8)) + ((c.b (k + 16 * t + 7)) + ((c.b (k + 16 * t + 6)) + ((c.b (k + 16 * t + 5)) + ((c.b (k + 16 * t + 4)) + ((c.b (k + 16 * t + 3)) + ((c.b (k + 16 * t + 2)) + ((c.b (k + 16 * t + 1)) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + ((c.b (k + 16 * t + 13)) + ((c.b (k + 16 * t + 12)) + ((c.b (k + 16 * t + 11)) + ((c.b (k + 16 * t + 10)) + ((c.b (k + 16 * t + 9)) + ((c.b (k + 16 * t + 8)) + ((c.b (k + 16 * t + 7)) + ((c.b (k + 16 * t + 6)) + ((c.b (k + 16 * t + 5)) + ((c.b (k + 16 * t + 4)) + ((c.b (k + 16 * t + 3)) + ((c.b (k + 16 * t + 2)) + ((c.b (k + 16 * t + 1)) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + ((c.b (k + 16 * t + 14)) + ((c.b (k + 16 * t + 13)) + ((c.b (k + 16 * t + 12)) + ((c.b (k + 16 * t + 11)) + ((c.b (k + 16 * t + 10)) + ((c.b (k + 16 * t + 9)) + ((c.b (k + 16 * t + 8)) + ((c.b (k + 16 * t + 7)) + ((c.b (k + 16 * t + 6)) + ((c.b (k + 16 * t + 5)) + ((c.b (k + 16 * t + 4)) + ((c.b (k + 16 * t + 3)) + ((c.b (k + 16 * t + 2)) + ((c.b (k + 16 * t + 1)) + ((c.b (k + 16 * t)) + ((BitVec.ofNat 64 (c.R k (16 * t)).1) + (BitVec.ofNat 64 (c.R k (16 * t + 16)).1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :
    loadN mem A 8 = some (BitVec.ofNat 64 (c.R k (16 * t + 16)).2) := by
  have hR16 := R16W c (k := k) (j := 16 * t) (by omega)
  rw [h, hR16.2]; exact congrArg some (do16C_s2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR16.1)

/-- A pointer step by 16. -/
theorem p_add16 (c : Ctx) (x : Nat) :
    c.p + (BitVec.ofNat 64 x + 16#64) = c.p + BitVec.ofNat 64 (x + 16) := by
  rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]

/-! ## Cut points and stops -/

/-- The bytes left, measured from a pointer register. -/
def meas (c : Ctx) (r : Reg) (s : MState) : Nat := c.n - (s.core.read r - c.p).toNat

/-- `0x80`: the `NMAX` chunk loop, `j` bytes into the chunk that starts after `k`. -/
def InvA (c : Ctx) (s : MState) : Prop :=
  Fr c s ∧ ∃ k j, k + NMAX ≤ c.n ∧ j < NMAX ∧ j % 16 = 0 ∧
    s.core.read .r8 = c.p + BitVec.ofNat 64 (k + j) ∧
    s.core.read .r15 = BitVec.ofNat 64 (c.R k j).1 ∧
    loadN s.memory (c.sp + 18446744073709551584#64) 8 = some (BitVec.ofNat 64 (c.R k j).2) ∧
    loadN s.memory (c.sp + 18446744073709551592#64) 8 = some (c.p + BitVec.ofNat 64 (k + NMAX)) ∧
    loadN s.memory (c.sp + 18446744073709551600#64) 8 = some (BitVec.ofNat 64 (c.n - k - NMAX)) ∧
    loadN s.memory (c.sp + 18446744073709551608#64) 8 = some (BitVec.ofNat 64 (c.n - k))

/-- `0x205`: the short byte loop (`2 ≤ len ≤ 15`), `i` bytes in. -/
def InvB (c : Ctx) (s : MState) : Prop :=
  Fr c s ∧ 2 ≤ c.n ∧ c.n ≤ 15 ∧ ∃ i, i < c.n ∧
    s.core.read .rcx = c.p + BitVec.ofNat 64 i ∧ s.core.read .rdx = c.p + BitVec.ofNat 64 c.n ∧
    s.core.read .r15 = BitVec.ofNat 64 (c.R 0 i).1 ∧ s.core.read .rax = BitVec.ofNat 64 (c.R 0 i).2

/-- `0x2e3`: the `DO16` loop of the last chunk (`16 ≤ rem = len - k ≤ 5551`), `t` blocks in. -/
def InvC (c : Ctx) (s : MState) : Prop :=
  Fr c s ∧ ∃ k t, 16 ≤ c.n - k ∧ c.n - k ≤ 5551 ∧ k ≤ c.n ∧ t ≤ (c.n - k - 16) / 16 ∧
    s.core.read .rcx = c.p + BitVec.ofNat 64 (k + 16 * t) ∧
    s.core.read .r15 = BitVec.ofNat 64 (c.R k (16 * t)).1 ∧
    loadN s.memory (c.sp + 18446744073709551584#64) 8 = some (BitVec.ofNat 64 (c.R k (16 * t)).2) ∧
    loadN s.memory (c.sp + 18446744073709551592#64) 8 =
      some (c.p + BitVec.ofNat 64 (k + 16 * ((c.n - k - 16) / 16 + 1))) ∧
    loadN s.memory (c.sp + 18446744073709551600#64) 8 =
      some (BitVec.ofNat 64 ((c.n - k - 16) / 16)) ∧
    loadN s.memory (c.sp + 18446744073709551608#64) 8 = some (BitVec.ofNat 64 (c.n - k))

/-- `0x3e0`: the byte tail of the last chunk (`rem ≤ 5551`), at byte `pos`. -/
def InvD (c : Ctx) (s : MState) : Prop :=
  Fr c s ∧ ∃ k pos, k ≤ pos ∧ pos < c.n ∧ c.n - k ≤ 5551 ∧
    s.core.read .r8 = c.p + BitVec.ofNat 64 pos ∧ s.core.read .rdx = c.p + BitVec.ofNat 64 c.n ∧
    s.core.read .r15 = BitVec.ofNat 64 (c.R k (pos - k)).1 ∧
    s.core.read .rax = BitVec.ofNat 64 (c.R k (pos - k)).2

/-- At a `ret`: the pushed registers are back, `rsp` is the entry's, the memory changed only in
the area, and `rax` is the result. -/
structure Q (c : Ctx) (s : MState) : Prop where
  pre : c.Pre
  sp : s.core.read .rsp = c.r0
  rbx : s.core.read .rbx = c.m0.core.read .rbx
  rbp : s.core.read .rbp = c.m0.core.read .rbp
  r12 : s.core.read .r12 = c.m0.core.read .r12
  r13 : s.core.read .r13 = c.m0.core.read .r13
  r14 : s.core.read .r14 = c.m0.core.read .r14
  r15 : s.core.read .r15 = c.m0.core.read .r15
  mem : FM c s.memory
  rax : s.core.read .rax = c.res

/-- `0x20`: after the prologue (six pushes, `s1` in `r15`, `s2` spilled). -/
structure InvP (c : Ctx) (s : MState) : Prop where
  pre : c.Pre
  sp : s.core.read .rsp = c.sp
  mem : FM c s.memory
  saved : Saved c s.memory
  rdx : s.core.read .rdx = c.m0.core.read .rdx
  rsi : s.core.read .rsi = c.p
  rcx : s.core.read .rcx = c.p
  r15 : s.core.read .r15 = BitVec.ofNat 64 (c.S 0).1
  s2 : loadN s.memory (c.sp + 18446744073709551584#64) 8 = some (BitVec.ofNat 64 (c.S 0).2)

def cuts (c : Ctx) : List (Nat × Silmaril.X86.SegVC.Cut (σ := MState)) :=
  [(32, ⟨InvP c, fun _ => c.n + 1⟩), (128, ⟨InvA c, meas c .r8⟩), (517, ⟨InvB c, meas c .rcx⟩), (739, ⟨InvC c, meas c .rcx⟩),
    (992, ⟨InvD c, meas c .r8⟩)]

def stops (c : Ctx) : List (Nat × (MState → Prop)) :=
  [(502, Q c), (628, Q c), (690, Q c), (1122, Q c)]

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
