module

public import Silmaril.Apps.Sha256sum.Binary.Digest.Code
public import Silmaril.Apps.Sha256sum.X86Sys.SegVC
public import Silmaril.X86.SegVC.Tactic

/-! # `sha_update`'s `memcpy` loop, by the segment VC generator

`[0x402f69, 0x402f81)` copies `k` bytes from `r12` to `rdi`, `1 ≤ k`, the inlined
`memcpy(s->blk + s->blen, p, k)`. One cut point (the loop head `0x402f70`), one stop
(`0x402f81`), no calls.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary.Digest.Copy

set_option allowUnsafeReducibility true in
attribute [local reducible] Silmaril.X86.Ext.Sz.bits Silmaril.X86.Ext.Narrow.bits

open Silmaril.X86 (State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.Apps.Sha256sum.X86Sys

/-- The ghost values of the copy: the count, the buffers, the source bytes, and the entry
registers and memory. -/
structure Ctx where
  k : Nat
  src : Word
  dst : Word
  bytes : Nat → Word
  r0 : Silmaril.X86.Reg → Word
  m0 : Memory

/-- The destination span. -/
def dstSpan (c : Ctx) (a : Nat) : Prop := c.dst.toNat ≤ a ∧ a < c.dst.toNat + c.k

/-- What the entry, the loop head and the exit share: registers other than `rcx`, `rdx` are
the entry's, memory changed only in the destination, and the entry facts. -/
structure Frame (c : Ctx) (s : XState) : Prop where
  regs : ∀ r, r ≠ .rcx → r ≠ .rdx → s.core.read r = c.r0 r
  writes : Memory.WritesWithin c.m0 s.memory (dstSpan c)
  k : c.r0 .r14 = BitVec.ofNat 64 c.k
  src : c.r0 .r12 = c.src
  dst : c.r0 .rdi = c.dst
  kPos : 1 ≤ c.k
  kLt : c.k < 2 ^ 32
  srcRead : ∀ j < c.k, loadN c.m0 (c.src + BitVec.ofNat 64 j) 1 = some (c.bytes j)
  dstWrite : c.m0.Permitted .write c.dst.toNat c.k
  dstRead : c.m0.Permitted .read c.dst.toNat c.k
  dstFit : c.dst.toNat + c.k < 2 ^ 64
  srcFit : c.src.toNat + c.k < 2 ^ 64
  apart : c.dst.toNat + c.k ≤ c.src.toNat ∨ c.src.toNat + c.k ≤ c.dst.toNat
  codeApart : c.dst.toNat + c.k ≤ base.toNat ∨ base.toNat + code.length ≤ c.dst.toNat
  small : ∀ j < c.k, (c.bytes j).toNat < 256

def pre (c : Ctx) (s : XState) : Prop := Frame c s ∧ s.memory = c.m0

def inv (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ (s.core.read .rdx).toNat < c.k ∧
    ∀ j < (s.core.read .rdx).toNat,
      loadN s.memory (c.dst + BitVec.ofNat 64 j) 1 = some (c.bytes j)

def post (c : Ctx) (s : XState) : Prop :=
  Frame c s ∧ ∀ j < c.k, loadN s.memory (c.dst + BitVec.ofNat 64 j) 1 = some (c.bytes j)

def cuts (c : Ctx) : List (Nat × Cut (σ := XState)) :=
  [(128, { inv := inv c, measure := fun s => c.k - (s.core.read .rdx).toNat })]

def stops (c : Ctx) : List (Nat × (XState → Prop)) := [(145, post c)]

theorem Frame.read_r14 {c : Ctx} {s : XState} (h : Frame c s) :
    s.core.read .r14 = BitVec.ofNat 64 c.k := (h.regs .r14 (by decide) (by decide)).trans h.k
theorem Frame.read_r12 {c : Ctx} {s : XState} (h : Frame c s) :
    s.core.read .r12 = c.src := (h.regs .r12 (by decide) (by decide)).trans h.src
theorem Frame.read_rdi {c : Ctx} {s : XState} (h : Frame c s) :
    s.core.read .rdi = c.dst := (h.regs .rdi (by decide) (by decide)).trans h.dst

theorem toNat_off {a : Word} {j k : Nat} (hj : j < k) (_hk : k < 2 ^ 32)
    (fit : a.toNat + k < 2 ^ 64) : (a + BitVec.ofNat 64 j).toNat = a.toNat + j := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- The source bytes survive writes to the destination. -/
theorem Frame.srcNow {c : Ctx} {s : XState} (h : Frame c s) :
    ∀ j < c.k, loadN s.memory (c.src + BitVec.ofNat 64 j) 1 = some (c.bytes j) := by
  intro j hj
  rw [← h.srcRead j hj]
  simp only [loadN]
  rw [h.writes.readBytes]
  intro off hoff hin
  have := toNat_off hj h.kLt h.srcFit
  simp only [dstSpan] at hin
  have := h.apart
  omega

theorem Frame.dstWriteNow {c : Ctx} {s : XState} (h : Frame c s) :
    s.memory.Permitted .write c.dst.toNat c.k :=
  (h.writes.permitted_iff _ _ _).mpr h.dstWrite

theorem Frame.dstReadNow {c : Ctx} {s : XState} (h : Frame c s) :
    s.memory.Permitted .read c.dst.toNat c.k :=
  (h.writes.permitted_iff _ _ _).mpr h.dstRead

/-- `movzbl` then `mov %cl`: the byte goes through `ecx` unchanged. -/
theorem byte_roundtrip (b : Word) (h : b.toNat < 256) :
    BitVec.ofNat 64 ((BitVec.setWidth 64 (BitVec.setWidth 8 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 8 b))))).toNat % 2 ^ 8) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  omega

/-- After a one-byte store into `dst[i]`, `i < k`: the image, the write frame, and the loads. -/
theorem store_facts {c : Ctx} {s : XState} (hF : Frame c s) (hl : Loaded s.memory base code)
    {i : Word} (hi : i.toNat < c.k) {v : Word} {after : Memory}
    (hst : storeN s.memory (c.dst + i) 1 v = some after) :
    Loaded after base code ∧ Memory.WritesWithin c.m0 after (dstSpan c) ∧
      loadN after (c.dst + i) 1 = some (BitVec.ofNat 64 (v.toNat % 2 ^ 8)) ∧
      (∀ j, j < i.toNat → loadN after (c.dst + BitVec.ofNat 64 j) 1 =
        loadN s.memory (c.dst + BitVec.ofNat 64 j) 1) := by
  have hS := Stored.of_storeN hst
  have haddr : (c.dst + i).toNat = c.dst.toNat + i.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by have := hF.dstFit; omega)
  have hlen : (leBytes v 1).length = 1 := length_leBytes v 1
  refine ⟨Loaded.of_stored hl hS ?_, hF.writes.trans (hS.writesWithin ?_), ?_, fun j hj => ?_⟩
  · rw [haddr, hlen]; have := hF.codeApart; omega
  · intro off hoff; rw [hlen] at hoff; rw [haddr]; simp only [dstSpan]; omega
  · exact loadN_storeN hst (by
      rw [haddr]; exact Memory.Permitted.sub hF.dstReadNow (by omega) (by omega) (by omega))
  · rw [loadN_storeN_disjoint hst ?_]
    rw [toNat_off (by omega) hF.kLt hF.dstFit, haddr]; omega

theorem vc_entry (r11 : Core → Word) (c : Ctx) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 121 → pre c s →
      wpN (Isa.sys r11) code listing (cuts c) (stops c) [] [] base none 8 121 s := by
  intro s hlv hl hrip hpre
  obtain ⟨hF, hm⟩ := hpre
  seg_vc [listing, cuts, stops, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl]
  refine ⟨⟨fun r h1 h2 => ?_, hF.writes, hF.k, hF.src, hF.dst, hF.kPos, hF.kLt, hF.srcRead,
    hF.dstWrite, hF.dstRead, hF.dstFit, hF.srcFit, hF.apart, hF.codeApart, hF.small⟩, ?_, ?_⟩
  · seg_read [h2]; exact hF.regs r h1 h2
  · seg_read []; have := hF.kPos; simp; omega
  · seg_read []; intro j hj; simp at hj

theorem vc_loop (r11 : Core → Word) (c : Ctx) :
    ∀ s : XState, s.faulted = false → Loaded s.memory base code →
      s.core.rip = base + BitVec.ofNat 64 128 → inv c s →
      wpN (Isa.sys r11) code listing (cuts c) (stops c) [] [] base
        (some (c.k - (s.core.read .rdx).toNat)) 8 128 s := by
  intro s hlv hl hrip hinv
  obtain ⟨hF, hlt, hdone⟩ := hinv
  have hld := hF.srcNow _ hlt
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hld
  seg_vc [listing, cuts, stops, Mem.ofReg, Silmaril.X86.Lift.ix, hrip, hl, hF.read_r12,
    hF.read_rdi, hF.read_r14, BitVec.shiftLeft_zero, BitVec.add_zero, hld]
  have hi : (s.core.read .rdx).toNat < c.k := hlt
  refine ⟨?_, fun after hst => ?_⟩
  · have hw := hF.dstWriteNow
    have haddr : (c.dst + s.core.read .rdx).toNat = c.dst.toNat + (s.core.read .rdx).toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by have := hF.dstFit; omega)
    rw [haddr]; exact Memory.Permitted.sub hw (by omega) (by omega) (by omega)
  obtain ⟨hL, hW, hnew, hold⟩ := store_facts hF hl hi hst
  rw [byte_roundtrip _ (hF.small _ hi)] at hnew
  have hrd : (s.core.read .rdx + 1#64).toNat = (s.core.read .rdx).toNat + 1 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; have := hF.kLt; omega
  have hk : (BitVec.ofNat 64 c.k).toNat = c.k := by
    simp only [BitVec.toNat_ofNat]; have := hF.kLt; omega
  have loads : ∀ j < (s.core.read .rdx).toNat + 1,
      loadN after (c.dst + BitVec.ofNat 64 j) 1 = some (c.bytes j) := by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · rw [hold j hj]; exact hdone j hj
    · subst hj; simpa using hnew
  have hF' : ∀ t : XState, t.memory = after → (∀ r, r ≠ .rcx → r ≠ .rdx →
      t.core.read r = s.core.read r) → Frame c t := fun t htm hr =>
    ⟨fun r h1 h2 => (hr r h1 h2).trans (hF.regs r h1 h2), htm ▸ hW, hF.k, hF.src, hF.dst,
      hF.kPos, hF.kLt, hF.srcRead, hF.dstWrite, hF.dstRead, hF.dstFit, hF.srcFit, hF.apart,
      hF.codeApart, hF.small⟩
  refine ⟨hL, hL, hL, fun hne => ⟨hL, ⟨?_, ?_, ?_⟩, ?_⟩, fun heq => ⟨hL, ?_, ?_⟩⟩
  · exact hF' _ rfl fun r h1 h2 => by seg_read [h1, h2]
  · seg_read []
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hne
    have hkk := hF.kLt
    have : c.k ≠ (s.core.read .rdx).toNat + 1 := fun e => hne (by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · seg_read []
    have hkk := hF.kLt
    intro j hj
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hj
    exact loads j (by omega)
  · try seg_read []
    have hkk := hF.kLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · exact hF' _ rfl fun r h1 h2 => by seg_read [h1, h2]
  · simp at heq
    have hkk := hF.kLt
    have : c.k = (s.core.read .rdx).toNat + 1 := by
      have := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this; omega
    intro j hj
    exact loads j (by omega)

theorem vc_all (r11 : Core → Word) (c : Ctx) :
    vc (Isa.sys r11) code listing (cuts c) (stops c) [] [] base 121 (pre c) 8 := by
  refine ⟨vc_entry r11 c, ?_⟩
  intro oc hoc
  simp only [cuts, List.mem_singleton] at hoc
  subst hoc
  exact vc_loop r11 c

/-- **VERIFIED.** The inlined `memcpy` of `sha_update` in `sha256sum-min` copies the `k`
source bytes to the destination, by internal process steps (no system call), and reaches
`0x402f81` with the image still loaded. -/
theorem copy_runs (r11 : Core → Word) (c : Ctx) (s : XState) (hlv : s.faulted = false)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 121)
    (hpre : pre c s) :
    ∃ t, Silmaril.Machine.Execution.Reaches (tauStep r11) s t ∧ post c t ∧
      t.core.rip = base + BitVec.ofNat 64 145 ∧ Loaded t.memory base code ∧
      t.faulted = false :=
  sound_one (I := Isa.sys r11) listing_valid (vc_all r11 c) s hlv hl hrip hpre

/-- **VERIFIED.** The copy loop as a summary for an enclosing segment (`SegVC` `subs`): from
`0x402f69` with some copy context, to `0x402f81` with its postcondition. -/
def summary (r11 : Core → Word) : Call (Isa.sys r11) where
  pre s := s.core.rip = base + BitVec.ofNat 64 121 ∧ Loaded s.memory base code ∧ ∃ c, pre c s
  post s t := t.core.rip = base + BitVec.ofNat 64 145 ∧ Loaded t.memory base code ∧
    ∃ c, pre c s ∧ post c t
  runs := by
    rintro s hlv ⟨hrip, hl, c, hpre⟩
    obtain ⟨t, hr, hpost, hrip', hl', _⟩ := copy_runs r11 c s hlv hl hrip hpre
    exact ⟨t, hr, hrip', hl', c, hpre, hpost⟩

end Silmaril.Apps.Sha256sum.Binary.Digest.Copy
