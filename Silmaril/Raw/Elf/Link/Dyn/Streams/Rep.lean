module

public import Silmaril.Elf.Link.Dyn.Streams.Defs
public import Silmaril.Elf.Link.Dyn.Image.Thms
public import Silmaril.Elf.Link.Dyn.Proc.Thms

/-! # A concrete stream representation (`slotRep`)

A witness for `StreamRep`: streams live in `KS` fixed slots of `S0` bytes from `A0` (the
library's private arena; its last slot, of `K0`, holds `errno`), read-only to the program. The `FILE` at slot address `f` holds `enc st`: a 64-byte header
(`_flags` with `reading`/`fail`/`EOF`/`ERR` in bits 0/1/4/5, the descriptor, `_IO_write_ptr`
and `_IO_write_end` both `0` — so the inline `putc` always takes the slow path —, and the
number of unread bytes) followed by the unread bytes. Output is never buffered (`buf = []`).
All laws of `StreamRep` hold (`slotRep`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Streams.Total

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (loadN leBytes leValue)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc

def A0 : Nat := 0x10000000
def S0 : Nat := 0x100000
def K0 : Nat := 16

/-- The private arena. -/
def Arena (a : Nat) : Prop := A0 ≤ a ∧ a < A0 + K0 * S0

/-- Streams use the first `KS` slots; the last slot of the arena holds `errno` (`eA`). -/
def KS : Nat := 15

def IsSlot (f : Word) : Prop := ∃ k < KS, f.toNat = A0 + k * S0

def flagsN (st : St) : Nat :=
  (if st.reading then 1 else 0) + (if st.fail then 2 else 0) + (if st.eof then 16 else 0) +
    (if st.err then 32 else 0)

def hdr (st : St) : List Byte :=
  leBytes (BitVec.ofNat 64 (flagsN st)) 8 ++ leBytes (BitVec.ofNat 64 st.fd) 8 ++
    List.replicate 24 0#8 ++ leBytes 0#64 8 ++ leBytes 0#64 8 ++
    leBytes (BitVec.ofNat 64 st.rd.length) 8

def enc (st : St) : List Byte := hdr st ++ st.rd

theorem hdr_length (st : St) : (hdr st).length = 64 := by simp [hdr, leBytes]

theorem enc_length (st : St) : (enc st).length = 64 + st.rd.length := by
  simp [enc, hdr_length]

/-- The states this representation can hold. -/
def Valid (st : St) : Prop := st.buf = [] ∧ st.fd < 2 ^ 64 ∧ 64 + st.rd.length ≤ S0

/-- A stream: its encoding at a slot, which the program cannot write (the library writes it;
the inline `putc` never does, `_IO_write_ptr = _IO_write_end`). -/
def fileR (m : Memory) (f : Word) (st : St) : Prop :=
  IsSlot f ∧ Valid st ∧ m.readBytes f.toNat (64 + st.rd.length) = some (enc st) ∧
    ∀ k < 64 + st.rd.length, m.permits .write (f.toNat + k) = false

/-- The unread-length word of the header at `f`. -/
def lenAt (m : Memory) (f : Word) : Nat := ((m.readBytes (f.toNat + 0x38) 8).map leValue).getD 0

def footR (m : Memory) (f : Word) (a : Nat) : Prop := f.toNat ≤ a ∧ a < f.toNat + 64 + lenAt m f

theorem slot_lt {f : Word} (h : IsSlot f) : f.toNat + S0 ≤ A0 + K0 * S0 ∧ A0 ≤ f.toNat := by
  obtain ⟨k, hk, he⟩ := h
  rw [he]; constructor
  · have : k * S0 + S0 ≤ K0 * S0 := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by unfold KS at hk; unfold K0; omega)
    omega
  · omega

theorem sub_read {m : Memory} {a n : Nat} {l : List Byte} (h : m.readBytes a n = some l)
    {k j : Nat} (hj : 0 < j) (hk : k + j ≤ n) : m.readBytes (a + k) j = some ((l.drop k).take j) :=
  Silmaril.X86.Ext.readWith_sub h hj hk

theorem enc_drop56 (st : St) : ((enc st).drop 56).take 8 = leBytes (BitVec.ofNat 64 st.rd.length) 8 := by
  simp [enc, hdr, leBytes]

theorem lenAt_of {m : Memory} {f : Word} {st : St} (h : fileR m f st) : lenAt m f = st.rd.length := by
  obtain ⟨hs, ⟨-, -, hS⟩, hr, -⟩ := h
  have := sub_read hr (k := 56) (j := 8) (by decide) (by omega)
  rw [enc_drop56] at this
  have hlt : st.rd.length < 2 ^ 64 := by unfold S0 at hS; omega
  simp only [lenAt, this, Option.map_some, Option.getD_some]
  simp [Silmaril.X86.Ext.leValue_leBytes]; exact hlt

theorem perm_of_read {m : Memory} {a n : Nat} {l : List Byte} (h : m.readBytes a n = some l) :
    a < 2 ^ 64 ∧ a + n ≤ 2 ^ 64 ∧ ∀ k < n, m.permits .read (a + k) = true := by
  unfold Memory.readBytes Memory.readWith at h
  split at h
  · rename_i hc
    rw [Memory.checkSpan_iff] at hc
    exact hc
  · cases h

theorem slot_small {f : Word} (h : IsSlot f) : f.toNat + S0 < 2 ^ 32 := by
  have := slot_lt h; unfold A0 K0 S0 at *; omega

theorem addK {f : Word} (h : IsSlot f) (k : Nat) (hk : k < S0) :
    (f + BitVec.ofNat 64 k).toNat = f.toNat + k := addr_toNat (by have := slot_small h; omega)

theorem leBytes_take4 (w : Word) : (leBytes w 8).take 4 = leBytes w 4 := by
  simp [leBytes, List.ofFn_succ]

theorem bits4 (r f e x : Bool) :
    (BitVec.ofNat 64 ((if r then 1 else 0) + (if f then 2 else 0) + (if e then 16 else 0) +
      (if x then 32 else 0))).getLsbD 4 = e ∧
    (BitVec.ofNat 64 ((if r then 1 else 0) + (if f then 2 else 0) + (if e then 16 else 0) +
      (if x then 32 else 0))).getLsbD 5 = x ∧
    (BitVec.ofNat 64 ((if r then 1 else 0) + (if f then 2 else 0) + (if e then 16 else 0) +
      (if x then 32 else 0))).getLsbD 8 = false := by
  cases r <;> cases f <;> cases e <;> cases x <;> decide +kernel

theorem flags_bits (st : St) :
    (BitVec.ofNat 64 (flagsN st)).getLsbD 4 = st.eof ∧ (BitVec.ofNat 64 (flagsN st)).getLsbD 5 = st.err ∧
      (BitVec.ofNat 64 (flagsN st)).getLsbD 8 = false :=
  bits4 st.reading st.fail st.eof st.err

theorem loadN_flags {m : Memory} {f : Word} {st : St} (h : fileR m f st) :
    loadN m f 4 = some (BitVec.ofNat 64 (flagsN st)) := by
  obtain ⟨hs, ⟨-, -, hS⟩, hr, -⟩ := h
  have := sub_read hr (k := 0) (j := 4) (by decide) (by omega)
  simp only [Nat.add_zero, List.drop_zero] at this
  have he : (enc st).take 4 = leBytes (BitVec.ofNat 64 (flagsN st)) 4 := by
    simp only [enc, hdr, List.append_assoc]
    rw [List.take_append_of_le_length (by simp [leBytes]), leBytes_take4]
  rw [he] at this
  have hlt : flagsN st < 2 ^ 32 := by
    unfold flagsN; split <;> split <;> split <;> split <;> omega
  simp only [loadN, this, Option.map_some, Silmaril.X86.Ext.leValue_leBytes]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp
  omega

theorem flagsN_lt64 (st : St) : flagsN st < 64 := by
  unfold flagsN; split <;> split <;> split <;> split <;> omega

theorem loadN_flags1 {m : Memory} {f : Word} {st : St} (h : fileR m f st) :
    loadN m f 1 = some (BitVec.ofNat 64 (flagsN st)) := by
  obtain ⟨hs, ⟨-, -, hS⟩, hr, -⟩ := h
  have := sub_read hr (k := 0) (j := 1) (by decide) (by omega)
  simp only [Nat.add_zero, List.drop_zero] at this
  have he : (enc st).take 1 = leBytes (BitVec.ofNat 64 (flagsN st)) 1 := by
    simp [enc, hdr, leBytes, List.ofFn_succ]
  rw [he] at this
  have hlt := flagsN_lt64 st
  simp only [loadN, this, Option.map_some, Silmaril.X86.Ext.leValue_leBytes]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp
  omega

theorem loadN_zero {m : Memory} {f : Word} {st : St} (h : fileR m f st) {k : Nat}
    (hk : k = 0x28 ∨ k = 0x30) : loadN m (f + BitVec.ofNat 64 k) 8 = some 0#64 := by
  obtain ⟨hs, ⟨-, -, hS⟩, hr, -⟩ := h
  have := sub_read hr (k := k) (j := 8) (by decide) (by omega)
  have he : ((enc st).drop k).take 8 = leBytes 0#64 8 := by
    rcases hk with rfl | rfl <;> simp [enc, hdr, leBytes]
  rw [he, ← addK hs k (by unfold S0; omega)] at this
  simp only [loadN, this, Option.map_some, Silmaril.X86.Ext.leValue_leBytes]
  rfl

/-- **The representation.** -/
def slotRep : StreamRep where
  file := fileR
  foot := footR
  priv _ := Arena
  foot_priv := by
    intro m f st a h ha
    have hl := lenAt_of h
    obtain ⟨hs, ⟨-, -, hS⟩, -⟩ := h
    have := slot_lt hs
    unfold footR at ha; rw [hl] at ha
    exact ⟨by omega, by omega⟩
  lo := A0 + K0 * S0
  foot_lo := by
    intro m f st a h ha
    have hl := lenAt_of h
    obtain ⟨hs, ⟨-, -, hS⟩, -⟩ := h
    have := slot_lt hs
    unfold footR at ha; rw [hl] at ha
    omega
  priv_lo := fun _ _ h => h.2
  priv_local := fun _ _ _ => rfl
  priv_keep := fun _ _ _ => rfl
  local_ := by
    intro m m' f st hk h
    have hl := lenAt_of h
    have hrd : ∀ k < 64 + st.rd.length, footR m f (f.toNat + k) := fun k hk' =>
      ⟨by omega, by rw [hl]; omega⟩
    have hlen : lenAt m' f = lenAt m f := by
      unfold lenAt
      rw [Keeps.readBytes hk (fun k hk' => ⟨by omega, by rw [hl]; omega⟩)]
    refine ⟨⟨h.1, h.2.1, ?_, fun k hk' => ?_⟩, ?_⟩
    · rw [Keeps.readBytes hk hrd]; exact h.2.2.1
    · rw [(hk _ (hrd k hk')).2]; exact h.2.2.2 k hk'
    · funext a; unfold footR; rw [hlen]
  flags := by
    intro m f st h
    exact ⟨_, loadN_flags h, flags_bits st⟩
  flags1 := by
    intro m f st h
    refine ⟨_, loadN_flags1 h, (flags_bits st).1, (flags_bits st).2.1, ?_⟩
    have := flagsN_lt64 st
    simp only [BitVec.toNat_ofNat]; omega
  ptrs := by
    intro m f st h
    refine ⟨⟨_, loadN_zero h (Or.inl rfl)⟩, ⟨_, loadN_zero h (Or.inr rfl)⟩, fun a h1 h2 => ⟨h1, ?_⟩⟩
    rw [lenAt_of h]
    have := addK h.1 0x38 (by unfold S0; omega)
    omega
  putc := by
    intro m f st p e c h hp he hlt
    rw [loadN_zero h (Or.inr rfl)] at he
    cases he
    simp at hlt

end Silmaril.Elf.Link.Dyn.Streams.Total
