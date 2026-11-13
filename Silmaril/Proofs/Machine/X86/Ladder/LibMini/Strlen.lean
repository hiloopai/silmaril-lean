module

public import Silmaril.Machine.X86.Ladder.LibMini.Defs
public import Silmaril.Machine.X86.Stencils.ByteLoop.Thms

/-!
# `strlen` (gcc -O2) as a `Scan` stencil instance

`cmpb $0, (reg)` is not liftable to Bir, so the blocks `0x00` and `0x14` are taken raw
(`cmpb_zero_run`); `0x05`, `0x10`, `0x19`, `0x20` are Bir blocks. The scan pointer is
`rax = s + t` with `t ≤ k`, `k` the string length (`strLen`); the measure is `2 (k - t)`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.Ladder.LibMini

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Lift.Bir (Block LInstr liftBlock)
open Silmaril.Machine.X86 Silmaril.Machine.X86.BlockCert Silmaril.Machine.X86.Stencils.ByteLoop
open Silmaril.Machine.X86.Ladder.LibMini

set_option linter.unusedSimpArgs false

/-- The exit condition: the contract's result. -/
abbrev lenQ (entry : Word) : MState → MState → Prop :=
  fun m0 t => (scanContract strlenCode entry).Result Open.isa m0 t
theorem len_checked0 : (strlenCert 0).checkedW = true := by decide +kernel

theorem strLen_spec {m0 : MState} (h : ∃ k, CStr m0.memory (arg0 m0) k) :
    CStr m0.memory (arg0 m0) (strLen m0) := by
  unfold strLen
  split
  · exact Classical.choose_spec ‹_›
  · exact absurd h ‹_›

theorem cstr_unique {mem : Silmaril.Process.Memory} {s k k' : Nat} (h : CStr mem s k)
    (h' : CStr mem s k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with hl | hl | hl
  · exact absurd h.2.2 (h'.2.1 k hl)
  · exact hl
  · exact absurd h'.2.2 (h.2.1 k' hl)

/-- The byte at offset `t ≤ k` of a string of length `k`, and whether it is the NUL. -/
theorem cstr_byte {m0 m : MState} {t : Nat} (hs : CStr m0.memory (arg0 m0) (strLen m0))
    (hm : m.memory = m0.memory) (ht : t ≤ strLen m0) {w : Word}
    (hw : w = m0.core.read .rdi + BitVec.ofNat 64 t) :
    ∃ b : Byte, Silmaril.X86.Ext.loadN m.memory w 1 = some (BitVec.ofNat 64 b.toNat) ∧
      (b = 0 ↔ t = strLen m0) := by
  obtain ⟨hlt, hrd, hsome⟩ := hs.1 t (by omega)
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
  simp only [Silmaril.Process.addressLimit, arg0] at hlt
  have hofs : (BitVec.ofNat 64 t).toNat = t := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hA : w.toNat = arg0 m0 + t := by
    rw [hw, toNat_add_lt (by rw [hofs]; omega), hofs]; rfl
  refine ⟨b, loadN_one (by rw [hA, hm]; exact hrd) (by rw [hA, hm]; exact hb), ?_⟩
  constructor
  · intro e; by_contra hne
    exact hs.2.1 t (by omega) (by rw [hb, e])
  · intro e; subst e; rw [hs.2.2] at hb; exact (Option.some.inj hb).symm

theorem lenOff_eq {m0 m : MState} {t : Nat} (h : m.core.read .rax = m0.core.read .rdi + BitVec.ofNat 64 t)
    (ht : t < 2 ^ 64) : lenOff m0 m = t := by
  rw [lenOff, h, add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht]

theorem strLen_lt {m0 : MState} (hs : CStr m0.memory (arg0 m0) (strLen m0)) : strLen m0 < 2 ^ 64 := by
  have := (hs.1 (strLen m0) (by omega)).1; simp [Silmaril.Process.addressLimit] at this; omega

theorem len_lifts05 : liftBlock lenL05 = some lenI05 := by decide +kernel
theorem len_lifts10 : liftBlock lenL10 = some lenI10 := by decide +kernel
theorem len_lifts19 : liftBlock lenL19 = some lenI19 := by decide +kernel
theorem len_lifts20 : liftBlock lenL20 = some lenI20 := by decide +kernel

theorem len_b00 (entry : Word) : (strlenCert entry).BlockVCW (lenQ entry) ⟨0x00, lenL00⟩ := by
  intro m0 m ⟨hm, hab, he⟩ hrip hl
  subst hm
  have hs := strLen_spec he.2.2
  obtain ⟨b, hlo, hb⟩ := cstr_byte (t := 0) hs rfl (by omega) (w := m.core.read .rdi) (by simp)
  obtain ⟨m', hrun, hmem, hreg, hrip'⟩ := cmpb_zero_run (r := .rdi) (rel := 0x1b) hlo (.inl rfl)
  refine ⟨m', hrun, ?_⟩
  have hf : LoopFrame m m' := (LoopFrame.entry hab).step (hreg _) (fun r _ => hreg r)
  by_cases hK : strLen m = 0
  · apply FunCert.next_ofW ⟨0x20, lenL20⟩ (by simp [strlenCert])
    · rw [hrip']; simp [hrip, strlenCert, BitVec.add_assoc]; exact hb.mpr hK.symm
    · rw [hmem]; exact hl
    · exact ⟨he, hf, hmem, hK⟩
    · simp [strlenCert, lenMeasure]
  · apply FunCert.next_ofW ⟨0x05, lenL05⟩ (by simp [strlenCert])
    · rw [hrip']; simp [hrip, strlenCert, BitVec.add_assoc]; exact fun e => hK (hb.mp e).symm
    · rw [hmem]; exact hl
    · exact ⟨he, hf, hmem, hreg _, by omega⟩
    · simp [strlenCert, lenMeasure]

theorem len_b05 (entry : Word) : (strlenCert entry).BlockVCW (lenQ entry) ⟨0x05, lenL05⟩ := by
  intro m0 m ⟨he, hf, hm, hrdi, hK⟩ hrip hl
  rw [runL_eq_runB len_lifts05]
  bir_simp [lenI05]
  apply FunCert.next_ofW ⟨0x10, lenL10⟩ (by simp [strlenCert])
  · bir_close [hrip, strlenCert, BitVec.add_assoc]
  · exact hl
  · refine ⟨he, 0, ⟨hf.step ?_ ?_, hm, ?_, ?_, by omega⟩, hK⟩
    all_goals bir_close [hrdi]
  · simp only [strlenCert, lenMeasure]
    rw [lenOff_eq (t := 0) (by bir_close [hrdi]) (by decide)]
    omega

theorem len_b10 (entry : Word) : (strlenCert entry).BlockVCW (lenQ entry) ⟨0x10, lenL10⟩ := by
  intro m0 m ⟨he, t, hL, ht⟩ hrip hl
  have hK := strLen_lt (strLen_spec he.2.2)
  have hrax : m.core.read .rax + 1 = m0.core.read .rdi + BitVec.ofNat 64 (t + 1) := by
    rw [hL.rax, BitVec.add_assoc, BitVec.ofNat_add]; rfl
  rw [runL_eq_runB len_lifts10]
  bir_simp [lenI10]
  apply FunCert.next_ofW ⟨0x14, lenL14⟩ (by simp [strlenCert])
  · bir_close [hrip, strlenCert, BitVec.add_assoc]
  · exact hl
  · refine ⟨he, t + 1, ⟨hL.frame.step ?_ ?_, hL.mem, ?_, ?_, by omega⟩⟩
    all_goals try (bir_close [hL.rdi]; done)
    bir_close; exact hrax
  · simp only [strlenCert, lenMeasure]
    rw [lenOff_eq (t := t + 1) (by bir_close; exact hrax) (by omega), lenOff_eq hL.rax (by omega)]
    omega

theorem len_b14 (entry : Word) : (strlenCert entry).BlockVCW (lenQ entry) ⟨0x14, lenL14⟩ := by
  intro m0 m ⟨he, t, hL⟩ hrip hl
  have hs := strLen_spec he.2.2
  have hK := strLen_lt hs
  obtain ⟨b, hlo, hb⟩ := cstr_byte hs hL.mem hL.le hL.rax
  obtain ⟨m', hrun, hmem, hreg, hrip'⟩ := cmpb_zero_run (r := .rax) (rel := 0xf7) hlo (.inr rfl)
  refine ⟨m', hrun, ?_⟩
  have hL' : LenAt m0 m' t := ⟨hL.frame.step (hreg _) (fun r _ => hreg r), hmem.trans hL.mem,
    (hreg _).trans hL.rdi, (hreg _).trans hL.rax, hL.le⟩
  by_cases ht : t = strLen m0
  · apply FunCert.next_ofW ⟨0x19, lenL19⟩ (by simp [strlenCert])
    · rw [hrip']; simp [hrip, strlenCert, BitVec.add_assoc]; exact hb.mpr ht
    · rw [hmem]; exact hl
    · exact ⟨he, ht ▸ hL'⟩
    · simp [strlenCert, lenMeasure]
  · apply FunCert.next_ofW ⟨0x10, lenL10⟩ (by simp [strlenCert])
    · rw [hrip']; simp [hrip, strlenCert, BitVec.add_assoc]; exact fun e => ht (hb.mp e)
    · rw [hmem]; exact hl
    · exact ⟨he, t, hL', by have := hL.le; omega⟩
    · simp only [strlenCert, lenMeasure]
      rw [lenOff_eq hL'.rax (by have := hL.le; omega), lenOff_eq hL.rax (by have := hL.le; omega)]
      omega

theorem len_b19 (entry : Word) : (strlenCert entry).BlockVCW (lenQ entry) ⟨0x19, lenL19⟩ := by
  intro m0 m ⟨he, hL⟩ _ _
  have hs := strLen_spec he.2.2
  rw [runL_eq_runB len_lifts19]
  bir_simp [lenI19, hL.frame.pop (by rw [hL.mem])]
  have hw : m0.memory.WritesWithin m.memory fun _ => False := by
    rw [hL.mem]; exact Silmaril.Process.Memory.WritesWithin.refl _ _
  refine .inl (hL.frame.result ?_ ?_ ?_ rfl hw ⟨fun k hk => ?_, hw⟩)
  all_goals try (bir_close; done)
  bir_close [hL.rax, hL.rdi, ← cstr_unique hs hk]

theorem len_b20 (entry : Word) : (strlenCert entry).BlockVCW (lenQ entry) ⟨0x20, lenL20⟩ := by
  intro m0 m ⟨he, hf, hm, hK⟩ _ _
  have hs := strLen_spec he.2.2
  rw [runL_eq_runB len_lifts20]
  bir_simp [lenI20, hf.pop (by rw [hm])]
  have hw : m0.memory.WritesWithin m.memory fun _ => False := by
    rw [hm]; exact Silmaril.Process.Memory.WritesWithin.refl _ _
  refine .inl (hf.result ?_ ?_ ?_ rfl hw ⟨fun k hk => ?_, hw⟩)
  all_goals try (bir_close; done)
  bir_close [← cstr_unique hs hk, hK]

theorem len_vc (entry : Word) : (strlenCert entry).VCW (lenQ entry) := FunCert.vcW_of_blocks (by
  simp only [strlenCert, List.mem_cons, List.not_mem_nil, or_false]
  rintro b (rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [len_b00 entry, len_b05 entry, len_b10 entry, len_b14 entry, len_b19 entry, len_b20 entry])

theorem len_checked (e : Word) : (strlenCert e).checkedW = true := len_checked0

theorem strlen_total (entry : Word) : (scanContract strlenCode entry).Total Open.isa :=
  FunCert.totalW _ (entry := ⟨0x00, lenL00⟩) (by simp [strlenCert]) (len_checked entry)
    (len_vc entry) fun m hab he => ⟨he.2.1, by rw [he.1]; simp [strlenCert], rfl, hab, he⟩

end Silmaril.Proofs.Machine.X86.Ladder.LibMini
