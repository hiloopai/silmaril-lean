module

public import Silmaril.X86.Ladder.LibMini.Defs
public import Silmaril.X86.Stencils.ByteLoop.Thms

/-!
# `memset` (gcc -O2) as a `Fill` stencil instance

gcc peels one byte when `n` is odd and unrolls the loop twice, so the store pointer `rcx = d + k`
moves by two with `n - k` even. Blocks `0x00`, `0x08` (split on parity), `0x17`/`0x1e`/`0x23`
(the peeled byte), `0x28`/`0x2b`/`0x33` (the loop body, cut after each store) and the two
`ret`s `0x38`, `0x39`. The measure is `2 (n - k)`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.LibMini

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Bir9 (Block LInstr liftBlock)
open Silmaril.X86 Silmaril.X86.BlockCert Silmaril.X86.Stencils.ByteLoop
open Silmaril.X86.Ladder.LibMini Silmaril.X86.Ladder.LibMini.Bir.memset

set_option linter.unusedSimpArgs false

/-- The exit condition: the contract's result. -/
abbrev setQ (entry : Word) : MState → MState → Prop :=
  fun m0 t => (fillContract memsetCode entry).Result Open.isa m0 t
theorem set_checked0 : (memsetCert 0).checkedW = true := by decide +kernel
theorem set_checked (e : Word) : (memsetCert e).checkedW = true := set_checked0

theorem set_b00 (entry : Word) : (memsetCert entry).BlockVCW (setQ entry) ⟨0x00, L_401380⟩ := by
  intro m0 m ⟨hm, hab, he⟩ hrip hl
  subst hm
  rw [runL_eq_runB lifts_401380]
  bir_simp [I_401380]
  by_cases hn : m.core.read .rdx = 0
  · have h2 : arg2 m = 0 := by simp [arg2, hn]
    apply FunCert.next_ofW ⟨0x38, L_4013b8⟩ (by simp [memsetCert])
    · bir_close [hrip, memsetCert, hn]
    · exact hl
    · refine ⟨he, LoopFrame.entry hab |>.step ?_ ?_, ?_, ?_⟩
      all_goals try (bir_close; done)
      rw [h2]; exact Prefix.init _ _ _
    · simp [memsetCert, setMeasure]
  · apply FunCert.next_ofW ⟨0x08, L_401388⟩ (by simp [memsetCert])
    · bir_close [hrip, memsetCert]; exact hn
    · exact hl
    · refine ⟨he, LoopFrame.entry hab |>.step ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try (bir_close; done)
      simpa [arg2, BitVec.toNat_eq] using hn
    · simp [memsetCert, setMeasure]

theorem set_b08 (entry : Word) : (memsetCert entry).BlockVCW (setQ entry) ⟨0x08, L_401388⟩ := by
  intro m0 m ⟨he, hf, hm, hrax, hrdi, hrsi, hrdx, hn⟩ hrip hl
  rw [runL_eq_runB lifts_401388]
  bir_simp [I_401388, and_one_zero]
  by_cases hev : (m.core.read .rdx).toNat % 2 = 0
  · apply FunCert.next_ofW ⟨0x28, setL28⟩ (by simp [memsetCert])
    · bir_close [hrip, memsetCert, hev, BitVec.add_assoc]
    · bir_close [hm]; rw [← hm]; exact hl
    · refine ⟨he, 0, ⟨hf.step ?_ ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      all_goals try (bir_close [hrax, hrsi, fillByte]; done)
      · bir_close [hrdx, hrdi]; exact BitVec.add_comm _ _
      · bir_close [hm]; exact Prefix.init _ _ _
      · bir_close [SetPtr, hrdi]
      · omega
      · rw [hrdx] at hev; simpa [arg2] using hev
    · bir_close [memsetCert, setMeasure, setOff, hrdi]
  · apply FunCert.next_ofW ⟨0x17, setL17⟩ (by simp [memsetCert])
    · bir_close [hrip, memsetCert, hev, BitVec.add_assoc]
    · exact hl
    · refine ⟨he, ⟨hf.step ?_ ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      all_goals try (bir_close [hrax, hrsi, fillByte]; done)
      · bir_close [hrdx, hrdi]; exact BitVec.add_comm _ _
      · bir_close [hm]; exact Prefix.init _ _ _
      · rw [hrdx] at hev; simp only [arg2]; omega
    · bir_close [memsetCert, setMeasure]

theorem set_lifts17 : liftBlock setL17 = some setI17 := by decide +kernel
theorem set_lifts1e : liftBlock setL1e = some setI1e := by decide +kernel
theorem set_lifts28 : liftBlock setL28 = some setI28 := by decide +kernel
theorem set_lifts2b : liftBlock setL2b = some setI2b := by decide +kernel
theorem set_lifts33 : liftBlock setL33 = some setI33 := by decide +kernel

theorem toNat_ptr {m0 m : MState} {p : Nat} (h : SetPtr m0 m p) (hp : arg0 m0 + p < 2 ^ 64) :
    (m.core.read .rcx).toNat = arg0 m0 + p := by
  rw [h, toNat_add_lt] <;> simp only [arg0, BitVec.toNat_ofNat] at hp ⊢ <;> rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem setOff_ptr {m0 m : MState} {p : Nat} (h : SetPtr m0 m p) (hp : p < 2 ^ 64) :
    setOff m0 m = p := by
  unfold SetPtr at h
  rw [setOff, h, add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]

theorem set_b17 (entry : Word) : (memsetCert entry).BlockVCW (setQ entry) ⟨0x17, setL17⟩ := by
  intro m0 m ⟨he, hs, hrsi, hodd⟩ hrip hl
  obtain ⟨hr0, hload, hW, hDC, hDR⟩ := he
  have hn : 0 < arg2 m0 := by omega
  have hA : (m.core.read .rax).toNat = arg0 m0 := by rw [hs.rax]; rfl
  have hst := fun v => storeN_one (mem := m.memory) (w := m.core.read .rax) (v := v)
    (by rw [hA, hs.pre.permits]; simpa using (hW 0 hn).2)
  rw [runL_eq_runB set_lifts17]
  bir_simp [setI17, hst]
  have hp := hs.pre.set1 (b := fillByte m0) rfl
  simp only [Nat.add_zero, Nat.zero_add] at hp
  apply FunCert.next_ofW ⟨0x1e, setL1e⟩ (by simp [memsetCert])
  · bir_close [hrip, memsetCert, BitVec.add_assoc]
  · simp (disch := decide) only [hA, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    rw [hrsi]; exact hp.loaded hn hDC hload
  · refine ⟨⟨hr0, hload, hW, hDC, hDR⟩, ⟨hs.frame.step ?_ ?_, ?_, ?_, ?_, ?_⟩, ?_, hodd⟩
    all_goals try (bir_close [hs.rax, hs.rdi, hs.r8]; done)
    · simp (disch := decide) only [hA, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
      bir_close [hrsi]; exact hp
    · bir_close [SetPtr, hs.rax]
  · bir_close [memsetCert, setMeasure]

theorem set_b1e (entry : Word) : (memsetCert entry).BlockVCW (setQ entry) ⟨0x1e, setL1e⟩ := by
  intro m0 m ⟨he, hs, hptr, hodd⟩ hrip hl
  rw [runL_eq_runB set_lifts1e]
  bir_simp [setI1e, subFlagsN_zero]
  have hiff : m.core.read .rcx = m.core.read .rdi ↔ 1 = arg2 m0 := by
    rw [hptr, hs.rdi]; exact ptr_eq_iff (by decide)
  by_cases h1 : 1 = arg2 m0
  · apply FunCert.next_ofW ⟨0x39, L_4013b9⟩ (by simp [memsetCert])
    · bir_close [hrip, memsetCert, hiff.mpr h1, BitVec.add_assoc]
    · exact hl
    · refine ⟨he, hs.frame.step ?_ ?_, ?_, ?_⟩
      all_goals try (bir_close [hs.rax]; done)
      bir_close; rw [← h1]; exact hs.pre
    · bir_close [memsetCert, setMeasure]
  · apply FunCert.next_ofW ⟨0x23, L_4013a3⟩ (by simp [memsetCert])
    · bir_close [hrip, memsetCert, BitVec.add_assoc]; exact mt hiff.mp h1
    · exact hl
    · refine ⟨he, ⟨hs.frame.step ?_ ?_, ?_, ?_, ?_, ?_⟩, ?_, by omega, hodd⟩
      all_goals try (bir_close [hs.rax, hs.rdi, hs.r8]; done)
      · bir_close; exact hs.pre
      · bir_close [SetPtr]; exact hptr
    · bir_close [memsetCert, setMeasure]

theorem set_b23 (entry : Word) : (memsetCert entry).BlockVCW (setQ entry) ⟨0x23, L_4013a3⟩ := by
  intro m0 m ⟨he, hs, hptr, h1, hodd⟩ hrip hl
  rw [runL_eq_runB lifts_4013a3]
  bir_simp [I_4013a3]
  apply FunCert.next_ofW ⟨0x28, setL28⟩ (by simp [memsetCert])
  · bir_close [hrip, memsetCert, BitVec.add_assoc]
  · exact hl
  · refine ⟨he, 1, ⟨hs.frame.step ?_ ?_, ?_, ?_, ?_, ?_⟩, ?_, h1, by omega⟩
    all_goals try (bir_close [hs.rax, hs.rdi, hs.r8]; done)
    · bir_close; exact hs.pre
    · bir_close [SetPtr]; exact hptr
  · rw [show (memsetCert entry).measure 0x28 m0 _ = 2 * (arg2 m0 - 1) + 2 by
      simp only [memsetCert, setMeasure]; rw [setOff_ptr (p := 1) (by bir_close [SetPtr]; exact hptr) (by decide)]]
    simp [memsetCert, setMeasure]; omega

theorem set_b28 (entry : Word) : (memsetCert entry).BlockVCW (setQ entry) ⟨0x28, setL28⟩ := by
  intro m0 m ⟨he, k, hs, hptr, hk, hev⟩ hrip hl
  obtain ⟨hr0, hload, hW, hDC, hDR⟩ := he
  have hA := toNat_ptr hptr (by have := (hW k hk).1; simp [Silmaril.Process.addressLimit] at this; omega)
  have hst := fun v => storeN_one (mem := m.memory) (w := m.core.read .rcx) (v := v)
    (by rw [hA, hs.pre.permits]; exact (hW k hk).2)
  rw [runL_eq_runB set_lifts28]
  bir_simp [setI28, hst]
  have hp := hs.pre.set1 (b := fillByte m0) rfl
  apply FunCert.next_ofW ⟨0x2b, setL2b⟩ (by simp [memsetCert])
  · bir_close [hrip, memsetCert, BitVec.add_assoc]
  · simp (disch := decide) only [hA, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    rw [hs.r8]; exact hp.loaded hk hDC hload
  · refine ⟨⟨hr0, hload, hW, hDC, hDR⟩, k, ⟨hs.frame.step ?_ ?_, ?_, ?_, ?_, ?_⟩, ?_, hk, hev⟩
    all_goals try (bir_close [hs.rax, hs.rdi, hs.r8]; done)
    · simp (disch := decide) only [hA, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
      bir_close [hs.r8]; exact hp
    · bir_close [SetPtr]; exact hptr
  · have hk64 : k < 2 ^ 64 := by have := (m0.core.read .rdx).isLt; simp only [arg2] at hk; omega
    simp only [memsetCert, setMeasure]
    rw [setOff_ptr (p := k) (by bir_close [SetPtr]; exact hptr) hk64, setOff_ptr hptr hk64]
    omega

theorem set_b2b (entry : Word) : (memsetCert entry).BlockVCW (setQ entry) ⟨0x2b, setL2b⟩ := by
  intro m0 m ⟨he, k, hs, hptr, hk, hev⟩ hrip hl
  obtain ⟨hr0, hload, hW, hDC, hDR⟩ := he
  have hk1 : k + 1 < arg2 m0 := by omega
  have hk64 : k + 2 < 2 ^ 64 := by
    have := (m0.core.read .rdx).isLt; simp only [arg2] at hk hk1 hev; omega
  have hA0 := toNat_ptr hptr (by have := (hW k hk).1; simp [Silmaril.Process.addressLimit] at this; omega)
  have hA : (m.core.read .rcx + 1).toNat = arg0 m0 + (k + 1) := by
    rw [toNat_add_lt, hA0] <;> simp <;> have := (hW (k + 1) hk1).1 <;>
      simp [Silmaril.Process.addressLimit] at this <;> omega
  have hst := fun v => storeN_one (mem := m.memory) (w := m.core.read .rcx + 1) (v := v)
    (by rw [hA, hs.pre.permits]; exact (hW (k + 1) hk1).2)
  have hptr2 : m.core.read .rcx + 2 = m0.core.read .rdi + BitVec.ofNat 64 (k + 2) := by
    rw [hptr, BitVec.add_assoc, BitVec.ofNat_add]; rfl
  rw [runL_eq_runB set_lifts2b]
  bir_simp [setI2b, hst]
  have hp := hs.pre.set1 (b := fillByte m0) rfl
  apply FunCert.next_ofW ⟨0x33, setL33⟩ (by simp [memsetCert])
  · bir_close [hrip, memsetCert, BitVec.add_assoc]
  · simp (disch := decide) only [hA, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    rw [hs.r8]; exact hp.loaded hk1 hDC hload
  · refine ⟨⟨hr0, hload, hW, hDC, hDR⟩, k + 2, ⟨hs.frame.step ?_ ?_, ?_, ?_, ?_, ?_⟩, ?_, by omega,
      by omega, by omega⟩
    all_goals try (bir_close [hs.rax, hs.rdi, hs.r8]; done)
    · simp (disch := decide) only [hA, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
      bir_close [hs.r8]; exact hp
    · bir_close [SetPtr]; exact hptr2
  · simp only [memsetCert, setMeasure]
    rw [setOff_ptr (p := k + 2) (by bir_close [SetPtr]; exact hptr2) hk64, setOff_ptr hptr (by omega)]
    omega

theorem set_b33 (entry : Word) : (memsetCert entry).BlockVCW (setQ entry) ⟨0x33, setL33⟩ := by
  intro m0 m ⟨he, k, hs, hptr, h2, hk, hev⟩ hrip hl
  rw [runL_eq_runB set_lifts33]
  bir_simp [setI33, subFlagsN_zero]
  have hk64 : k < 2 ^ 64 := by have := (m0.core.read .rdx).isLt; simp only [arg2] at hk; omega
  have hiff : m.core.read .rcx = m.core.read .rdi ↔ k = arg2 m0 := by
    rw [hptr, hs.rdi]; exact ptr_eq_iff hk64
  by_cases h1 : k = arg2 m0
  · apply FunCert.next_ofW ⟨0x38, L_4013b8⟩ (by simp [memsetCert])
    · bir_close [hrip, memsetCert, hiff.mpr h1, BitVec.add_assoc]
    · exact hl
    · refine ⟨he, hs.frame.step ?_ ?_, ?_, ?_⟩
      all_goals try (bir_close [hs.rax]; done)
      bir_close; rw [← h1]; exact hs.pre
    · bir_close [memsetCert, setMeasure]
  · apply FunCert.next_ofW ⟨0x28, setL28⟩ (by simp [memsetCert])
    · bir_close [hrip, memsetCert, BitVec.add_assoc]; exact mt hiff.mp h1
    · exact hl
    · refine ⟨he, k, ⟨hs.frame.step ?_ ?_, ?_, ?_, ?_, ?_⟩, ?_, by omega, hev⟩
      all_goals try (bir_close [hs.rax, hs.rdi, hs.r8]; done)
      · bir_close; exact hs.pre
      · bir_close [SetPtr]; exact hptr
    · simp only [memsetCert, setMeasure]
      rw [setOff_ptr (p := k) (by bir_close [SetPtr]; exact hptr) hk64, setOff_ptr hptr hk64]
      omega

theorem set_ret {entry : Word} {L : List (LInstr × Nat)} (hI : liftBlock L = some I_4013b8)
    {m0 m : MState} (he : (fillContract memsetCode entry).entry m0) (hd : SetDone m0 m) :
    ∃ m', runL L m = some m' ∧ setQ entry m0 m' := by
  rw [runL_eq_runB hI]
  bir_simp [I_4013b8, hd.frame.pop (hd.pre.readBytes le_rfl he.2.2.2.2)]
  refine hd.frame.result ?_ ?_ ?_ rfl (hd.pre.writesWithin le_rfl) ⟨?_, ?_, ?_⟩
  all_goals try (bir_close [hd.rax]; done)
  · exact hd.pre.writesWithin le_rfl
  · intro i hi; exact hd.pre.inside i hi

theorem set_b38 (entry : Word) : (memsetCert entry).BlockVCW (setQ entry) ⟨0x38, L_4013b8⟩ := by
  intro m0 m ⟨he, hd⟩ _ _
  obtain ⟨m', h1, h2⟩ := set_ret lifts_4013b8 he hd
  exact ⟨m', h1, .inl h2⟩

theorem set_b39 (entry : Word) : (memsetCert entry).BlockVCW (setQ entry) ⟨0x39, L_4013b9⟩ := by
  intro m0 m ⟨he, hd⟩ _ _
  obtain ⟨m', h1, h2⟩ := set_ret (lifts_4013b9.trans rfl) he hd
  exact ⟨m', h1, .inl h2⟩

theorem set_vc (entry : Word) : (memsetCert entry).VCW (setQ entry) := FunCert.vcW_of_blocks (by
  simp only [memsetCert, List.mem_cons, List.not_mem_nil, or_false]
  rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [set_b00 entry, set_b08 entry, set_b17 entry, set_b1e entry, set_b23 entry, set_b28 entry,
    set_b2b entry, set_b33 entry, set_b38 entry, set_b39 entry])

theorem memset_total (entry : Word) : (fillContract memsetCode entry).Total Open.isa :=
  FunCert.totalW _ (entry := ⟨0x00, L_401380⟩) (by simp [memsetCert]) (set_checked entry)
    (set_vc entry) fun m hab he => ⟨he.2.1, by rw [he.1]; simp [memsetCert], rfl, hab, he⟩

end Silmaril.Proofs.X86.Ladder.LibMini
