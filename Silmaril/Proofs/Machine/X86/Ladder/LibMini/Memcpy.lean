module

public import Silmaril.Machine.X86.Ladder.LibMini.Defs
public import Silmaril.Machine.X86.Stencils.ByteLoop.Thms

/-!
# `memcpy` (gcc -O2) as a `Copy` stencil instance

Blocks `0x00` (`n = 0` test), `0x08` (`i := 0`), `0x10` (`movzbl; store`: one byte of the
prefix), `0x19` (`add; cmp; jne`: next index or exit) and `0x22` (`ret`). The annotation at the
loop is `CpyAt m0 m i` with `i = rcx < n`; the measure is `2 (n - i)`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.Ladder.LibMini

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Lift.Bir (Block LInstr liftBlock)
open Silmaril.Machine.X86 Silmaril.Machine.X86.BlockCert Silmaril.Machine.X86.Stencils.ByteLoop
open Silmaril.Machine.X86.Ladder.LibMini Silmaril.Machine.X86.Ladder.LibMini.Bir.memcpy

set_option linter.unusedSimpArgs false

/-- The exit condition: the contract's result. -/
abbrev cpyQ (entry : Word) : MState → MState → Prop :=
  fun m0 t => (copyContract memcpyCode entry).Result Open.isa m0 t
theorem cpy_checked0 : (memcpyCert 0).checkedW = true := by decide +kernel
theorem cpy_checked (e : Word) : (memcpyCert e).checkedW = true := cpy_checked0

theorem cpy_b00 (entry : Word) : (memcpyCert entry).BlockVCW (cpyQ entry) ⟨0x00, L_401300⟩ := by
  intro m0 m ⟨hm, hab, he⟩ hrip hl
  subst hm
  rw [runL_eq_runB lifts_401300]
  bir_simp [I_401300]
  have hsp : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, r ≠ Reg.rax := by decide
  by_cases hn : m.core.read .rdx = 0
  · have h2 : arg2 m = 0 := by simp [arg2, hn]
    apply FunCert.next_ofW ⟨0x22, L_401322⟩ (by simp [memcpyCert])
    · bir_close [hrip, memcpyCert, hn]
    · exact hl
    · refine ⟨he, LoopFrame.entry hab |>.step ?_ ?_, ?_, ?_, ?_, ?_⟩
      all_goals try (bir_close; done)
      rw [h2]; exact Prefix.init _ _ _
    · simp [memcpyCert, cpyMeasure]
  · apply FunCert.next_ofW ⟨0x08, L_401308⟩ (by simp [memcpyCert])
    · bir_close [hrip, memcpyCert, BitVec.add_assoc]; exact hn
    · exact hl
    · refine ⟨he, ⟨LoopFrame.entry hab |>.step ?_ ?_, ?_, ?_, ?_, Prefix.init _ _ _⟩, ?_⟩
      all_goals try (bir_close; done)
      simpa [arg2, BitVec.toNat_eq] using hn
    · simp [memcpyCert, cpyMeasure]

theorem cpy_lifts10 : liftBlock cpyL10 = some cpyI10 := by decide +kernel
theorem cpy_lifts19 : liftBlock cpyL19 = some cpyI19 := by decide +kernel

theorem cpy_b08 (entry : Word) : (memcpyCert entry).BlockVCW (cpyQ entry) ⟨0x08, L_401308⟩ := by
  intro m0 m ⟨he, hc, hn⟩ hrip hl
  rw [runL_eq_runB lifts_401308]
  bir_simp [I_401308]
  apply FunCert.next_ofW ⟨0x10, cpyL10⟩ (by simp [memcpyCert])
  · bir_close [hrip, memcpyCert, BitVec.add_assoc]
  · exact hl
  · refine ⟨he, ⟨hc.frame.step ?_ ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try (bir_close [hc.rax, hc.rsi, hc.rdx]; done)
    · bir_close; exact hc.pre
    · bir_close; omega
  · bir_close [memcpyCert, cpyMeasure]

theorem cpy_b10 (entry : Word) : (memcpyCert entry).BlockVCW (cpyQ entry) ⟨0x10, cpyL10⟩ := by
  intro m0 m ⟨he, hc, hi⟩ hrip hl
  obtain ⟨hr0, hload, hW, hR, hDS, hDC, hDR⟩ := he
  set i := (m.core.read .rcx).toNat with hi_def
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hR i hi).2.2
  have hA : (m.core.read .rax + m.core.read .rcx).toNat = arg0 m0 + i := by
    rw [toNat_add_lt] <;> rw [hc.rax] <;> simp only [arg0] at hW ⊢ <;> have := (hW i hi).1 <;>
      simp [Silmaril.Process.addressLimit] at this <;> omega
  have hS : (m.core.read .rsi + m.core.read .rcx).toNat = arg1 m0 + i := by
    rw [toNat_add_lt] <;> rw [hc.rsi] <;> simp only [arg1] at hR ⊢ <;> have := (hR i hi).1 <;>
      simp [Silmaril.Process.addressLimit] at this <;> omega
  have hlo := loadN_one (mem := m.memory) (w := m.core.read .rsi + m.core.read .rcx) (b := b)
    (by rw [hS, hc.pre.permits]; exact (hR i hi).2.1)
    (by rw [hS, hc.pre.get_apart hi.le hDS hi]; exact hb)
  have hst := fun v => storeN_one (mem := m.memory) (w := m.core.read .rax + m.core.read .rcx) (v := v)
    (by rw [hA, hc.pre.permits]; exact (hW i hi).2)
  rw [runL_eq_runB cpy_lifts10]
  bir_simp [cpyI10, hlo, hst]
  have hp := hc.pre.set1 (b := b) (by simpa using hb)
  apply FunCert.next_ofW ⟨0x19, cpyL19⟩ (by simp [memcpyCert])
  · bir_close [hrip, memcpyCert, BitVec.add_assoc]
  · simp (disch := decide) only [hA, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      BitVec.ofNat_toNat]
    exact hp.loaded hi hDC hload
  · refine ⟨⟨hr0, hload, hW, hR, hDS, hDC, hDR⟩, ⟨hc.frame.step ?_ ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try (bir_close [hc.rax, hc.rsi, hc.rdx]; done)
    · simp (disch := decide) only [hA, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
        BitVec.ofNat_toNat]
      bir_close
      exact hp
    · bir_close; exact hi
  · bir_close [memcpyCert, cpyMeasure]

theorem cpy_b19 (entry : Word) : (memcpyCert entry).BlockVCW (cpyQ entry) ⟨0x19, cpyL19⟩ := by
  intro m0 m ⟨he, hc, hi⟩ hrip hl
  rw [runL_eq_runB cpy_lifts19]
  bir_simp [cpyI19, subFlagsN_zero]
  have hn2 : arg2 m0 < 2 ^ 64 := (m0.core.read .rdx).isLt
  have hr1 : (m.core.read .rcx + 1).toNat = (m.core.read .rcx).toNat + 1 := by
    rw [toNat_add_lt] <;> simp
    omega
  have hr1' : ((m.core.read .rcx).toNat + 1) % 18446744073709551616 = (m.core.read .rcx).toNat + 1 :=
    Nat.mod_eq_of_lt (by omega)
  by_cases h : (m.core.read .rcx).toNat + 1 = arg2 m0
  · have heq : m.core.read .rdx = m.core.read .rcx + 1 := by
      apply BitVec.eq_of_toNat_eq; rw [hr1, hc.rdx]; exact h.symm
    apply FunCert.next_ofW ⟨0x22, L_401322⟩ (by simp [memcpyCert])
    · bir_close [hrip, memcpyCert, heq, BitVec.add_assoc]
    · exact hl
    · refine ⟨he, ⟨hc.frame.step ?_ ?_, ?_, ?_, ?_, ?_⟩⟩
      all_goals try (bir_close [hc.rax, hc.rsi, hc.rdx]; done)
      bir_close; rw [← h]; exact hc.pre
    · bir_close [memcpyCert, cpyMeasure]; omega
  · have heq : ¬ m.core.read .rdx = m.core.read .rcx + 1 := by
      intro e; apply h; rw [← hr1, ← e, hc.rdx]; rfl
    apply FunCert.next_ofW ⟨0x10, cpyL10⟩ (by simp [memcpyCert])
    · bir_close [hrip, memcpyCert, BitVec.add_assoc]; exact heq
    · exact hl
    · refine ⟨he, ⟨hc.frame.step ?_ ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try (bir_close [hc.rax, hc.rsi, hc.rdx]; done)
      · bir_close [hr1, hr1']; exact hc.pre
      · bir_close [hr1, hr1']; omega
    · bir_close [memcpyCert, cpyMeasure, hr1, hr1']; omega

theorem cpy_b22 (entry : Word) : (memcpyCert entry).BlockVCW (cpyQ entry) ⟨0x22, L_401322⟩ := by
  intro m0 m ⟨he, hc⟩ _ _
  rw [runL_eq_runB lifts_401322]
  bir_simp [I_401322, hc.frame.pop (hc.pre.readBytes le_rfl he.2.2.2.2.2.2)]
  refine .inl (hc.frame.result ?_ ?_ ?_ rfl (hc.pre.writesWithin le_rfl) ⟨?_, ?_, ?_⟩)
  all_goals try (bir_close [hc.rax]; done)
  · exact hc.pre.writesWithin le_rfl
  · intro i hi; exact hc.pre.inside i hi

theorem cpy_vc (entry : Word) : (memcpyCert entry).VCW (cpyQ entry) := FunCert.vcW_of_blocks (by
  simp only [memcpyCert, List.mem_cons, List.not_mem_nil, or_false]
  rintro b (rfl | rfl | rfl | rfl | rfl)
  exacts [cpy_b00 entry, cpy_b08 entry, cpy_b10 entry, cpy_b19 entry, cpy_b22 entry])

theorem memcpy_total (entry : Word) : (copyContract memcpyCode entry).Total Open.isa :=
  FunCert.totalW _ (entry := ⟨0x00, L_401300⟩) (by simp [memcpyCert]) (cpy_checked entry)
    (cpy_vc entry) fun m hab he => ⟨he.2.1, by rw [he.1]; simp [memcpyCert], rfl, hab, he⟩

end Silmaril.Proofs.Machine.X86.Ladder.LibMini
