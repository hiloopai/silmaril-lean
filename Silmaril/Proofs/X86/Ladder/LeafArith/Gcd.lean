module

public import Silmaril.X86.Ladder.LeafArith.Defs
import Silmaril.X86.BlockCert.Thms
public import Silmaril.X86.Open.Thms
/-!
# `gcd_u32` (gcc -O2): Euclid's loop, with a cut and a `div`

The loop head `0x401380` is a cut with Euclid's invariant `gcd eax edx = gcd a b`,
`edx ≠ 0`, and measure `3·edx + 3`; the loop body is cut at `div %ecx`, which Bir cannot
lift, so `0x401384` is a one-instruction block whose VC unfolds `Ext.exec` (`Ext.divide` with
`edx = 0`). The other blocks are Bir blocks, listed by hand and checked by `decide +kernel`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.LeafArith

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Bir9 (Block LInstr liftBlock)
open Silmaril.X86 Silmaril.X86.BlockCert Silmaril.X86.Ladder.LeafArith

set_option linter.unusedSimpArgs false

abbrev gcdQ : MState → MState → Prop := fun m0 t => gcdSpec'.Result Open.isa m0 t

private theorem mem {o : Nat} {L : List (LInstr × Nat)}
    (h : (⟨o, L⟩ : Blk) ∈ gcdCert.blocks := by simp [gcdCert]) :
    (⟨o, L⟩ : Blk) ∈ gcdCert.blocks :=
  h

theorem gcd_lifts00 : liftBlock gcdL00 = some gcdI00 := by decide +kernel
theorem gcd_lifts08 : liftBlock gcdL08 = some gcdI08 := by decide +kernel
theorem gcd_lifts10 : liftBlock gcdL10 = some gcdI10 := by decide +kernel
theorem gcd_lifts16 : liftBlock gcdL16 = some gcdI16 := by decide +kernel
theorem gcd_lifts1c : liftBlock gcdL1c = some gcdI1c := by decide +kernel
theorem gcd_lifts20 : liftBlock gcdL20 = some gcdI20 := by decide +kernel

theorem gcd_checked : gcdCert.checked = true := by decide +kernel

theorem gcd_b00 : gcdCert.BlockVC gcdQ ⟨0x00, gcdL00⟩ := by
  intro m0 m ⟨hm, hab⟩ hrip _
  subst hm
  rw [runL_eq_runB gcd_lifts00]
  bir_simp [gcdI00]
  have hf := Frame.entry hab
  by_cases hc : r32 .rsi m = 0 <;> have hc' := hc <;> simp [r32] at hc'
  · apply FunCert.next_of ⟨0x20, gcdL20⟩ mem
    · bir_close [hrip, gcdCert, base, hc']
    · exact ⟨Frame.step hf rfl (by bir_close) (by bir_close), by bir_close, hc⟩
    · simp [gcdCert, gcdMeasure]
  · apply FunCert.next_of ⟨0x08, gcdL08⟩ mem
    · bir_close [hrip, gcdCert, base, hc']
    · refine ⟨Frame.step hf rfl ?_ ?_, ?_, ?_⟩ <;> bir_close [r32, gcdInv, hc']
    · simp [gcdCert, gcdMeasure]

theorem gcd_b08 : gcdCert.BlockVC gcdQ ⟨0x08, gcdL08⟩ := by
  intro m0 m ⟨hf, h1, h2⟩ hrip _
  rw [runL_eq_runB gcd_lifts08]
  bir_simp [gcdI08]
  apply FunCert.next_of ⟨0x10, gcdL10⟩ mem
  · bir_close [hrip, gcdCert, base]
  · simp [r32, gcdInv] at h1 h2
    refine ⟨Frame.step hf rfl ?_ ?_, ?_, ?_⟩ <;> bir_close [r32, gcdInv, h1, h2]
  · have := (r32 .rdx m).isLt
    simp only [gcdCert, gcdMeasure, r32] at this ⊢
    bir_close
    omega

theorem gcd_b10 : gcdCert.BlockVC gcdQ ⟨0x10, gcdL10⟩ := by
  intro m0 m ⟨hf, h1, h2⟩ hrip _
  rw [runL_eq_runB gcd_lifts10]
  bir_simp [gcdI10]
  simp [r32, gcdInv] at h1 h2
  apply FunCert.next_of ⟨0x14, gcdL14⟩ mem
  · bir_close [hrip, gcdCert, base]
  · refine ⟨Frame.step hf rfl ?_ ?_, ?_, ?_, ?_⟩ <;> bir_close [r32, gcdInv, h1, h2]
  · simp only [gcdCert, gcdMeasure, r32]
    bir_close

theorem gcd_b14 : gcdCert.BlockVC gcdQ ⟨0x14, gcdL14⟩ := by
  intro m0 m ⟨hf, h1, h2, h3⟩ hrip _
  simp [r32, gcdInv] at h1 h2 h3
  simp [runL, gcdL14, Silmaril.X86.Bir9.execBlock, Silmaril.X86.Bir9.LInstr.exec,
    Silmaril.X86.Bir9.liftR, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM,
    Silmaril.X86.Ext.divide, Silmaril.X86.Ext.Sz.read, xs, ofX, h2, h3]
  have hB : (m.core.read .rcx).toNat % 4294967296 ≠ 0 := by
    intro h; apply h2; apply BitVec.eq_of_toNat_eq; simpa using h
  have hq : ¬ 4294967296 ≤ (m.core.read .rax).toNat % 4294967296 /
      ((m.core.read .rcx).toNat % 4294967296) := by
    have := Nat.div_le_self ((m.core.read .rax).toNat % 4294967296)
      ((m.core.read .rcx).toNat % 4294967296)
    omega
  simp only [hB, hq, ite_false, Silmaril.X86.Ext.retire, Option.some.injEq, exists_eq_left']
  have hrd : ∀ (W : State) a f q,
      ({ regs := W.regs, rip := a, flags := f, fsBase := W.fsBase } : State).read q = W.read q :=
    fun _ _ _ _ => rfl
  apply FunCert.next_of ⟨0x16, gcdL16⟩ mem
  · bir_close [hrip, gcdCert, base]
  · refine ⟨Frame.step hf rfl ?_ ?_, ?_, ?_⟩ <;>
      simp [hrd, Silmaril.X86.State.read_write, Silmaril.X86.Ext.Sz.write, r32, gcdInv,
        Silmaril.X86.sysv64_calleeSaved]
    all_goals
      have hlt := Nat.mod_lt ((m.core.read .rax).toNat % 4294967296) (Nat.pos_of_ne_zero hB)
      rw [Nat.mod_eq_of_lt (by omega : (m.core.read .rax).toNat % 4294967296 %
        ((m.core.read .rcx).toNat % 4294967296) < 4294967296)]
    · rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]; exact h1
    · exact hlt
  · simp [gcdCert, gcdMeasure, hrd, Silmaril.X86.State.read_write, Silmaril.X86.Ext.Sz.write, r32]

theorem gcd_b16 : gcdCert.BlockVC gcdQ ⟨0x16, gcdL16⟩ := by
  intro m0 m ⟨hf, h1, h2⟩ hrip _
  rw [runL_eq_runB gcd_lifts16]
  bir_simp [gcdI16]
  simp [r32, gcdInv] at h1 h2
  by_cases hc : r32 .rdx m = 0 <;> have hc' := hc <;> simp [r32] at hc'
  · apply FunCert.next_of ⟨0x1c, gcdL1c⟩ mem
    · bir_close [hrip, gcdCert, base, hc']
    · have h0 : (m.core.read .rdx).toNat % 4294967296 = 0 := by
        simpa using congrArg BitVec.toNat hc'
      rw [h0, Nat.gcd_zero_right] at h1
      refine ⟨Frame.step hf rfl ?_ ?_, ?_⟩ <;> bir_close [r32, gcdInv, hc', h1]
    · simp [gcdCert, gcdMeasure]
  · apply FunCert.next_of ⟨0x10, gcdL10⟩ mem
    · bir_close [hrip, gcdCert, base, hc']
    · refine ⟨Frame.step hf rfl ?_ ?_, ?_, ?_⟩ <;> bir_close [r32, gcdInv, hc', h1]
    · simp [gcdCert, gcdMeasure, r32]
      bir_close
      omega

theorem gcd_b1c : gcdCert.BlockVC gcdQ ⟨0x1c, gcdL1c⟩ := by
  intro m0 m ⟨hf, h1⟩ _ _
  rw [runL_eq_runB gcd_lifts1c]
  bir_simp [gcdI1c, hf.pop]
  simp [r32, gcdInv] at h1
  refine .inl (Silmaril.X86.BlockCert.Frame.result_open hf ?_ ?_ ?_ rfl ?_) <;> bir_close [gcdSpec', leafSpec, gcdSpec, r32, ← h1]
  apply congrArg (BitVec.setWidth 64)
  apply BitVec.eq_of_toNat_eq
  simp

theorem gcd_b20 : gcdCert.BlockVC gcdQ ⟨0x20, gcdL20⟩ := by
  intro m0 m ⟨hf, hdi, h1⟩ _ _
  rw [runL_eq_runB gcd_lifts20]
  bir_simp [gcdI20, hf.pop]
  have h0 : (m0.core.read .rsi).toNat % 4294967296 = 0 := by
    simpa [r32] using congrArg BitVec.toNat h1
  refine .inl (Silmaril.X86.BlockCert.Frame.result_open hf ?_ ?_ ?_ rfl ?_) <;> bir_close [gcdSpec', leafSpec, gcdSpec, r32, hdi, h0]
  apply congrArg (BitVec.setWidth 64)
  apply BitVec.eq_of_toNat_eq
  simp

theorem gcd_vc : gcdCert.VC gcdQ := FunCert.vc_of_blocks (by
  simp only [gcdCert, List.mem_cons, List.not_mem_nil, or_false]
  rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [gcd_b00, gcd_b08, gcd_b10, gcd_b14, gcd_b16, gcd_b1c, gcd_b20])

theorem gcd_total : gcdSpec'.Total Open.isa :=
  FunCert.total gcdSpec' (entry := ⟨0x00, gcdL00⟩) (by simp [gcdCert]) gcd_checked gcd_vc
    fun _ hab he => ⟨he.1, he.2, rfl, hab⟩

end Silmaril.Proofs.X86.Ladder.LeafArith
