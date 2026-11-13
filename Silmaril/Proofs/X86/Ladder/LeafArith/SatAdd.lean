module

public import Silmaril.X86.Ladder.LeafArith.Defs
import Silmaril.X86.BlockCert.Thms
public import Silmaril.X86.Open.Thms
/-!
# `sat_add_u32` (gcc -O2): five Bir blocks, two paths

gcc keeps the carry of `add %esi,%edi` in `edx` (`0x401416` sets it, then jumps back to
`0x401406`) and tests it there. Each block VC is `bir_simp` plus a case split on the carry
(`addCarryN_eq_ult`: the carry is the C test `a + b < a`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.LeafArith

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Bir9 (Block LInstr)
open Silmaril.X86 Silmaril.X86.BlockCert Silmaril.X86.Ladder.LeafArith
open Silmaril.X86.Ladder.LeafArith.Bir.sat_add_u32

set_option linter.unusedSimpArgs false

abbrev satQ : MState → MState → Prop := fun m0 t => satSpec.Result Open.isa m0 t

private theorem mem {o : Nat} {L : List (LInstr × Nat)}
    (h : (⟨o, L⟩ : Blk) ∈ satCert.blocks := by simp [satCert]) : (⟨o, L⟩ : Blk) ∈ satCert.blocks :=
  h

theorem sat_checked : satCert.checked = true := by decide +kernel

theorem sat_b90 : satCert.BlockVC satQ ⟨0x90, L_401400⟩ := by
  intro m0 m ⟨hm, hab⟩ hrip _
  subst hm
  rw [runL_eq_runB lifts_401400]
  bir_simp [I_401400]
  have hf := Frame.entry hab
  cases hc : (r32 .rdi m + r32 .rsi m).ult (r32 .rdi m) <;> simp only [r32] at hc
  · apply FunCert.next_of ⟨0x96, L_401406⟩ mem
    · bir_close [hrip, satCert, base, hc]
    · refine ⟨Frame.step hf rfl ?_ ?_, ?_, ?_⟩ <;> bir_close [r32, satOvf, hc]
    · simp [satCert]
  · apply FunCert.next_of ⟨0xa6, L_401416⟩ mem
    · bir_close [hrip, satCert, base, hc]
    · refine ⟨Frame.step hf rfl ?_ ?_, ?_, ?_⟩ <;> bir_close [r32, satOvf, hc]
    · simp [satCert]

theorem sat_ba6 : satCert.BlockVC satQ ⟨0xa6, L_401416⟩ := by
  intro m0 m ⟨hf, h1, h2⟩ hrip _
  rw [runL_eq_runB lifts_401416]
  bir_simp [I_401416]
  apply FunCert.next_of ⟨0x96, L_401406⟩ mem
  · bir_close [hrip, satCert, base]
  · simp only [r32] at h1
    refine ⟨Frame.step hf rfl ?_ ?_, ?_, ?_⟩ <;> bir_close [r32, h1, h2]
  · simp [satCert]

theorem sat_b96 : satCert.BlockVC satQ ⟨0x96, L_401406⟩ := by
  intro m0 m ⟨hf, h1, h2⟩ hrip _
  rw [runL_eq_runB lifts_401406]
  bir_simp [I_401406]
  cases hc : satOvf m0
  · apply FunCert.next_of ⟨0x9c, L_40140c⟩ mem
    · bir_close [hrip, satCert, base, h2, hc]
    · simp only [r32] at h1
      refine ⟨Frame.step hf rfl ?_ ?_, ?_, ?_⟩ <;> bir_close [r32, h1, h2, hc]
    · simp [satCert]
  · apply FunCert.next_of ⟨0xa0, L_401410⟩ mem
    · bir_close [hrip, satCert, base, h2, hc]
    · exact ⟨Frame.step hf rfl (by bir_close) (by bir_close), hc⟩
    · simp [satCert]

theorem sat_b9c : satCert.BlockVC satQ ⟨0x9c, L_40140c⟩ := by
  intro m0 m ⟨hf, h1, h2⟩ _ _
  rw [runL_eq_runB lifts_40140c]
  bir_simp [I_40140c, hf.pop]
  simp only [satOvf] at h2
  refine .inl (Silmaril.X86.BlockCert.Frame.result_open hf ?_ ?_ ?_ rfl ?_) <;> bir_close [satSpec, leafSpec, h1, satAddSpec, h2]

theorem sat_ba0 : satCert.BlockVC satQ ⟨0xa0, L_401410⟩ := by
  intro m0 m ⟨hf, h1⟩ _ _
  rw [runL_eq_runB lifts_401410]
  bir_simp [I_401410, hf.pop]
  simp only [satOvf] at h1
  refine .inl (Silmaril.X86.BlockCert.Frame.result_open hf ?_ ?_ ?_ rfl ?_) <;> bir_close [satSpec, leafSpec, satAddSpec, h1]

theorem sat_vc : satCert.VC satQ := FunCert.vc_of_blocks (by
  simp only [satCert, List.mem_cons, List.not_mem_nil, or_false]
  rintro b (rfl | rfl | rfl | rfl | rfl)
  exacts [sat_b90, sat_ba6, sat_b96, sat_b9c, sat_ba0])

theorem sat_total : satSpec.Total Open.isa :=
  FunCert.total satSpec (entry := ⟨0x90, L_401400⟩) (by simp [satCert]) sat_checked sat_vc
    fun _ hab he => ⟨he.1, he.2, rfl, hab⟩

end Silmaril.Proofs.X86.Ladder.LeafArith
