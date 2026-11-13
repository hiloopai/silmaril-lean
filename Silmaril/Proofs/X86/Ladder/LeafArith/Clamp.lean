module

public import Silmaril.X86.Ladder.LeafArith.Defs
import Silmaril.X86.BlockCert.Thms
public import Silmaril.X86.Open.Thms
/-!
# `clamp_i32` (gcc -O2): three Bir blocks, one CMOV

`cmp %esi,%edi; jl` to `mov %esi,%eax; ret`, else `cmp %edx,%edi; mov %edx,%eax;
cmovle %edi,%eax; ret`. The listings are written by hand from `Transcript.listing`, with the
CMOV as the Bir extension form `LInstr.x (.cmov …)` (which `BlockCert.toExt` checks against
the `Ext` decoding of the bytes); `liftBlock` is checked by `decide +kernel`. The flags after
`cmp` are signed compares (`eval_l_sub`, `eval_le_sub`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Ladder.LeafArith

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Bir9 (Block LInstr liftBlock)
open Silmaril.X86 Silmaril.X86.BlockCert Silmaril.X86.Ladder.LeafArith

set_option linter.unusedSimpArgs false

abbrev clampQ : MState → MState → Prop := fun m0 t => clampSpec'.Result Open.isa m0 t

private theorem mem {o : Nat} {L : List (LInstr × Nat)}
    (h : (⟨o, L⟩ : Blk) ∈ clampCert.blocks := by simp [clampCert]) :
    (⟨o, L⟩ : Blk) ∈ clampCert.blocks :=
  h

theorem clamp_lifts30 : liftBlock clampL30 = some clampI30 := by decide +kernel
theorem clamp_lifts34 : liftBlock clampL34 = some clampI34 := by decide +kernel
theorem clamp_lifts40 : liftBlock clampL40 = some clampI40 := by decide +kernel

theorem clamp_checked : clampCert.checked = true := by decide +kernel

theorem clamp_b30 : clampCert.BlockVC clampQ ⟨0x30, clampL30⟩ := by
  intro m0 m ⟨hm, hab⟩ hrip _
  subst hm
  rw [runL_eq_runB clamp_lifts30]
  bir_simp [clampI30]
  have hf := Frame.entry hab
  cases hc : (r32 .rdi m).slt (r32 .rsi m) <;> simp only [r32] at hc
  · apply FunCert.next_of ⟨0x34, clampL34⟩ mem
    · bir_close [hrip, clampCert, base, hc]
    · refine ⟨Frame.step hf rfl ?_ ?_, ?_, ?_, ?_⟩ <;> bir_close [r32, hc]
    · simp [clampCert]
  · apply FunCert.next_of ⟨0x40, clampL40⟩ mem
    · bir_close [hrip, clampCert, base, hc]
    · refine ⟨Frame.step hf rfl ?_ ?_, ?_, ?_⟩ <;> bir_close [r32, hc]
    · simp [clampCert]

theorem clamp_b34 : clampCert.BlockVC clampQ ⟨0x34, clampL34⟩ := by
  intro m0 m ⟨hf, h1, h2, h3⟩ _ _
  rw [runL_eq_runB clamp_lifts34]
  bir_simp [clampI34, hf.pop]
  simp only [r32] at h3
  refine .inl (Silmaril.X86.BlockCert.Frame.result_open hf ?_ ?_ ?_ rfl ?_) <;>
    bir_close [clampSpec', leafSpec, clampSpec, r32, h1, h2, h3]
  rw [BitVec.sle_eq_not_slt]
  by_cases h : (r32 .rdx m0).slt (r32 .rdi m0) = true <;> simp_all [r32]

theorem clamp_b40 : clampCert.BlockVC clampQ ⟨0x40, clampL40⟩ := by
  intro m0 m ⟨hf, h1, h2⟩ _ _
  rw [runL_eq_runB clamp_lifts40]
  bir_simp [clampI40, hf.pop]
  simp only [r32] at h2
  refine .inl (Silmaril.X86.BlockCert.Frame.result_open hf ?_ ?_ ?_ rfl ?_) <;>
    bir_close [clampSpec', leafSpec, clampSpec, r32, h1, h2]

theorem clamp_vc : clampCert.VC clampQ := FunCert.vc_of_blocks (by
  simp only [clampCert, List.mem_cons, List.not_mem_nil, or_false]
  rintro b (rfl | rfl | rfl)
  exacts [clamp_b30, clamp_b34, clamp_b40])

theorem clamp_total : clampSpec'.Total Open.isa :=
  FunCert.total clampSpec' (entry := ⟨0x30, clampL30⟩) (by simp [clampCert]) clamp_checked
    clamp_vc fun _ hab he => ⟨he.1, he.2, rfl, hab⟩

end Silmaril.Proofs.X86.Ladder.LeafArith
