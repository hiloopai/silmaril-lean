module

public import Silmaril.Elf.Abi.Asm.Example.Defs
public import Silmaril.Elf.Abi.Asm.Thms
public import Silmaril.Elf.Asm.Example.Thms

/-! # The typed adapter on `crc32_z`: proof -/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.AsmExample

open Silmaril.Elf Silmaril.Elf.Abi Silmaril.Elf.Abi.AsmExample
open Silmaril.Elf.Staged.Pinned.ZlibChecksums (F L bodies ld parses)

theorem crc32z_codeOf : CodeOf F .symtab "crc32_z" crc32zCode := by
  refine codeOf_ofAsm (d := ⟨14, 4200848, 291, false, false⟩) (by decide)
    Silmaril.Elf.Asm.Example.crc32_z_bytes ⟨_, 1, parses, rfl, by decide +kernel⟩
    Silmaril.Elf.Asm.Example.crc32_z_symbol rfl ?_ ⟨_, parses, by decide +kernel⟩ rfl rfl rfl rfl
    ⟨_, parses, rfl⟩
  rintro s ⟨A, hA, hs⟩
  have : A = L.assemble bodies ld := Option.some.inj (hA.symm.trans parses)
  subst this
  have h14 : ((L.assemble bodies ld).symbols .symtab)[14]?.map (·.kind) = some 2 := by decide +kernel
  change ((L.assemble bodies ld).symbols .symtab)[14]? = some s at hs
  rw [hs] at h14
  have hk : s.kind = 2 := Option.some.inj h14
  rw [hk]; decide

end Silmaril.Proofs.Elf.Abi.AsmExample

end
