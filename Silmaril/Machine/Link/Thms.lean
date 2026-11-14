module

public import Silmaril.Machine.Link.Defs
public import Silmaril.Proofs.Machine.Link.Patch

/-! # Static ELF section linking: theorems (header)

From the imported source: `Silmaril.Formats.ELF.Link.applyPatch_size`.
New (`Silmaril.Proofs.Machine.Link.Patch`, PROVED, standard axioms):
`applyPatch_get`, `foldl_patches_get`, `foldl_patches_get_mem`,
`foldl_patches_size`, `linkSection_some`, `link_some`, `addressAt_of_mem`,
`resolveRelocations_mem`. The x86-64 relocation profile and the call-decode
lemma are in `Silmaril.Machine.X86.Reloc.Thms`; ABI-tagged linking is in
`Silmaril.Machine.Link.Abi.Thms`.
-/
