module

public import Silmaril.Raw.Machine.Link.ELF

/-! # Static ELF section linking (header)

Re-exports the architecture-independent static linker imported unchanged from
`an earlier development` `Silmaril/Formats/ELF/Link.lean`
(`Silmaril.Raw.Machine.Link.ELF`, namespace `Silmaril.Formats.ELF.Link`): explicit
`Layout`, strong/local/absolute `resolveSymbol`, `resolveRelocations`, the
`Relocator` callback, `applyPatch`, `linkSection` and `link`. Relocatable objects
come from the public certified reader `Silmaril.Formats.ELF.Object`
(`readObject`). The output is a list of placed sections, not an ELF writer.

Profile (explicit rejections, never silent acceptance): no archives, weak,
COMMON, COMDAT, TLS, interposition or dynamic linking; every nonempty allocated
section must be placed exactly once, aligned and pairwise disjoint.

New definitions here are only vocabulary for the theorems in
`Silmaril.Machine.Link.Thms`.
-/

@[expose] public section

namespace Silmaril.Machine.Link

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Link

/-- Section offset `i` is overwritten by `patch`. -/
def Covers (patch : Patch) (i : Nat) : Prop :=
  patch.offset ≤ i ∧ i < patch.offset + patch.bytes.size

instance (patch : Patch) (i : Nat) : Decidable (Covers patch i) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Silmaril.Machine.Link
