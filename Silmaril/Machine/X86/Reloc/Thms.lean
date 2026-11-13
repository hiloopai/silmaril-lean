module

public import Silmaril.Machine.X86.Reloc.Defs
public import Silmaril.Machine.Link.Thms
public import Silmaril.Proofs.Machine.X86.Reloc.CallDecode
public import Silmaril.Raw.Machine.X86.Linking.Checks
public import Silmaril.Raw.Machine.X86.Linking.Fixture

/-! # x86-64 static relocation: theorems (header)

Imported unchanged from `an earlier development` (PROVED there and
re-checked here):

* `Silmaril.X86.Linking.Relocation`: `patch_spec`, `patch_decoded`,
  `decodeLE_encodeLE`, `decodeLE_encoded`, `encoded_size`, `unsupported`,
  `relocate_success`, `linkBytes_of_parse`;
* `Silmaril.X86.Linking.Checks`: `succeeds` (non-vacuity) and the eleven
  negative cases `unresolved`, `duplicate_definition`, `overlapping_layout`,
  `incomplete_layout`, `misaligned_layout`, `overlapping_patches`,
  `unused_weak`, `unused_common`, `unused_ifunc`, `unused_tls`, `unused_group`,
  all by `rfl` on small ASTs;
* `Silmaril.X86.Linking.Fixture.linked`: two real gcc `.o` files parsed by
  `readObject` and linked by this profile give exactly the section bytes of the
  retained GNU `ld` output (`reference_bytes_*`, `reference_metadata_*`), by
  `rfl`. This is translation validation of one `ld` run, and slow (about ten
  minutes of elaboration).

New (`Silmaril.Proofs.Machine.X86.Reloc.CallDecode`, PROVED, standard axioms):
`encoded_rel32`, `call_patch_decodes`, `call_patch_target`, `plt_call_target`,
`call_patch_exec`, `linkSection_call`, `link_call`, `link_resolved`.
Non-vacuity (here): `fixture_call_decodes`, `fixture_call_target`, and
`callObj_link_call`, which discharges every hypothesis of `link_call` on a
small linked AST.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Reloc

/-- Non-vacuity on the real fixture: the linked caller section starts with
`e8 1b 00 00 00`, which decodes to `call +0x1b`. -/
theorem fixture_call_decodes :
    Silmaril.X86.Ext.decode (Silmaril.X86.Linking.Fixture.expected[0]).data.toList =
      some (.call 27#32, 5) := by
  decide +kernel

/-- That call, at 0x1000, goes to 0x1020, where the layout places the callee's
`.text` (`⟨1, 3⟩ ↦ 4128`). -/
theorem fixture_call_target :
    BitVec.ofNat 64 (4096 + 5) + (27#32).signExtend 64 = BitVec.ofNat 64 4128 := by
  decide

/-! Non-vacuity of `link_call` on a small AST: a caller whose section is
`e8 00 00 00 00` with `R_X86_64_PLT32 f-4` at offset 1, linked against the
`Checks.callee` at `0x1020`. All hypotheses of `link_call` are discharged. -/

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Link Silmaril.X86.Linking in
def callPart : ObjectSection := ⟨⟨0, 1, 6, 0, 0, 5, 0, 0, 1, 0⟩, [], #[0xE8, 0, 0, 0, 0]⟩

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Link Silmaril.X86.Linking in
def callObj : ObjectFile :=
  ⟨Checks.header, [Checks.nullPart, callPart], [Checks.nullSymbol, Checks.undefined],
    [⟨1, 1, 1, 4, -4⟩]⟩

open Silmaril.Formats.ELF.Link in
def callRel : ResolvedRelocation := ⟨⟨0, 1⟩, 1, 0x1001, 0x1020, 4, -4⟩

open Silmaril.Formats.ELF.Link Silmaril.X86.Linking in
theorem callObj_resolves :
    resolveRelocations [callObj, Checks.callee] Checks.layout [] = some [callRel] := by rfl

open Silmaril.Formats.ELF.Link Silmaril.X86.Linking in
theorem callObj_links :
    Relocation.link [callObj, Checks.callee] Checks.layout = some
      [⟨⟨0, 1⟩, 0x1000, 6, 5, #[0xE8, 0x1b, 0, 0, 0]⟩, ⟨⟨1, 1⟩, 0x1020, 6, 1, #[0x90]⟩] := by
  rfl

open Silmaril.Formats.ELF.Link Silmaril.X86.Linking in
/-- `link_call` instantiated: the linked caller decodes to `call (S + A - P)` and
its target is `S + A + 4 = 0x1020`. -/
theorem callObj_link_call :
    ∃ s ∈ [(⟨⟨0, 1⟩, 0x1000, 6, 5, #[0xE8, 0x1b, 0, 0, 0]⟩ : LinkedSection),
        ⟨⟨1, 1⟩, 0x1020, 6, 1, #[0x90]⟩], s.key = ⟨0, 1⟩ ∧ s.address = 0x1000 ∧
      Silmaril.X86.Ext.decode (s.data.toList.drop 0) =
        some (.call (BitVec.ofInt 32 (Relocation.value callRel)), 5) ∧
      BitVec.ofNat 64 (s.address + 0 + 5) +
          (BitVec.ofInt 32 (Relocation.value callRel)).signExtend 64 =
        BitVec.ofInt 64 ((callRel.symbolValue : Int) + callRel.addend + 4) :=
  link_call (placement := ⟨⟨0, 1⟩, 0x1000⟩) (part := callPart) callObj_links callObj_resolves
    (by decide) rfl (by simp) rfl (by decide) rfl rfl
    (by intro r' hr' _; simp at hr'; subst hr'; decide)

/-- The displacement in `callObj_link_call` is `0x1b` and the target `0x1020`. -/
theorem callRel_value : Silmaril.X86.Linking.Relocation.value callRel = 0x1b := by decide

end Silmaril.Machine.X86.Reloc
