module

public import Silmaril.X86.Linking.Defs
public import Silmaril.Formats.ELF.Link.Thms
import Silmaril.Proofs.X86.Linking

/-! # x86-64 static relocation: theorems

* `linkBytes_of_parse`: byte inputs that parse to an AST link as that AST;
* `encodeLE_length`, `decodeLE_encodeLE`, `encoded_size`, `decodeLE_encoded`: the emitted
  little-endian field has exactly its width and decodes to the two's-complement residue;
* `unsupported`: an unsupported kind never acquires bytes;
* `patch_spec`, `patch_decoded`, `relocate_success`: a successful patch has the prescribed
  offset, width, encoding, kind and range, and stays inside its section; the `Option`
  callback of the shared linker cannot hide a diagnostic failure;
* range and error vectors for `patch` (by `rfl`);
* `Checks`: non-vacuity (`succeeds`) and eleven rejections (`unresolved`,
  `duplicate_definition`, `overlapping_layout`, `incomplete_layout`, `misaligned_layout`,
  `overlapping_patches`, `unused_weak`, `unused_common`, `unused_ifunc`, `unused_tls`,
  `unused_group`), all by `rfl` on small ASTs.
-/

@[expose] public section

namespace Silmaril.X86.Linking.Relocation

open Formats.ELF Formats.ELF.Link

/-- Byte/AST parser certificates compose with linking without trusting the
external AST producer. A lossless concrete AST uses its serialized bytes here. -/
theorem linkBytes_of_parse {raw : List Bytes} {objects : List ObjectFile}
    (parsed : raw.mapM readObject = some objects) (layout : Layout)
    (absolute : AbsoluteSymbols) : linkBytes raw layout absolute = link objects layout absolute := by
  simp [linkBytes, parsed]

@[simp] theorem encodeLE_length (n v : Nat) : (encodeLE n v).length = n :=
  Proofs.X86.Linking.encodeLE_length n v

/-- Byte encoding is exact for every in-range unsigned value, not just fixtures. -/
theorem decodeLE_encodeLE (n v : Nat) (fits : v < 256 ^ n) :
    decodeLE (encodeLE n v) = v :=
  Proofs.X86.Linking.decodeLE_encodeLE n v fits

/-- Every emitted field has exactly its specified width. -/
@[simp] theorem encoded_size (kind : Nat) (v : Int) :
    (encoded kind v).size = width kind := by simp [encoded]

/-- The actual emitted bytes decode to the specified two's-complement residue. -/
theorem decodeLE_encoded (kind : Nat) (v : Int) :
    decodeLE (encoded kind v).toList = (v % (256 ^ width kind)).toNat :=
  Proofs.X86.Linking.decodeLE_encoded kind v

/-- Unsupported relocation kinds cannot silently acquire bytes. -/
theorem unsupported (all : List ResolvedRelocation) (r : ResolvedRelocation)
    (bytes : Bytes) (h : ¬ supported r.kind) : relocate all r bytes = none := by
  simp [relocate, patch, h, Except.toOption]

/-- Successful patches have the prescribed offset, width, exact arithmetic
encoding, supported kind and signedness range, and stay within their section. -/
theorem patch_spec {r : ResolvedRelocation} {bytes : Bytes} {p : Patch}
    (success : patch r bytes = .ok p) :
    supported r.kind ∧ Fits r.kind (value r) ∧
      p.offset = r.offset ∧ p.bytes = encoded r.kind (value r) ∧
      p.bytes.size = width r.kind ∧ p.offset + p.bytes.size ≤ bytes.size :=
  Proofs.X86.Linking.patch_spec success

theorem patch_decoded {r : ResolvedRelocation} {bytes : Bytes} {p : Patch}
    (success : patch r bytes = .ok p) :
    decodeLE p.bytes.toList = (value r % (256 ^ width r.kind)).toNat := by
  rw [(patch_spec success).2.2.2.1]
  exact decodeLE_encoded r.kind (value r)

/-- The shared linker's Option callback cannot hide a diagnostic failure. -/
theorem relocate_success {all : List ResolvedRelocation} {r : ResolvedRelocation}
    {bytes : Bytes} {p : Patch} (success : relocate all r bytes = some p) :
    patch r bytes = .ok p :=
  Proofs.X86.Linking.relocate_success success

/-- Range boundaries and error classifications are exercised independently of ELF parsing. -/
example : patch ⟨⟨0, 1⟩, 0, 0x1000, 0x1100, 4, -4⟩ #[0, 0, 0, 0] =
    .ok ⟨0, #[0xfc, 0, 0, 0]⟩ := by rfl
example : patch ⟨⟨0, 1⟩, 0, 0, 0x80000000, 2, 0⟩ #[0, 0, 0, 0] =
    .error (.overflow 2 0x80000000) := by rfl
example : patch ⟨⟨0, 1⟩, 0, 0x80000000, 0, 2, 0⟩ #[0, 0, 0, 0] =
    .ok ⟨0, #[0, 0, 0, 0x80]⟩ := by rfl
example : patch ⟨⟨0, 1⟩, 0, 0, 0, 11, -1⟩ #[0, 0, 0, 0] =
    .ok ⟨0, #[0xff, 0xff, 0xff, 0xff]⟩ := by rfl
example : patch ⟨⟨0, 1⟩, 0, 0, 0, 10, -1⟩ #[0, 0, 0, 0] =
    .error (.overflow 10 (-1)) := by rfl
example : patch ⟨⟨0, 1⟩, 0, 0, 0, 1, -1⟩ #[0, 0, 0, 0, 0, 0, 0, 0] =
    .error (.overflow 1 (-1)) := by rfl
example : patch ⟨⟨0, 1⟩, 1, 0, 0, 1, 0⟩ #[0, 0, 0, 0] =
    .error (.outOfBounds 1 8 4) := by rfl
example : patch ⟨⟨0, 1⟩, 0, 0, 0, 9, 0⟩ #[] =
    .error (.unsupportedKind 9) := by rfl

end Silmaril.X86.Linking.Relocation

namespace Silmaril.X86.Linking.Checks

open Formats.ELF Formats.ELF.Link Relocation

/-- Nonvacuity: the same ASTs used in the failure checks do successfully link. -/
theorem succeeds : Relocation.link [caller, callee] layout = some
    [⟨⟨0, 1⟩, 0x1000, 6, 4, #[0x20, 0, 0, 0]⟩,
     ⟨⟨1, 1⟩, 0x1020, 6, 1, #[0x90]⟩] := by rfl

theorem unresolved : Relocation.link [caller] [⟨⟨0, 1⟩, 0x1000⟩] = none := by rfl

/-- Complete, disjoint placement does not rescue duplicate strong definitions. -/
theorem duplicate_definition : Relocation.link [caller, callee, callee]
    (layout ++ [⟨⟨2, 1⟩, 0x1040⟩]) = none := by rfl

theorem overlapping_layout : Relocation.link [caller, callee]
    [⟨⟨0, 1⟩, 0x1000⟩, ⟨⟨1, 1⟩, 0x1002⟩] = none := by rfl

theorem incomplete_layout : Relocation.link [caller, callee]
    [⟨⟨0, 1⟩, 0x1000⟩] = none := by rfl

theorem misaligned_layout : Relocation.link [caller, callee]
    [⟨⟨0, 1⟩, 0x1001⟩, ⟨⟨1, 1⟩, 0x1020⟩] = none := by rfl

theorem overlapping_patches : Relocation.link
    [{ caller with relocations := caller.relocations ++ caller.relocations }, callee]
    layout = none := by rfl

/-- Unsupported mechanisms are rejected even if no relocation references them. -/
theorem unused_weak : Relocation.link
    [{ callee with symbols := [⟨{ defined.raw with info := 34 }, defined.name⟩] }]
    [⟨⟨0, 1⟩, 0x1000⟩] = none := by rfl

theorem unused_common : Relocation.link
    [{ callee with symbols := [⟨{ defined.raw with sectionIndex := 0xfff2 }, defined.name⟩] }]
    [⟨⟨0, 1⟩, 0x1000⟩] = none := by rfl

theorem unused_ifunc : Relocation.link
    [{ callee with symbols := [⟨{ defined.raw with info := 26 }, defined.name⟩] }]
    [⟨⟨0, 1⟩, 0x1000⟩] = none := by rfl

theorem unused_tls : Relocation.link
    [{ callee with symbols := [⟨{ defined.raw with info := 22 }, defined.name⟩] }]
    [⟨⟨0, 1⟩, 0x1000⟩] = none := by rfl

theorem unused_group : Relocation.link
    [{ callee with sections := callee.sections ++
      [⟨{ nullPart.header with kind := 17 }, [], #[]⟩] }]
    [⟨⟨0, 1⟩, 0x1000⟩] = none := by rfl

end Silmaril.X86.Linking.Checks
