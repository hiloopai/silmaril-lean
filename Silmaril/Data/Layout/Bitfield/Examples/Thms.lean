module

public import Silmaril.Data.Layout.Bitfield.Examples.Defs

/-! # Bit-field layouts against real compilers: the checks

PROVED (`decide +kernel`, standard axioms):

* `cases_agree`: **on all 25 cases of `examples/layout/cases.h`** (structs and unions with
  bit-fields of every integer width, `_Bool` and enum bit-fields, zero-width and unnamed bit-fields,
  straddling, `_Alignas`, `long`, `long double`, pointers and arrays), `bitLayout` agrees with gcc
  13.3's x86-64 System V layout (`sysv`, `sysvX86_64`) and with clang 18.1's MSVC record layout
  (`ms`, `msX64`; clang's emulation of MSVC, not `cl.exe`) on every size, alignment, member bit
  offset and width they report. This is agreement on these 25 measured cases, not a proof that
  either policy is the ABI for every aggregate;
* named examples of `sizeof`, `_Alignof`, C's `offsetof` (which refuses every bit-field, also a
  whole byte at offset 0: `byteBitfield_offsetof`), physical placement (`bitOffsetOf`) and padding
  bits and bytes, and where the two policies differ.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Examples

open Silmaril.Data.Layout

/-- **Every measured case agrees with gcc and with clang's MSVC emulation.** -/
theorem cases_agree :
    cases.all (fun (d, g, m) => agrees g (bitLayout .sysv sysvX86_64 [] d) &&
      agrees m (bitLayout .ms msX64 [] d)) = true := by decide +kernel

/-- `struct { char a : 4; int b : 4; }`: 4 bytes under System V (both in one `int` unit), 8 under
Microsoft x64 (a `char` unit, then an `int` unit). -/
theorem c03_sizes :
    (bitShapeOf .sysv sysvX86_64 [c03] .struct "c03").toOption = some ⟨4, 4⟩ ∧
    (bitShapeOf .ms msX64 [c03] .struct "c03").toOption = some ⟨8, 4⟩ := by decide +kernel

/-- `struct { long a; int b : 5; }`: `long` is 8 bytes under LP64 (16 in all), 4 under LLP64
(8 in all). -/
theorem c16_sizes :
    (bitShapeOf .sysv sysvX86_64 [c16] .struct "c16").toOption = some ⟨16, 8⟩ ∧
    (bitShapeOf .ms msX64 [c16] .struct "c16").toOption = some ⟨8, 4⟩ := by decide +kernel

/-- `offsetof(struct c13, c)` (after `int a; char b : 2;`) is 5 under both ABIs. -/
theorem c13_offsetof :
    (offsetOf .sysv sysvX86_64 [c13] .struct "c13" "c").toOption = some 5 ∧
    (offsetOf .ms msX64 [c13] .struct "c13" "c").toOption = some 5 := by decide +kernel

/-- **C's `offsetof` refuses every bit-field**, wherever it lies: `c02.b` starts on a byte
boundary (bit 8) and is still refused; its physical placement is `bitOffsetOf`. -/
theorem c02_offsetof_bitfield :
    (offsetOf .sysv sysvX86_64 [c02] .struct "c02" "b").toOption = none ∧
    (bitOffsetOf .sysv sysvX86_64 [c02] .struct "c02" "b").toOption = some (8, 4) ∧
    (offsetOf .sysv sysvX86_64 [c03] .struct "c03" "b").toOption = none := by decide +kernel

/-- `struct t { unsigned x : 8; }`: the bit-field is a whole byte at offset 0, and `offsetof` still
refuses it under both ABIs; `bitOffsetOf` gives bit 0, width 8. -/
theorem byteBitfield_offsetof :
    let t : Decl := ⟨.struct, "t", [{ name := "x", ty := .int .int .unsigned, bits := some 8 }]⟩
    (offsetOf .sysv sysvX86_64 [t] .struct "t" "x").toOption = none ∧
    (offsetOf .ms msX64 [t] .struct "t" "x").toOption = none ∧
    (bitOffsetOf .sysv sysvX86_64 [t] .struct "t" "x").toOption = some (0, 8) ∧
    (bitOffsetOf .ms msX64 [t] .struct "t" "x").toOption = some (0, 8) := by decide +kernel

/-- `struct { char a; long long : 3; }`: the unnamed `long long` bit-field is not a member and adds
no alignment under System V: 2 bytes, of which the second is padding (its 3 bits belong to the
unnamed bit-field), so 8 padding bits and 1 padding byte. Under Microsoft x64 it opens an aligned
`long long` unit: 16 bytes, 15 of them padding. -/
theorem c05_padding :
    (bitLayout .sysv sysvX86_64 [] c05).toOption.map (fun (ss, sh) => (sh, paddingBits ss sh, paddingBytes ss sh)) =
      some (⟨2, 1⟩, 8, 1) ∧
    (bitLayout .ms msX64 [] c05).toOption.map (fun (ss, sh) => (sh, paddingBits ss sh, paddingBytes ss sh)) =
      some (⟨16, 8⟩, 120, 15) := by decide +kernel

end Silmaril.Data.Layout.Examples
