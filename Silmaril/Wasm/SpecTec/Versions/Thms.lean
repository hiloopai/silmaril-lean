module

public import Silmaril.Wasm.SpecTec.Versions.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Versions.Import
public import Silmaril.Proofs.Wasm.SpecTec.Versions.Checks
public import Silmaril.Proofs.Wasm.SpecTec.Versions.Binary
public import Silmaril.Proofs.Wasm.SpecTec.Versions.Legacy
public import Silmaril.Proofs.Wasm.SpecTec.Versions.Rules
public import Silmaril.Proofs.Wasm.SpecTec.Versions.Text

/-!
# SpecTec versions: which defects of the pinned scripts are still on `WebAssembly/spec` main

The pinned scripts (`WebAssembly/spec@608711107b`) stay as they were: the example of importing a
SpecTec specification *with* defects, and of stating each defect as a predicate a later revision
can be tested against.  The main scripts (`WebAssembly/spec@e7a9df7c`) are imported here the same
way (`generated_main_wasmNN_eq`, and the build-time checks of `Versions/Checks.lean`) and tested
against the same predicates.  Every statement is a kernel theorem; the table in
`docs/projects/spectec-divergences.md` lists them.
-/

public section

namespace Silmaril.Wasm.SpecTec.Versions

open Silmaril.SpecTec
open Silmaril.Wasm.SpecTec.Broken
open Silmaril.Wasm.SpecTec.Scripts

/-- **Fixed upstream between the pin and main (wasm-3.0):** `Bi32` is no longer unsigned (#654),
`$cont(0x80)` is defined (#655), the four-byte UTF-8 clause accepts U+1F601 (#656, now in
`$utf8single`), the `\u{E000}` escape is accepted (#661), and `$sx` is defined at reference types
(sim item U5).  Each was broken at the pin. -/
theorem wasm30_fixed_on_main :
    (Bi32Unsigned Wasm30.original ∧ ¬ Bi32Unsigned Main.Wasm30.original) ∧
      (ContUndefAt80 Wasm30.original ∧ ¬ ContUndefAt80 Main.Wasm30.original) ∧
      (Utf8ClauseRejectsGrin Wasm30.original "utf8" 4 ∧
        ¬ Utf8ClauseRejectsGrin Main.Wasm30.original "utf8single" 3) ∧
      (EscapeRejectsE000 Wasm30.original ∧ ¬ EscapeRejectsE000 Main.Wasm30.original) ∧
      (SxUndefAtRef Wasm30.original ∧ ¬ SxUndefAtRef Main.Wasm30.original) :=
  ⟨⟨bi32Unsigned_original, not_bi32Unsigned_main⟩,
    ⟨contUndefAt80_original, not_contUndefAt80_main⟩,
    ⟨utf8ClauseRejectsGrin_original, not_utf8singleRejectsGrin_main⟩,
    ⟨escapeRejectsE000_original, not_escapeRejectsE000_main⟩,
    ⟨sxUndefAtRef_original, not_sxUndefAtRef_main⟩⟩

/-- **Still present on main (wasm-3.0):** `BsN(32)` derives nothing from `FF 7E` (#803, the
`int`-to-`nat` narrowing of `BsN`'s third production), so the now-signed `Bi32` cannot read
`i32.const -129`; `$s33_to_u32` has no clauses; and `Step/table.grow-succeed` never fires. -/
theorem wasm30_still_broken_on_main :
    BsNLosesFF7E Main.Wasm30.original ∧
      (∀ ρ v, ¬ Sem.gramRelSup Main.Wasm30.env ρ (.varG "Bi32" []) [0xFF, 0x7E] v) ∧
      S33ToU32Undefined Main.Wasm30.original ∧ TableGrowNeverFires Main.Wasm30.original :=
  ⟨bsnLosesFF7E_main, not_bi32_FF7E_main, s33ToU32Undefined_main, ruleDead_tableGrowSucceed_main⟩

/-- **wasm-1.0 and wasm-2.0 on main:** the four-byte bound is fixed in both (#684 and its 2.0
twin); the missing continuation-byte bound (#685 and its 2.0 twin) and `$dataidx_instrs`'s
missing descent into blocks (#673) are still there. -/
theorem legacy_on_main :
    (¬ Utf8RejectsGrin10 Main.Wasm10.original ∧
      ¬ Utf8ClauseRejectsGrin Main.Wasm20.original "utf8" 3) ∧
      (Utf8AcceptsC2C0 Main.Wasm10.original ∧
        Utf8ClauseAcceptsC2C0 Main.Wasm20.original "utf8" 1 ∧
        DataidxMissesNested Main.Wasm20.original) :=
  ⟨⟨not_utf8RejectsGrin10_main,
      not_premsFail_of_premsHold utf8AcceptsGrin20_main⟩,
    ⟨utf8AcceptsC2C0_main, utf8AcceptsC2C0_20_main, dataidxMissesNested_main⟩⟩

/-- **`$ieee_` has no clauses at the pin and on main (wasm-3.0)**, so no call of it has a value:
the decimal and hexadecimal float literals of the text format denote no float in the IL. -/
theorem wasm30_ieee_undefined :
    IeeeUndefined Wasm30.original ∧ IeeeUndefined Main.Wasm30.original ∧
      ∀ args, CallUndef Main.Wasm30.original "ieee_" args :=
  ⟨ieeeUndefined_original, ieeeUndefined_main, callUndef_of_noClauses ieeeUndefined_main⟩

end Silmaril.Wasm.SpecTec.Versions
