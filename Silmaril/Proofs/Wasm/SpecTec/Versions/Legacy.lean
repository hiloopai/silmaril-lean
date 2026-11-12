module

public import Silmaril.Wasm.SpecTec.Versions.Defs
public import Silmaril.Wasm.SpecTec.Broken.Thms

/-!
# wasm-1.0, wasm-2.0 and the wasm-3.0 text escape on the main scripts

Kernel evaluations at fuel 100 (`with_unfolding_all rfl`), lifted to every fuel by
`Broken/Fuel.lean`.  As in `Broken/Legacy.lean`, the `$utf8` statements are about one clause's
premises under an explicit assignment of its variables.

wasm-2.0 had both UTF-8 defects of wasm-1.0 at the pin (`wasm-2.0/A-binary.spectec:55-57`), but
no erratum file covers them (`Errata/Wasm20.lean` patches #670–#673 only); they are proved here for
the pinned and the main wasm-2.0 scripts.
-/

public section

namespace Silmaril.Wasm.SpecTec.Versions

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Broken
open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000

/-! ## wasm-1.0 -/

/-- #684 is fixed upstream: the main four-byte clause accepts U+1F601. -/
theorem utf8AcceptsGrin10_main :
    Utf8ClauseAcceptsGrin Main.Wasm10.original "utf8" 3 :=
  ⟨_, by rfl, 100, _, by with_unfolding_all rfl⟩

theorem not_utf8RejectsGrin10_main : ¬ Utf8RejectsGrin10 Main.Wasm10.original :=
  not_premsFail_of_premsHold utf8AcceptsGrin10_main

/-- **#685 is still there**: the main two-byte clause accepts `C2 C0` for U+00C0. -/
theorem utf8AcceptsC2C0_main : Utf8AcceptsC2C0 Main.Wasm10.original :=
  ⟨_, by rfl, 100, _, by with_unfolding_all rfl⟩

/-! ## wasm-2.0 -/

/-- The pinned wasm-2.0 four-byte clause rejects U+1F601 (the 2.0 spelling of #684; no erratum). -/
theorem utf8RejectsGrin20_original : Utf8ClauseRejectsGrin Wasm20.original "utf8" 3 :=
  premsFail_of_undef (N := 100) (by rfl) (by with_unfolding_all rfl)

/-- …and the main one accepts it: fixed upstream. -/
theorem utf8AcceptsGrin20_main : Utf8ClauseAcceptsGrin Main.Wasm20.original "utf8" 3 :=
  ⟨_, by rfl, 100, _, by with_unfolding_all rfl⟩

/-- The pinned wasm-2.0 two-byte clause accepts `C2 C0` (the 2.0 spelling of #685; no erratum). -/
theorem utf8AcceptsC2C0_20_original : Utf8ClauseAcceptsC2C0 Wasm20.original "utf8" 1 :=
  ⟨_, by rfl, 100, _, by with_unfolding_all rfl⟩

/-- **…and so does the main one: still there.** -/
theorem utf8AcceptsC2C0_20_main : Utf8ClauseAcceptsC2C0 Main.Wasm20.original "utf8" 1 :=
  ⟨_, by rfl, 100, _, by with_unfolding_all rfl⟩

/-- **#673 is still there**: `$dataidx_instrs` of `(block (memory.init 0))` is empty on main. -/
theorem dataidxMissesNested_main : DataidxMissesNested Main.Wasm20.original :=
  ⟨100, by with_unfolding_all rfl⟩

/-! ## wasm-3.0 text -/

/-- #661 is fixed upstream: the `\u{n}` guard holds at `n = 0xE000`. -/
theorem escapeAcceptsE000_main :
    PremsHold Main.Wasm30.original (prodPrems Main.Wasm30.original "Tstringchar" 7)
      escapeE000Scope :=
  ⟨_, by rfl, 100, _, by with_unfolding_all rfl⟩

theorem not_escapeRejectsE000_main : ¬ EscapeRejectsE000 Main.Wasm30.original :=
  not_premsFail_of_premsHold escapeAcceptsE000_main

end Silmaril.Wasm.SpecTec.Versions
