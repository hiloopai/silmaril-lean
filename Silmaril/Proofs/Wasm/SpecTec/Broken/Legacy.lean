module

public import Silmaril.Proofs.Wasm.SpecTec.Broken.Fuel
public import Silmaril.Wasm.SpecTec.Scripts.Thms

/-!
# wasm-1.0 and wasm-2.0: #684, #685 and #673 on the generated scripts

Kernel evaluations at fuel 100, lifted to every fuel by `Fuel.lean`.  The `$utf8` statements
are about one clause's premises under an explicit assignment of its variables (the clauses bind
their bytes only through `if` premises, which the evaluator reads as side conditions, so a call
`$utf8(ch)` has no value in either script; the clause-level reading is the one the specification
intends).
-/

public section

namespace Silmaril.Wasm.SpecTec.Broken

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000

/-! ## #684: the four-byte clause stops at U+11000 -/

theorem utf8RejectsGrin10_original : Utf8RejectsGrin10 Wasm10.original :=
  premsFail_of_undef (N := 100) (by rfl) (by with_unfolding_all rfl)

theorem utf8AcceptsGrin10_fixed :
    PremsHold Wasm10.fixed (clausePrems Wasm10.fixed "utf8" 3) grinScope :=
  ⟨_, by rfl, 100, _, by with_unfolding_all rfl⟩

theorem not_utf8RejectsGrin10_fixed : ¬ Utf8RejectsGrin10 Wasm10.fixed :=
  not_premsFail_of_premsHold utf8AcceptsGrin10_fixed

/-! ## #685: no upper bound on continuation bytes -/

theorem utf8AcceptsC2C0_original : Utf8AcceptsC2C0 Wasm10.original :=
  ⟨_, by rfl, 100, _, by with_unfolding_all rfl⟩

/-- The same clause also accepts the correct spelling `C3 80` of U+00C0, so in the original
`$utf8` relates U+00C0 to two byte strings. -/
theorem utf8AcceptsC380_original :
    PremsHold Wasm10.original (clausePrems Wasm10.original "utf8" 1)
      (scopeOf [("b_2", 0x80), ("b_1", 0xC3), ("ch", 0xC0)]) :=
  ⟨_, by rfl, 100, _, by with_unfolding_all rfl⟩

theorem utf8RejectsC2C0_fixed :
    PremsFail Wasm10.fixed (clausePrems Wasm10.fixed "utf8" 1) c2c0Scope :=
  premsFail_of_undef (N := 100) (by rfl) (by with_unfolding_all rfl)

theorem not_utf8AcceptsC2C0_fixed : ¬ Utf8AcceptsC2C0 Wasm10.fixed :=
  fun h => not_premsFail_of_premsHold h utf8RejectsC2C0_fixed

/-! ## #673 (wasm-2.0): `$dataidx_instrs` misses a nested `memory.init` -/

theorem dataidxMissesNested_original : DataidxMissesNested Wasm20.original :=
  ⟨100, by with_unfolding_all rfl⟩

theorem dataidxNested_fixed :
    CallIs Wasm20.fixed "dataidx_instrs" [.expA IL.Wasm20.nestedMemoryInit]
      (.list [IL.Wasm20.idxZeroV]) :=
  ⟨100, by with_unfolding_all rfl⟩

theorem not_dataidxMissesNested_fixed : ¬ DataidxMissesNested Wasm20.fixed := by
  intro h
  cases callIs_unique h dataidxNested_fixed

end Silmaril.Wasm.SpecTec.Broken
