module

public import Silmaril.Proofs.Wasm.SpecTec.Broken.Fuel
public import Silmaril.Wasm.SpecTec.Scripts.Thms

/-!
# wasm-3.0 text format: #661 on the generated scripts

The side condition of the `\u{n}` production of `Tstringchar` (production 7,
`6.1-text.values.spectec:98`), evaluated by the kernel at `n = 0xE000`.  This is a guard-level
statement: it says the production's premise fails, not that the whole grammar `Tstringchar`
rejects the text `\u{E000}` (the byte-level grammar semantics denotes `⊥` on every §6 grammar,
`Equiv/Text.lean`'s `gramRelSup_tchar_eq_bot`, so that statement would be vacuous there).
-/

public section

namespace Silmaril.Wasm.SpecTec.Broken

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000

theorem escapeRejectsE000_original : EscapeRejectsE000 Wasm30.original :=
  premsFail_of_undef (N := 100) (by rfl) (by with_unfolding_all rfl)

theorem escapeAcceptsE000_fixed :
    PremsHold Wasm30.fixed (prodPrems Wasm30.fixed "Tstringchar" 7) escapeE000Scope :=
  ⟨_, by rfl, 100, _, by with_unfolding_all rfl⟩

theorem not_escapeRejectsE000_fixed : ¬ EscapeRejectsE000 Wasm30.fixed :=
  not_premsFail_of_premsHold escapeAcceptsE000_fixed

end Silmaril.Wasm.SpecTec.Broken
