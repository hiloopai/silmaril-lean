module

public import Silmaril.Proofs.Wasm.SpecTec.Broken.Fuel
public import Silmaril.Wasm.SpecTec.Scripts.Thms

/-!
# wasm-3.0 binary format: #654, #655, #656 and #803 on the generated scripts

`Bi32`/`BsN` facts come from `Equiv/BinaryValues.lean`, whose theorems are stated for any
environment satisfying a `Has…` hypothesis; here those hypotheses are discharged at the generated
`original` (by transport along `wasm30_original_eq`) and the generated `fixed` (by `rfl`).
`$cont` and `$utf8` facts are kernel evaluations (`with_unfolding_all rfl`) of the evaluator at
fuel 100, lifted to every fuel by `Fuel.lean`.
-/

public section

namespace Silmaril.Wasm.SpecTec.Broken

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv
open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000

/-! ## The `Has…` hypotheses at the generated scripts -/

theorem hasLeb_original : HasLeb Wasm30.envOriginal := by
  rw [Wasm30.envOriginal, wasm30_original_eq]; exact hasLeb_wasm30

theorem hasPinnedBi_original : HasPinnedBi Wasm30.envOriginal := by
  rw [Wasm30.envOriginal, wasm30_original_eq]; exact hasPinnedBi_wasm30

theorem hasSignedLeb_original : HasSignedLeb Wasm30.envOriginal := by
  rw [Wasm30.envOriginal, wasm30_original_eq]; exact hasSignedLeb_wasm30

theorem hasLeb_fixed : HasLeb Wasm30.envFixed := ⟨by rfl, by rfl⟩

theorem hasSignedLeb_fixed : HasSignedLeb Wasm30.envFixed := ⟨by rfl, by rfl⟩

theorem hasCorrectedBi_fixed : HasCorrectedBi Wasm30.envFixed := ⟨by rfl, by rfl⟩

/-! ## #654: `Bi32` is unsigned -/

theorem bi32Unsigned_original : Bi32Unsigned Wasm30.original :=
  fun ρ bs v => bi32_pinned_iff_un hasLeb_original hasPinnedBi_original ρ bs v

/-- A signed `Bi32` (`BiN(32)` over the pinned `BsN`) reads nothing from `FF 7E`. -/
theorem not_bi32_FF7E {env : Env} (hl : HasLeb env) (hs : HasSignedLeb env)
    (hb : HasCorrectedBi env) (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup env ρ (.varG "Bi32" []) [0xFF, 0x7E] v := by
  intro hd
  rw [wrap_rel_iff hb.bi32 hs.bin ρ _ v] at hd
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
  exact not_bin_FF7E hl hs VarEnv.empty ρ' v hd

/-- `FF 7E` is the unsigned LEB128 encoding of `16255`. -/
theorem u32_FF7E : Silmaril.Wasm.Binary.U32 [0xFF, 0x7E] 16255 :=
  .cont 0xFF (by decide) (by decide) (.byte 0x7E (by decide) (by decide))

/-- The fixed `Bi32` is not the unsigned grammar: the unsigned grammar reads `FF 7E` as `16255`,
the fixed one does not read it at all.  (That it reads nothing is #803, below.) -/
theorem not_bi32Unsigned_fixed : ¬ Bi32Unsigned Wasm30.fixed := by
  intro h
  exact not_bi32_FF7E hasLeb_fixed hasSignedLeb_fixed hasCorrectedBi_fixed VarEnv.empty
    (uNV 16255) ((h VarEnv.empty _ _).mpr ⟨16255, u32_FF7E, rfl⟩)

/-! ## #803: `BsN(32)` loses `FF 7E`, before and after the errata -/

theorem bsnLosesFF7E_original : BsNLosesFF7E Wasm30.original :=
  not_bsn_FF7E hasLeb_original hasSignedLeb_original

theorem bsnLosesFF7E_fixed : BsNLosesFF7E Wasm30.fixed :=
  not_bsn_FF7E hasLeb_fixed hasSignedLeb_fixed

/-! ## #655: `$cont(0x80)` -/

theorem contUndefAt80_original : ContUndefAt80 Wasm30.original :=
  callUndef_of_undef (N := 100) (by with_unfolding_all rfl)

theorem cont80_fixed : CallIs Wasm30.fixed "cont" [.expA (numCaseE 0x80)] (.num (.natN 0)) :=
  ⟨100, by with_unfolding_all rfl⟩

theorem not_contUndefAt80_fixed : ¬ ContUndefAt80 Wasm30.fixed :=
  not_callUndef_of_callIs cont80_fixed

/-! ## #656: the four-byte `$utf8` clause stops at U+11000 -/

theorem utf8RejectsGrin_original : Utf8RejectsGrin Wasm30.original :=
  premsFail_of_undef (N := 100) (by rfl) (by with_unfolding_all rfl)

theorem utf8AcceptsGrin_fixed : PremsHold Wasm30.fixed (clausePrems Wasm30.fixed "utf8" 4) grinScope :=
  ⟨_, by rfl, 100, _, by with_unfolding_all rfl⟩

theorem not_utf8RejectsGrin_fixed : ¬ Utf8RejectsGrin Wasm30.fixed :=
  not_premsFail_of_premsHold utf8AcceptsGrin_fixed

end Silmaril.Wasm.SpecTec.Broken
