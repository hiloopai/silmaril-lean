module

public import Silmaril.Wasm.SpecTec.Versions.Defs
public import Silmaril.Wasm.SpecTec.Broken.Thms

/-!
# The wasm-3.0 binary and numerics defects on the main script

Grammar facts transport `Equiv/BinaryValues.lean`'s environment-generic theorems: the `Has…`
hypotheses are discharged by kernel `rfl` on the generated main script, which says that `Bbyte`,
`BuN`, `BsN` and `BiN` are, term for term, the pinned definitions and that `Bi32`/`Bi64` are the
corrected (`BiN`) wrappers of erratum #654.  Evaluator facts are kernel evaluations at fuel 100
(`with_unfolding_all rfl`), lifted to every fuel by `Broken/Fuel.lean`, as in `Broken`.
-/

public section

namespace Silmaril.Wasm.SpecTec.Versions

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv
open Silmaril.Wasm.SpecTec.Broken
open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000

/-! ## The `Has…` hypotheses at the main script -/

theorem hasLeb_main : HasLeb Main.Wasm30.env := ⟨by rfl, by rfl⟩

/-- `BsN` and `BiN` on main are the pinned definitions, term for term. -/
theorem hasSignedLeb_main : HasSignedLeb Main.Wasm30.env := ⟨by rfl, by rfl⟩

/-- `Bi32` and `Bi64` on main are erratum #654's corrected wrappers, term for term. -/
theorem hasCorrectedBi_main : HasCorrectedBi Main.Wasm30.env := ⟨by rfl, by rfl⟩

/-! ## #654 is fixed upstream -/

theorem not_bi32Unsigned_main : ¬ Bi32Unsigned Main.Wasm30.original := by
  intro h
  exact not_bi32_FF7E hasLeb_main hasSignedLeb_main hasCorrectedBi_main VarEnv.empty
    (uNV 16255) ((h VarEnv.empty _ _).mpr ⟨16255, u32_FF7E, rfl⟩)

/-! ## #803 is still there -/

/-- **`BsN(32)` still derives nothing from `FF 7E` (`-129`) on main.** -/
theorem bsnLosesFF7E_main : BsNLosesFF7E Main.Wasm30.original :=
  not_bsn_FF7E hasLeb_main hasSignedLeb_main

/-- **The main `BsN(N)` is the hand-written `SN N` exactly on single bytes and non-negative
values**, as at the pin: the side condition `0 ≤ i ∨ bs.length = 1` is the narrowing of #803. -/
theorem bsn_main_iff_sn (W : Nat) (hW : 0 < W) (bs : Silmaril.SpecTec.Grammar.Bytes) (v : Value)
    (ρ : VarEnv) :
    gramRelSup Main.Wasm30.env ρ (.varG "BsN" [.expA (.numE (.natN W))]) bs v ↔
      ∃ i, Silmaril.Wasm.Binary.SN W bs i ∧ (0 ≤ i ∨ bs.length = 1) ∧ v = sNV i :=
  bsn_iff_sn hasLeb_main hasSignedLeb_main W hW bs v ρ

/-- So the main `Bi32` (`BiN(32)`) does not read `i32.const -129` either. -/
theorem not_bi32_FF7E_main (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup Main.Wasm30.env ρ (.varG "Bi32" []) [0xFF, 0x7E] v :=
  not_bi32_FF7E hasLeb_main hasSignedLeb_main hasCorrectedBi_main ρ v

/-- …and so the main `Bi32` is still not the signed LEB128 grammar `IN 32`. -/
theorem bi32_main_disagrees_with_in (ρ : VarEnv) :
    ¬ ∀ (bs : Silmaril.SpecTec.Grammar.Bytes) (v : Value),
        gramRelSup Main.Wasm30.env ρ (.varG "Bi32" []) bs v ↔
          ∃ bv : BitVec 32, Silmaril.Wasm.Binary.IN 32 bs bv ∧ v = iNV bv := by
  intro h
  exact not_bi32_FF7E_main ρ (iNV (BitVec.ofInt 32 (-129)))
    ((h [0xFF, 0x7E] _).mpr ⟨BitVec.ofInt 32 (-129), in32_FF7E, rfl⟩)

/-! ## #655 is fixed upstream -/

theorem cont80_main :
    CallIs Main.Wasm30.original "cont" [.expA (numCaseE 0x80)] (.num (.natN 0)) :=
  ⟨100, by with_unfolding_all rfl⟩

theorem not_contUndefAt80_main : ¬ ContUndefAt80 Main.Wasm30.original :=
  not_callUndef_of_callIs cont80_main

/-! ## #656 is fixed upstream (in `$utf8single`) -/

/-- On main the four-byte clause is clause 3 of `$utf8single`, and it accepts U+1F601. -/
theorem utf8singleAcceptsGrin_main : Utf8ClauseAcceptsGrin Main.Wasm30.original "utf8single" 3 :=
  ⟨_, by rfl, 100, _, by with_unfolding_all rfl⟩

theorem not_utf8singleRejectsGrin_main :
    ¬ Utf8ClauseRejectsGrin Main.Wasm30.original "utf8single" 3 :=
  not_premsFail_of_premsHold utf8singleAcceptsGrin_main

/-- The pinned clause, restated with the parametrised predicate. -/
theorem utf8ClauseRejectsGrin_original : Utf8ClauseRejectsGrin Wasm30.original "utf8" 4 :=
  utf8RejectsGrin_original

/-! ## `$sx` at reference types (sim item U5) is fixed upstream -/

theorem sxUndefAtRef_original : SxUndefAtRef Wasm30.original :=
  callUndef_of_undef (N := 100) (by with_unfolding_all rfl)

theorem sxRef_main : CallIs Main.Wasm30.original "sx" [.expA refFuncE] (.opt none) :=
  ⟨100, by with_unfolding_all rfl⟩

theorem not_sxUndefAtRef_main : ¬ SxUndefAtRef Main.Wasm30.original :=
  not_callUndef_of_callIs sxRef_main

/-! ## `$s33_to_u32` is still declared without clauses -/

theorem s33ToU32Undefined_original : S33ToU32Undefined Wasm30.original := ⟨_, _, by rfl⟩

theorem s33ToU32Undefined_main : S33ToU32Undefined Main.Wasm30.original := ⟨_, _, by rfl⟩

end Silmaril.Wasm.SpecTec.Versions
