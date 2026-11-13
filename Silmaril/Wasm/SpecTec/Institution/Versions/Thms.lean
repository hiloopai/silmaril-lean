module

public import Silmaril.Wasm.SpecTec.Institution.Versions.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Versions
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionCountRows
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionCount1020
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionCount2030
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionCountMain
public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionDiffRows

/-!
# Versions of a SpecTec specification as theories: results

Proofs in `Silmaril.Proofs.Wasm.SpecTec.Institution.Versions`; see `docs/projects/wasm-extras.md`.

* `theoryOf_applyErrata`, `dropped_applyErrata`: errata whose corrected definitions declare no
  relation (`ErrataRelFree`) leave the theory of a script unchanged.
* `Versions.theoryOf_wasm30_fixed`, `theoryOf_wasm30_binary51`, `theoryOf_wasm30_text6x`,
  `theoryOf_wasm20_fixed`: the `spectec-gen theory-diff` rows with nothing dropped, in Lean.
* `dropped_applyErrata_sub`, `Versions.dropped_wasm10_fixed`: errata that correct only the
  relations `X` drop and add only rules of `X`; for wasm-1.0, `X = [Module_ok]`.
* `theory_diff_rows`: the cross-version counts of `spectec-gen theory-diff`, evaluated by the
  kernel: 132, 259 and 566 rules; 49 of wasm-1.0's retained by wasm-2.0, 9 of wasm-2.0's by
  wasm-3.0, 130 of wasm-1.0's by main `e7a9df7c` (`retainedCount`, which counts the rules of
  `theoryOf` in `retained`: `theoryOf_eq_ruleList`, `inTheoryB_iff_retained`).
* `theory_diff_rows_exact`: the remaining rows, with their exact dropped sets (`dropped_eq_of_all`,
  checked in chunks, `VersionDiff*`): wasm-1.0 original → fixed drops one rule, of `Module_ok`;
  meta-IL original → fixed drops the four `Step_exp` rules of `keysMetaFixed` (229 of 233
  retained); wasm-1.0 and wasm-2.0 pinned → main drop the rules of `Module_ok` and `Export_ok`
  (257 of 259 retained for 2.0); wasm-3.0 pinned → main drops the 23 rules of `keysWasm30Main`
  (543 of 566 retained).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Versions.theoryOf_wasm30_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Institution.Versions.theoryOf_wasm30_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Versions.theoryOf_wasm20_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Institution.Versions.theoryOf_wasm20_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Versions.dropped_wasm10_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Institution.Versions.dropped_wasm10_fixed

public section

namespace Silmaril.Wasm.SpecTec.Institution.Versions

open Silmaril.Wasm.SpecTec.Scripts

/-- **`theory-diff` rows in Lean.** The rule totals of the pinned wasm-1.0, 2.0 and 3.0 scripts,
and the numbers of rules retained for wasm-1.0 → 2.0, 2.0 → 3.0 and wasm-1.0 pinned → main, all
as `spectec-gen theory-diff` reports them. -/
theorem theory_diff_rows :
    (ruleList Wasm10.envOriginal).length = 132 ∧ (ruleList Wasm20.envOriginal).length = 259 ∧
      (ruleList Wasm30.envOriginal).length = 566 ∧
      retainedCount Wasm10.envOriginal Wasm20.envOriginal = 49 ∧
      retainedCount Wasm20.envOriginal Wasm30.envOriginal = 9 ∧
      retainedCount Wasm10.envOriginal Versions.Main.Wasm10.env = 130 :=
  ⟨ruleList_wasm10_length, ruleList_wasm20_length, ruleList_wasm30_length,
    retained_wasm10_wasm20, retained_wasm20_wasm30, retained_wasm10_main⟩

/-- **The remaining `theory-diff` rows in Lean, with their dropped sets.** A rule sentence's key
is its relation name and rule name (`SSen.key`); each dropped set is the set of rules of the
earlier script with a key in the listed keys, and each key names exactly one rule
(`droppedKeys_*`). -/
theorem theory_diff_rows_exact :
    (∃ φ, dropped Wasm10.envOriginal Wasm10.envFixed = {φ} ∧ φ.key = ("Module_ok", "")) ∧
      retainedCount Wasm10.envOriginal Wasm10.envFixed = 131 ∧
      dropped Meta.envO Meta.envF = {φ | φ ∈ theoryOf Meta.envO ∧ φ.key ∈ keysMetaFixed} ∧
      retainedCount Meta.envO Meta.envF = 229 ∧
      dropped Wasm10.envOriginal Versions.Main.Wasm10.env =
        {φ | φ ∈ theoryOf Wasm10.envOriginal ∧ φ.key ∈ keysWasm10Main} ∧
      dropped Wasm20.envOriginal Versions.Main.Wasm20.env =
        {φ | φ ∈ theoryOf Wasm20.envOriginal ∧ φ.key ∈ keysWasm20Main} ∧
      retainedCount Wasm20.envOriginal Versions.Main.Wasm20.env = 257 ∧
      dropped Wasm30.envOriginal Versions.Main.Wasm30.env =
        {φ | φ ∈ theoryOf Wasm30.envOriginal ∧ φ.key ∈ keysWasm30Main} ∧
      retainedCount Wasm30.envOriginal Versions.Main.Wasm30.env = 543 :=
  ⟨dropped_wasm10_fixed_singleton, retained_wasm10_fixed, dropped_metaIL, retained_metaIL,
    dropped_wasm10_main, dropped_wasm20_main, retained_wasm20_main, dropped_wasm30_main,
    retained_wasm30_main⟩

end Silmaril.Wasm.SpecTec.Institution.Versions

end

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Versions.theory_diff_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Institution.Versions.theory_diff_rows

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Versions.theory_diff_rows_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Institution.Versions.theory_diff_rows_exact
