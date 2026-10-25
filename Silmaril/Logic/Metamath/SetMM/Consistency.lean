module

public import Silmaril.Logic.Metamath.SetMM.Model
public import Silmaril.Logic.Metamath.Verify.EndToEnd

@[expose] public section

/-!
# Consistency of set.mm's ZFC

The `ZFSet` model (`Silmaril.Logic.Metamath.SetMM.Model`) refutes
`|- -. x = x` (`SetMM.negEq`) and is not trivial at `|-`, so set.mm's `ZFC`
with `df-bi`, `df-an`, `df-or` and `df-ex` is consistent:

* at the tree level, it derives neither `|- -. x = x` nor `|- ph`
  (`not_tderivable_negEq`, `tConsistent_zfc`);
* at the string level, the syntax axioms and the flattened axioms derive
  neither (`not_derivable_negEq`, `not_derivable_falsum`), the string system
  is non-universal and its theory is below the top theory
  (`nonUniversal_zfc`, `theory_ne_top_zfc`); the same holds for the string
  axioms of `ZFC` listed in `zfcList` (`not_derivable_negEq_str`);
* end to end, every theorem of a database accepted by
  `Silmaril.Logic.Metamath.Verify.verifyText` whose axioms are string axioms
  of `ZFC` holds in the `ZFSet` model (`verifyText_satisfiesStr`,
  `verifyText_provable_satisfiesStr`), so no such database proves
  `|- -. x = x` (`verifyText_ne_negEq`). Whether the axioms of a database are
  string axioms of `ZFC` is decided by `axiomsIn zfcStrList`
  (`verifyText_satisfiesStr_of_axiomsIn`). These contracts retain explicit
  hypotheses for checker acceptance and axiom membership.

`PropCalc`, `PredCalc` and `ZF` are consistent as subsystems
(`tConsistent_zf`, ...).
-/

namespace Silmaril.Logic.Metamath.SetMM

open Silmaril.Logic.Metamath Grammar Grammar.TAssertion Silmaril.Logic.SetTheory Env
open Silmaril.Logic.Metamath.Model.SetMM (opEq_cv)

universe u

/-- `|- -. x = x`, in the frame of the set variable `x`. -/
def negEq : TAssertion L String String := ⟨[], [fs "x"], pf (wn (weq "x" "x"))⟩

theorem wellFormed_negEq : negEq.WellFormed grammar := .of_checkWF (by decide)

/-- The string assertion `|- -. x = x` with the floating hypothesis `setvar x`. -/
theorem flatten_negEq : negEq.flatten grammar =
    ⟨[], [.float "setvar" "x"], ⟨"|-", [c "-.", v "x", c "=", v "x"]⟩⟩ := by decide

variable {N : Type (u + 1)} [DecidableEq N] [Infinite N]

/-- The `ZFSet` model refutes `|- -. x = x`. -/
theorem not_satisfies_negEq : ¬ (model ZFSet.{u} N).Satisfies negEq := by
  intro h
  let ρ : (model ZFSet.{u} N).Valuation negEq.ctx := fun _ _ h =>
    Classical.choice ((model ZFSet.{u} N).nonempty h.2)
  obtain ⟨ht, hv⟩ := (holds_iff ρ _).1
    (h ρ (by simp [Model.DVHolds, negEq]) (by simp [negEq, essentials]))
  simp only [value_wn, value_wceq, value_cv, Model.value_var,
    opEq_cv (N := N) extensional_zfset] at hv
  exact hv (fun _ => ∅) rfl

/-- The `ZFSet` model is not trivial at `|-`: the constantly false formula is
not true. -/
theorem not_trivialAt :
    ¬ (model ZFSet.{u} N).TrivialAt (c := "|-") (s := "wff") rfl :=
  fun h => h (Term.const False) fun _ => ∅

/-! ## Tree level -/

/-- `ZFC` does not derive `|- -. x = x`. -/
theorem not_tderivable_negEq : ¬ TDerivable grammar zfc negEq :=
  (model ZFSet.{0} (ULift.{1} ℕ)).not_tderivable wellFormed_zfc isModel_zfc not_satisfies_negEq

/-- `ZFC` does not derive `|- ph`. -/
theorem not_tderivable_falsum : ¬ TDerivable grammar zfc (falsum "|-" "wff" "ph") :=
  Model.not_tderivable_falsum (M := model ZFSet.{0} (ULift.{1} ℕ)) wellFormed_zfc isModel_zfc rfl
    not_trivialAt "ph"

/-- `ZFC` is consistent at `|-`. -/
theorem tConsistent_zfc : TConsistent grammar zfc "|-" :=
  tConsistent_of_not_falsum rfl not_tderivable_falsum

theorem tConsistent_zf : TConsistent grammar zf "|-" := tConsistent_zfc.mono zf_subset_zfc

theorem tConsistent_predCalc : TConsistent grammar predCalc "|-" :=
  tConsistent_zf.mono predCalc_subset_zf

theorem tConsistent_propCalc : TConsistent grammar propCalc "|-" :=
  tConsistent_predCalc.mono propCalc_subset_predCalc

/-- Every tree theorem of `ZFC` holds in the `ZFSet` model. -/
theorem sound_zfc {A : TAssertion L String String} (h : TDerivable grammar zfc A) :
    (model ZFSet.{u} N).Satisfies A :=
  (model ZFSet.{u} N).sound wellFormed_zfc isModel_zfc h

/-! ## String level -/

/-- The syntax axioms and the flattened axioms of `ZFC` do not derive
`|- -. x = x`. -/
theorem not_derivable_negEq : ¬ Derivable (grammar.axioms zfc) (negEq.flatten grammar) :=
  Model.not_derivable (M := model ZFSet.{0} (ULift.{1} ℕ)) unambiguous wellFormed_zfc isModel_zfc
    wellFormed_negEq not_satisfies_negEq

/-- The string axioms of `ZFC` do not derive `|- -. x = x`. -/
theorem not_derivable_negEq_str :
    ¬ Derivable (strAxioms zfSyntax zfcList) (negEq.flatten grammar) :=
  fun h => not_derivable_negEq (h.mono (strAxioms_subset_axioms _ _))

/-- The syntax axioms and the flattened axioms of `ZFC` do not derive `|- ph`. -/
theorem not_derivable_falsum :
    ¬ Derivable (grammar.axioms zfc) ((falsum "|-" "wff" "ph").flatten grammar) :=
  Model.not_derivable_falsum (M := model ZFSet.{0} (ULift.{1} ℕ)) unambiguous wellFormed_zfc
    isModel_zfc rfl not_trivialAt "ph"

/-- The string system of `ZFC` is non-universal. -/
theorem nonUniversal_zfc : (system (grammar.axioms zfc)).NonUniversal :=
  Model.nonUniversal_system (M := model ZFSet.{0} (ULift.{1} ℕ)) unambiguous wellFormed_zfc
    isModel_zfc rfl not_trivialAt "ph"

/-- The theory of the string axioms of `ZFC` is consistent. -/
theorem theory_ne_top_zfc : Theory.of (grammar.wfAxioms zfc) ≠ ⊤ :=
  Model.theory_ne_top (M := model ZFSet.{0} (ULift.{1} ℕ)) unambiguous wellFormed_zfc
    isModel_zfc rfl not_trivialAt "ph"

/-- Every string theorem of `ZFC` holds in the `ZFSet` model. -/
theorem sound_str_zfc {A : Assertion String String} (h : Derivable (grammar.axioms zfc) A) :
    (model ZFSet.{u} N).SatisfiesStr A :=
  (model ZFSet.{u} N).sound_str unambiguous wellFormed_zfc isModel_zfc h

/-! ## End to end -/

open Verify in
/-- Every theorem of a database accepted by the checker whose axioms are string
axioms of `ZFC` holds in the `ZFSet` model. -/
theorem verifyText_satisfiesStr {text : String} {db : Database String String}
    (h : verifyText text = .ok db) (hax : db.axioms ⊆ grammar.axioms zfc) {i : ℕ}
    (hi : i < db.entries.size) (hk : db.entries[i].kind = .theorem) :
    (model ZFSet.{u} N).SatisfiesStr db.entries[i].assertion :=
  sound_str_zfc ((verifyText_sound h i hi hk).mono
    ((db.kindBefore_mono _ hi.le).trans hax))

open Verify Text in
/-- End to end: each `$p` statement of an accepted file whose axioms are string
axioms of `ZFC` is recorded with its label, typecode and math string, and holds
in the `ZFSet` model. -/
theorem verifyText_provable_satisfiesStr {text : String} {db : Database String String}
    (h : verifyText text = .ok db) {src : Source} (hsrc : parse text = .ok src)
    (hax : db.axioms ⊆ grammar.axioms zfc) {l tc : String} {body : List String}
    {prf : ProofText} (hst : Stmt.provable l tc body prf ∈ src) :
    ∃ i, ∃ hi : i < db.entries.size, db.entries[i].label = l ∧
      db.entries[i].assertion.concl.tc = tc ∧
      db.entries[i].assertion.concl.body.map symToken = body ∧
      (model ZFSet.{u} N).SatisfiesStr db.entries[i].assertion := by
  obtain ⟨i, hi, hl, htc, hb, hd⟩ := verifyText_provable h hsrc hst
  exact ⟨i, hi, hl, htc, hb, sound_str_zfc (hd.mono ((db.kindBefore_mono _ hi.le).trans hax))⟩

open Verify in
/-- No theorem of a database accepted by the checker whose axioms are string
axioms of `ZFC` asserts `|- -. x = x` in the frame of the set variable `x`. -/
theorem verifyText_ne_negEq {text : String} {db : Database String String}
    (h : verifyText text = .ok db) (hax : db.axioms ⊆ grammar.axioms zfc) {i : ℕ}
    (hi : i < db.entries.size) (hk : db.entries[i].kind = .theorem) :
    db.entries[i].assertion ≠ negEq.flatten grammar := fun he =>
  not_derivable_negEq (he ▸ (verifyText_sound h i hi hk).mono
    ((db.kindBefore_mono _ hi.le).trans hax))

/-! ## Checking the axioms of a database -/

/-- The string axioms of `ZFC`, as a list: the syntax axioms and the flattened
axioms. -/
def zfcStrList : List (Assertion String String) :=
  L.all.map (fun r => (rules r).toAssertion) ++ zfcList.map fun p => p.2.flatten grammar

theorem mem_axioms_of_mem_zfcStrList {A : Assertion String String} (h : A ∈ zfcStrList) :
    A ∈ grammar.axioms zfc := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 h
    exact Or.inl ⟨r, rfl⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact Or.inr ⟨p.2, ⟨p, hp, rfl⟩, rfl⟩

open Verify in
/-- Every axiom of the database is in the list. -/
def axiomsIn (l : List (Assertion String String)) (db : Database String String) : Bool :=
  db.entries.all fun e => e.kind != .axiom || l.contains e.assertion

open Verify in
theorem axioms_subset_of_axiomsIn {l : List (Assertion String String)}
    {db : Database String String} (h : axiomsIn l db = true) : db.axioms ⊆ {A | A ∈ l} := by
  rintro _ ⟨j, hj, -, hk, rfl⟩
  have := Array.all_eq_true.1 h j hj
  simp only [hk, bne_self_eq_false, Bool.false_or, List.contains_iff_mem] at this
  exact this

open Verify in
/-- End to end, with a computable check of the axioms: every theorem of a
database accepted by the checker whose axioms pass `axiomsIn zfcStrList` holds
in the `ZFSet` model. -/
theorem verifyText_satisfiesStr_of_axiomsIn {text : String} {db : Database String String}
    (h : verifyText text = .ok db) (hc : axiomsIn zfcStrList db = true) {i : ℕ}
    (hi : i < db.entries.size) (hk : db.entries[i].kind = .theorem) :
    (model ZFSet.{u} N).SatisfiesStr db.entries[i].assertion :=
  verifyText_satisfiesStr h (fun _ hA => mem_axioms_of_mem_zfcStrList
    (axioms_subset_of_axiomsIn hc hA)) hi hk

end Silmaril.Logic.Metamath.SetMM
