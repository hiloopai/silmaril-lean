module

public import Silmaril.Project.Registry.Formal.Defs
public import Silmaril.LogicGraph.Consequence.Defs
public import Silmaril.Logic.Consequence.Arithmetic.Thms
public import Silmaril.Logic.Consequence.SecondOrder.Thms
public import Silmaril.Logic.Consequence.FirstOrder.Thms
public import Silmaril.Logic.HOLLight.SExp.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Thms
public meta import Silmaril.Logic.Consequence.Arithmetic.Thms
public meta import Silmaril.Logic.Consequence.SecondOrder.Thms
public meta import Silmaril.Logic.Consequence.FirstOrder.Thms

/-!
# The formal rows: FOL, PA, second-order arithmetic, HOL and MLTT

Registers each logic's consequence systems, presentations, properties and concrete problems
(`docs/projects/formal-rows.md`). Lean checks every property's **statement** against its role and
system, every problem's claims against its sentence, and computes each problem's S-expression by
running the presentation's printer.
-/

@[expose] public section

namespace Silmaril.LogicGraph.Consequence.Formal

open Silmaril.Consequence Silmaril.Logic.Concrete

/-- PA derivability over the default S-expression presentation. -/
noncomputable def paDerivesSExp := Arithmetic.paDerives.viaCodec Logic.Arithmetic.SExp.sentenceCodec
/-- Second-order derivability, one per subsystem. -/
def rca0Derives := SecondOrder.derives .RCA0
/-- WKL₀ (Σ⁰₁ separation). -/
def wkl0Derives := SecondOrder.derives .WKL0Sep
/-- ACA₀. -/
def aca0Derives := SecondOrder.derives .ACA0
/-- Z₂. -/
def z2Derives := SecondOrder.derives .Z2
/-- Z₂ derivability over the default S-expression presentation. -/
noncomputable def z2DerivesSExp := (SecondOrder.derives .Z2).viaCodec Logic.SecondOrderArithmetic.SExp.codec
/-- The second presentation of arithmetic sentences. -/
def paWords := Logic.Arithmetic.SExp.wordsCodec 0
/-- First-order semantic consequence over `orderSig`. -/
def folConsequence := FirstOrder.consequence FirstOrder.orderSig
/-- Truth in ℕ over `orderSig`. -/
def folTruthNat := FirstOrder.truthIn FirstOrder.natStructure

end Silmaril.LogicGraph.Consequence.Formal

open Silmaril.LogicGraph.Consequence.Formal

/-! ## Systems -/

silmaril consequence_system logic.formal.pa.derives := Silmaril.Consequence.Arithmetic.paDerives
  (reading := "derivability") (title := "PA: explicit natural-deduction proofs")
silmaril consequence_system logic.formal.q.derives := Silmaril.Consequence.Arithmetic.qDerives
  (reading := "derivability") (title := "Q (Robinson arithmetic): explicit proofs")
silmaril consequence_system logic.formal.pa.truth := Silmaril.Consequence.Arithmetic.truth
  (title := "Truth in the standard model ℕ")
silmaril consequence_system logic.formal.pa.derives.sexp :=
    Silmaril.LogicGraph.Consequence.Formal.paDerivesSExp
  (reading := "derivability") (title := "PA over S-expressions (silmaril.arithmetic.formula)")
silmaril consequence_system logic.formal.rca0.derives := Silmaril.LogicGraph.Consequence.Formal.rca0Derives
  (reading := "derivability") (title := "RCA₀: Hilbert proofs from hypotheses")
silmaril consequence_system logic.formal.wkl0.derives := Silmaril.LogicGraph.Consequence.Formal.wkl0Derives
  (reading := "derivability") (title := "WKL₀ (Σ⁰₁ separation): Hilbert proofs from hypotheses")
silmaril consequence_system logic.formal.aca0.derives := Silmaril.LogicGraph.Consequence.Formal.aca0Derives
  (reading := "derivability") (title := "ACA₀: Hilbert proofs from hypotheses")
silmaril consequence_system logic.formal.z2.derives := Silmaril.LogicGraph.Consequence.Formal.z2Derives
  (reading := "derivability") (title := "Z₂ (full second-order arithmetic): Hilbert proofs from hypotheses")
silmaril consequence_system logic.formal.z2.derives.sexp :=
    Silmaril.LogicGraph.Consequence.Formal.z2DerivesSExp
  (reading := "derivability") (title := "Z₂ over S-expressions (silmaril.soa.formula)")
silmaril consequence_system logic.formal.fol.consequence :=
    Silmaril.LogicGraph.Consequence.Formal.folConsequence
  (title := "FOL over orderSig: truth in every structure")
silmaril consequence_system logic.formal.fol.truth_nat := Silmaril.LogicGraph.Consequence.Formal.folTruthNat
  (title := "FOL over orderSig: truth in ℕ")

/-! ## Presentations -/

silmaril presentation logic.formal.pa.sexp := Silmaril.Logic.Arithmetic.SExp.sentenceCodec (default := true)
  (title := "Arithmetic sentences as S-expressions")
silmaril presentation logic.formal.pa.sexp_words := Silmaril.LogicGraph.Consequence.Formal.paWords
  (title := "Arithmetic sentences as S-expressions, with add and mul")
silmaril presentation logic.formal.soa.sexp := Silmaril.Logic.SecondOrderArithmetic.SExp.codec (default := true)
  (title := "Second-order arithmetic formulas as S-expressions")
silmaril presentation logic.formal.fol.sexp := Silmaril.Consequence.FirstOrder.orderCodec (default := true)
  (title := "First-order sentences over orderSig as S-expressions")
silmaril presentation logic.formal.hol.sexp := Silmaril.Logic.HOLLight.SExp.codec (default := true)
  (title := "HOL Light terms as S-expressions")
silmaril presentation logic.formal.mltt.sexp := Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.codec
  (default := true) (title := "Extensional MLTT judgments as S-expressions")

/-! ## Properties: each statement is checked against its role -/

silmaril logic_property logic.formal.pa.soundness := Silmaril.Consequence.Arithmetic.pa_soundFor
  (role := "soundness") (system := "logic.formal.pa.derives")
silmaril logic_property logic.formal.q.soundness := Silmaril.Consequence.Arithmetic.q_soundFor
  (role := "soundness") (system := "logic.formal.q.derives")
silmaril logic_property logic.formal.pa.consistency := Silmaril.Consequence.Arithmetic.pa_consistent
  (role := "consistency") (system := "logic.formal.pa.derives")
silmaril logic_property logic.formal.q.consistency := Silmaril.Consequence.Arithmetic.q_consistent
  (role := "consistency") (system := "logic.formal.q.derives")
silmaril logic_property logic.formal.pa.nontriviality := Silmaril.Consequence.Arithmetic.pa_nontrivial
  (role := "nontriviality") (system := "logic.formal.pa.derives")
silmaril logic_property logic.formal.pa.sexp.consistency :=
    Silmaril.Consequence.Arithmetic.paConcrete_consistent
  (role := "consistency") (system := "logic.formal.pa.derives.sexp")
silmaril logic_property logic.formal.q.pa := Silmaril.Consequence.Arithmetic.q_le_pa
  (role := "inclusion") (system := "logic.formal.q.derives") (target := "logic.formal.pa.derives")

silmaril logic_property logic.formal.rca0.soundness.full := Silmaril.Consequence.SecondOrder.derives_soundFor_full
  (arg := ".RCA0") (role := "soundness") (system := "logic.formal.rca0.derives")
silmaril logic_property logic.formal.wkl0.soundness.full := Silmaril.Consequence.SecondOrder.derives_soundFor_full
  (arg := ".WKL0Sep") (role := "soundness") (system := "logic.formal.wkl0.derives")
silmaril logic_property logic.formal.aca0.soundness.full := Silmaril.Consequence.SecondOrder.derives_soundFor_full
  (arg := ".ACA0") (role := "soundness") (system := "logic.formal.aca0.derives")
silmaril logic_property logic.formal.z2.soundness.full := Silmaril.Consequence.SecondOrder.derives_soundFor_full
  (arg := ".Z2") (role := "soundness") (system := "logic.formal.z2.derives")
silmaril logic_property logic.formal.rca0.soundness.henkin := Silmaril.Consequence.SecondOrder.derives_soundFor_henkin
  (arg := ".RCA0") (role := "soundness") (system := "logic.formal.rca0.derives")
silmaril logic_property logic.formal.wkl0.soundness.henkin := Silmaril.Consequence.SecondOrder.derives_soundFor_henkin
  (arg := ".WKL0Sep") (role := "soundness") (system := "logic.formal.wkl0.derives")
silmaril logic_property logic.formal.aca0.soundness.henkin := Silmaril.Consequence.SecondOrder.derives_soundFor_henkin
  (arg := ".ACA0") (role := "soundness") (system := "logic.formal.aca0.derives")
silmaril logic_property logic.formal.z2.soundness.henkin := Silmaril.Consequence.SecondOrder.derives_soundFor_henkin
  (arg := ".Z2") (role := "soundness") (system := "logic.formal.z2.derives")
silmaril logic_property logic.formal.rca0.consistency := Silmaril.Consequence.SecondOrder.consistent
  (arg := ".RCA0") (role := "consistency") (system := "logic.formal.rca0.derives")
silmaril logic_property logic.formal.wkl0.consistency := Silmaril.Consequence.SecondOrder.consistent
  (arg := ".WKL0Sep") (role := "consistency") (system := "logic.formal.wkl0.derives")
silmaril logic_property logic.formal.aca0.consistency := Silmaril.Consequence.SecondOrder.consistent
  (arg := ".ACA0") (role := "consistency") (system := "logic.formal.aca0.derives")
silmaril logic_property logic.formal.z2.consistency := Silmaril.Consequence.SecondOrder.consistent
  (arg := ".Z2") (role := "consistency") (system := "logic.formal.z2.derives")
silmaril logic_property logic.formal.z2.sexp.consistency := Silmaril.Consequence.SecondOrder.concrete_consistent
  (arg := ".Z2") (role := "consistency") (system := "logic.formal.z2.derives.sexp")
silmaril logic_property logic.formal.rca0.aca0 := Silmaril.Consequence.SecondOrder.rca0_le_aca0
  (role := "inclusion") (system := "logic.formal.rca0.derives") (target := "logic.formal.aca0.derives")
silmaril logic_property logic.formal.aca0.z2 := Silmaril.Consequence.SecondOrder.aca0_le_z2
  (role := "inclusion") (system := "logic.formal.aca0.derives") (target := "logic.formal.z2.derives")
silmaril logic_property logic.formal.rca0.wkl0 := Silmaril.Consequence.SecondOrder.rca0_le_wkl0
  (role := "inclusion") (system := "logic.formal.rca0.derives") (target := "logic.formal.wkl0.derives")

silmaril logic_property logic.formal.fol.satisfiable := Silmaril.Consequence.FirstOrder.orderTheory_satisfiable
  (role := "satisfiability")
silmaril logic_property logic.formal.fol.nontrivial := Silmaril.Consequence.FirstOrder.orderTheory_nontrivial
  (role := "consistency") (system := "logic.formal.fol.consequence")

silmaril logic_property logic.formal.hol.kernel.soundness := Silmaril.Consequence.HOL.kernel_le_seq
  (arg := "(S := Silmaril.LogicGraph.Consequence.holSig)") (role := "inclusion")
  (system := "logic.consequence.hol.kernel") (target := "logic.consequence.hol.seq")
silmaril logic_property logic.formal.mltt.extensional.soundness :=
    Silmaril.Consequence.TypeTheory.extensionalDerives_le_entails
  (role := "inclusion") (system := "logic.consequence.mltt.extensional.derives")
  (target := "logic.consequence.mltt.extensional.entails")

/-! ## Concrete problems -/

silmaril logic_problem logic.formal.pa.zero_add_zero := Silmaril.Consequence.Arithmetic.zeroAddZero
  (presentation := "logic.formal.pa.sexp")
  (derived := Silmaril.Consequence.Arithmetic.zeroAddZero_derived) (system := "logic.formal.pa.derives")
  (truth := Silmaril.Consequence.Arithmetic.zeroAddZero_true)
  (interpretation := Silmaril.Consequence.Arithmetic.standard)
  (title := "0 + 0 = 0")
silmaril logic_problem logic.formal.pa.zero_or_successor := Silmaril.Consequence.Arithmetic.zeroOrSuccessor
  (presentation := "logic.formal.pa.sexp")
  (derived := Silmaril.Consequence.Arithmetic.zeroOrSuccessor_derived) (system := "logic.formal.pa.derives")
  (truth := Silmaril.Consequence.Arithmetic.zeroOrSuccessor_true)
  (interpretation := Silmaril.Consequence.Arithmetic.standard)
  (title := "Every number is zero or a successor")
silmaril logic_problem logic.formal.soa.succ_ne_zero := Silmaril.Consequence.SecondOrder.succNeZero
  (presentation := "logic.formal.soa.sexp")
  (derived := Silmaril.Consequence.SecondOrder.succNeZero_derived) (system := "logic.formal.rca0.derives")
  (truth := Silmaril.Consequence.SecondOrder.succNeZero_true)
  (interpretation := Silmaril.Consequence.SecondOrder.full)
  (title := "succ 0 ≠ 0 (RCA₀)")
silmaril logic_problem logic.formal.soa.comprehension_eq := Silmaril.Consequence.SecondOrder.comprehensionEq
  (presentation := "logic.formal.soa.sexp")
  (derived := Silmaril.Consequence.SecondOrder.comprehensionEq_z2) (system := "logic.formal.z2.derives")
  (truth := Silmaril.Consequence.SecondOrder.comprehensionEq_true)
  (interpretation := Silmaril.Consequence.SecondOrder.full)
  (title := "∃X ∀x (x ∈ X ↔ x = x), by full comprehension (Z₂)")
silmaril logic_problem logic.formal.fol.succ_irrefl := Silmaril.Consequence.FirstOrder.succIrrefl
  (presentation := "logic.formal.fol.sexp")
  (entailed := Silmaril.Consequence.FirstOrder.orderTheory_entails_succIrrefl)
  (entailed_by := "logic.formal.fol.consequence")
  (truth := Silmaril.Consequence.FirstOrder.succIrrefl_true)
  (interpretation := "Silmaril.Consequence.FirstOrder.inStructure Silmaril.Consequence.FirstOrder.natStructure")
  (title := "∀x ¬ succ x < succ x, from the order theory in every structure")

/-! ## Rows -/

silmaril logic_row logic.formal.row.fol
  (title := "First-order logic (unsorted), over orderSig")
  (variant := "Unsorted first-order logic with equality; signature orderSig (zero, succ, <); structures with nonempty carriers. No derivation system yet: consistency is model existence.")
  (institution := "logic.institution.examples.ufol.inst")
  (systems := [logic.formal.fol.consequence, logic.formal.fol.truth_nat])
  (interpretations := [Silmaril.Consequence.FirstOrder.inStructure])
  (presentations := [logic.formal.fol.sexp])
  (properties := [logic.formal.fol.satisfiable, logic.formal.fol.nontrivial])
  (problems := [logic.formal.fol.succ_irrefl])
  (order := 1)
silmaril logic_row logic.formal.row.pa
  (title := "Peano arithmetic (and Robinson's Q)")
  (variant := "First-order PA: Q's axioms and the induction schema for every formula; classical natural deduction; standard model ℕ.")
  (systems := [logic.formal.pa.derives, logic.formal.q.derives, logic.formal.pa.truth, logic.formal.pa.derives.sexp])
  (interpretations := [Silmaril.Consequence.Arithmetic.standard])
  (presentations := [logic.formal.pa.sexp, logic.formal.pa.sexp_words])
  (properties := [logic.formal.pa.soundness, logic.formal.q.soundness, logic.formal.pa.consistency,
    logic.formal.q.consistency, logic.formal.pa.nontriviality, logic.formal.pa.sexp.consistency, logic.formal.q.pa])
  (problems := [logic.formal.pa.zero_add_zero, logic.formal.pa.zero_or_successor])
  (order := 2)
silmaril logic_row logic.formal.row.second_order
  (title := "Second-order arithmetic: RCA₀, WKL₀, ACA₀, Z₂")
  (variant := "Two-sorted Hilbert systems: RCA₀ (Σ⁰₁ induction, Δ⁰₁ comprehension), WKL₀ as RCA₀ + Σ⁰₁ separation (equivalence to weak König's lemma not proved), ACA₀ (arithmetical comprehension), Z₂ (full induction and comprehension). Full semantics: ℕ and every subset; Henkin semantics: structures validating the subsystem's axioms.")
  (systems := [logic.formal.rca0.derives, logic.formal.wkl0.derives, logic.formal.aca0.derives,
    logic.formal.z2.derives, logic.formal.z2.derives.sexp])
  (interpretations := [Silmaril.Consequence.SecondOrder.full, Silmaril.Consequence.SecondOrder.henkin])
  (presentations := [logic.formal.soa.sexp])
  (properties := [logic.formal.rca0.soundness.full, logic.formal.wkl0.soundness.full,
    logic.formal.aca0.soundness.full, logic.formal.z2.soundness.full,
    logic.formal.rca0.soundness.henkin, logic.formal.wkl0.soundness.henkin,
    logic.formal.aca0.soundness.henkin, logic.formal.z2.soundness.henkin,
    logic.formal.rca0.consistency, logic.formal.wkl0.consistency, logic.formal.aca0.consistency,
    logic.formal.z2.consistency, logic.formal.z2.sexp.consistency,
    logic.formal.rca0.aca0, logic.formal.aca0.z2, logic.formal.rca0.wkl0])
  (problems := [logic.formal.soa.succ_ne_zero, logic.formal.soa.comprehension_eq])
  (order := 3)
silmaril logic_row logic.formal.row.hol
  (title := "HOL (HOL Light kernel)")
  (variant := "HOL Light's kernel over its initial signature; standard models with full function spaces. Consistency of ETA + SELECT + INFINITY is proved in the library (HOLLight.classical_consistent) but not yet stated in this framework; the standard denotation of typed terms is the next stage.")
  (systems := [logic.consequence.hol.kernel, logic.consequence.hol.seq])
  (presentations := [logic.formal.hol.sexp])
  (properties := [logic.formal.hol.kernel.soundness])
  (order := 4)
silmaril logic_row logic.formal.row.mltt
  (title := "Extensional MLTT")
  (variant := "Extensional MLTT with cumulative universes, Π, Σ, ℕ, identity with reflection; validity in set hierarchies (universe 0). Bounded-height consistency (1–3 levels) is proved in the library but not yet stated in this framework.")
  (systems := [logic.consequence.mltt.extensional.derives, logic.consequence.mltt.extensional.entails])
  (presentations := [logic.formal.mltt.sexp])
  (properties := [logic.formal.mltt.extensional.soundness])
  (order := 5)
