module

public import Silmaril.Project.Registry.Formal.Defs
public import Silmaril.LogicGraph.Consequence.Defs
public import Silmaril.Logic.Consequence.Arithmetic.Thms
public import Silmaril.Logic.Consequence.SecondOrder.Thms
public import Silmaril.Logic.Consequence.FirstOrder.Thms
public import Silmaril.Logic.HOLLight.SExp.Thms
public import Silmaril.Logic.Consequence.HOL.Standard.Thms
public meta import Silmaril.Logic.Consequence.HOL.Standard.Thms
public import Silmaril.Logic.Consequence.HOL.UserSig.Thms
public meta import Silmaril.Logic.Consequence.HOL.UserSig.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Thms
public meta import Silmaril.Logic.Consequence.Arithmetic.Thms
public meta import Silmaril.Logic.Consequence.SecondOrder.Thms
public meta import Silmaril.Logic.Consequence.FirstOrder.Thms
public meta import Silmaril.Logic.Consequence.TypeTheory.Thms
public import Silmaril.Logic.Consequence.Arithmetic.Derivation.Examples
public import Silmaril.Logic.Consequence.FirstOrder.Derivation.Examples
public meta import Silmaril.Logic.Consequence.FirstOrder.Derivation.Examples
public meta import Silmaril.Logic.Consequence.Arithmetic.Derivation.Examples

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
/-- HOL propositions over the initial signature, as S-expressions (decode and type-check). -/
def holPropCodec := HOL.propCodec HOL.initialSig
/-- HOL propositions over the user signature `coinSig` (one boolean constant `c`). -/
def holCoinCodec := HOL.propCodec HOL.coinSig
/-- Pure HOL over `coinSig`. -/
def holCoinKernel := HOL.kernel HOL.coinSig
/-- HOL over `coinSig` with the axiom `c`. -/
def holCoinTheory := HOL.kernelFrom HOL.coinSig HOL.cTheory
/-- HOL with HOL Light's classical axioms (ETA, SELECT, INFINITY), on propositions. -/
def holClassical := HOL.kernelFrom HOL.initialSig Logic.HOLLight.classicalTheory
/-- `⊢ 0 : ℕ`, with one universe level. -/
def mlttZero := Logic.TypeTheory.ExtensionalMLTT.Finite.zeroSentence 1
/-- Bounded MLTT judgments (one universe level) as S-expressions. -/
def mlttBounded1Codec := TypeTheory.boundedCodec 1
/-- Extensional MLTT with one universe level (bounded rules). -/
def mlttBounded1 := TypeTheory.boundedDerives.{1} 1
/-- Two universe levels. -/
def mlttBounded2 := TypeTheory.boundedDerives.{2} 2
/-- Three universe levels. -/
def mlttBounded3 := TypeTheory.boundedDerives.{3} 3
/-- PA derivability by checked proof trees (the derivation system). -/
def paTreeDerives := Arithmetic.ND.treeDerives .pa
/-- Q derivability by checked proof trees. -/
def qTreeDerives := Arithmetic.ND.treeDerives .q
/-- First-order derivability over `orderSig` by checked proof trees. -/
def folTreeDerives := FirstOrder.ND.treeDerives FirstOrder.orderSig
/-- First-order judgments over `orderSig` as S-expressions. -/
def folSeqCodec := FirstOrder.ND.seqCodec FirstOrder.orderOps FirstOrder.orderRels
/-- First-order proofs over `orderSig` as S-expression trees. -/
def folTreeCodec := FirstOrder.ND.treeCodec FirstOrder.orderOps FirstOrder.orderRels
/-- First-order proofs over `orderSig` as indexed S-expression lines. -/
def folLinesCodec := FirstOrder.ND.linesCodec FirstOrder.orderOps FirstOrder.orderRels
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
silmaril consequence_system logic.formal.hol.classical := Silmaril.LogicGraph.Consequence.Formal.holClassical
  (reading := "derivability") (title := "HOL with ETA, SELECT and INFINITY: the kernel on propositions")
silmaril consequence_system logic.formal.hol.coin.kernel := Silmaril.LogicGraph.Consequence.Formal.holCoinKernel
  (reading := "derivability") (title := "Pure HOL over the user signature coinSig (one boolean constant c)")
silmaril consequence_system logic.formal.hol.coin.theory := Silmaril.LogicGraph.Consequence.Formal.holCoinTheory
  (reading := "derivability") (title := "HOL over coinSig with the axiom c")
silmaril consequence_system logic.formal.mltt.bounded1.derives := Silmaril.LogicGraph.Consequence.Formal.mlttBounded1
  (reading := "derivability") (title := "Extensional MLTT with 1 universe level: derivability")
silmaril consequence_system logic.formal.mltt.bounded2.derives := Silmaril.LogicGraph.Consequence.Formal.mlttBounded2
  (reading := "derivability") (title := "Extensional MLTT with 2 universe levels: derivability")
silmaril consequence_system logic.formal.mltt.bounded3.derives := Silmaril.LogicGraph.Consequence.Formal.mlttBounded3
  (reading := "derivability") (title := "Extensional MLTT with 3 universe levels: derivability")
silmaril consequence_system logic.formal.fol.consequence :=
    Silmaril.LogicGraph.Consequence.Formal.folConsequence
  (title := "FOL over orderSig: truth in every structure")
silmaril consequence_system logic.formal.fol.tree.derives :=
    Silmaril.LogicGraph.Consequence.Formal.folTreeDerives
  (reading := "derivability") (title := "FOL over orderSig: checked natural-deduction proof trees")
silmaril consequence_system logic.formal.fol.truth_nat := Silmaril.LogicGraph.Consequence.Formal.folTruthNat
  (title := "FOL over orderSig: truth in ℕ")

silmaril consequence_system logic.formal.pa.tree.derives := Silmaril.LogicGraph.Consequence.Formal.paTreeDerives
  (reading := "derivability") (title := "PA: checked proof trees (derivation system)")
silmaril consequence_system logic.formal.q.tree.derives := Silmaril.LogicGraph.Consequence.Formal.qTreeDerives
  (reading := "derivability") (title := "Q: checked proof trees (derivation system)")

/-! ## Presentations -/

silmaril presentation logic.formal.pa.sexp := Silmaril.Logic.Arithmetic.SExp.sentenceCodec (default := true)
  (title := "Arithmetic sentences as S-expressions")
silmaril presentation logic.formal.pa.sexp_words := Silmaril.LogicGraph.Consequence.Formal.paWords
  (title := "Arithmetic sentences as S-expressions, with add and mul")
silmaril presentation logic.formal.soa.sexp := Silmaril.Logic.SecondOrderArithmetic.SExp.codec (default := true)
  (title := "Second-order arithmetic formulas as S-expressions")
silmaril presentation logic.formal.fol.sexp := Silmaril.Consequence.FirstOrder.orderCodec (default := true)
  (title := "First-order sentences over orderSig as S-expressions")
silmaril presentation logic.formal.hol.prop.sexp := Silmaril.LogicGraph.Consequence.Formal.holPropCodec
  (default := true) (title := "HOL propositions as S-expressions (decoded, then type-checked as bool)")
silmaril presentation logic.formal.hol.sexp := Silmaril.Logic.HOLLight.SExp.codec
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

silmaril logic_property logic.formal.hol.soundness := Silmaril.Consequence.HOL.kernel_soundFor
  (arg := "Silmaril.Consequence.HOL.initialSig") (role := "soundness") (system := "logic.consequence.hol.kernel")
silmaril logic_property logic.formal.hol.consistency := Silmaril.Consequence.HOL.kernel_consistent
  (role := "consistency") (system := "logic.consequence.hol.kernel")
silmaril logic_property logic.formal.hol.classical.consistency := Silmaril.Consequence.HOL.classical_consistent'
  (role := "consistency") (system := "logic.formal.hol.classical")
silmaril logic_property logic.formal.hol.nontriviality := Silmaril.Consequence.HOL.kernel_nontrivial
  (role := "nontriviality") (system := "logic.consequence.hol.kernel")
silmaril logic_property logic.formal.hol.kernel.soundness := Silmaril.Consequence.HOL.kernel_le_seq
  (arg := "(S := Silmaril.LogicGraph.Consequence.holSig)") (role := "inclusion")
  (system := "logic.consequence.hol.kernel") (target := "logic.consequence.hol.seq")
silmaril logic_property logic.formal.mltt.bounded1.consistency := Silmaril.Consequence.TypeTheory.bounded_consistent_one
  (role := "nontriviality") (system := "logic.formal.mltt.bounded1.derives")
silmaril logic_property logic.formal.mltt.bounded2.consistency := Silmaril.Consequence.TypeTheory.bounded_consistent_two
  (role := "nontriviality") (system := "logic.formal.mltt.bounded2.derives")
silmaril logic_property logic.formal.mltt.bounded3.consistency := Silmaril.Consequence.TypeTheory.bounded_consistent_three
  (role := "nontriviality") (system := "logic.formal.mltt.bounded3.derives")
silmaril logic_property logic.formal.mltt.intensional.consistency := Silmaril.Consequence.TypeTheory.intensional_consistent
  (arg := "⊤") (role := "nontriviality") (system := "logic.consequence.mltt.intensional.derives")
silmaril logic_property logic.formal.mltt.intensional.soundness :=
    Silmaril.Consequence.TypeTheory.intensionalDerives_le_entails
  (arg := "⊤") (role := "inclusion") (system := "logic.consequence.mltt.intensional.derives")
  (target := "logic.consequence.mltt.intensional.entails")
silmaril logic_property logic.formal.mltt.extensional.soundness :=
    Silmaril.Consequence.TypeTheory.extensionalDerives_le_entails
  (role := "inclusion") (system := "logic.consequence.mltt.extensional.derives")
  (target := "logic.consequence.mltt.extensional.entails")

/-! ## Derivation systems and derivations -/

silmaril presentation logic.formal.pa.sequent := Silmaril.Consequence.Arithmetic.ND.seqCodec
  (title := "PA judgments: (seq n (hypotheses) conclusion)")
silmaril presentation logic.formal.pa.proof_tree := Silmaril.Consequence.Arithmetic.ND.treeCodec
  (title := "PA proofs as S-expression trees")
silmaril presentation logic.formal.pa.proof_lines := Silmaril.Consequence.Arithmetic.ND.linesCodec
  (title := "PA proofs as indexed S-expression lines")

silmaril logic_property logic.formal.pa.tree.soundness := Silmaril.Consequence.Arithmetic.ND.treeDerives_soundFor
  (arg := ".pa") (role := "soundness") (system := "logic.formal.pa.tree.derives")
  (title := "Checked PA proof trees are sound for ℕ (by local soundness)")
silmaril logic_property logic.formal.q.tree.soundness := Silmaril.Consequence.Arithmetic.ND.treeDerives_soundFor
  (arg := ".q") (role := "soundness") (system := "logic.formal.q.tree.derives")
  (title := "Checked Q proof trees are sound for ℕ (by local soundness)")
silmaril logic_property logic.formal.pa.tree.consistency := Silmaril.Consequence.Arithmetic.ND.pa_tree_consistent
  (role := "consistency") (system := "logic.formal.pa.tree.derives")
  (title := "Checked PA proof trees do not derive ⊥")
silmaril logic_property logic.formal.q.tree.consistency := Silmaril.Consequence.Arithmetic.ND.q_tree_consistent
  (role := "consistency") (system := "logic.formal.q.tree.derives")
  (title := "Checked Q proof trees do not derive ⊥")

silmaril derivation_system logic.formal.pa.nd := Silmaril.Consequence.Arithmetic.ND.system (arg := ".pa")
  (judgments := "logic.formal.pa.sequent")
  (formats := [logic.formal.pa.proof_tree, logic.formal.pa.proof_lines])
  (locally_sound := "Silmaril.Consequence.Arithmetic.ND.locallySound_valid .pa")
  (agrees := "Silmaril.Consequence.Arithmetic.ND.treeDerives_pa") (system := "logic.formal.pa.derives")
  (title := "PA natural deduction: rule instances checked step by step")
silmaril derivation_system logic.formal.q.nd := Silmaril.Consequence.Arithmetic.ND.system (arg := ".q")
  (judgments := "logic.formal.pa.sequent")
  (formats := [logic.formal.pa.proof_tree, logic.formal.pa.proof_lines])
  (locally_sound := "Silmaril.Consequence.Arithmetic.ND.locallySound_valid .q")
  (agrees := "Silmaril.Consequence.Arithmetic.ND.treeDerives_q") (system := "logic.formal.q.derives")
  (title := "Q natural deduction: rule instances checked step by step")

silmaril derivation logic.formal.pa.proof.zero_add := Silmaril.Consequence.Arithmetic.ND.Examples.zeroAdd
  (presentation := "logic.formal.pa.proof_tree") (system := "logic.formal.pa.nd")
  (verdicts := [Silmaril.Consequence.Arithmetic.ND.Examples.zeroAdd_checks_pa,
    Silmaril.Consequence.Arithmetic.ND.Examples.zeroAdd_rejected_q])
  (derives := Silmaril.Consequence.Arithmetic.ND.Examples.zeroAdd_derives)
  (derives_system := "logic.formal.pa.derives")
  (title := "∀x. 0 + x = x, by induction (PA accepts, Q rejects)")
silmaril derivation logic.formal.pa.proof.zero_add_zero := Silmaril.Consequence.Arithmetic.ND.Examples.zeroAddZero
  (presentation := "logic.formal.pa.proof_tree") (system := "logic.formal.pa.nd")
  (verdicts := [Silmaril.Consequence.Arithmetic.ND.Examples.zeroAddZero_checks_pa,
    Silmaril.Consequence.Arithmetic.ND.Examples.zeroAddZero_checks_q])
  (derives := Silmaril.Consequence.Arithmetic.ND.Examples.zeroAddZero_derives)
  (derives_system := "logic.formal.pa.derives")
  (title := "0 + 0 = 0, by the axiom add-zero")
silmaril derivation logic.formal.pa.proof.inst_add_zero := Silmaril.Consequence.Arithmetic.ND.Examples.instAddZero
  (presentation := "logic.formal.pa.proof_tree") (system := "logic.formal.q.nd")
  (verdicts := [Silmaril.Consequence.Arithmetic.ND.Examples.instAddZero_checks,
    Silmaril.Consequence.Arithmetic.ND.Examples.instAddZero_lines_checks])
  (derives := Silmaril.Consequence.Arithmetic.ND.Examples.instAddZero_derives)
  (derives_system := "logic.formal.q.derives")
  (title := "0 + 0 = 0 from ∀x. x + 0 = x, by ∀-elimination (trees and lines)")
silmaril derivation logic.formal.pa.proof.eq_symm := Silmaril.Consequence.Arithmetic.ND.Examples.eqSymm
  (presentation := "logic.formal.pa.proof_tree") (system := "logic.formal.q.nd")
  (verdicts := [Silmaril.Consequence.Arithmetic.ND.Examples.eqSymm_checks])
  (derives := Silmaril.Consequence.Arithmetic.ND.Examples.eqSymm_derives)
  (derives_system := "logic.formal.q.derives")
  (title := "∀x ∀y. x = y → y = x, by equality elimination")
silmaril derivation logic.formal.pa.proof.wrong_axiom := Silmaril.Consequence.Arithmetic.ND.Examples.wrongAxiom
  (presentation := "logic.formal.pa.proof_tree") (system := "logic.formal.pa.nd")
  (verdicts := [Silmaril.Consequence.Arithmetic.ND.Examples.wrongAxiom_rejected])
  (title := "Rejected: add-zero does not conclude 0 + 0 = S0")
silmaril derivation logic.formal.pa.proof.unknown_rule := Silmaril.Consequence.Arithmetic.ND.Examples.unknownRule
  (presentation := "logic.formal.pa.proof_tree") (system := "logic.formal.pa.nd")
  (verdicts := [Silmaril.Consequence.Arithmetic.ND.Examples.unknownRule_rejected])
  (title := "Rejected: an unknown rule")
silmaril derivation logic.formal.pa.proof.missing_hyp := Silmaril.Consequence.Arithmetic.ND.Examples.missingHyp
  (presentation := "logic.formal.pa.proof_tree") (system := "logic.formal.pa.nd")
  (verdicts := [Silmaril.Consequence.Arithmetic.ND.Examples.missingHyp_rejected])
  (title := "Rejected: a hypothesis that is not in the context")

silmaril presentation logic.formal.fol.sequent := Silmaril.LogicGraph.Consequence.Formal.folSeqCodec
  (title := "FOL judgments over orderSig: (seq k (hypotheses) conclusion)")
silmaril presentation logic.formal.fol.proof_tree := Silmaril.LogicGraph.Consequence.Formal.folTreeCodec
  (title := "FOL proofs over orderSig as S-expression trees")
silmaril presentation logic.formal.fol.proof_lines := Silmaril.LogicGraph.Consequence.Formal.folLinesCodec
  (title := "FOL proofs over orderSig as indexed S-expression lines")

silmaril logic_property logic.formal.fol.tree.soundness :=
    Silmaril.Consequence.FirstOrder.ND.treeDerives_le_consequence
  (arg := "(Sg := Silmaril.Consequence.FirstOrder.orderSig)")
  (role := "inclusion") (system := "logic.formal.fol.tree.derives")
  (target := "logic.formal.fol.consequence")
  (title := "Checked FOL proof trees derive only semantic consequences (soundness)")
silmaril logic_property logic.formal.fol.tree.soundness_nat := Silmaril.Consequence.FirstOrder.ND.treeDerives_soundFor
  (arg := "Silmaril.Consequence.FirstOrder.natStructure")
  (role := "soundness") (system := "logic.formal.fol.tree.derives")
  (title := "Checked FOL proof trees are sound for the structure ℕ")
silmaril logic_property logic.formal.fol.tree.consistency :=
    Silmaril.Consequence.FirstOrder.ND.orderTheory_tree_consistent
  (role := "consistency") (system := "logic.formal.fol.tree.derives")
  (title := "The order theory does not derive ¬⊤ by checked proof trees")

silmaril derivation_system logic.formal.fol.nd := Silmaril.Consequence.FirstOrder.ND.system
  (arg := "Silmaril.Consequence.FirstOrder.orderSig")
  (judgments := "logic.formal.fol.sequent")
  (formats := [logic.formal.fol.proof_tree, logic.formal.fol.proof_lines])
  (locally_sound := "Silmaril.Consequence.FirstOrder.ND.locallySound (Sg := Silmaril.Consequence.FirstOrder.orderSig)")
  (title := "FOL natural deduction over orderSig: rule instances checked step by step")

silmaril derivation logic.formal.fol.proof.succ_irrefl :=
    Silmaril.Consequence.FirstOrder.ND.Examples.succIrreflProof
  (presentation := "logic.formal.fol.proof_tree") (system := "logic.formal.fol.nd")
  (verdicts := [Silmaril.Consequence.FirstOrder.ND.Examples.succIrreflProof_checks,
    Silmaril.Consequence.FirstOrder.ND.Examples.succIrreflProof_lines_checks])
  (derives := Silmaril.Consequence.FirstOrder.ND.Examples.succIrrefl_derives)
  (derives_system := "logic.formal.fol.tree.derives")
  (title := "∀x ¬ succ x < succ x from the order theory, by ∀-elimination (trees and lines)")
silmaril derivation logic.formal.fol.proof.eq_symm := Silmaril.Consequence.FirstOrder.ND.Examples.eqSymmProof
  (presentation := "logic.formal.fol.proof_tree") (system := "logic.formal.fol.nd")
  (verdicts := [Silmaril.Consequence.FirstOrder.ND.Examples.eqSymmProof_checks])
  (derives := Silmaril.Consequence.FirstOrder.ND.Examples.eqSymm_derives)
  (derives_system := "logic.formal.fol.tree.derives")
  (title := "∀x ∀y ¬(x = y ∧ ¬ y = x), by equality elimination")
silmaril derivation logic.formal.fol.proof.not_a_hyp := Silmaril.Consequence.FirstOrder.ND.Examples.notAHyp
  (presentation := "logic.formal.fol.proof_tree") (system := "logic.formal.fol.nd")
  (verdicts := [Silmaril.Consequence.FirstOrder.ND.Examples.notAHyp_rejected])
  (title := "Rejected: ∀x ¬ succ x < succ x is not a hypothesis of the order theory")
silmaril derivation logic.formal.fol.proof.wrong_instance :=
    Silmaril.Consequence.FirstOrder.ND.Examples.wrongInstance
  (presentation := "logic.formal.fol.proof_tree") (system := "logic.formal.fol.nd")
  (verdicts := [Silmaril.Consequence.FirstOrder.ND.Examples.wrongInstance_rejected])
  (title := "Rejected: ∀-elimination at x claimed as the instance at succ x")
silmaril derivation logic.formal.fol.proof.unknown_rule := Silmaril.Consequence.FirstOrder.ND.Examples.unknownRule
  (presentation := "logic.formal.fol.proof_tree") (system := "logic.formal.fol.nd")
  (verdicts := [Silmaril.Consequence.FirstOrder.ND.Examples.unknownRule_rejected])
  (title := "Rejected: an unknown rule")

silmaril presentation logic.formal.mltt.bounded1.sexp := Silmaril.LogicGraph.Consequence.Formal.mlttBounded1Codec
  (title := "Bounded MLTT judgments (one universe level) as S-expressions")

silmaril logic_property logic.formal.mltt.bounded1.soundness := Silmaril.Consequence.TypeTheory.bounded_soundFor_one
  (role := "soundness") (system := "logic.formal.mltt.bounded1.derives")
  (title := "Extensional MLTT with 1 universe level is sound for its finite ZFSet towers (Lean universe 1)")
silmaril logic_property logic.formal.mltt.bounded2.soundness := Silmaril.Consequence.TypeTheory.bounded_soundFor_two
  (role := "soundness") (system := "logic.formal.mltt.bounded2.derives")
  (title := "Extensional MLTT with 2 universe levels is sound for its finite ZFSet towers (Lean universe 2)")
silmaril logic_property logic.formal.mltt.bounded3.soundness := Silmaril.Consequence.TypeTheory.bounded_soundFor_three
  (role := "soundness") (system := "logic.formal.mltt.bounded3.derives")
  (title := "Extensional MLTT with 3 universe levels is sound for its finite ZFSet towers (Lean universe 3)")
silmaril logic_property logic.formal.mltt.bounded1.no_empty :=
    Silmaril.Consequence.TypeTheory.bounded_empty_consistent_one
  (role := "consistency") (system := "logic.formal.mltt.bounded1.derives")
  (title := "⊢ 0 : 𝟘 is not derivable with 1 universe level")
silmaril logic_property logic.formal.mltt.bounded2.no_empty :=
    Silmaril.Consequence.TypeTheory.bounded_empty_consistent_two
  (role := "consistency") (system := "logic.formal.mltt.bounded2.derives")
  (title := "⊢ 0 : 𝟘 is not derivable with 2 universe levels")
silmaril logic_property logic.formal.mltt.bounded3.no_empty :=
    Silmaril.Consequence.TypeTheory.bounded_empty_consistent_three
  (role := "consistency") (system := "logic.formal.mltt.bounded3.derives")
  (title := "⊢ 0 : 𝟘 is not derivable with 3 universe levels")

silmaril presentation logic.formal.hol.coin.sexp := Silmaril.LogicGraph.Consequence.Formal.holCoinCodec
  (title := "HOL propositions over coinSig as S-expressions")

silmaril logic_property logic.formal.hol.coin.soundness := Silmaril.Consequence.HOL.kernelFrom_soundFor
  (arg := "Silmaril.Consequence.HOL.coinSig Silmaril.Consequence.HOL.cTheory")
  (role := "soundness") (system := "logic.formal.hol.coin.theory")
  (title := "HOL with the axiom c is sound for the models of c")
silmaril logic_property logic.formal.hol.coin.consistency := Silmaril.Consequence.HOL.cTheory_consistent
  (role := "consistency") (system := "logic.formal.hol.coin.theory")
  (title := "The theory c over coinSig does not derive ⊥ (its model interprets c as true)")

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
silmaril logic_problem logic.formal.hol.truth := Silmaril.Consequence.HOL.truthProp
  (presentation := "logic.formal.hol.prop.sexp")
  (derived := Silmaril.Consequence.HOL.truthProp_derived) (system := "logic.consequence.hol.kernel")
  (truth := Silmaril.Consequence.HOL.truthProp_true)
  (interpretation := "Silmaril.Consequence.HOL.points.{0} Silmaril.Consequence.HOL.initialSig")
  (title := "⊤, in pure HOL")
silmaril logic_problem logic.formal.hol.refl := Silmaril.Consequence.HOL.reflProp
  (presentation := "logic.formal.hol.prop.sexp")
  (derived := Silmaril.Consequence.HOL.reflProp_derived) (system := "logic.consequence.hol.kernel")
  (truth := Silmaril.Consequence.HOL.reflProp_true)
  (interpretation := "Silmaril.Consequence.HOL.points.{0} Silmaril.Consequence.HOL.initialSig")
  (title := "x = x for a free boolean x, by REFL")
silmaril logic_problem logic.formal.hol.excluded_middle := Silmaril.Consequence.HOL.emProp
  (presentation := "logic.formal.hol.prop.sexp")
  (derived := Silmaril.Consequence.HOL.emProp_derived) (system := "logic.formal.hol.classical")
  (title := "⊤ ∨ ¬⊤, by excluded middle from the classical axioms")
silmaril logic_problem logic.formal.fol.succ_irrefl := Silmaril.Consequence.FirstOrder.succIrrefl
  (presentation := "logic.formal.fol.sexp")
  (derived := Silmaril.Consequence.FirstOrder.ND.Examples.succIrrefl_derives)
  (system := "logic.formal.fol.tree.derives")
  (entailed := Silmaril.Consequence.FirstOrder.orderTheory_entails_succIrrefl)
  (entailed_by := "logic.formal.fol.consequence")
  (truth := Silmaril.Consequence.FirstOrder.succIrrefl_true)
  (interpretation := "Silmaril.Consequence.FirstOrder.inStructure Silmaril.Consequence.FirstOrder.natStructure")
  (title := "∀x ¬ succ x < succ x, from the order theory in every structure")

silmaril logic_problem logic.formal.mltt.zero := Silmaril.LogicGraph.Consequence.Formal.mlttZero
  (presentation := "logic.formal.mltt.bounded1.sexp")
  (derived := Silmaril.Consequence.TypeTheory.bounded_zero_derived)
  (system := "logic.formal.mltt.bounded1.derives")
  (truth := Silmaril.Consequence.TypeTheory.bounded_zero_true)
  (interpretation := "Silmaril.Consequence.TypeTheory.boundedTowers.{1} 1")
  (title := "⊢ 0 : ℕ with one universe level: derived, and true in every tower")

silmaril logic_problem logic.formal.hol.coin.c := Silmaril.Consequence.HOL.cProp
  (presentation := "logic.formal.hol.coin.sexp")
  (derived := Silmaril.Consequence.HOL.cProp_derived) (system := "logic.formal.hol.coin.theory")
  (truth := Silmaril.Consequence.HOL.cProp_true)
  (interpretation := "Silmaril.Consequence.HOL.pointsOf.{0} Silmaril.Consequence.HOL.coinSig Silmaril.Consequence.HOL.cTheory")
  (title := "c, over the user signature coinSig, from its axiom: true in the model c ↦ true")
silmaril logic_problem logic.formal.hol.coin.refl := Silmaril.Consequence.HOL.cReflProp
  (presentation := "logic.formal.hol.coin.sexp")
  (derived := Silmaril.Consequence.HOL.cReflProp_derived) (system := "logic.formal.hol.coin.kernel")
  (truth := Silmaril.Consequence.HOL.cReflProp_true)
  (interpretation := "Silmaril.Consequence.HOL.points.{0} Silmaril.Consequence.HOL.coinSig")
  (title := "c = c over coinSig, by REFL: true at every point of every model")

/-! ## Rows -/

silmaril logic_row logic.formal.row.fol
  (title := "First-order logic (unsorted), over orderSig")
  (variant := "Unsorted first-order logic with equality (=, relations, ⊤, ¬, ∧, ∀); signature orderSig (zero, succ, <); structures with nonempty carriers. Classical natural deduction over any signature with decidable symbols, sound for every structure; consistency of the order theory by the model ℕ.")
  (institution := "logic.institution.examples.ufol.inst")
  (systems := [logic.formal.fol.consequence, logic.formal.fol.truth_nat, logic.formal.fol.tree.derives])
  (interpretations := [Silmaril.Consequence.FirstOrder.inStructure])
  (presentations := [logic.formal.fol.sexp, logic.formal.fol.sequent, logic.formal.fol.proof_tree,
    logic.formal.fol.proof_lines])
  (properties := [logic.formal.fol.satisfiable, logic.formal.fol.nontrivial, logic.formal.fol.tree.soundness,
    logic.formal.fol.tree.soundness_nat, logic.formal.fol.tree.consistency])
  (problems := [logic.formal.fol.succ_irrefl])
  (derivation_systems := [logic.formal.fol.nd])
  (derivations := [logic.formal.fol.proof.succ_irrefl, logic.formal.fol.proof.eq_symm,
    logic.formal.fol.proof.not_a_hyp, logic.formal.fol.proof.wrong_instance, logic.formal.fol.proof.unknown_rule])
  (order := 1)
silmaril logic_row logic.formal.row.pa
  (title := "Peano arithmetic (and Robinson's Q)")
  (variant := "First-order PA: Q's axioms and the induction schema for every formula; classical natural deduction; standard model ℕ.")
  (systems := [logic.formal.pa.derives, logic.formal.q.derives, logic.formal.pa.truth, logic.formal.pa.derives.sexp,
    logic.formal.pa.tree.derives, logic.formal.q.tree.derives])
  (interpretations := [Silmaril.Consequence.Arithmetic.standard])
  (presentations := [logic.formal.pa.sexp, logic.formal.pa.sexp_words, logic.formal.pa.sequent,
    logic.formal.pa.proof_tree, logic.formal.pa.proof_lines])
  (properties := [logic.formal.pa.soundness, logic.formal.q.soundness, logic.formal.pa.consistency,
    logic.formal.q.consistency, logic.formal.pa.nontriviality, logic.formal.pa.sexp.consistency, logic.formal.q.pa,
    logic.formal.pa.tree.soundness, logic.formal.q.tree.soundness, logic.formal.pa.tree.consistency,
    logic.formal.q.tree.consistency])
  (problems := [logic.formal.pa.zero_add_zero, logic.formal.pa.zero_or_successor])
  (derivation_systems := [logic.formal.pa.nd, logic.formal.q.nd])
  (derivations := [logic.formal.pa.proof.zero_add, logic.formal.pa.proof.zero_add_zero,
    logic.formal.pa.proof.inst_add_zero, logic.formal.pa.proof.eq_symm, logic.formal.pa.proof.wrong_axiom,
    logic.formal.pa.proof.unknown_rule, logic.formal.pa.proof.missing_hyp])
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
  (variant := "HOL Light's kernel over its initial signature (bool, ind, =, @), on propositions; pure and with HOL Light's classical axioms ETA, SELECT and INFINITY. Standard semantics: models in Type u with bool as ULift Bool, ind as ULift ℕ, full function spaces, = as equality and @ as Hilbert choice; consistency is relative to the standard model at universe 0. Also over a user signature (coinSig, one boolean constant c) with the axiom c: sound for the models of its axioms, consistent by the model c ↦ true. No definition rules (new_definition, new_type_definition).")
  (systems := [logic.consequence.hol.kernel, logic.formal.hol.classical, logic.consequence.hol.seq,
    logic.formal.hol.coin.kernel, logic.formal.hol.coin.theory])
  (interpretations := [Silmaril.Consequence.HOL.points, Silmaril.Consequence.HOL.pointsOf])
  (presentations := [logic.formal.hol.prop.sexp, logic.formal.hol.sexp, logic.formal.hol.coin.sexp])
  (properties := [logic.formal.hol.soundness, logic.formal.hol.consistency,
    logic.formal.hol.classical.consistency, logic.formal.hol.nontriviality, logic.formal.hol.kernel.soundness,
    logic.formal.hol.coin.soundness, logic.formal.hol.coin.consistency])
  (problems := [logic.formal.hol.truth, logic.formal.hol.refl, logic.formal.hol.excluded_middle,
    logic.formal.hol.coin.c, logic.formal.hol.coin.refl])
  (order := 4)
silmaril logic_row logic.formal.row.mltt
  (title := "Martin-Löf type theory: extensional (bounded universes) and intensional (original rules)")
  (variant := "Extensional MLTT (Π, Σ, ℕ, 𝟎, 𝟏, identity with reflection, cumulative universes): consistent with 1, 2 or 3 universe levels, relative to Lean and ZFSet towers at Lean universes 1–3 (no inaccessibles assumed); the unbounded system is sound for assumed set hierarchies, whose existence is not proved, so its consistency is not claimed. Intensional MLTT (Martin-Löf's original rules with J, unbounded cumulative universes): consistent at every stage, by term realizability (a syntactic model, not a Lean-type model). Consistency here is nontriviality: some judgment is not derivable. The bounded systems are sound for their standard set-theoretic interpretation, finite ZFSet towers at fixed low universes, and do not derive ⊢ 0 : 𝟘. A standard interpretation in Lean types (rather than ZFSets) is not done: it needs a dependent interpretation of typing derivations.")
  (systems := [logic.formal.mltt.bounded1.derives, logic.formal.mltt.bounded2.derives,
    logic.formal.mltt.bounded3.derives, logic.consequence.mltt.extensional.derives,
    logic.consequence.mltt.extensional.entails, logic.consequence.mltt.intensional.derives,
    logic.consequence.mltt.intensional.entails])
  (presentations := [logic.formal.mltt.sexp, logic.formal.mltt.bounded1.sexp])
  (properties := [logic.formal.mltt.bounded1.consistency, logic.formal.mltt.bounded2.consistency,
    logic.formal.mltt.bounded3.consistency, logic.formal.mltt.intensional.consistency,
    logic.formal.mltt.extensional.soundness, logic.formal.mltt.intensional.soundness,
    logic.formal.mltt.bounded1.soundness, logic.formal.mltt.bounded2.soundness, logic.formal.mltt.bounded3.soundness,
    logic.formal.mltt.bounded1.no_empty, logic.formal.mltt.bounded2.no_empty, logic.formal.mltt.bounded3.no_empty])
  (problems := [logic.formal.mltt.zero])
  (order := 5)
