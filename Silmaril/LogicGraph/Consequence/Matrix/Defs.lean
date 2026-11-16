module

public import Silmaril.LogicGraph.Consequence.Defs
public import Silmaril.LogicGraph.Consequence.Concrete.Defs
public import Silmaril.Logic.HOLLight.SExp.Examples
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Examples
public import Silmaril.Logic.Consequence.Concrete.Thms
public import Silmaril.Logic.HOLLight.SExp.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Thms
public import Silmaril.Logic.TypeTheory.LambdaPi.Institution.Thms
public import Silmaril.Logic.Metamath.Text.RoundTrip
public import Silmaril.Logic.Metamath.Verify.Thms

/-!
# The logic graph: a coverage matrix of the consequence systems of its logics

One row per logic family and feature: abstract syntax, institution, derivability, semantic
consequence, soundness, identity/weakening/cut, substitution, completeness, concrete syntax,
concrete institution, concrete consequence systems, and registration in the explorer, kept apart from
the formal definitions: `explorer: abstract` (the abstract systems) and `explorer: concrete` (the
concrete institutions, rooms, corridors, comorphisms and systems). A `proved` concrete cell is a formal
statement; whether it is registered is the `explorer: concrete` cell. Each row names
the Lean declaration it is about and the theorems that support it. Lean checks that every name
exists when the matrix is registered (`consequence_matrix logic.consequence.coverage`, in
`Silmaril.LogicGraph.Consequence.Coverage.Defs`); the classification (`defined`, `proved`,
`registered`, `absent`, `not claimed`) and the note are this module's, and every `absent` or
`not claimed` cell says why.

Completeness is `not claimed` for every family. Where the library has a completeness theorem (λΠ
with its syntactic models of closed theories), it holds by construction and says nothing about a
semantics; the note says so.
-/

@[expose] public section

namespace Silmaril.LogicGraph.Consequence

/-- The coverage matrix: `(family, declaration, supporting theorems, feature, status, note)`. -/
def coverageRows : Silmaril.Project.MatrixRows := [
  ("HOL", ``Silmaril.Logic.HOLLight.Tm, [], "abstract syntax", "defined", "HOL Light types (Ty), constants (Const) and terms (Tm), locally nameless"),
  ("HOL", ``Silmaril.Logic.Institution.Metatheory.HOL.inst, [``Silmaril.Logic.Institution.Metatheory.HOL.logic_sound], "institution", "defined", "sentences are sequents H ⊢ p; the logic HOL.logic adds derivability"),
  ("HOL", ``Silmaril.Consequence.HOL.kernelFrom, [``Silmaril.Consequence.HOL.kernel], "derivability", "defined", "the HOL Light kernel on propositions, from axioms Δ; between sequents: LogicalSystem.listSys HOL.logic"),
  ("HOL", ``Silmaril.Consequence.HOL.seq, [``Silmaril.Consequence.HOL.gentzen, ``Silmaril.Consequence.HOL.globalSeq], "semantic consequence", "defined", "point-wise (seq, LK gentzen) and model-wise (globalSeq) readings, kept apart"),
  ("HOL", ``Silmaril.Consequence.HOL.kernel, [``Silmaril.Consequence.HOL.kernel_le_seq, ``Silmaril.Consequence.HOL.logic_listSys_le_roomSeq, ``Silmaril.Consequence.HOL.derives_le_globalSeq], "soundness", "proved", ""),
  ("HOL", ``Silmaril.Consequence.HOL.kernelFrom, [``Silmaril.Consequence.HOL.kernelFrom_closed, ``Silmaril.Consequence.HOL.seq_closed], "identity, weakening, cut", "proved", ""),
  ("HOL", ``Silmaril.Consequence.HOL.kernelFrom, [``Silmaril.Consequence.HOL.kernelFrom_substitutive_ty, ``Silmaril.Consequence.HOL.kernelFrom_substitutive_free, ``Silmaril.Consequence.HOL.seq_substitutive_ty, ``Silmaril.Consequence.HOL.seq_substitutive_free], "substitution", "proved", "along well-formed INST_TYPE and type-respecting INST"),
  ("HOL", ``Silmaril.Consequence.HOL.seq, [], "completeness", "not claimed", "the standard semantics is incomplete for the kernel"),
  ("HOL", ``Silmaril.Logic.HOLLight.SExp.encodeTm, [``Silmaril.Logic.HOLLight.SExp.decodeTm_eq_some_iff, ``Silmaril.Logic.HOLLight.SExp.parseTm_printTm, ``Silmaril.Logic.HOLLight.SExp.Examples.idEqId], "concrete syntax", "proved", "S-expressions; the decoder accepts exactly the canonical forms; bytes round trip for every term; examples and rejected inputs in HOLLight/SExp/Examples.lean"),
  ("HOL", ``Silmaril.Consequence.Concrete.holInst, [``Silmaril.Consequence.Concrete.holToAbstract_modelExpansive, ``Silmaril.Consequence.Concrete.holRoom_seq_iff], "concrete institution", "proved", "formal: one signature; a model-expansive comorphism into the HOL institution (registration: the explorer: concrete column)"),
  ("HOL", ``Silmaril.Consequence.Concrete.holKernel, [``Silmaril.Consequence.Concrete.holKernel_ofProp_iff, ``Silmaril.Consequence.Concrete.holKernel_le_holSeq, ``Silmaril.Consequence.Concrete.holKernel_closed], "concrete consequence systems", "proved", "consequence preserved and reflected by the relation to the abstract syntax"),
  ("HOL", ``Silmaril.LogicGraph.Consequence.holKernel, [], "explorer: abstract", "registered", "logic.consequence.hol.* (kernel, seq, sequent.derives, sequent.entails)"),
  ("HOL", ``Silmaril.LogicGraph.Consequence.Concrete.holKernel, [``Silmaril.Consequence.Concrete.holInst, ``Silmaril.Consequence.Concrete.holToAbstract, ``Silmaril.Consequence.Concrete.holCorridor], "explorer: concrete", "registered", "logic.consequence.concrete.hol.institution, logic.consequence.concrete.hol.room, logic.consequence.concrete.hol.corridor, logic.consequence.concrete.hol.to_abstract (to logic.institution.metatheory.hol.institution); systems logic.consequence.concrete.hol.kernel, logic.consequence.concrete.hol.seq, logic.consequence.concrete.hol.sequent.entails, with soundness and translations to and from the abstract systems"),
  ("extensional MLTT", ``Silmaril.Logic.TypeTheory.ExtensionalMLTT.EJdg, [], "abstract syntax", "defined", "scoped terms ETm k, contexts ECtx, judgments Γ ⊢ a ≡ b : A"),
  ("extensional MLTT", ``Silmaril.Logic.TypeTheory.ExtensionalMLTT.Institution.inst, [``Silmaril.Logic.TypeTheory.ExtensionalMLTT.Institution.logic_sound], "institution", "defined", "models are set hierarchies"),
  ("extensional MLTT", ``Silmaril.Consequence.TypeTheory.extensionalDerives, [], "derivability", "defined", "premises are whole judgments (hypothetical derivability); the context Γ is part of each judgment"),
  ("extensional MLTT", ``Silmaril.Consequence.TypeTheory.extensionalEntails, [], "semantic consequence", "defined", "validity in every set hierarchy"),
  ("extensional MLTT", ``Silmaril.Consequence.TypeTheory.extensionalDerives, [``Silmaril.Consequence.TypeTheory.extensionalDerives_le_entails], "soundness", "proved", ""),
  ("extensional MLTT", ``Silmaril.Consequence.TypeTheory.extensionalDerives, [``Silmaril.Consequence.TypeTheory.extensionalDerives_closed, ``Silmaril.Consequence.TypeTheory.extensionalEntails_closed], "identity, weakening, cut", "proved", ""),
  ("extensional MLTT", ``Silmaril.Consequence.TypeTheory.extensionalDerives, [], "substitution", "absent", "weakening and substitution of the context Γ are admissible rules of the type theory, over judgments; not laws of this relation"),
  ("extensional MLTT", ``Silmaril.Consequence.TypeTheory.extensionalEntails, [], "completeness", "not claimed", ""),
  ("extensional MLTT", ``Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.encodeJdg, [``Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.decodeJdg_eq_some_iff, ``Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.parseJdg_printJdg, ``Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.legalNames_of_parseJdg, ``Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Examples.polyId], "concrete syntax", "proved", "S-expressions; bytes round trip exactly for the judgments whose names are legal atoms; examples and rejected inputs in ExtensionalMLTT/SExp/Examples.lean"),
  ("extensional MLTT", ``Silmaril.Consequence.Concrete.mlttInst, [``Silmaril.Consequence.Concrete.mlttToAbstract_modelExpansive, ``Silmaril.Consequence.Concrete.mlttRoom_seq_iff], "concrete institution", "proved", ""),
  ("extensional MLTT", ``Silmaril.Consequence.Concrete.mlttDerives, [``Silmaril.Consequence.Concrete.mlttDerives_ofJdg_iff, ``Silmaril.Consequence.Concrete.mlttDerives_le_entails, ``Silmaril.Consequence.Concrete.mlttDerives_closed], "concrete consequence systems", "proved", ""),
  ("extensional MLTT", ``Silmaril.LogicGraph.Consequence.extensionalEntails, [], "explorer: abstract", "registered", "logic.consequence.mltt.extensional.*"),
  ("extensional MLTT", ``Silmaril.Consequence.Concrete.mlttDerives, [``Silmaril.Consequence.Concrete.mlttInst, ``Silmaril.Consequence.Concrete.mlttToAbstract, ``Silmaril.Consequence.Concrete.mlttCorridor], "explorer: concrete", "registered", "logic.consequence.concrete.mltt.institution, logic.consequence.concrete.mltt.room, logic.consequence.concrete.mltt.corridor, logic.consequence.concrete.mltt.to_abstract; systems logic.consequence.concrete.mltt.derives, logic.consequence.concrete.mltt.entails, with soundness and translations to and from the abstract systems"),
  ("intensional MLTT", ``Silmaril.Logic.TypeTheory.IntensionalMLTT.Term, [], "abstract syntax", "defined", "Martin-Löf's original rules with J"),
  ("intensional MLTT", ``Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution.inst, [``Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution.logic_sound], "institution", "defined", "per universe stage; models are code capacities (realizability)"),
  ("intensional MLTT", ``Silmaril.Consequence.TypeTheory.intensionalDerives, [], "derivability", "defined", "proof trees within the stage, with judgment hypotheses"),
  ("intensional MLTT", ``Silmaril.Consequence.TypeTheory.intensionalEntails, [], "semantic consequence", "defined", "realizability"),
  ("intensional MLTT", ``Silmaril.Consequence.TypeTheory.intensionalDerives, [``Silmaril.Consequence.TypeTheory.intensionalDerives_le_entails], "soundness", "proved", ""),
  ("intensional MLTT", ``Silmaril.Consequence.TypeTheory.intensionalDerives, [``Silmaril.Consequence.TypeTheory.intensionalDerives_closed, ``Silmaril.Consequence.TypeTheory.intensionalEntails_closed], "identity, weakening, cut", "proved", ""),
  ("intensional MLTT", ``Silmaril.Consequence.TypeTheory.intensionalDerives, [], "substitution", "absent", "context substitution is an admissible rule over judgments (IntensionalMLTT.Substitution), not a law of this relation"),
  ("intensional MLTT", ``Silmaril.Consequence.TypeTheory.intensionalEntails, [], "completeness", "not claimed", ""),
  ("intensional MLTT", ``Silmaril.Logic.TypeTheory.IntensionalMLTT.Term, [], "concrete syntax", "absent", "not yet; the extensional pattern applies"),
  ("intensional MLTT", ``Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution.inst, [], "concrete institution", "absent", "needs the concrete syntax first"),
  ("intensional MLTT", ``Silmaril.Consequence.TypeTheory.intensionalDerives, [], "concrete consequence systems", "absent", "needs the concrete syntax first"),
  ("intensional MLTT", ``Silmaril.LogicGraph.Consequence.intensionalDerives, [], "explorer: abstract", "registered", "logic.consequence.mltt.intensional.*, at the full stage ⊤"),
  ("intensional MLTT", ``Silmaril.Logic.TypeTheory.IntensionalMLTT.Term, [], "explorer: concrete", "absent", "no concrete syntax"),
  ("λΠ modulo rewriting", ``Silmaril.Logic.TypeTheory.LambdaPi.Judgment, [], "abstract syntax", "defined", "per calculus (a signature with rewrite rules)"),
  ("λΠ modulo rewriting", ``Silmaril.Logic.TypeTheory.LambdaPi.Calculus.logic, [], "institution", "defined", "paired with the syntactic models of closed theories"),
  ("λΠ modulo rewriting", ``Silmaril.Consequence.TypeTheory.lambdaPiDerives, [], "derivability", "defined", ""),
  ("λΠ modulo rewriting", ``Silmaril.Logic.TypeTheory.LambdaPi.Calculus.logic, [], "semantic consequence", "absent", "closed-theory models coincide with derivability by construction (Calculus.logic_sound, logic_complete): no semantics of λΠ"),
  ("λΠ modulo rewriting", ``Silmaril.Logic.TypeTheory.LambdaPi.Calculus.logic, [], "soundness", "absent", "no semantics to be sound for"),
  ("λΠ modulo rewriting", ``Silmaril.Consequence.TypeTheory.lambdaPiDerives, [``Silmaril.Consequence.TypeTheory.lambdaPiDerives_closed], "identity, weakening, cut", "proved", ""),
  ("λΠ modulo rewriting", ``Silmaril.Consequence.TypeTheory.lambdaPiDerives, [], "substitution", "absent", "context substitution is an admissible rule over judgments, not a law of this relation"),
  ("λΠ modulo rewriting", ``Silmaril.Logic.TypeTheory.LambdaPi.Calculus.logic, [], "completeness", "not claimed", "only for the syntactic models, by construction"),
  ("λΠ modulo rewriting", ``Silmaril.Logic.TypeTheory.LambdaPi.Judgment, [], "concrete syntax", "absent", "not yet in this library (Dedukti text is a candidate)"),
  ("λΠ modulo rewriting", ``Silmaril.Logic.TypeTheory.LambdaPi.Calculus.logic, [], "concrete institution", "absent", "needs the concrete syntax first"),
  ("λΠ modulo rewriting", ``Silmaril.Consequence.TypeTheory.lambdaPiDerives, [], "concrete consequence systems", "absent", "needs the concrete syntax first"),
  ("λΠ modulo rewriting", ``Silmaril.Consequence.TypeTheory.lambdaPiDerives, [], "explorer: abstract", "absent", "a family over calculi; no instance registered"),
  ("λΠ modulo rewriting", ``Silmaril.Logic.TypeTheory.LambdaPi.Judgment, [], "explorer: concrete", "absent", "no concrete syntax"),
  ("Metamath", ``Silmaril.Logic.Metamath.Grammar.TAssertion, [], "abstract syntax", "defined", "tree assertions: disjoint-variable conditions, floating and essential hypotheses, conclusion"),
  ("Metamath", ``Silmaril.Logic.Institution.Metatheory.Metamath.room, [``Silmaril.Logic.Institution.Metatheory.Metamath.entailment], "institution", "defined", "a room per grammar and the entailment system MMSig ⥤ ER; the model functor (reducts along rewrites) is not constructed"),
  ("Metamath", ``Silmaril.Consequence.Metamath.derives, [``Silmaril.Logic.Metamath.Grammar.TDerivable], "derivability", "defined", "Metamath's proof system: a derivation applies an assertion only under a DV-safe substitution"),
  ("Metamath", ``Silmaril.Consequence.Metamath.entails, [``Silmaril.Logic.Metamath.Model.Satisfies], "semantic consequence", "defined", "Carneiro's models"),
  ("Metamath", ``Silmaril.Consequence.Metamath.derives, [``Silmaril.Consequence.Metamath.derives_le_entails, ``Silmaril.Logic.Institution.Metatheory.Metamath.sound], "soundness", "proved", "Carneiro, Models for Metamath, Theorem 1"),
  ("Metamath", ``Silmaril.Consequence.Metamath.derives, [``Silmaril.Consequence.Metamath.derives_closed, ``Silmaril.Consequence.Metamath.entails_closed], "identity, weakening, cut", "proved", "cut is cut admissibility (infinitely many variables)"),
  ("Metamath", ``Silmaril.Consequence.Metamath.derives, [``Silmaril.Consequence.Metamath.derives_rewrite, ``Silmaril.Consequence.Metamath.derives_substitutive], "substitution", "proved", "along syntax rewrites"),
  ("Metamath", ``Silmaril.Consequence.Metamath.entails, [], "completeness", "not claimed", ""),
  ("Metamath", ``Silmaril.Logic.Metamath.Text.parse, [``Silmaril.Logic.Metamath.Text.parse_print, ``Silmaril.Logic.Metamath.Verify.verifyText_sound], "concrete syntax", "proved", "Metamath's own .mm text: parse ∘ print round trip on valid sources; the verifier is sound"),
  ("Metamath", ``Silmaril.Logic.Institution.Metatheory.Metamath.room, [], "concrete institution", "absent", "no institution over .mm text; the abstract room has no model functor either"),
  ("Metamath", ``Silmaril.Consequence.Metamath.derives, [], "concrete consequence systems", "absent", "the verifier reads .mm text into the derivability above"),
  ("Metamath", ``Silmaril.LogicGraph.Consequence.setMMDerives, [], "explorer: abstract", "registered", "logic.consequence.metamath.set_mm.*"),
  ("Metamath", ``Silmaril.Logic.Metamath.Text.parse, [], "explorer: concrete", "absent", "the .mm text format is formal (parse_print) but no institution over it is defined or registered"),
  ("PA (peano.mm)", ``Silmaril.Consequence.Metamath.PA, [], "abstract syntax", "defined", "axioms transcribed from the Metamath database, over its grammar"),
  ("PA (peano.mm)", ``Silmaril.Logic.Institution.Metatheory.Metamath.room, [], "institution", "defined", "the Metamath room of its grammar"),
  ("PA (peano.mm)", ``Silmaril.Consequence.Metamath.paTheory, [], "derivability", "defined", "derivability from the axioms: Γ ⊢_T A iff T ∪ Γ derives A"),
  ("PA (peano.mm)", ``Silmaril.LogicGraph.Consequence.paEntails, [``Silmaril.Consequence.roomTheorySeq], "semantic consequence", "defined", "consequence over the models of the axioms"),
  ("PA (peano.mm)", ``Silmaril.Consequence.Metamath.paTheory, [``Silmaril.Consequence.Metamath.theory_le_theoryEntails], "soundness", "proved", ""),
  ("PA (peano.mm)", ``Silmaril.Consequence.Metamath.paTheory, [``Silmaril.Consequence.Metamath.theory_closed, ``Silmaril.Consequence.theorySys_closed], "identity, weakening, cut", "proved", ""),
  ("PA (peano.mm)", ``Silmaril.Consequence.Metamath.paTheory, [``Silmaril.Consequence.Metamath.theory_rewrite, ``Silmaril.Consequence.Metamath.theory_substitutive], "substitution", "proved", "along rewrites mapping the axioms to theorems (presentation morphisms)"),
  ("PA (peano.mm)", ``Silmaril.LogicGraph.Consequence.paEntails, [], "completeness", "not claimed", ""),
  ("PA (peano.mm)", ``Silmaril.Logic.Metamath.Text.parse, [``Silmaril.Logic.Metamath.Text.parse_print], "concrete syntax", "proved", "Metamath's .mm text"),
  ("PA (peano.mm)", ``Silmaril.Logic.Institution.Metatheory.Metamath.room, [], "concrete institution", "absent", "as for Metamath"),
  ("PA (peano.mm)", ``Silmaril.Consequence.Metamath.paTheory, [], "concrete consequence systems", "absent", "as for Metamath: the verifier reads .mm text into the derivability"),
  ("PA (peano.mm)", ``Silmaril.Consequence.Metamath.paTheory, [], "explorer: abstract", "registered", "logic.consequence.metamath.pa.*"),
  ("PA (peano.mm)", ``Silmaril.Logic.Metamath.Text.parse, [], "explorer: concrete", "absent", "as for Metamath"),
  ("ZF (set.mm)", ``Silmaril.Consequence.Metamath.ZF0, [], "abstract syntax", "defined", "axioms transcribed from the Metamath database, over its grammar"),
  ("ZF (set.mm)", ``Silmaril.Logic.Institution.Metatheory.Metamath.room, [], "institution", "defined", "the Metamath room of its grammar"),
  ("ZF (set.mm)", ``Silmaril.Consequence.Metamath.zfTheory, [], "derivability", "defined", "derivability from the axioms: Γ ⊢_T A iff T ∪ Γ derives A"),
  ("ZF (set.mm)", ``Silmaril.LogicGraph.Consequence.zfEntails, [``Silmaril.Consequence.roomTheorySeq], "semantic consequence", "defined", "consequence over the models of the axioms"),
  ("ZF (set.mm)", ``Silmaril.Consequence.Metamath.zfTheory, [``Silmaril.Consequence.Metamath.theory_le_theoryEntails, ``Silmaril.Consequence.Metamath.zfTheory_le_zfcTheory], "soundness", "proved", ""),
  ("ZF (set.mm)", ``Silmaril.Consequence.Metamath.zfTheory, [``Silmaril.Consequence.Metamath.theory_closed, ``Silmaril.Consequence.theorySys_closed], "identity, weakening, cut", "proved", ""),
  ("ZF (set.mm)", ``Silmaril.Consequence.Metamath.zfTheory, [``Silmaril.Consequence.Metamath.theory_rewrite, ``Silmaril.Consequence.Metamath.theory_substitutive], "substitution", "proved", "along rewrites mapping the axioms to theorems (presentation morphisms)"),
  ("ZF (set.mm)", ``Silmaril.LogicGraph.Consequence.zfEntails, [], "completeness", "not claimed", ""),
  ("ZF (set.mm)", ``Silmaril.Logic.Metamath.Text.parse, [``Silmaril.Logic.Metamath.Text.parse_print], "concrete syntax", "proved", "Metamath's .mm text"),
  ("ZF (set.mm)", ``Silmaril.Logic.Institution.Metatheory.Metamath.room, [], "concrete institution", "absent", "as for Metamath"),
  ("ZF (set.mm)", ``Silmaril.Consequence.Metamath.zfTheory, [], "concrete consequence systems", "absent", "as for Metamath: the verifier reads .mm text into the derivability"),
  ("ZF (set.mm)", ``Silmaril.Consequence.Metamath.zfTheory, [], "explorer: abstract", "registered", "logic.consequence.metamath.zf.*"),
  ("ZF (set.mm)", ``Silmaril.Logic.Metamath.Text.parse, [], "explorer: concrete", "absent", "as for Metamath"),
  ("ZFC (set.mm)", ``Silmaril.Consequence.Metamath.ZFC, [], "abstract syntax", "defined", "axioms transcribed from the Metamath database, over its grammar"),
  ("ZFC (set.mm)", ``Silmaril.Logic.Institution.Metatheory.Metamath.room, [], "institution", "defined", "the Metamath room of its grammar"),
  ("ZFC (set.mm)", ``Silmaril.Consequence.Metamath.zfcTheory, [], "derivability", "defined", "derivability from the axioms: Γ ⊢_T A iff T ∪ Γ derives A"),
  ("ZFC (set.mm)", ``Silmaril.LogicGraph.Consequence.zfcEntails, [``Silmaril.Consequence.roomTheorySeq], "semantic consequence", "defined", "consequence over the models of the axioms"),
  ("ZFC (set.mm)", ``Silmaril.Consequence.Metamath.zfcTheory, [``Silmaril.Consequence.Metamath.theory_le_theoryEntails, ``Silmaril.Consequence.Metamath.setMMZFCTheory_sound_zfSet], "soundness", "proved", ""),
  ("ZFC (set.mm)", ``Silmaril.Consequence.Metamath.zfcTheory, [``Silmaril.Consequence.Metamath.theory_closed, ``Silmaril.Consequence.theorySys_closed], "identity, weakening, cut", "proved", ""),
  ("ZFC (set.mm)", ``Silmaril.Consequence.Metamath.zfcTheory, [``Silmaril.Consequence.Metamath.theory_rewrite, ``Silmaril.Consequence.Metamath.theory_substitutive], "substitution", "proved", "along rewrites mapping the axioms to theorems (presentation morphisms)"),
  ("ZFC (set.mm)", ``Silmaril.LogicGraph.Consequence.zfcEntails, [], "completeness", "not claimed", ""),
  ("ZFC (set.mm)", ``Silmaril.Logic.Metamath.Text.parse, [``Silmaril.Logic.Metamath.Text.parse_print], "concrete syntax", "proved", "Metamath's .mm text"),
  ("ZFC (set.mm)", ``Silmaril.Logic.Institution.Metatheory.Metamath.room, [], "concrete institution", "absent", "as for Metamath"),
  ("ZFC (set.mm)", ``Silmaril.Consequence.Metamath.zfcTheory, [], "concrete consequence systems", "absent", "as for Metamath: the verifier reads .mm text into the derivability"),
  ("ZFC (set.mm)", ``Silmaril.Consequence.Metamath.zfcTheory, [], "explorer: abstract", "registered", "logic.consequence.metamath.zfc.*"),
  ("ZFC (set.mm)", ``Silmaril.Logic.Metamath.Text.parse, [], "explorer: concrete", "absent", "as for Metamath")
]

end Silmaril.LogicGraph.Consequence
