module

public import Silmaril.Logic.SecondOrderArithmetic.MetamathSyntax
public import Silmaril.Logic.Metamath.SecondOrder.Arithmetic

@[expose] public section

/-! First-order arithmetic is a syntactically selected fragment. The native
arithmetic embedding commutes with our independent encoding. This is not a
Q/PA derivability equivalence. -/
namespace Silmaril.Logic.SecondOrderArithmetic

open Silmaril.Logic.Metamath Grammar

variable {N : Type}

inductive FirstOrder : Formula N → Prop
  | equal (t u) : FirstOrder (.equal t u)
  | less (t u) : FirstOrder (.less t u)
  | neg {φ} : FirstOrder φ → FirstOrder (.neg φ)
  | imp {φ ψ} : FirstOrder φ → FirstOrder ψ → FirstOrder (.imp φ ψ)
  | iff {φ ψ} : FirstOrder φ → FirstOrder ψ → FirstOrder (.iff φ ψ)
  | conj {φ ψ} : FirstOrder φ → FirstOrder ψ → FirstOrder (.conj φ ψ)
  | all (x) {φ} : FirstOrder φ → FirstOrder (.all x φ)
  | ex (x) {φ} : FirstOrder φ → FirstOrder (.ex x φ)

def Term.toArithTree : Term SecondOrder.V → Tree SecondOrder.AL SecondOrder.V
  | .var q => .node .tvar [.var q]
  | .zero => .node .t0 []
  | .succ t => .node .tS [t.toArithTree]
  | .add t u => .node .tpl [t.toArithTree, u.toArithTree]
  | .mul t u => .node .tmu [t.toArithTree, u.toArithTree]

private theorem embTree_var (q : SecondOrder.V) :
    SecondOrder.embTree (.var q) = .var q := rfl

theorem Term.arithmetic_embedding (t : Term SecondOrder.V) :
    SecondOrder.embTree t.toArithTree = t.toTree := by
  induction t <;> simp_all [toArithTree, toTree, SecondOrder.embTree_node, SecondOrder.AL.emb, embTree_var]

def Formula.toArithTree : Formula SecondOrder.V → Option (Tree SecondOrder.AL SecondOrder.V)
  | .equal t u => some (.node .weq [t.toArithTree, u.toArithTree])
  | .less t u => some (.node .wlt [t.toArithTree, u.toArithTree])
  | .member _ _ | .setEqual _ _ | .setAll _ _ | .setEx _ _ => none
  | .neg φ => return .node .wn [← φ.toArithTree]
  | .imp φ ψ => return .node .wi [← φ.toArithTree, ← ψ.toArithTree]
  | .iff φ ψ => return .node .wb [← φ.toArithTree, ← ψ.toArithTree]
  | .conj φ ψ => return .node .wa [← φ.toArithTree, ← ψ.toArithTree]
  | .all q φ => return .node .wal [← φ.toArithTree, .var q]
  | .ex q φ => return .node .wex [← φ.toArithTree, .var q]

/-- A concrete arithmetic syntax witness and its commuting embedding. -/
theorem FirstOrder.arithmetic_embedding {φ : Formula SecondOrder.V} (h : FirstOrder φ) :
    ∃ t, φ.toArithTree = some t ∧ SecondOrder.embTree t = φ.toTree := by
  induction h with
  | equal t u =>
    refine ⟨.node .weq [t.toArithTree, u.toArithTree], ?_, ?_⟩
    · simp [Formula.toArithTree]
    · simp [Formula.toTree, SecondOrder.embTree_node, SecondOrder.AL.emb, Term.arithmetic_embedding]
  | less t u =>
    refine ⟨.node .wlt [t.toArithTree, u.toArithTree], ?_, ?_⟩
    · simp [Formula.toArithTree]
    · simp [Formula.toTree, SecondOrder.embTree_node, SecondOrder.AL.emb, Term.arithmetic_embedding]
  | neg h ih =>
    obtain ⟨a, ha, ea⟩ := ih
    refine ⟨.node .wn [a], ?_, ?_⟩
    · simp [Formula.toArithTree, ha]
    · simp [Formula.toTree, SecondOrder.embTree_node, SecondOrder.AL.emb, ea]
  | imp h h' ih ih' =>
    obtain ⟨a, ha, ea⟩ := ih
    obtain ⟨b, hb, eb⟩ := ih'
    refine ⟨.node .wi [a, b], ?_, ?_⟩
    · simp [Formula.toArithTree, ha, hb]
    · simp [Formula.toTree, SecondOrder.embTree_node, SecondOrder.AL.emb, ea, eb]
  | iff h h' ih ih' =>
    obtain ⟨a, ha, ea⟩ := ih
    obtain ⟨b, hb, eb⟩ := ih'
    refine ⟨.node .wb [a, b], ?_, ?_⟩
    · simp [Formula.toArithTree, ha, hb]
    · simp [Formula.toTree, SecondOrder.embTree_node, SecondOrder.AL.emb, ea, eb]
  | conj h h' ih ih' =>
    obtain ⟨a, ha, ea⟩ := ih
    obtain ⟨b, hb, eb⟩ := ih'
    refine ⟨.node .wa [a, b], ?_, ?_⟩
    · simp [Formula.toArithTree, ha, hb]
    · simp [Formula.toTree, SecondOrder.embTree_node, SecondOrder.AL.emb, ea, eb]
  | all q h ih =>
    obtain ⟨a, ha, ea⟩ := ih
    refine ⟨.node .wal [a, .var q], ?_, ?_⟩
    · simp [Formula.toArithTree, ha]
    · simp [Formula.toTree, SecondOrder.embTree_node, SecondOrder.AL.emb, embTree_var, ea]
  | ex q h ih =>
    obtain ⟨a, ha, ea⟩ := ih
    refine ⟨.node .wex [a, .var q], ?_, ?_⟩
    · simp [Formula.toArithTree, ha]
    · simp [Formula.toTree, SecondOrder.embTree_node, SecondOrder.AL.emb, embTree_var, ea]

end Silmaril.Logic.SecondOrderArithmetic
