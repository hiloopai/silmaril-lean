module

public import Silmaril.Logic.SAT.CNF.Defs
public import Silmaril.Logic.ManyValued.Defs

@[expose] public section

/-! # Valuation semantics of CNF over arbitrary atom types -/

namespace Silmaril.Logic.SAT.Institution

open Silmaril.Logic.ManyValued

universe u v w

/-- A signed atom. Keeping polarity separate lets signature maps identify atoms freely. -/
structure Literal (A : Type u) where
  atom : A
  positive : Bool

/-- A disjunction of signed atoms. -/
abbrev Clause (A : Type u) := List (Literal A)

/-- A SAT problem is a conjunction of clauses over the given signature. -/
abbrev Problem (A : Type u) := List (Clause A)

variable {A : Type u} {B : Type v}

def Literal.rename (f : A → B) (l : Literal A) : Literal B := ⟨f l.atom, l.positive⟩

def Problem.rename (f : A → B) (F : Problem A) : Problem B := F.map (·.map (Literal.rename f))

/-- Read the existing integer syntax using its variable and polarity operations. -/
def Problem.ofCNF (F : SAT.CNF) : Problem Nat := F.map (·.map fun l => ⟨l.var, l.pos⟩)

/-- Reduce a target valuation by precomposition with a signature map. -/
def reduct {V : Type w} (f : A → B) (v : B → V) : A → V := v ∘ f

/-- A partial Boolean assignment, with `none` for an atom left unassigned. -/
abbrev PartialValuation (A : Type u) := A → Option Bool

abbrev TotalValuation (A : Type u) := A → Bool

abbrev K3Valuation (A : Type u) := A → K3

abbrev EvidenceValuation (A : Type u) := A → FDE

/-- Interpret unassigned atoms as the strong Kleene unknown. -/
def PartialValuation.toK3 (v : PartialValuation A) : K3Valuation A := K3.ofOptionBool ∘ v

/-- Evaluate a signed atom using the chosen negation. -/
def Literal.evalWith {V : Type w} (neg : V → V) (v : A → V) (l : Literal A) : V :=
  if l.positive then v l.atom else neg (v l.atom)

/-- Fold a clause as a disjunction, with `bot` for the empty clause. -/
def Clause.evalWith {V : Type w} (bot : V) (neg : V → V) (disj : V → V → V)
    (v : A → V) (C : Clause A) : V :=
  C.foldr (fun l acc => disj (l.evalWith neg v) acc) bot

namespace Problem

/-- Interpret signed atoms, clause disjunction and problem conjunction in a truth algebra. -/
def evalWith {V : Type w} (top bot : V) (neg : V → V) (conj disj : V → V → V)
    (v : A → V) (F : Problem A) : V :=
  F.foldr (fun C acc => conj (Clause.evalWith bot neg disj v C) acc) top

/-- Classical evaluation under a total Boolean assignment. -/
def eval (v : TotalValuation A) (F : Problem A) : Bool :=
  F.all fun C => C.any fun l => v l.atom == l.positive

/-- Compositional strong Kleene evaluation. -/
def evalK3 (v : K3Valuation A) (F : Problem A) : K3 :=
  F.evalWith (K3.ofBool true) (K3.ofBool false) K3.neg K3.conj K3.disj v

/-- Evaluate a partial Boolean assignment using the typed strong Kleene algebra. -/
def evalK3Partial (v : PartialValuation A) (F : Problem A) : K3 := F.evalK3 v.toK3

/-- Compatibility adapter for strong Kleene evaluation with `Option Bool` input and output. -/
def evalK3Option (v : PartialValuation A) (F : Problem A) : Option Bool :=
  (F.evalK3Partial v).toOptionBool

/-- Compositional Belnap/FDE evaluation (conjunction and disjunction in the truth order). -/
def evalEvidence (v : EvidenceValuation A) (F : Problem A) : FDE :=
  F.evalWith FDE.tt FDE.ff FDE.neg FDE.conj FDE.disj v

end Problem

/-- A total assignment completes a partial one when it agrees at every known atom. -/
def Completes (v : PartialValuation A) (t : TotalValuation A) : Prop :=
  ∀ a b, v a = some b → t a = b

/-- Every completion of the reduct lifts to a completion of the target valuation. -/
def CompletionCovers (f : A → B) (v : PartialValuation B) : Prop :=
  ∀ s, Completes (reduct f v) s → ∃ t, Completes v t ∧ reduct f t = s

/-- Independent universal satisfaction and refutation over total completions. -/
noncomputable def Problem.completionEvidence (v : PartialValuation A) (F : Problem A) : FDE :=
  letI := Classical.propDecidable
  FDE.ofBits (decide (∀ t, Completes v t → F.eval t = true))
    (decide (∀ t, Completes v t → F.eval t = false))

/-- Supervaluation is true or false when all completions agree, and unknown when they split. -/
noncomputable def Problem.superEvalK3 (v : PartialValuation A) (F : Problem A) : K3 :=
  (F.completionEvidence v).toK3?.getD .unknown

/-- The legacy projection of the strong Kleene supervaluation verdict. -/
noncomputable def Problem.superEval (v : PartialValuation A) (F : Problem A) : Option Bool :=
  (F.superEvalK3 v).toOptionBool

end Silmaril.Logic.SAT.Institution
