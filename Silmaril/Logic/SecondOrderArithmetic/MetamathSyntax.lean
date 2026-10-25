module

public import Silmaril.Logic.SecondOrderArithmetic.Semantics
public import Mathlib.Data.List.Basic

@[expose] public section

/-! Encoding and checked decoding of the independent syntax in the native
Metamath syntax trees. The round trips prove injectivity without identifying
formulas that merely have the same meaning. -/
namespace Silmaril.Logic.SecondOrderArithmetic

open Silmaril.Logic.Metamath Grammar

def Term.toTree : Term SecondOrder.V → Tree SecondOrder.L SecondOrder.V
  | .var namex => .node .tvar [.var namex]
  | .zero => .node .t0 []
  | .succ t => .node .tS [t.toTree]
  | .add t u => .node .tpl [t.toTree, u.toTree]
  | .mul t u => .node .tmu [t.toTree, u.toTree]

def Term.ofTree : Tree SecondOrder.L SecondOrder.V → Option (Term SecondOrder.V)
  | .node .tvar [.var namex] => some (.var namex)
  | .node .t0 [] => some .zero
  | .node .tS [t] => return .succ (← Term.ofTree t)
  | .node .tpl [t, u] => return .add (← Term.ofTree t) (← Term.ofTree u)
  | .node .tmu [t, u] => return .mul (← Term.ofTree t) (← Term.ofTree u)
  | _ => none

@[simp] theorem Term.ofTree_toTree (t : Term SecondOrder.V) : Term.ofTree t.toTree = some t := by
  induction t <;> simp_all [toTree, ofTree]

theorem Term.toTree_injective : Function.Injective Term.toTree := by
  intro t u h
  simpa using congrArg Term.ofTree h

def Formula.toTree : Formula SecondOrder.V → Tree SecondOrder.L SecondOrder.V
  | .equal t u => .node .weq [t.toTree, u.toTree]
  | .less t u => .node .wlt [t.toTree, u.toTree]
  | .member t nameX => .node .wel [.var nameX, t.toTree]
  | .setEqual nameX nameY => .node .wseq [.var nameX, .var nameY]
  | .neg φ => .node .wn [φ.toTree]
  | .imp φ ψ => .node .wi [φ.toTree, ψ.toTree]
  | .iff φ ψ => .node .wb [φ.toTree, ψ.toTree]
  | .conj φ ψ => .node .wa [φ.toTree, ψ.toTree]
  | .all namex φ => .node .wal [φ.toTree, .var namex]
  | .ex namex φ => .node .wex [φ.toTree, .var namex]
  | .setAll namex φ => .node .wsal [φ.toTree, .var namex]
  | .setEx namex φ => .node .wsex [φ.toTree, .var namex]

def Formula.ofTree : Tree SecondOrder.L SecondOrder.V → Option (Formula SecondOrder.V)
  | .node .weq [t, u] => return .equal (← Term.ofTree t) (← Term.ofTree u)
  | .node .wlt [t, u] => return .less (← Term.ofTree t) (← Term.ofTree u)
  | .node .wel [.var nameX, t] => return .member (← Term.ofTree t) nameX
  | .node .wseq [.var nameX, .var nameY] => some (.setEqual nameX nameY)
  | .node .wn [φ] => .neg <$> Formula.ofTree φ
  | .node .wi [φ, ψ] => return .imp (← Formula.ofTree φ) (← Formula.ofTree ψ)
  | .node .wb [φ, ψ] => return .iff (← Formula.ofTree φ) (← Formula.ofTree ψ)
  | .node .wa [φ, ψ] => return .conj (← Formula.ofTree φ) (← Formula.ofTree ψ)
  | .node .wal [φ, .var namex] => .all namex <$> Formula.ofTree φ
  | .node .wex [φ, .var namex] => .ex namex <$> Formula.ofTree φ
  | .node .wsal [φ, .var namex] => .setAll namex <$> Formula.ofTree φ
  | .node .wsex [φ, .var namex] => .setEx namex <$> Formula.ofTree φ
  | _ => none

@[simp] theorem Formula.ofTree_toTree (φ : Formula SecondOrder.V) : Formula.ofTree φ.toTree = some φ := by
  induction φ <;> simp_all [toTree, ofTree]

theorem Formula.toTree_injective : Function.Injective Formula.toTree := by
  intro φ ψ h
  simpa using congrArg Formula.ofTree h

variable {ctx : SecondOrder.V → SecondOrder.C → Prop}

/-- The context may distinguish number and set names; both requirements are
explicit. This convenience lemma uses a context accepting all names at both sorts;
`toTree_surjective` below works in arbitrary name-only contexts. -/
theorem Term.toTree_hasSort (hn : ∀ namex, ctx namex .nvar) (t : Term SecondOrder.V) :
    SecondOrder.grammar.HasSort ctx t.toTree .term := by
  induction t with
  | var namex =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p rfl
    exact .var (hn _)
  | zero  =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_nil_left, List.not_mem_nil]
    intro p hp
    cases hp
  | succ t ih =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p rfl
    exact ih
  | add t u ih ih' =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl) <;> assumption
  | mul t u ih ih' =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl) <;> assumption

theorem Formula.toTree_hasSort (hn : ∀ namex, ctx namex .nvar) (hs : ∀ nameX, ctx nameX .svar)
    (φ : Formula SecondOrder.V) : SecondOrder.grammar.HasSort ctx φ.toTree .wff := by
  induction φ with
  | equal t u =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl) <;> exact Term.toTree_hasSort hn _
  | less t u =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl) <;> exact Term.toTree_hasSort hn _
  | member t nameX =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl)
    · exact .var (hs _)
    · exact Term.toTree_hasSort hn _
  | setEqual nameX nameY =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl) <;> exact .var (hs _)
  | neg φ ih =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p rfl
    exact ih
  | imp φ ψ ih ih' =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl) <;> assumption
  | iff φ ψ ih ih' =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl) <;> assumption
  | conj φ ψ ih ih' =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl) <;> assumption
  | all namex φ ih =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl)
    · exact ih
    · exact .var (hn _)
  | ex namex φ ih =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl)
    · exact ih
    · exact .var (hn _)
  | setAll namex φ ih =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl)
    · exact ih
    · exact .var (hs _)
  | setEx namex φ ih =>
    apply HasSort.node rfl
    simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl)
    · exact ih
    · exact .var (hs _)



/-- Native contexts containing only the two name sorts have no opaque term
or formula metavariables. This is the concrete-expression fragment. -/
def NameContext (ctx : SecondOrder.V → SecondOrder.C → Prop) : Prop :=
  ∀ q c, ctx q c → c = .nvar ∨ c = .svar

private def Realizes : SecondOrder.C → Tree SecondOrder.L SecondOrder.V → Prop
  | .nvar, t | .svar, t => ∃ q, t = .var q
  | .term, t => ∃ a : Term SecondOrder.V, a.toTree = t
  | .wff, t => ∃ φ : Formula SecondOrder.V, φ.toTree = t
  | _, _ => False

private theorem realizes_of_hasSort {ctx : SecondOrder.V → SecondOrder.C → Prop}
    (hc : NameContext ctx) {t : Tree SecondOrder.L SecondOrder.V} {c : SecondOrder.C}
    (h : SecondOrder.grammar.HasSort ctx t c) : Realizes c t := by
  induction h with
  | var hv =>
    rcases hc _ _ hv with rfl | rfl <;> exact ⟨_, rfl⟩
  | @node l args hlen _ ih =>
    cases l with
    | tvar =>
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .nvar, .x ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      exact ⟨.var va, rfl⟩
    | t0 =>
      have ha : args = [] := List.length_eq_zero_iff.mp hlen
      subst ha
      exact ⟨.zero, rfl⟩
    | tS =>
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .term, .t ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      exact ⟨.succ va, rfl⟩
    | tpl =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .term, .t ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      obtain ⟨vb, ha1⟩ := ih (b, .term, .u ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha1
      exact ⟨.add va vb, rfl⟩
    | tmu =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .term, .t ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      obtain ⟨vb, ha1⟩ := ih (b, .term, .u ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha1
      exact ⟨.mul va vb, rfl⟩
    | wn =>
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .wff, .ph ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      exact ⟨.neg va, rfl⟩
    | wi =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .wff, .ph ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      obtain ⟨vb, ha1⟩ := ih (b, .wff, .ps ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha1
      exact ⟨.imp va vb, rfl⟩
    | wb =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .wff, .ph ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      obtain ⟨vb, ha1⟩ := ih (b, .wff, .ps ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha1
      exact ⟨.iff va vb, rfl⟩
    | wa =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .wff, .ph ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      obtain ⟨vb, ha1⟩ := ih (b, .wff, .ps ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha1
      exact ⟨.conj va vb, rfl⟩
    | wal =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .wff, .ph ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      obtain ⟨vb, ha1⟩ := ih (b, .nvar, .x ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha1
      exact ⟨.all vb va, rfl⟩
    | wex =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .wff, .ph ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      obtain ⟨vb, ha1⟩ := ih (b, .nvar, .x ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha1
      exact ⟨.ex vb va, rfl⟩
    | wsal =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .wff, .ph ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      obtain ⟨vb, ha1⟩ := ih (b, .svar, .X ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha1
      exact ⟨.setAll vb va, rfl⟩
    | wsex =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .wff, .ph ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      obtain ⟨vb, ha1⟩ := ih (b, .svar, .X ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha1
      exact ⟨.setEx vb va, rfl⟩
    | weq =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .term, .t ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      obtain ⟨vb, ha1⟩ := ih (b, .term, .u ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha1
      exact ⟨.equal va vb, rfl⟩
    | wlt =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .term, .t ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      obtain ⟨vb, ha1⟩ := ih (b, .term, .u ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha1
      exact ⟨.less va vb, rfl⟩
    | wel =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .svar, .X ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      obtain ⟨vb, ha1⟩ := ih (b, .term, .t ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha1
      exact ⟨.member vb va, rfl⟩
    | wseq =>
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
      obtain ⟨va, ha0⟩ := ih (a, .svar, .X ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha0
      obtain ⟨vb, ha1⟩ := ih (b, .svar, .Y ) (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
      subst ha1
      exact ⟨.setEqual va vb, rfl⟩

/-- Every well-sorted concrete native term has an independent syntax preimage. -/
theorem Term.toTree_surjective {ctx : SecondOrder.V → SecondOrder.C → Prop}
    (hc : NameContext ctx) {t : Tree SecondOrder.L SecondOrder.V}
    (h : SecondOrder.grammar.HasSort ctx t .term) :
    ∃ a : Term SecondOrder.V, a.toTree = t := realizes_of_hasSort hc h

/-- The reverse syntax correspondence excludes opaque formula metavariables. -/
theorem Formula.toTree_surjective {ctx : SecondOrder.V → SecondOrder.C → Prop}
    (hc : NameContext ctx) {t : Tree SecondOrder.L SecondOrder.V}
    (h : SecondOrder.grammar.HasSort ctx t .wff) :
    ∃ φ : Formula SecondOrder.V, φ.toTree = t := realizes_of_hasSort hc h

end Silmaril.Logic.SecondOrderArithmetic
