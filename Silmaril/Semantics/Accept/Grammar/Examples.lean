module

public import Silmaril.Semantics.Accept.Grammar.Thms

/-! # Grammar presentations: worked examples and regression tests

The headline example is the grammar `S → ( S ) | ε` over bytes (`(` is `40`, `)` is `41`):
its language is exactly the words `(ⁿ )ⁿ` (`lang_parens`, both soundness and completeness of
the grammar), and the Bool checker `parensCheck` decides that language (`decides_parens`).
Further examples combine it with a one-word grammar by union and reverse it. Every `example`
is checked when the library builds.
-/

@[expose] public section

namespace Silmaril.Accept.GrammarExamples

open Silmaril.Accept Silmaril.Accept.Grammar

/-- `S → ( S ) | ε` over bytes. -/
abbrev parens : ContextFreeGrammar UInt8 := nested 40 41

/-- The Bool checker for `(ⁿ )ⁿ`. -/
def parensCheck : List UInt8 → Bool := nestedCheck 40 41

/-- The grammar derives exactly `(ⁿ )ⁿ`. -/
theorem lang_parens :
    lang parens = {w | ∃ n, w = List.replicate n 40 ++ List.replicate n 41} :=
  lang_nested 40 41

/-- Soundness and completeness of the grammar, separately. -/
example : Grammar.Sound parens (nestedLang 40 41) := (presents_nested 40 41).sound
example : Grammar.Complete parens (nestedLang 40 41) := (presents_nested 40 41).complete

/-- The checker decides the grammar's language. -/
theorem decides_parens : Decides parensCheck (lang parens) := decides_nestedCheck 40 41

/-- The accepted set of the checker is the grammar's language. -/
example : ofBool parensCheck = lang parens := decides_lang_iff_ofBool_eq.1 decides_parens

/-! ## Checker regression tests -/

example : parensCheck [] = true := by decide
example : parensCheck [40, 41] = true := by decide
example : parensCheck [40, 40, 40, 41, 41, 41] = true := by decide
example : parensCheck [40, 41, 40, 41] = false := by decide
example : parensCheck [41, 40] = false := by decide
example : parensCheck [40, 40, 41] = false := by decide

/-! ## Membership in the grammar language, through the checker -/

example : [40, 40, 41, 41] ∈ lang parens := (decides_parens _).1 (by decide)
example : [40, 41, 40, 41] ∉ lang parens := fun h => absurd ((decides_parens _).2 h) (by decide)
example : ([] : List UInt8) ∈ lang parens := by rw [lang_parens]; exact ⟨0, rfl⟩

/-- A two-step derivation by hand: `S ⇒ ( S ) ⇒ ( )`. -/
example : parens.Derives [.nonterminal ()] [.terminal 40, .terminal 41] :=
  (ContextFreeGrammar.Produces.single ⟨nestedStep 40 41, by simp,
      ContextFreeRule.Rewrites.input_output⟩).trans_produces
    ⟨nestedStop, by simp, ContextFreeRule.Rewrites.cons _ (.head _)⟩

/-! ## Union and reversal -/

/-- `(ⁿ )ⁿ` or the single word `0`. -/
noncomputable abbrev parensOrZero : ContextFreeGrammar UInt8 := union parens (word [0])

example : lang parensOrZero = lang parens ∪ {[0]} := by rw [lang_union, lang_word]

example : Decides (fun w => parensCheck w || decide (w = [0])) (lang parensOrZero) :=
  decides_parens.union_grammar (by rw [lang_word]; exact fun _ => decide_eq_true_iff)

example : [0] ∈ lang parensOrZero := by rw [lang_union, lang_word]; exact Or.inr rfl

/-- The reversed grammar `S → ) S ( | ε` is decided by checking the reversed word. -/
example : Decides (parensCheck ∘ List.reverse) (lang parens.reverse) :=
  decides_parens.reverse_grammar

example : [41, 41, 40, 40] ∈ lang parens.reverse :=
  (decides_parens.reverse_grammar _).1 (by decide)

/-! ## Context-freeness -/

example : Language.IsContextFree (T := UInt8) (nestedLang 40 41 ∪ {[0]} : Set (List UInt8)) :=
  isContextFree_union (isContextFree_nestedLang 40 41) (isContextFree_singleton [0])

end Silmaril.Accept.GrammarExamples
