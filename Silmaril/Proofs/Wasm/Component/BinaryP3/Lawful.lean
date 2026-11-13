module

public import Silmaril.Wasm.Component.BinaryP3.Defs
public import Silmaril.Wasm.Component.Binary.Thms

/-!
# Proofs: the WASI 0.3 component grammars are lawful

The grammars of `Silmaril.Wasm.Component.BinaryP3.Defs` that differ from
`Silmaril.Wasm.Component.Binary`'s are lawful (`Grammar.Lawful`), by `grammar_lawful`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryP3

open Silmaril.Parse.ByteParse
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Component.Binary (DefType defTypeG)

instance lawful_flagG (what : String) : (flagG what).Lawful := by grammar_lawful
instance lawful_canonG : canonG.Lawful := by grammar_lawful

instance lawful_sectionG (c : GrammarE Ast) (t : Grammar DefType) (ht : NonEmpty t.G)
    [c.Lawful] [t.Lawful] : (sectionG c t ht).Lawful := by
  unfold sectionG
  grammar_lawful

instance lawful_componentG : ∀ k, (componentG k).Lawful
  | 0 => inferInstanceAs (GrammarE.ofGrammar (fail : Grammar Ast)).Lawful
  | k + 1 => by
    have := lawful_componentG k
    unfold componentG
    grammar_lawful

end Silmaril.Wasm.Component.BinaryP3
