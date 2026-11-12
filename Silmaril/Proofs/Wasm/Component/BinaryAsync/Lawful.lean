module

public import Silmaril.Wasm.Component.BinaryAsync.Defs
public import Silmaril.Wasm.Component.Binary.Thms

/-!
# Proofs: the async component grammars are lawful

The grammars of `Silmaril.Wasm.Component.BinaryAsync.Defs` are lawful (`Grammar.Lawful`), by
`grammar_lawful`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryAsync

open Silmaril.Parse.ByteParse
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Component.Binary

theorem canonXBody_lawful {b : UInt8} {g : Grammar CanonX} (h : canonXBody b = some g) :
    g.Lawful := by
  unfold canonXBody at h
  grammar_lawful_of h

instance lawful_canonXG : canonXG.Lawful := Grammar.Lawful.tagged fun _ _ h => canonXBody_lawful h

instance lawful_sectionXG (c : GrammarE AstX) (t : Grammar DefType) (ht : NonEmpty t.G)
    [c.Lawful] [t.Lawful] : (sectionXG c t ht).Lawful := by
  unfold sectionXG
  grammar_lawful

instance lawful_componentXG : ∀ k, (componentXG k).Lawful
  | 0 => inferInstanceAs (GrammarE.ofGrammar (fail : Grammar AstX)).Lawful
  | k + 1 => by
    have := lawful_componentXG k
    unfold componentXG
    grammar_lawful

end Silmaril.Wasm.Component.BinaryAsync
