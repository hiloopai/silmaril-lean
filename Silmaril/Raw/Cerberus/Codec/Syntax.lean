module

public import Silmaril.Cerberus.Codec.WellFormed.Defs
public import Silmaril.Semantics.CPort.Formats.SExp.Syntax.Defs

/-!
# The cerberus-tagged dialect as a `TreeSyntax`

`taggedSyntax` is the tree layer of the cerberus-tagged dialect
(`Silmaril.Semantics.CPort.Formats.SExp`): the shared Lisp reader followed by `taggedDoc?`, printed
with `printTagged` and one final newline. Its re-printing restriction
`taggedSyntax.checked` is canonical by the generic law, and composing it with
the `document` codec gives the Cerberus document syntax, canonical again by
the generic law. `parseDocument` adds the map-order, digest and enum checks on
top, so its success implies success of the composed syntax.

The tree-level round trip `taggedSyntax.RoundTripOn _` is not yet proved: the
document reader re-checks the spelling instead.
-/

@[expose] public section

namespace Silmaril.Cerberus.Codec.WellFormed

open Silmaril.Formats Silmaril.Formats.SExpEncoding Silmaril.TaggedCodec

/-- The cerberus-tagged dialect on tagged trees. -/
def taggedSyntax : TreeSyntax String Tree where
  print t := printTagged t ++ "\n"
  parse := parseTagged?

/-- Cerberus documents: the canonical tagged syntax composed with the codec. -/
def documentSyntax : TreeSyntax String Document := taggedSyntax.checked.withCodec document

theorem documentSyntax_canonical : documentSyntax.Canonical :=
  (taggedSyntax.checked_canonical).withCodec document

/-- `parseDocument` refines the composed syntax. -/
theorem documentSyntax_parse_of_parseDocument {text : String} {doc : Document}
    (h : parseDocument text = .ok doc) : documentSyntax.parse text = some doc := by
  obtain ⟨s, t, hs, ht, hl, hd, _⟩ := parseDocument_eq_ok_iff.1 h
  have hp : taggedSyntax.parse text = some t := by
    simp [taggedSyntax, parseTagged?, hs, ht]
  have hc : taggedSyntax.checked.parse text = some t :=
    (taggedSyntax.checked_parse_eq_some).2 ⟨hp, hl⟩
  simp [documentSyntax, TreeSyntax.withCodec, hc, hd]

/-- The document printer is the composed printer. -/
theorem documentSyntax_print (doc : Document) :
    documentSyntax.print doc = printTagged (document.enc doc) ++ "\n" := rfl

end Silmaril.Cerberus.Codec.WellFormed
