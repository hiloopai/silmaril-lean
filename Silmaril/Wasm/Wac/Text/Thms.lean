module

public import Silmaril.Proofs.Wasm.Wac.Text.TokOk

/-!
# WAC text: verified reading and printing

The round trip of the WAC text front end (`Silmaril.Wasm.Wac.Text`), with proofs in
`Silmaril.Proofs.Wasm.Wac.Text.*`:

* `parse_print : wf d = true → parse (print d) = some d`: printing a well-formed
  document and parsing the text gives the document back (no normal form is needed: the
  AST has exactly the information of the text up to layout, comments and `%` escapes);
* `parse_renderWith`: the same for every layout of the printed tokens with any
  nonempty whitespace (space, tab, line feed, carriage return) after each token and
  any whitespace before doc lines;
* the pieces: `lexAux_renderWith` (every layout of well-formed tokens lexes back),
  `renderWith_good` (the text has no character `lex` rejects), `document_pr` (the
  parser inverts the printer on tokens), `document_tokOk` (the printer writes
  well-formed tokens).

`wf` asks for identifiers, strings and doc comments that can be written, package names
and paths in the lexer's syntax, versions valid for `semver` and read back whole by the
lexer, and nonempty tuples, variants, records, flags and enums (`wac-parser` rejects the
empty ones).

Every theorem is proved; no `sorry` or axiom beyond Lean's.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

/-- A separator of a layout: nonempty whitespace without form feed. -/
def SepOk (s : List Char) : Prop := ∃ c t, s = c :: t ∧ isWs c = true ∧ t.all isWs = true ∧
  ∀ x ∈ s, x ≠ '\x0c'

theorem good_of_sep {x : Char} (h : isWs x = true) (hf : x ≠ '\x0c') : badChar x = false := by
  simp only [isWs, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((h | h) | h) | h) | h <;> subst h <;> first | decide | exact absurd rfl hf

/-- Every layout of a well-formed document parses back to it. -/
theorem parse_renderWith (d : Document) (h : wf d = true) (sep ind : Nat → List Char)
    (hsep : ∀ i, SepOk (sep i))
    (hind : ∀ i, (ind i).all isWs = true ∧ ∀ x ∈ ind i, x ≠ '\x0c') :
    (lex (renderWith sep ind 0 (Pr.document d))).bind Parse.document = some d := by
  have htok := document_tokOk d h
  have hgood := renderWith_good sep ind
    (fun i x hx => by
      obtain ⟨c, t, he, hc, ht, hf⟩ := hsep i
      have : isWs x = true := by
        rw [he] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hc
        · exact List.all_eq_true.mp ht x hx
      exact good_of_sep this (hf x hx))
    (fun i x hx => good_of_sep (List.all_eq_true.mp (hind i).1 x hx) ((hind i).2 x hx))
    _ 0 htok
  have hlex := lexAux_renderWith sep ind
    (fun i => by obtain ⟨c, t, he, hc, ht, -⟩ := hsep i; exact ⟨c, t, he, hc, ht⟩)
    (fun i => (hind i).1) _ 0 htok
  simp [lex, inputOk_of_good hgood, hlex, document_pr d h]

/-- The round trip: printing a well-formed document and parsing it gives it back. -/
theorem parse_print (d : Document) (h : wf d = true) : parse (print d) = some d := by
  have := parse_renderWith d h (fun _ => [' ']) (fun _ => [])
    (fun _ => ⟨' ', [], rfl, by decide, by decide, by simp⟩) (fun _ => ⟨by decide, by simp⟩)
  simpa [parse, print, render] using this

end Silmaril.Wasm.Wac.Text
