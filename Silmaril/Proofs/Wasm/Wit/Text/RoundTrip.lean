module

public import Silmaril.Proofs.Wasm.Wit.Text.Document
public import Silmaril.Proofs.Wasm.Wit.Text.Ok

/-!
# WIT text: the round trip

`parse (print d) = some (Document.norm d)` for every printable document
(`parse_print`), for every layout of the printed tokens (`parse_render`), and the
consequence that the text determines the normal form (`norm_eq_of_print_eq`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

/-- Any layout of the printer's tokens parses to the normal form: whitespace and the
choice of breaks do not matter. -/
theorem parse_render (d : Document) (h : printable d = true) (ps : List PTok)
    (hps : toks ps = toks (prDocument d)) (n : Nat) :
    parse (String.ofList (render n ps)) = some (Document.norm d) := by
  have hok : ∀ p ∈ ps, p.1.ok = true := by
    intro p hp
    have hm : p.1 ∈ toks ps := List.mem_map_of_mem hp
    rw [hps] at hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    rw [← he]
    exact List.all_eq_true.mp (okL_prDocument d h) q hq
  unfold parse
  rw [String.toList_ofList, lex_render n ps hok, Option.bind_some, hps]
  exact document_prDocument d h

/-- The round trip: a printable document reads back to its normal form. -/
theorem parse_print (d : Document) (h : printable d = true) :
    parse (print d) = some (Document.norm d) :=
  parse_render d h (prDocument d) rfl 0

/-- The printed text determines the normal form. -/
theorem norm_eq_of_print_eq {d e : Document} (hd : printable d = true) (he : printable e = true)
    (h : print d = print e) : Document.norm d = Document.norm e := by
  have h1 := parse_print d hd
  rw [h, parse_print e he] at h1
  exact (Option.some.inj h1).symm

end Silmaril.Wasm.Wit.Text
