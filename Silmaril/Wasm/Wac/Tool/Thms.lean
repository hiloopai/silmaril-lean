module

public import Silmaril.Wasm.Wac.Tool.Defs
public import Silmaril.Wasm.Wac.Text.Thms
public import Silmaril.Wasm.Wac.Targets.Thms

/-!
# The `wasm-wac` tool: what its commands guarantee

* `parseDoc_print`: the document `wasm-wac print` writes (for a well-formed document)
  is read back by every command to the same document; `wasm-wac check` tests the same
  on its input, and also for `pretty` (whose layout is not covered by
  `Silmaril.Wasm.Wac.Text.parse_renderWith`: it omits the space around some symbols).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Tool

open Silmaril.Wasm.Wac.Text

theorem parseDoc_eq (src : String) :
    parseDoc src = match parse src with
      | some d => .ok d
      | none => .error (if (lex src.toList).isSome then "syntax error" else "lexical error") := by
  unfold parseDoc parse
  cases h : lex src.toList with
  | none => rfl
  | some ts => cases hd : Parse.document ts <;> simp [hd]

theorem parseDoc_print (d : Document) (h : wf d = true) : parseDoc (print d) = .ok d := by
  rw [parseDoc_eq, parse_print d h]

end Silmaril.Wasm.Wac.Tool
