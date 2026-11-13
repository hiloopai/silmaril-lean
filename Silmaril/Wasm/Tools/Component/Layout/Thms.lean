module

public import Silmaril.Wasm.Tools.Component.Layout.Defs
public import Silmaril.Proofs.Wasm.Tools.Component.Layout.RoundTrip
public import Silmaril.Proofs.Wasm.Tools.Component.Layout.Named

/-!
# wasmprinter's layout: verified

Proofs in `Silmaril.Proofs.Wasm.Tools.Component.Layout.RoundTrip`:

* `tk_lay : E.on = false → tk (lay E m s) = toks s`: without names, the layout (line breaks,
  `(;i;)` comments) keeps the tokens of the S-expression, in every mode and with any
  counters;
* `lex_render`: the lexer reads `render d l` as `tk l`; together, the text is lexed into the
  same tokens as `Wat.print`'s;
* `renderF_eq`: the fast renderer (a `String` accumulator) equals `render`;
  `printW_eq : printW c = printWSpec c`;
* `read_printW : Wat.read (printW c) = some (Wat.norm c)`: the verified reader reads what
  `wasm-tools print` writes back to the normal form of the component.

Proofs in `Silmaril.Proofs.Wasm.Tools.Component.Layout.Named`, for the text with names
(`printWN`, what the tool writes):

* `printWN_eq_printW : NoNames c → printWN c = printW c`: on a component with nothing to name
  (no `component-name` section and no printed `producers` section, at any depth) the named
  text is the verified text (`lay_silent`: the layout does not depend on a naming context
  without names);
* `read_printWN : NoNames c → Wat.read (printWN c) = some (Wat.norm c)`;
* `printBytesW_read` (below): what `wasm-tools print` writes for such a binary is read back
  to the normal form of its decoding.

Not proved: that the layout is wasmprinter's (tested byte for byte against wasm-tools 1.262.0,
`tools/wasm-tools/tests/compval/print-parse.sh`), and the text with names when there are
names: `$name`s replace indices, so the verified reader does not read it; `parse` reads it
through `Wac.WatX`'s resolver (tested by the same script).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Layout

/-- **`wasm-tools print` round trip** on a binary with nothing to name. -/
theorem printBytesW_read {b : ByteArray} {s : String} (h : printBytesW b = .ok s) :
    ∃ c, Silmaril.Wasm.Component.BinaryP3.parse b = .ok c ∧
      (NoNames c → Wat.read s = some (Wat.norm c)) := by
  unfold printBytesW at h
  split at h
  · next c hc =>
    split at h
    · cases h
    · cases h; exact ⟨c, hc, read_printWN⟩
  · cases h

end Silmaril.Wasm.Tools.Component.Layout
