module

public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Proofs.Wasm.Component.Binary.RoundTrip

/-!
# Component binaries: verified parsing

Proofs in `Silmaril.Proofs.Wasm.Component.Binary.RoundTrip`:

* `parse_sound : parse b = .ok c → (componentG (b.size + 1)).G b.data.toList c`
  (the parser's result is related to the whole input by the grammar);
* `parse_encode : encode c = some b → parse b = .ok c` (round trip; the
  encoder fails only on numbers or lengths of `2 ^ 32` or more);
* `componentG_functional`: the grammar is unambiguous.

Every production's parser is sound and complete for its grammar: the `Grammar.Lawful`
instances of `Silmaril.Proofs.Wasm.Component.Binary.Lawful` (`Grammar.sound`,
`Grammar.complete`, `GrammarE.complete`).
-/
