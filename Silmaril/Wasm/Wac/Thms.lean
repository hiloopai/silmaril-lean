module

public import Silmaril.Wasm.Wac.Profile.Thms
public import Silmaril.Wasm.Wac.Graph.Thms
public import Silmaril.Wasm.Wac.Seq.Thms
public import Silmaril.Wasm.Wac.Lower.Defs
public import Silmaril.Wasm.Wac.Example.Thms

/-!
# WAC (WebAssembly Compositions)

See `docs/projects/wasm-components.md`.

* `Silmaril.Wasm.Wac.Profile`: the composition profile of component WAT (the IR) and its
  round trip;
* `Silmaril.Wasm.Wac.Graph`: composition graphs, their translation to the component IR
  (promotion and merging of imports) and compositionality;
* `Silmaril.Wasm.Wac.Seq`: plugging (sequential composition) and its associativity;
* `Silmaril.Wasm.Wac.Lower`: profile WAT to composition graphs (and, with
  `Binary.lower`, to the component IR);
* `Silmaril.Wasm.Wac.Example`: a worked composition.
-/
