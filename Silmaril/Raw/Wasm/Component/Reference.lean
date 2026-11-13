module

public import Silmaril.Raw.Wasm.Component.Embedding
public import Silmaril.Raw.Wasm.Component.Validation.Check
public import Silmaril.Raw.Wasm.Component.Validation.Core3
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Instance
public import Silmaril.Raw.Wasm.Component.Engine.Lime1.Properties

/-!
# The unrefined proofs of the component-model reference copy

The definitions of the copy are in `Silmaril.Wasm.Component.Reference.**.Defs`, reached through
the header `Silmaril.Wasm.Component.Reference.Defs`. The theorems that are not yet refined stay
in the Raw modules re-exported here (the roots of the copy: the embedding API, validation and
its Core 3.0 profile, and the Core 3.0 and Lime1 engines with their laws). Proof modules of
the component region that use those theorems import this module; headers do not.
-/
