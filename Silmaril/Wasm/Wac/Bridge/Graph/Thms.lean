module

public import Silmaril.Wasm.Wac.Bridge.Graph.Defs
public import Silmaril.Proofs.Wasm.Wac.Bridge.Lower

/-!
# WAC bridge: the encoding agrees with the direct translation

**`lower_encode`**: for an elaborated graph `g` without value kinds (`NoValue`, values
are outside `Lower.graph`), if `encode nom g = .ok c` then `Lower.graph S c = .ok
(toGraph S g)`, for every assignment `S` of interfaces to component indices. Reading the
WAT of a composition back as a composition graph gives the graph read off the
elaborator's output directly: the encoder's index bookkeeping (types, functions,
instances, components, packages) is right, an imported instance's type declares its
function exports, and instantiation arguments, aliases and exports refer to the
intended items. With `encode_profile`, the encoding is in the composition profile.

Not covered: the *types* in the WAT (`Lower.graph` keeps placeholder types for
declared imports and reads only the function exports of instance types), and the
semantics of the packages (`S` is arbitrary).

Proof: `Silmaril.Proofs.Wasm.Wac.Bridge.Lower`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary

/-- **The encoding of a graph lowers to its direct translation.** -/
theorem encode_correct (S : Nat → PkgSig) {nom : NomTable} {g : CGraph} {c : Ast} (hnv : NoValue g)
    (h : encode nom g = .ok c) : Profile c ∧ Lower.graph S c = .ok (toGraph S g) :=
  ⟨encode_profile h, lower_encode S hnv h⟩

end Silmaril.Wasm.Wac.Bridge
