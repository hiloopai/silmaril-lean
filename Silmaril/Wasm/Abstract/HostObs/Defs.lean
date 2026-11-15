module

public import Silmaril.Wasm.Abstract.HostClosing.Defs

/-!
# Core 3.0 invocations against the logged closed semantics with host calls: definitions

`CoreEnd c e`: a stuck Core configuration `c` is the end `e` of a logged behaviour of
`wasmEvFun` (`Silmaril.Wasm.Abstract.HostClosing`): returned values `ws` in store `s₂`
are the values `ws` in `s₂` with the empty frame; a trap is `[trap]` (the logged end
forgets the store). Thrown exceptions and divergence are no finished Core end.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- A stuck Core end and a finished end of the logged closed semantics agree. -/
def CoreEnd (c : Config H) : End (Store H) (List Val ⊕ Nat) → Prop
  | .ret (.inl ws) s₂ => c = ⟨s₂, {}, vals ws⟩
  | .trap => ∃ s₂, c = ⟨s₂, {}, [.trap]⟩
  | _ => False

end Silmaril.Wasm.Abstract
