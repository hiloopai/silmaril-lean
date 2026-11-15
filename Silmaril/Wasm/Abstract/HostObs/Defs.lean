module

public import Silmaril.Wasm.Abstract.HostClosing.Defs
public import Silmaril.Games.Abstract.HostRun.Defs
public import Silmaril.Wasm.Abstract.HostClosingInf.Defs

/-!
# Core 3.0 invocations against the logged closed semantics with host calls: definitions

`CoreEnd c e`: a stuck Core configuration `c` is the end `e` of a logged behaviour of
`wasmEvFun` (`Silmaril.Wasm.Abstract.HostClosing`): returned values `ws` in store `s₂`
are the values `ws` in `s₂` with the empty frame; a trap is `[trap]` (the logged end
forgets the store). Thrown exceptions and divergence are no finished Core end.

`wasmHostObs host s a vs`: the observations of the invocation against the relational host
`coreHostRel host` (`HostRun.hostObs` of `wasmEvFun` and `wasmEvPend`). `CoreObs P host s a vs o`:
what the observation `o` is in Core 3.0: a run of `invoke s a vs` to a stuck end agreeing with
`e` (`done`), divergence (`hostDiv`), or a run to a stuck end blocked at a host call (`blocked`).
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

/-- The observations of an invocation against the relational host `coreHostRel host`. -/
def wasmHostObs (host : HostSemantics H) (s : Store H) (a : Nat) (vs : List Val) :
    Set (HObs (wasmHostSig H) (Store H) (List Val ⊕ Nat)) :=
  hostObs (coreHostRel host) wasmEvFun wasmEvPend s (a, vs)

/-- An observation, in Core 3.0: the behaviour of `invoke s a vs` it stands for. -/
def CoreObs (P : Numerics.Profile) (host : HostSemantics H) (s : Store H) (a : Nat)
    (vs : List Val) : HObs (wasmHostSig H) (Store H) (List Val ⊕ Nat) → Prop
  | .done _ e => ∃ c, Steps P host (invoke s a vs) c ∧ (∀ c', ¬ Step P host c c') ∧ CoreEnd c e
  | .hostDiv _ _ => Diverges P host (invoke s a vs)
  | .blocked _ _ => ∃ c : Config H, Steps P host (invoke s a vs) c ∧
      Silmaril.Wasm.Abstract.Pending host c.store c.code ∧ ∀ c', ¬ Step P host c c'

end Silmaril.Wasm.Abstract
