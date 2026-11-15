module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Games.Abstract.HostRunInf.Defs

/-!
# Productive runs of invocations: definitions

The infinite counterpart of `Silmaril.Wasm.Abstract.HostClosing`. `wasmEvFun` and `wasmEvPend`
observe finished behaviours and pending calls; neither can show a productive run (infinitely
many answered host calls). `wasmEvInf P s (a, vs)` is the set of productive runs of an
invocation, host-independently: Core runs under the universal host `anyHost` cut at their host
events (`CoreInf`). Each stream is witnessed by one coherent run, and its finite prefixes are
the actual event logs of that run (`coreInf_prefix`).

Theorems in `Silmaril.Wasm.Abstract.HostClosingInf.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The universal host: every answer and divergence is allowed. -/
def anyHost : HostSemantics H := fun _ _ _ _ => True

/-- **The productive runs of an invocation**, host-independently: Core runs under the
universal host cut at their host events, one coherent run per stream. -/
def wasmEvInf (P : Numerics.Profile) : PInf (wasmHostSig H) (Store H) (Nat × List Val) :=
  fun s p => {ω | CoreInf P anyHost (invoke s p.1 p.2) ω}

end Silmaril.Wasm.Abstract
