module

public import Silmaril.Wasm.Abstract.HostClosingInf.Defs
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Games.Abstract.HostRunInf.Thms
import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Basic

/-!
# Productive runs of invocations: theorems

Proofs in `Silmaril.Proofs.Wasm.Abstract.HostClosingInf`. Every profile and host:

* `wasmEvInf_hostObsInf` (**adequacy**): the productive observations against a host,
  `hostObsInf (coreHostRel host) (wasmEvInf P)`, are exactly the productive Core runs with that
  host (`CoreInf`);
* `wasmEvInf_prefix` (**prefix agreement**): the first `n` events of such a run are the actual
  event log of a finite run of the invocation (`EvRun`), continued productively.

Not yet: agreement of these prefixes with the logged pending prefixes of `wasmEvPend` with the
same log, and a characterization by the logged native semantics `wasmHOpen`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- **The productive observations against a host are its productive Core runs.** -/
theorem wasmEvInf_hostObsInf {s : Store H} {a : Nat} {vs : List Val}
    {ω : Nat → Call (wasmHostSig H)} :
    ω ∈ hostObsInf (coreHostRel host) (wasmEvInf P) s (a, vs) ↔
      CoreInf P host (invoke s a vs) ω :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.wasmEvInf_hostObsInf

/-- **Prefix agreement**: the first `n` events of a productive run of an invocation are the
actual event log of a finite run of it, continued productively. -/
theorem wasmEvInf_prefix {s : Store H} {a : Nat} {vs : List Val} {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host (invoke s a vs) ω) (n : Nat) :
    ∃ c', EvRun P host (invoke s a vs) (streamTake ω n) c' ∧
      CoreInf P host c' (fun k => ω (n + k)) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.wasmEvInf_prefix h n

end Silmaril.Wasm.Abstract
