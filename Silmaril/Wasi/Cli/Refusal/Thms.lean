module

public import Silmaril.Wasi.Cli.Refusal.Defs
public import Silmaril.Wasi.Cli.Thms
public import Silmaril.Proofs.Wasi.Cli.Refusal

/-!
# WASI 0.2 components against behaviour specs, with refusals: theorems

PROVED (standard axioms), namespace `Silmaril.Wasi.Cli.Refusal`.

* **`hello_orRefused`**: the WASI 0.2 component `hello` (`Silmaril.Wasi.Examples.hello`: get stdout,
  `blocking-write-and-flush` of `hi`, drop, return `ok`, ignoring the write's result) satisfies
  `orRefused hiSpec` through the bridge's `p2View` (`CliSat`), for every host whose
  `get-stdout` answers a handle (`stdoutTyped`, the WIT typing theory of the slice, in which a
  write may fail). It does not
  satisfy `hiSpec` itself, nor `orFail hiSpec`: after a refused write it prints nothing and
  exits `0` (`hello_not_hiSpec`, `hello_not_orFail`). **`hello_every_host`**: the same, in every
  interaction with every such host.

The proof (`Silmaril.Proofs.Wasi.Cli.Refusal`) follows the plays of `hello` with at most one run:
each is a prefix of `call run; get-stdout → hd; write → r; drop → r'; return ok`, and its view
is nothing yet, then `hi` if `r` is success or a refusal with nothing written otherwise, and
exit `0` once `run` returned.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Refusal

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Examples Silmaril.Games
open Silmaril.Wasm.Resource (Protocol)

/-- **`hello` meets `orRefused hiSpec` for every typed WASI 0.2 host.** -/
theorem hello_orRefused :
    CliSat (W := stdoutWorld) (ofBody hello) (fun _ => stdoutTyped) p2View
      (Spec.orRefused Silmaril.Wasi.Cli.hiSpec) :=
  fun i _ ⟨_, hs⟩ hA h1 => hello_partial i hs hA h1

/-- **`hello` in every interaction with every typed host.** -/
theorem hello_every_host (i : Input) {Y : Sig.{0}} (η : Host Y stdoutWorld.imports)
    (hη : (hostSat stdoutTyped.Accepts).holds η) :
    ∀ p ∈ link η (ofBody hello), ∃ t ∈ ofBody hello, xtrace p = expView (wtrace t) ∧
      p2View.Guar (Spec.orRefused Silmaril.Wasi.Cli.hiSpec) i (wtrace t) :=
  hello_orRefused.every_host i η hη

/-- **`hello` does not meet `orFail hiSpec`** (so not `hiSpec` either): on the play
`failMoves`, a typed host refuses the write and `hello` exits `0` having printed nothing. -/
theorem hello_not_orFail :
    ¬ CliSat (W := stdoutWorld) (ofBody hello) (fun _ => stdoutTyped) p2View
      (Spec.orFail Silmaril.Wasi.Cli.hiSpec) :=
  fun h => hello_not_orFail_partial {} (h {} failMoves ⟨_, failMoves_reach⟩ failMoves_typed
    (by rw [failMoves_wtrace]; decide))

theorem hello_not_hiSpec :
    ¬ CliSat (W := stdoutWorld) (ofBody hello) (fun _ => stdoutTyped) p2View
      Silmaril.Wasi.Cli.hiSpec :=
  fun h => hello_not_orFail h.orFail

end Silmaril.Wasi.Cli.Refusal
