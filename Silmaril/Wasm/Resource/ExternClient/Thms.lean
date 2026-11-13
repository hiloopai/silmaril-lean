module

public import Silmaril.Wasm.Resource.ExternClient.Defs
public import Silmaril.Proofs.Wasm.Resource.ExternClient.Plays

@[expose] public section

/-!
# A typestate checker for `externref` clients: results

Proofs in `Silmaril.Proofs.Wasm.Resource.ExternClient.{Tight,TightStep,Inv,Thread,Plays}`. Every
profile `P`; no determinism is assumed.

* `Step.tight`: every host-free Core 3.0 step keeps `Tight R` (call instructions consume
  references into `R`), outside the calls of the three imports (`BadStep`).
* `Step.clientU`: `Step.client` of `Silmaril.Wasm.Resource.Client` for a reachable set containing
  the host functions of the imports; `okA_gl`: without handle pairs the check depends on no
  global, so it survives the stores the environment hands over.
* `step_invU`: one step of an invariant thread (`InvU`) leads to an invariant or a guarded
  thread (`GuardedU`).
* **`uClientIn_accepts`**: under `UClientIn U S₀ R G fs ia iu if_`, every play of `U.strategy P`
  is accepted by `keptSpecA S₀ G ia iu if_`, through `untyped_accepts` and the protocol invariant
  `uClientInv` of `U.lts P`.
* **`checkU_sound`**: `checkU S₀ fs addrs ia iu if_ = true` gives the same for the guard set
  `guardU S₀ fs addrs ia iu if_` (`uClientIn_of_checkU`).
* **`checkModU_sound`**: the whole-module check `checkModU m = true` gives the same for the
  untyped instance of the module `modU m` (all its function exports), its instantiated store
  and the guard set `modGuardU m`.
-/

namespace Silmaril.Wasm.Resource.ExternClient

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Resource.ExternExamples Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)

/-- **Soundness of the whole-module check** (every profile): if `checkModU m` passes, every play
of the untyped instance of `m` (all its function exports) is accepted by the client sentence
`keptSpecA` on its instantiated store, for the guard set `modGuardU m` and the host codes `0`,
`1`, `2` of `env.alloc`, `env.use`, `env.free`. -/
theorem checkModU_sound {m : Module} (h : checkModU m = true) (P : Profile) :
    ∀ p ∈ (modU m).strategy P,
      (keptSpecA (ι := (modU m).X) (storeOf m) (· ∈ modGuardU m) 0 1 2).Accepts p :=
  checkU_sound (Bool.and_eq_true_iff.1 h).2 (fun _ => List.getElem_mem _) P

end Silmaril.Wasm.Resource.ExternClient
