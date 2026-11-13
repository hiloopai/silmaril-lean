module

public import Silmaril.Wasm.Resource.Client.Defs
public import Silmaril.Proofs.Wasm.Resource.Client.Plays

@[expose] public section

/-!
# A typestate verifier for clients of the handle protocol: results

Proofs in `Silmaril.Proofs.Wasm.Resource.Client.{Basic,Step,Plays}`. Every profile `P`; no
determinism is assumed.

* `okL_mono`, `okA_mono`: the checks are monotone in the abstract state (`CLe`);
  `okA_npre_indep`: after the value prefix the check depends neither on the live handles nor on
  the store.
* **`Step.client`**: every host-free Core 3.0 step rule keeps the client invariant (`CPost`):
  store invariant (`Sigma`), sound facts, and the check of every continuation; the families,
  `post_globalGet` (`getTop_sound`), `post_globalSet` (`setF_sound`), `post_ifTrue`,
  `post_ifFalse`, `post_block`, `post_loop`, `post_tryTable`, `post_brLabelZero`,
  `post_callRefFunc`, `post_call`, and the context rules `post_ctxtInstrs`, `post_ctxtLabel`,
  `post_ctxtHandler`, `post_ctxtFrame`.
* `client_guard`: a use or a free is preceded, in its innermost sequence, by a live handle
  (resp. a live handle held by no flagged pair); `guardedC_of_badStep`, `step_invC`.
* **`clientLTSInv`**: under `ClientIn I G fs ia iu if_ ps`, a protocol invariant of
  `I.dlts P I.store` for `(clientSpec ia iu if_).comap moveEvent`; `clientIn_accepts`,
  `clientIn_sound`.
* **`checkClient_sound`**: `checkClient m ia iu if_ ps = true` gives
  `Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
  (progOf m) (clientSpec ia iu if_)`.

## `resource_client`

`resource_client` closes `Models (protoLogic …) (wasmSem P) (progOf m) (clientSpec ia iu if_)`
by `checkClient_sound` and kernel evaluation of the checker (`decide +kernel`, no
native evaluation); `resource_client ps` passes the pairs of flag and handle globals.
-/

namespace Silmaril.Wasm.Resource.Client

/-- Prove the client sentence on a module by the typestate checker, in the kernel, with the
given handle pairs (store addresses of the flag and handle globals; none by default). -/
syntax "resource_client" (term)? : tactic

macro_rules
  | `(tactic| resource_client) => `(tactic| (apply checkClient_sound (ps := []); decide +kernel))
  | `(tactic| resource_client $ps) =>
    `(tactic| (apply checkClient_sound (ps := $ps); decide +kernel))

end Silmaril.Wasm.Resource.Client
