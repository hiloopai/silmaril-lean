module

public import Silmaril.Wasm.Resource.ClientArg.Defs
public import Silmaril.Proofs.Wasm.Resource.ClientArg.Plays

@[expose] public section

/-!
# Handles passed to internal callees: results

Proofs in `Silmaril.Proofs.Wasm.Resource.ClientArg.{Basic,Plays}`. Every profile `P`; no
determinism is assumed.

* `ArgCore`, `InvH`, `GuardedH`: the client analysis with the helpers `H` as further callable
  functions; `EnterH`: a thread between the call of a helper and the entry of its frame.
* `enterH_of_call`: a helper call checked with a handle on top leads to an entering thread whose
  frame starts from the entry fact `loc 0` (`hole_helper`); `enterH_step`: its only step enters
  the frame, by the context step inversion `Silmaril.Wasm.Game.ULink.step_fill_call`.
* `step_invH`, `JH`, **`argLTSInv`**, `argIn_accepts`, `argIn_sound`.
* **`checkClientArg_sound`**: `checkClientArg m ia iu if_ ps hs = true` gives
  `Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
  (progOf m) (clientSpec ia iu if_)`.

## `resource_client_arg`

`resource_client_arg hs` closes such a goal by `checkClientArg_sound` (no global pairs) and
kernel evaluation of the checker (`decide +kernel`, no native evaluation).
-/

namespace Silmaril.Wasm.Resource.ClientArg

/-- Prove the client sentence on a module by the checker with the helpers `hs` (module function
indices), no global pairs. -/
syntax "resource_client_arg" term:max : tactic

macro_rules
  | `(tactic| resource_client_arg $hs) =>
    `(tactic| (apply checkClientArg_sound (ps := []) (hs := $hs); decide +kernel))

end Silmaril.Wasm.Resource.ClientArg
