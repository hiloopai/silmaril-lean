module

public import Silmaril.Wasm.Resource.OBClient.Defs
public import Silmaril.Proofs.Wasm.Resource.OBClient.Plays
public import Silmaril.Proofs.Wasm.Resource.OBClient.OwnPlays

@[expose] public section

/-!
# A typestate verifier for borrowing clients: results

Proofs in `Silmaril.Proofs.Wasm.Resource.OBClient.{Basic,Plays}`. Every profile `P`; no
determinism is assumed.

* `obSpec_oTotal`: environment moves never break the ownership sentence.
* `OBIn`: the thread-level client analysis (`ClientCore`, held handles as the live list, no
  global pairs, no free import), the role exports (entered only by the environment; bodies
  checked from the entry fact `loc 0`) and the roles.
* `EntryO`, `entry_step`: a pending invocation of a role export enters the callee frame, where
  the parameter is known to be held (`invC_entry`).
* **`obLTSInv`**: the protocol invariant of `I.dlts P I.store` for
  `(obSpec ρ).comap moveEvent`; `obIn_accepts`, `obIn_sound`.
* **`checkOB_sound`**: `checkOB m ia iu ρ = true` gives
  `Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode)))) (wasmSem P)
  (progOf m) (obSpec ρ.toOB)`.

## Frees of owned handles

Proofs in `Silmaril.Proofs.Wasm.Resource.OBClient.{Own,OwnPlays}`.

* `InvB`, `InvAB`: the owned-handle instance (`cfgO`, uses neutral, live list: the owned
  handles) and its conjunction with the held instance; `GuardedAB`: a use needs a held handle, a
  free an owned one; `step_invAB`, every host-free step.
* `EntryF`, `entryF_step`: a role export is entered with `loc 0` in the held instance, and in
  the owned instance when it takes ownership.
* `OFIn`, `JF`, **`ofLTSInv`**, `ofIn_accepts`, `ofIn_sound`. The held handles of a protocol
  state are distinct (`WF`), so a free removes the handle from both lists.
* **`checkOF_sound`**: `checkOF m ia iu if_ ρ = true` gives the same `Models … (obSpec ρ.toOB)`.

## `resource_ob`, `resource_of`

`resource_ob` closes such a goal by `checkOB_sound` and kernel evaluation of the checker
(`decide +kernel`, no native evaluation); `resource_of ia iu if_` by `checkOF_sound`.
-/

namespace Silmaril.Wasm.Resource.OBClient

/-- Prove the ownership sentence on a module by the borrowing-client checker, in the kernel,
with the allocating and using imports `ia`, `iu`. -/
syntax "resource_ob" term:max term:max : tactic

macro_rules
  | `(tactic| resource_ob $ia $iu) =>
    `(tactic| (apply checkOB_sound (ia := $ia) (iu := $iu); decide +kernel))

/-- Prove the ownership sentence on a module by the checker with frees, in the kernel, with the
allocating, using and freeing imports `ia`, `iu`, `if_`. -/
syntax "resource_of" term:max term:max term:max : tactic

macro_rules
  | `(tactic| resource_of $ia $iu $if_) =>
    `(tactic| (apply checkOF_sound (ia := $ia) (iu := $iu) (if_ := $if_); decide +kernel))

end Silmaril.Wasm.Resource.OBClient
