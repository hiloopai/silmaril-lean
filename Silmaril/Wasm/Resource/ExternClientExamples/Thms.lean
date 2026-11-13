module

public import Silmaril.Wasm.Resource.ExternClientExamples.Defs
public import Silmaril.Proofs.Wasm.Resource.ExternClientExamples.Basic

@[expose] public section

/-!
# Real `externref` clients that use and free their handles: results

Proofs in `Silmaril.Proofs.Wasm.Resource.ExternClientExamples.{Run,Basic}`. Every profile `P`; no
determinism is assumed. The Core runs are hand-built steps (`call_ref` of a Wasm function,
`call`, `local.set`, `local.get`, under `label`/`frame` contexts), valid at every profile; the
stores and the checker's verdicts come from kernel evaluation (`decide +kernel`).

* **Proof.** `exAUF_client`: `exAUF` (allocate into a local, use, free) satisfies
  `keptSpecA aufS (· ∈ aufG) 0 1 2` (`checkU_sound`, `auf_check`; `aufG = [3, 0, 1, 2]`).
  `aufUse_mem`, `aufFree_mem`: plays of `exAUF` reach `use hnd` and `free hnd` after
  `alloc` answered `hnd`. So the sentence constrains reachable `use`/`free` callouts.
* **Whole module.** `exAUF_module_client`: the same through the whole-module check
  `checkModU exAUF = true` (`checkModU_sound`), for the instance `modU exAUF` (export addresses
  `modAddrsU exAUF = [3]`) and the guard set `modGuardU exAUF = [3, 0, 1, 2]`, both computed from
  the module; `exUAF_module_rejected`: `checkModU exUAF = false`.
* **The guard needs the allocator's arity.** `exAUF_refuted_kept`: under `keptSpec` (no arity
  guard) `exAUF` is refuted for every guard list: the answer `values [hnd₂, hnd]` to `alloc` is no
  allocation, and `run` uses `hnd`.
* **Refutation.** `exUAF_rejected`: the checker answers `false` on `exUAF`;
  `exUAF_refuted`: `exUAF` uses `hnd` after freeing it, and is refuted by `keptSpecA` for every
  guard list (`uafPlay_mem`, an environment answering in the instance's own store).
-/
