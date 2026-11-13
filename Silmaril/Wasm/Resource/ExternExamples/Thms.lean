module

public import Silmaril.Wasm.Resource.ExternExamples.Defs
public import Silmaril.Proofs.Wasm.Resource.ExternExamples.Basic

@[expose] public section

/-!
# Real `externref` clients: results

Proofs in `Silmaril.Proofs.Wasm.Resource.ExternExamples.Basic`. Every profile `P`; no determinism
is assumed. The Core runs are hand-built steps (`Step.callRefFunc`, `local.get`, `call`, under
`label`/`frame` contexts), valid at every profile; the stores come from the spec's allocation by
kernel evaluation (`decide +kernel`).

* **Refutation.** `badPlay_mem`: `badPlay` (`run hnd`, then `use hnd`) is a play of
  `exUseU.strategy P`. `exUse_refuted`: not every play of `exUse` is accepted by
  `uClientSpec 0 1 2`; `exUse_refuted_kept`: nor by `keptSpec exUseS (· ∈ useG) 0 1 2`, so the
  violation is the module's, not the environment's.
* **The unguarded sentence is too strong.** `exAlloc_refuted_unkept`: `exAlloc`, which never
  reaches `use` or `free`, is refuted by `uClientSpec 0 1 2` as well, since Opponent may hand it
  `exUse`'s store. In the untyped game the store is part of the move, and an untyped instance
  records only export addresses.
* **Proof.** `kept_accepts`: an untyped instance whose exports lie in a function set closed for
  the module and avoiding the `use` and `free` host functions (`KeptHyp`) satisfies
  `keptSpec`, every profile, through `untyped_accepts` and the protocol invariant `keptInv` of
  `U.lts P` (the reachability invariant `CfgIn` of `Silmaril.Wasm.Verify.Reach` on threads, carried
  across environment answers by the guard). `exAlloc_client`: `exAlloc` satisfies
  `keptSpec exAllocS (· ∈ allocG) 0 1 2`, with `KeptHyp` from the checker's Boolean
  certificates (`closedB`, `avoidsB`) by kernel evaluation. `allocPlay_mem`: `exAlloc` does call
  `alloc`.

This is the degenerate client case: `use` and `free` are unreachable. A client that allocates
and then uses its handle needs the typestate invariant of the Gaps of `docs/projects/wasm-wasi.md`.
-/
