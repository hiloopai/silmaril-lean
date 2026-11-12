module

public import Silmaril.Wasm.Verify.Split.Defs
public import Silmaril.Proofs.Wasm.Verify.Split.Plays

@[expose] public section

/-!
# Escaping references and callable functions: results

Proofs in `Silmaril.Proofs.Wasm.Verify.Split.*`. Every profile `P`; no determinism is assumed.

* `Step.vIn`: **every Core 3.0 step rule preserves the escaping-reference invariant** `VIn V b`
  (store, locals and every non-transient reference of the code in `V`) from a configuration
  satisfying the reachability invariant `CfgIn C fs (PlVC V C fs)`, for hosts returning the
  store unchanged with references in `V`. With `Step.cfgIn` at `C` (`Silmaril.Wasm.Verify.Reach`),
  the pair `TInv V C fs` is preserved (`internalP_tInv`, `reach_tInv`).
  - `Step.nextCall_false`: a stepping code list never starts with a call instruction.
  - The families through the reachability invariant at `V` (`vIn_of_family`, `RFPl`).
  - Lemmas on `LooseIn`: `looseIn_append`, `LooseIn.mono`, `looseIn_vals_append`,
    `looseIn_of_codeIn`, `LooseIn.fill`; `plVC_plainOK`.
* `resume_vIn`: resuming with a scalar answer keeps `VIn V`; `invoke_tInv`: an export call
  starts with both invariants.
* `SplitIn I V Cs fs`: the escaping set `V` holds the store's references, each export `j` has a
  callable set `Cs j` (closed for `PlVC V (Cs j) fs`, containing `V` and the export).
  `trans_sInv`, `path_sInv`: the hidden states keep `SplitInv`; `stExp_trans`, `stExp_path`: the
  pending export of the hidden state is `activeExport` of the trace.
* **`neverCallFrom_of_splitIn`**: if `Cs e` avoids import `i`, the program
  `WasmProg.ofInstance I` satisfies `neverCallFrom (i, e)` in `wasmSem P`, every profile.
-/
