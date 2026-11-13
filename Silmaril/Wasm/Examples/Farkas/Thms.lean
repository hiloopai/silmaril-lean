module

public import Silmaril.Proofs.Wasm.Examples.Farkas.Total

@[expose] public section

/-!
# A Farkas certificate checker in Wasm: results

Proofs in `Silmaril.Proofs.Wasm.Examples.Farkas.*`. Every profile `P`, every environment `K`,
partial correctness (`HWP`) for soundness, total correctness (`TWP`) for termination; no
`sorry`, axiom or `Task`.

* **`farkas_session`**: in every closed-world Core 3.0 session `Session P farkasI K
  farkasI.store (l₁ ++ c :: l₂)`, if `c` is a call of `check` answered with the value `1`, then
  `WRows.IsCert (loaded l₁)`: the rows loaded by the `row`/`entry` calls since the last `check`
  in `l₁`, with their multipliers, are a valid Farkas certificate;
* **`farkas_session_infeasible`**: hence `¬ Feasible 𝕜 (loaded l₁).system` for every ordered
  field `𝕜` (`ℚ`, `ℝ`);
* the parts: `farkas_spec` (every export call meets `Common.callSpec farkasI Rep next Good`, for
  every host relation), from `row_hwp`, `entry_hwp`, `check_hwp` (the bodies, by
  `Common.Wp.exec_eq` and `HWP.loop`) and `inv_row`, `inv_entry`, `inv_check`,
  `cert_of_check` (the invariant `Inv`, with exact `i64` arithmetic under the bounds,
  `macc_toInt`);
* tests: `bogus_rejected`, `overflow_rejected` (with `overflow_wraps`, `overflow_feasible`).

Completeness under the bounds (`Silmaril.Proofs.Wasm.Examples.Farkas.{Complete,Total}`):

* **`farkas_complete`** (partial correctness): in every session, a `check` after `row`/`entry`
  calls that passed the bounds since the last `check` (`LoadsOk`, per command `CmdOk`) and
  loaded a valid certificate answers `1` (from `farkas_specC`: `bad` stays `0` exactly under
  the bounds, `bad_rowM`, `bad_entryM`, and `check_complete`);
* total correctness: `row_twp`, `entry_twp`, `check_twp` (`TWP.loop` with the variant
  `nVars - i`), `tspec_valid` (every export call terminates with typed results);
  **`farkas_total`**: every sequence of export calls is a session; **`farkas_accepts`**: for
  every sequence of calls followed by `check` there is a session, and its `check` answers `1`
  under `LoadsOk` and `IsCert`;
* positive tests: `cert_accepted` (every session loading `x₀ ≤ 1, -x₀ ≤ -2` with multipliers
  `1, 1` answers `1` to the following `check`) and `cert_session` (such a session exists).

The instance `farkasI` is computed from `farkasMod` by silmaril-lean's `instantiateOnce?`; its
store, globals, memory and function types are checked by `rfl` and `decide +kernel`
(`farkasStore_funcs`, `farkasStore_holds`).
-/
