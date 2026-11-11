module

public import Silmaril.Proofs.Wasm.Logic.Total.Call

/-!
# Total correctness for the every-run logic: rules and adequacy

Rules for the inductive total-correctness predicate `Hoare.TSafe`/`Hoare.TWP`
over pinned silmaril-lean's Core 3.0 `Step P host`, for every profile and every
host relation (definitions in `Silmaril.Wasm.Logic.Total.Defs`):

* structure: `TSafe.post_mono`, `TSafe.step_inv`, `TSafe.seq`/`TWP.seq`,
  `TSafe.label`, `TSafe.frame` (including tail calls out of the frame);
* control: `TWP.block`, `TWP.if_`, `TWP.brIf`, and **`TWP.loop`** with an
  invariant and a natural-number variant;
* instructions: every rule of `Silmaril.Wasm.Logic.Instr.Thms` at `Wp .total`, and
  the generic `TWP.fam`, `TWP.det`, `TSafe.head`;
* calls: `TFSpecAt.of_body`, **`TSafe.call`**, `TSafe.callIdx`, `framePostT_tail`;
* recursion: **`TCtx.valid_of_measure`** (a measure on the arguments of the
  functions of a context that every recursive call decreases), and the **total
  module rule** `TCtxSat.valid`/`TCtxSat.link`;
* adequacy: `TFSpecAt.valid` (total implies partial), `TFSpecAt.invoke_terminates`
  (no infinite run of `$invoke`), `TFSpecAt.invoke_vals`; `Hoare.twp_terminates`.

Not covered for total correctness: exception handlers (`try_table`; the partial
rule is `Hoare.HWP.handler`).

A Silmaril addition.
-/
