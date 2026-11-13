module

public import Silmaril.Proofs.Wasm.FX.Logic.Instr

/-!
# A handler-aware weakest-precondition calculus for WasmFX: rules

`WP P host fx s K f code Q` (`Silmaril.Wasm.FX.Logic.Defs`) is the existential weakest
precondition for `StepFX'` (CoreFX with continuation references as values): some run of `code`
reaches a final form, including an unhandled effect (`susp`, `swtch`), whose outcome satisfies
`Q`. Every rule holds for every profile `P`, host relation `host` and FX function table `fx`.

Rules (proofs in `Silmaril.Proofs.Wasm.FX.Logic.{Runs,Rules,Instr}`):

* runs in contexts: `steps_seq`, `steps_label`, `steps_frame`, `steps_handler`, `steps_core`,
  `step_ctx`, `steps_ctx`;
* structural: `WP.mono`, `WP.steps`, `WP.step`, `wp_ends`, `wp_head`, `wp_heads`; final forms
  `wp_val`, `wp_br`, `wp_ret`, `wp_trap`, `wp_throwing`, and the effects `wp_suspend`,
  `wp_switch`;
* contexts: `wp_seq`, `wp_app`, `wp_label`, `wp_frame` and **`wp_handler`** (the handler rule:
  caught effects continue as the clauses say, `handler_suspend`, `handler_switch`);
* stack switching: `wp_contNew`, `wp_contBind`, `wp_resume`, **`wp_resume_handle`**,
  `wp_resumeThrow`, **`wp_resumeThrow_handle`**, `wp_dropCont`, and the traps on null and
  consumed continuations (`wp_contNew_null`, `wp_contBind_null`, `wp_contBind_used`,
  `wp_resume_null`, `wp_resume_used`, `wp_resumeThrow_null`);
* FX functions: `wp_invoke`, `wp_call_fx`; structured control: `wp_block`, `wp_block_enter`,
  `wp_loop`, `wp_if_true`, `wp_if_false`;
* Core code: `wp_coreStep`, `wp_refFunc`, `wp_exec` (the `exec` interpreter of the Core
  calculus), `wp_coreWP` (a Core `Silmaril.Wasm.Logic.Core.WP` proof is an FX proof);
* adequacy: **`WP.behaviour`**: a result proved by the calculus is a behaviour of
  `behavioursFX'`.

Soundness is by construction: `WP` is defined from `StepsFX'`, so each rule is a lemma about
runs. What the calculus does **not** give: every-run (partial or total) correctness. `WP` asks
for one run, so a proved result is *a* behaviour, not *the* behaviour; the every-run and
step-indexed logics of `Silmaril.Wasm.Logic.Hoare` are not ported to WasmFX here.

New statements.
-/
