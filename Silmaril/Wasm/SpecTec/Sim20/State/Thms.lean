module

public import Silmaril.Wasm.SpecTec.Sim20.State.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StateVar
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StateGlobal
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StateRefNull

/-!
# SpecTec 2.0 references and variables ↔ V2, rule by rule

The theorems, in `Silmaril.Wasm.SpecTec.Sim20.State` (proofs in `Sim20.StateVar`), each under the
Round 6 backend reading `FiresB` on `simEnv20 B`, at the image of the V2 left-hand side:

* **Provenance**: `hasRuleAt_*` (kernel `rfl`) for `Step_pure` 28, 55, `Step_read` 6, 7, 8 and
  `Step` 4.
* `firesB_noPrems_iff`: a rule without premises fires under the backend reading iff some
  assignment evaluates its conclusion, whether or not its relation is closed.
* `localTee_iff` (`Step_pure` 55) and `refIsNullTrue_iff` (28), unconditional apart from typing.
* `localGet_iff` (`Step_read` 7), `globalGet_iff` (8), `refFunc_iff` (6), at configurations where
  V2's lookup is defined, with the V2 steps `localGet_step`, `globalGet_step`, `refFunc_step`;
  `read1_iff` is the generic one-instruction `Step_read` lemma.
* `localSet_iff` (`Step` 4), at a local index in range (`Step.localSet`'s own premise), with
  `localSet_step`.
* `globalSet_iff` (`Step` 5, `Sim20.StateGlobal`, pass 4), where V2's global lookups are defined
  (`Step.globalSet`'s premises), with `globalSet_step`; `$with_global` is evaluated by
  `evalExp_withGlobal20`.
* `refIsNullFalse_iff` (`Step_pure` 29, `Sim20.StateRefNull`, pass 5): its `otherwise` premise is
  read by refuting rules 0–27 by their tags and rule 28 at a non-null reference
  (`otherwise_refIsNullFalse`, `null_of_body28`), with `refIsNullFalse_step`.
* `call_iff` (`Step_read` 2, pass 5), where the function address is defined, with `call_step`.

The 2.0 accessors `$local`, `$global`, `$funcaddr`, `$with_local` are evaluated by
`evalExp_local20`, `evalExp_global20`, `evalExp_funcaddr20`, `evalExp_withLocal20`.
-/
