module

public import Silmaril.Wasm.SpecTec.Sim20.Pure.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureRules
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureControl
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureNumeric
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureNumericV2
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureTransfer
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureConcat
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureCvt
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumEnv
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumAgree
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumTyping
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumCvt

/-!
# SpecTec 2.0 `Step_pure` ↔ V2 `PureStep`, rule by rule

The theorems, in `Silmaril.Wasm.SpecTec.Sim20.Pure`:

* **Provenance** (`PureRules`): `hasRuleAt_*` for rules 0–27 of `Step_pure` in `simEnv20 B`
  (kernel `rfl`); `closedB_pure20`, so `firesB_pure20_iff` and `sPureB20_iff` (the backend reading
  is the declarative reading on `Step_pure`).
* **Control family, unconditional** (`PureControl`), each `FiresB … k (lhs, w) ↔ side
  conditions ∧ w = rhs` under typing hypotheses on the rule's quantified variables:
  `unreachable_iff`, `nop_iff`, `drop_iff`, `selectTrue_iff`, `selectFalse_iff`, `ifTrue_iff`,
  `ifFalse_iff`, `labelVals_iff`, `brIfTrue_iff`, `brIfFalse_iff`, `brTableLt_iff`,
  `brTableGe_iff`, `frameVals_iff`, `trapLabel_iff`, `trapFrame_iff`.
* **Numeric family** (`PureNumeric`, `PureNumericV2`): at the IL level, unconditionally,
  `unopVal_inv/_fires`, `binopVal_inv/_fires`, `binopTrap_inv/_fires`, `testop_inv/_fires`,
  `relop_inv/_fires`; as V2 constructors under the assumed `NumAgree`/`NumTyped`:
  `intUnOp_iff`, `floatUnOp_iff`, `intBinOp_iff`, `floatBinOp_iff`, `intBinOpTrap_iff`,
  `testOp_iff`, `intRelOp_iff`, `floatRelOp_iff`.
* **Census transfer** (`PureTransfer`): `sameRules_20_30`, and the round 3 lemmas applied
  verbatim to the wasm-2.0 script, `spure20_unreachable`, `spure20_nop`, `spure20_ifTrue`,
  `spure20_ifFalse`.

* **Concatenation rules** (`PureSplit`, `PureConcat`, pass 3): `brZero_iff`, `brSucc_iff`,
  `returnFrame_iff`, `returnLabel_iff`, `trapVals_iff`, with `*_bwd` (SpecTec firing → V2 step,
  no typing hypothesis) and `brZero_step`/`returnFrame_step`. The read-back direction rests on
  the unique-split lemma `split_unique` and the typing inversions `valHead_of_typed` (a typed
  2.0 `val` has one of `val`'s five constructors) and `labelidx_inv` (a typed `labelidx` is a
  numeral `%(k)`).
* **`unop-trap`, `cvtop-val`, `cvtop-trap`** (`PureCvt`, pass 3): IL level, unconditional,
  `unopTrap_inv/_fires`, `cvtopVal_inv/_fires`, `cvtopTrap_inv/_fires`; V2 level
  `intUnOpTrap_iff`, `floatUnOpTrap_iff` (under `NumAgree`/`NumTyped`; both sides are `False`, so
  `intUnOpTrap_never`, `floatUnOpTrap_never`), and `cvtOp_iff`, `cvtOpTrap_iff` under the assumed
  `CvtAgree` and `CvtTyped`.
* **The numeric hypotheses** (`NumEnv`, pass 3): `CvtTyped` is discharged
  (`cvtTyped_simEnv20`), and so is `NumTyped.numtype` (`typedV_numtype20`). `NumAgree` is not:
  `not_numEnv_simEnv20` shows the shared library `Equiv.NumEnv` fails for the 2.0 script, only
  at `$iextend_` (absent in 2.0), while the other 24 primitives are 2.0's verbatim
  (`numEnv20_simEnv20`); `numEnv_of_numEnv20` makes the split exact.
* **`NumAgree`, discharged** (`NumLookup`, `NumInt`, `NumAgree`, pass 4): the library's lemmas now
  take `Equiv.NumEnvCore` (the 24 shared definitions, `numEnvCore_simEnv20`), and the 2.0
  dispatchers are walked opcode by opcode (`applies_unop_int20`, `applies_binop_int20`,
  `applies_testop_int20`, `applies_relop_int20`, `applies_unop_float20`,
  `applies_binop_float20`, `applies_relop_float20`), giving
  `numAgree_simEnv20 : IntB B → FloatB P B → NumAgree (simEnv20 B) P` and
  `numAgree_floatIntB20`.
* **`NumTyped`, discharged** (`NumTyping`, pass 4): `numTyped_simEnv20 : NumTyped (simEnv20 B)`
  for every `B`, by the 3.0 typing proofs ported to the 2.0 script (whose number and float type
  definitions are 3.0's verbatim; only `unop_` and the size functions differ).
* **`CvtAgree`, discharged** (`NumCvt`, pass 4): `cvtAgree_simEnv20 : FloatB P B → CvtAgree
  (simEnv20 B) P`, walking 2.0's `$cvtop__` (`Original.d224`) clause by clause. With the above,
  `numericHyps_simEnv20` makes every numeric iff unconditional under `IntB B` and `FloatB P B`.
-/
