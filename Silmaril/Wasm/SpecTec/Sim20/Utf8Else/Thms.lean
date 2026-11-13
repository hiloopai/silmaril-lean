module

public import Silmaril.Wasm.SpecTec.Sim20.Utf8Else.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim20.Utf8Else.Agree
public import Silmaril.Raw.Wasm.SpecTec.Sim20.Utf8Else.Typ
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElseGood
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElseEq
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElseMove
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElseEnv
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElseClean20
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElseEnv20
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElsePairs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElseTask

/-!
# Reading `otherwise` back across the 2.0 `$utf8` erratum: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.Utf8Else`; see `docs/projects/spectec/README.md`, "utf8-fwd".

* `Raw/…/Utf8Else/Agree`: for any `EnvExt e₁ e₂ x₀` with `Clean e₁ x₀`, every member of the
  evaluator answers in `e₁` at least what it answers in `e₂`, on terms that never refer to `x₀`
  (`agreeAt`). With round 6's monotonicity, the two evaluate alike there (`Utf8ElseEq`:
  `evalExp_eq`, `evalExp_iff`, …).
* `Utf8ElseEq`: `clean20T`, the 2.0 instance (`simEnv20T B` refers to `$utf8` only in `$utf8`),
  by one kernel check over `fixedT20` (`refFree20T`).
* `Raw/…/Utf8Else/Typ`, `Utf8ElseEnv`: types off a closed set that never refer to `x₀` type alike
  (`tEqAt`, `hasTyp_iff`); for 2.0 the set is `badU20`, the twelve types that reach `name`
  (`typsOffB_badU20`, kernel; `hasTyp_u20T_iff`).
* `Utf8ElseClean20`, `Utf8ElseEnv20`: the same two facts for the other 2.0 pair,
  `simEnv20 B`/`utf8Env20 B` (`clean20`, `hasTyp_u20_iff`).
* `Utf8ElseMove`: a step moves under the `otherwise` premises that occur (`ElseMonoR`,
  `sstepB_extR`); `otherwise` moves when every earlier rule reads back (`PairBackU`,
  `otherwiseAtB_moveU`).
* `Utf8ElsePairs`, `Utf8ElseTask`: the pair check `pairOkU` and its soundness; the kernel runs it
  on `Step_read` and `Step_pure` and finds no other `otherwise` rule. **`elseMonoR20T`**,
  **`sstepB_utf8_20T`** (every step of `simEnv20T B` is a step of `utf8Env20T B`), and
  **`fwd_good20B_utf8T'`**, `runU_good20B'`: round 6's forward theorem in `utf8Env20T` from
  `Good20B`, without its `ElseMono` hypothesis.

Still open: `Utf8Mono.Task.fwdU20` (the forward theorem from `Good20BU`, whose modules may export
non-empty names).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Else.agreeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Else.agreeAt

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Else.clean20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Else.clean20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Else.tEqAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Else.tEqAt

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Else.hasTyp_u20T_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Else.hasTyp_u20T_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Else.otherwiseAtB_moveU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Else.otherwiseAtB_moveU

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Else.elseMonoR20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Else.elseMonoR20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Else.sstepB_utf8_20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Else.sstepB_utf8_20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Else.fwd_good20B_utf8T'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Else.fwd_good20B_utf8T'

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Else.runU_good20B'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Else.runU_good20B'

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Else.clean20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Else.clean20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Utf8Else.hasTyp_u20_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Utf8Else.hasTyp_u20_iff
