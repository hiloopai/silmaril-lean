module

public import Silmaril.Wasm.SpecTec.Sim20.ElseAgree.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim20.ElseAgree.Typ
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.ElseAgreeEnv
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.ElseAgreeMove
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.ElseAgreePairs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.ElseAgreeTask

/-!
# The `otherwise` premises of `simEnv20S` and `simEnv20T` agree: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.ElseAgree`; see `docs/projects/spectec/README.md`, "fwd20
".

* `Raw/…/ElseAgree/Typ`: two environments that evaluate alike and whose type tables agree off a
  closed set `bad` of type names type alike off `bad` (`tEqAt`, `hasTyp_off_iff`).
* `ElseAgreeEnv`: `simEnv20S B` and `simEnv20T B` are such a pair with `bad = tbad20`, the fifteen
  types that reach `instr` or `admininstr` (`typsOffB_fixedS20`, kernel; `hasTyp_off20T`).
* `ElseAgreeMove`: an `otherwise` premise moves from `e₁` to `e₂` when every earlier rule reads
  back (`PairBack`, `otherwiseAt_move`).
* `ElseAgreePairs`: three Boolean pair checks and their soundness: different last constructors,
  the same left-hand side with quantifiers off `tbad20` (or the shared state `z`), and a `TRAP`
  pattern against a code without one (`pairOkB`, `pairBack_of_pairsOkB`).
* `ElseAgreeTask`: the kernel runs the checks on `Step_read` and `Step_pure` and finds no other
  `otherwise` rule. **`elseAgree20T : StoreAgree.Task.elseAgree20T`**, so `Good20C`'s steps, and
  every `Fwd20` result, reach `simEnv20T` with no hypothesis (`sstepB20T_of_sstepB20S'`,
  `fwd20T_of_fwd20'`, `fwd20T_goodT20'`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.ElseAgree

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.ElseAgree.typsOffB_fixedS20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typsOffB_fixedS20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.ElseAgree.hasTyp_off20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hasTyp_off20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.ElseAgree.otherwiseAt_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms otherwiseAt_move

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.ElseAgree.pairBack_of_pairsOkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairBack_of_pairsOkB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.ElseAgree.readPairs20S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readPairs20S

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.ElseAgree.purePairs20S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms purePairs20S

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.ElseAgree.elseAgree20T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms elseAgree20T

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.ElseAgree.sstepB20T_of_sstepB20S'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstepB20T_of_sstepB20S'

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.ElseAgree.fwd20T_goodT20'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwd20T_goodT20'

end Silmaril.Wasm.SpecTec.Sim20.ElseAgree
