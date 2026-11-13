module

public import Silmaril.Wasm.SpecTec.Sim20.XSwap.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.XSwap.Holds
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.XSwap.Holds10

/-!
# SpecTec's 2.0 `Step` is invariant under an involutive re-encoding of export lists

Namespaces `Silmaril.Wasm.SpecTec.Sim20.XSwap.{Swap,Erase,EraseAll,Typ}`; see `docs/projects/spectec/README.md`,
"utf8". Definitions are in `Sim20/XSwap/Defs.lean`.

* **The evaluator** (`Raw/…/Sim20/XSwap/{Value,…,EAll}.lean`): round 8's `Round8.CodeErase` copied
  for `EXPORTS` fields and an arbitrary injective replacement (`XTau`). `EraseAll.eraseAt`: each
  of the 29 members of the evaluator commutes with `swapX` on syntax that passes the check
  `xExp`, given `Hyps`.
* **The 2.0 script** (`EraseAll.hyps20`): every definition and relation `Step` reaches in the
  corrected 2.0 script passes the check (twenty kernel chunks, `Check0`–`Check3`), and the
  primitives of `utf8Env20T (storeB P)` commute with `swapX` (`biSwap_storeB`, 's
  strictness argument and the 2.0 encoders).
* **Typing** (`Typ.hasTyp_erase`): typing at a checked type (`CheckTyp`: `xTypMap20`,
  `xRelQuants20`) moves to the re-encoded side, `K` fuel later, when `τ` loses at most `K` fuel on
  `exportinst*` (`Typ.ExpK`).
* **Derivations** (`Typ.dderivesB_swap`, `Typ.ruleBodyB_swap`): derivations of `Step`,
  `Step_read` and `Step_pure` under `DDerivesB` move forward, for any reading of `otherwise` that
  does.
* **`otherwise`** (`Typ.otherwiseAtB_swap`): when `τ` is an involution, forward is backward, so
  SpecTec's `otherwise` moves too; **`Typ.sstepB_swap`**: steps move.
* **`swapStep20_holds`**: the leaf `Utf8Swap.Task.swapStep20`. So **`fwdU20_holds`**
  (`Utf8Mono.Task.fwdU20`) and **`unstripStep20_holds`** (`Utf8Strip.Task.unstripStep20`).
* **The 1.0 script** (`EraseAll.hyps10`, `Typ10.*`, `Raw/…/XSwap/*10.lean`): the same for
  `utf8Env10T (fwdB10 nd r)` (two kernel halves `Check10`, `CheckTyp10`). **`swapStep10_holds`**
  (`Utf8Swap10.Task.swapStep10`), so **`stepFwd10U_holds`**, **`wholeRunFwd10U_holds`** (the 1.0
  forward step and run at non-empty export names, under round 4's invariants) and
  `unstripStep10_inv`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll.hyps20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll.hyps20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ.sstepB_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ.sstepB_swap

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.XSwap.swapStep20_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.XSwap.swapStep20_holds

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.XSwap.fwdU20_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.XSwap.fwdU20_holds

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.XSwap.unstripStep20_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.XSwap.unstripStep20_holds

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll.hyps10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll.hyps10

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.XSwap.swapStep10_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.XSwap.swapStep10_holds

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.XSwap.stepFwd10U_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.XSwap.stepFwd10U_holds

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.XSwap.wholeRunFwd10U_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.XSwap.wholeRunFwd10U_holds

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.XSwap.unstripStep10_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.XSwap.unstripStep10_inv
