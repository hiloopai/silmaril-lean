module

public import Silmaril.Wasm.Perf.ValidateR.Defs
public import Silmaril.Wasm.Perf.ValidateF.Thms
import Silmaril.Proofs.Wasm.Perf.ValidateR.Eq

/-!
# The reversed-stack validator is silmaril's validator

* Stack reading (`prefixSub Δ R t.reverse` reads the operands at the head of the reversed
  stack): `stepAR_eq`, `stepBR_eq`, `finishCheckR_eq`, `checkBySigR_eq`, `topHeapR_eq`;
* the atom oracle and the direct step: `atomR_eq`, `directStepGR_eq`, `directStepR_eq`;
* by mutual induction on instructions, `checkInstrR_eq` and **`checkSeqR_eq`**:
  `checkSeqR … r r.length poly goal acc l` is `checkSeqF … r.reverse poly goal l` with the
  dead-code count dropped and the locals reversed onto `acc`;
* **`validateR_eq : validateR = validate?`**, registered with `@[csimp]`
  (`validate?_eq_validateR`).

The proofs (with the direct paths `fastR_cases`) are in `Silmaril.Proofs.Wasm.Perf.ValidateR.Eq`;
they build on `ValidateF`'s equations, which `Silmaril.Wasm.Perf.ValidateF.Thms` states.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.ValidateR

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Validation.CheckInstrs
open Silmaril.Wasm.Perf.ValidateF

/-! ## Reading operands from the head -/

theorem stepAR_eq (Δ : TypeCtx) (R t₁ : List CValType) (xs : List Nat) (out : List CValType) :
    stepAR Δ R t₁ xs out = stepA Δ R.reverse t₁ xs out :=
  Silmaril.Proofs.Wasm.Perf.ValidateR.stepAR_eq Δ R t₁ xs out

theorem stepBR_eq (Δ : TypeCtx) (R t₁ : List CValType) :
    stepBR Δ R t₁ = stepB Δ R.reverse t₁ :=
  Silmaril.Proofs.Wasm.Perf.ValidateR.stepBR_eq Δ R t₁

theorem finishCheckR_eq (C : Context) (R : List CValType) :
    finishCheckR C R = finishCheck C R.reverse :=
  Silmaril.Proofs.Wasm.Perf.ValidateR.finishCheckR_eq C R

theorem checkBySigR_eq (Δ : TypeCtx) (sig : Option InstrType) (R : List CValType) :
    checkBySigR Δ sig R = checkBySig Δ sig R.reverse :=
  Silmaril.Proofs.Wasm.Perf.ValidateR.checkBySigR_eq Δ sig R

theorem topHeapR_eq (R : List CValType) : topHeapR R = topHeap R.reverse :=
  Silmaril.Proofs.Wasm.Perf.ValidateR.topHeapR_eq R

/-! ## The atom oracle and the direct step -/

theorem atomR_eq (C : Context) (R : List CValType) (i : Instr) :
    atomR C R i = atomC C R.reverse i :=
  Silmaril.Proofs.Wasm.Perf.ValidateR.atomR_eq C R i

theorem directStepGR_eq (C : Context) (R : List CValType) (i : Instr) :
    directStepGR C R i = directStep atomC tyOkC C R.reverse i :=
  Silmaril.Proofs.Wasm.Perf.ValidateR.directStepGR_eq C R i

theorem directStepR_eq (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType)
    (C : Context) (R : List CValType) (i : Instr) :
    directStepR fa rs la C R i = directStepF fa rs la C R.reverse i :=
  Silmaril.Proofs.Wasm.Perf.ValidateR.directStepR_eq fa rs la C R i

/-! ## Instructions, sequences, modules -/

theorem checkInstrR_eq (fa : Array DefType) (rs : Std.HashSet Nat) (i : Instr) :
    ∀ (la : Array LocalType) (C : Context) (R : List CValType),
      checkInstrR fa rs la C R i = checkInstrF fa rs la C R.reverse i :=
  Silmaril.Proofs.Wasm.Perf.ValidateR.checkInstrR_eq fa rs i

/-- **The reversed-stack sequence checker is `checkSeqF`**, with the dead-code count dropped
and the initialised locals reversed onto `acc`. -/
theorem checkSeqR_eq (fa : Array DefType) (rs : Std.HashSet Nat) (l : List Instr) :
    ∀ (la : Array LocalType) (C : Context) (r : List CValType) (poly : Bool)
      (goal : Option (List CValType)) (acc : List Nat),
      checkSeqR fa rs la C r r.length poly goal acc l =
        (checkSeqF fa rs la C r.reverse poly goal l).map (fun p => (p.1, p.2.1.reverse ++ acc)) :=
  Silmaril.Proofs.Wasm.Perf.ValidateR.checkSeqR_eq fa rs l

theorem checkExprR_eq : checkExprR = checkExprF :=
  Silmaril.Proofs.Wasm.Perf.ValidateR.checkExprR_eq

theorem checkModuleR_eq : checkModuleR = checkModuleF :=
  Silmaril.Proofs.Wasm.Perf.ValidateR.checkModuleR_eq

/-- **The reversed-stack validator is silmaril's `validate?`.** -/
theorem validateR_eq : validateR = validate? :=
  Silmaril.Proofs.Wasm.Perf.ValidateR.validateR_eq

/-- Compiled code that imports this module and calls silmaril's `validate?` runs `validateR`. -/
@[csimp] theorem validate?_eq_validateR :
    @Silmaril.Wasm.Validation.validate? = @Silmaril.Wasm.Perf.ValidateR.validateR :=
  validateR_eq.symm

end Silmaril.Wasm.Perf.ValidateR
