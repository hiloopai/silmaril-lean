module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeFlat
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIU1
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIU2
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIB1
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIB2
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIB3
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIB4
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIB5
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIB6
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIB7
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIR1
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIR2
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIR3
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIR4
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIR5
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIR6
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIR7
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeIR8

/-!
# Typing from validity: straight-line vector code is typed in `simEnv20V B`

An earlier step typed an integer vector operator only by reading it off the typed code of a
`Good20B` configuration (`VecTyp.instr_vecNB_of_good20B`, with the instruction in the code).
That hypothesis can never be met: `Good20B` code is `okB`, and `okB` admits no vector operator
(`not_mem_vecIntUnOp_good20B`, …), so the three integer `_good20B` lifts  are vacuous.

Here the typing comes from V2 validation instead:

* **`typedA_vecIntUnOp_valid`**, `typedA_vecIntBinOp_valid`, `typedA_vecIntRelOp_valid`: every
  integer vector operator V2 accepts at its shape (`VecIntUnOp.valid`, `V2.VecIntBinOp.valid`,
  `IntRelOp.validShape`, which are `V2.Instr.immediatesValid`) is a typed `admininstr` of
  `simEnv20V B`, for every `B`. The 79 valid pairs are checked by evaluation (`VecWholeIU*`,
  `VecWholeIB*`, `VecWholeIR*`).
* `typedA_of_vecOkI`: every instruction of straight-line vector code is typed, and
  **`typV_of_vecOk`**: a configuration with straight-line vector code and a typed state is
  `TypV`. **`typV_of_good20B`**: in particular at the state of any `Good20B` configuration.
* `sstepV_vecIntUnOp_valid`, …: an earlier integer lifts at a `Good20B` state with validity in
  place of the unsatisfiable membership hypothesis.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecWhole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (SStep cfgV TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V typedV_of_hasTyp_true)
open Silmaril.Wasm.SpecTec.Sim20.VecNum (vecNB vecNumAgree_vecNB)

variable {B : Builtins}

/-! ## The integer operators, from validity -/

/-- **A valid integer `vunop` is a typed `admininstr` of `simEnv20V B`.** -/
theorem typedA_vecIntUnOp_valid {s : IntShape} {op : VecIntUnOp} (h : op.valid s = true) :
    TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV (.vecIntUnOp s op)) := by
  refine typedV_of_hasTyp_true (n := 200) ?_
  cases s <;> cases op <;> simp [VecIntUnOp.valid] at h <;> first
    | (apply hasTyp_iu_1; decide)
    | (apply hasTyp_iu_2; decide)

/-- **A valid integer `vbinop` is a typed `admininstr` of `simEnv20V B`.** -/
theorem typedA_vecIntBinOp_valid {s : IntShape} {op : V2.VecIntBinOp} (h : op.valid s = true) :
    TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV (.vecIntBinOp s op)) := by
  refine typedV_of_hasTyp_true (n := 200) ?_
  cases s <;> rcases op with _ | _ | _ | (_ | _) | (_ | _) | _ | _ | (_ | _) | (_ | _) <;>
    simp [V2.VecIntBinOp.valid, IntShape.laneWidth] at h <;> first
    | (apply hasTyp_ib_1; decide)
    | (apply hasTyp_ib_2; decide)
    | (apply hasTyp_ib_3; decide)
    | (apply hasTyp_ib_4; decide)
    | (apply hasTyp_ib_5; decide)
    | (apply hasTyp_ib_6; decide)
    | (apply hasTyp_ib_7; decide)

/-- **A valid integer `vrelop` is a typed `admininstr` of `simEnv20V B`.** -/
theorem typedA_vecIntRelOp_valid {s : IntShape} {op : IntRelOp} (h : op.validShape s = true) :
    TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV (.vecIntRelOp s op)) := by
  refine typedV_of_hasTyp_true (n := 200) ?_
  cases s <;> rcases op with _ | _ | (_ | _) | (_ | _) | (_ | _) | (_ | _) <;>
    simp [IntRelOp.validShape] at h <;> first
    | (apply hasTyp_ir_1; decide)
    | (apply hasTyp_ir_2; decide)
    | (apply hasTyp_ir_3; decide)
    | (apply hasTyp_ir_4; decide)
    | (apply hasTyp_ir_5; decide)
    | (apply hasTyp_ir_6; decide)
    | (apply hasTyp_ir_7; decide)
    | (apply hasTyp_ir_8; decide)

end Silmaril.Wasm.SpecTec.Sim20.VecWhole
