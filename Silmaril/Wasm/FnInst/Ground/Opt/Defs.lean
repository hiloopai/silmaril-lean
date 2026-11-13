module

public import Silmaril.Wasm.FnInst.Ground.Defs
public import Silmaril.Wasm.FnInst.Opt.Seg.Defs

@[expose] public section

/-! # The opt track's stack-only segments, grounded

The opt track (`Silmaril.Wasm.FnInst.Opt`) runs its fragment over `i32` values only, under its
own big-step semantics with stack heights as types. Its stack-only instructions (`i32.const`,
the six binary operators, `i32.eqz`, `drop`) translate one to one into the grounded fragment
(`ofOptStk`, `trStk`); the translation keeps stack heights (`popS`, `pushS`, `chkS`).

`Forces n g`: whenever `g` runs, the top `n` operands it starts from are `i32` values. Equal
runs in the opt semantics only speak about `i32` operands; on the machine an operand of another
type can make one side run and the other get stuck (`drop` against `i32.eqz; drop`), so the
transfer of an opt equivalence to `RunRef` (`runRef_of_runEq`) asks the left side to force the
type of its inputs.
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The stack-only instructions of the opt fragment. -/
def ofOptStk : Opt.Instr → Option GInstr
  | .const k => some (.const k)
  | .add => some (.bin .add)
  | .sub => some (.bin .sub)
  | .mul => some (.bin .mul)
  | .and => some (.bin .and)
  | .or => some (.bin .or)
  | .xor => some (.bin .xor)
  | .eqz => some .eqz
  | .drop => some .drop
  | _ => none

/-- Stack-only opt code, translated. -/
def trStk (c : Opt.Code) : Option (List GInstr) := c.mapM ofOptStk

/-- Operands popped by a stack-only instruction. -/
def popS : GInstr → ℕ
  | .bin _ => 2
  | .eqz | .drop => 1
  | _ => 0

/-- Results pushed by a stack-only instruction. -/
def pushS : GInstr → ℕ
  | .const _ | .bin _ | .eqz => 1
  | _ => 0

/-- Stack heights of stack-only code (`none`: underflow). -/
def chkS : List GInstr → ℕ → Option ℕ
  | [], h => some h
  | i :: c, h => if popS i ≤ h then chkS c (h - popS i + pushS i) else none

/-- The top `n` operands of every stack `g` runs from are `i32` values. -/
def Forces (n : ℕ) (g : List GInstr) : Prop :=
  ∀ f st r, run g f st = some r →
    ∃ (vs : List (BitVec 32)) (S : List Val), st = vs.map Val.i32 ++ S ∧ vs.length = n

/-- The outcome of an opt run as a machine stack (`none`: trap or divergence). -/
def outS : Opt.Out → Option (List Val)
  | .ok st => some (st.stack.map Val.i32)
  | _ => none

/-- Deterministic execution of call-free opt code. -/
def execStk : Opt.Code → Opt.St → Opt.Out
  | [], st => .ok st
  | i :: c, st =>
    match Opt.exec1 i st with
    | .ok st' => execStk c st'
    | o => o

end Silmaril.Wasm.FnInst.Ground
