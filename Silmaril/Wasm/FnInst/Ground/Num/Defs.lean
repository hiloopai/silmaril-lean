module

public import Silmaril.Wasm.Execution.Core.Sim.Closure.Basic
public import Silmaril.Wasm.SingleThreaded.Exec.Pure

@[expose] public section

/-! # A grounded stack fragment with both integer types, traps and branches

The first grounded fragment (`Silmaril.Wasm.FnInst.Ground.Defs`) has the non-trapping `i32`
binary operators and `i32.eqz` only, so its restatements of `neutral-ops` and `eqz-pair` cover
part of those stages. This fragment has what the full stages need, and nothing that reads the
frame:

* `NInstr`: integer constants, unary, binary, test and comparison operators of **both**
  integer types (shifts, rotations, division and remainder included), `drop`, `nop`, `select`
  and `br_if`, each lowered to one silmaril `Instr` (`NInstr.lower`);
* `run c st`: a straight-line interpreter on a top-first operand stack. Its outcome is either
  the final stack (`Out.ok`) or a **stop** (`Out.stop W k c'`): the stack `W` below a
  `trap` (division by zero, signed overflow) or a `br l` (a taken `br_if`), with the code `c'`
  still after it. `none` is the stuck machine (an operand of the wrong type, too few
  operands);
* `RunRef a b`: wherever `a` has an outcome, `b` has the same one;
* `NGood a b`: a left side that is not all constants with `RunRef`; `NBI`, `NB` the source
  and runtime base relations of silmaril's code-simulation closure.

The bridge `nBaseSim : BaseSim P closedHost F NBI NB gCodeRank` (every numerical profile) is in
`Silmaril.Wasm.FnInst.Ground.Num.Thms`.
-/

namespace Silmaril.Wasm.FnInst.Ground.Num

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Exec.Pure (asInt)

/-- Instructions of the stack fragment. -/
inductive NInstr where
  | const (t : IntType) (k : BitVec t.width)
  | un (t : IntType) (op : IntUnOp)
  | bin (t : IntType) (op : IntBinOp)
  | test (t : IntType) (op : IntTestOp)
  | rel (t : IntType) (op : IntRelOp)
  | drop
  | nop
  | select (ts : Option (List ValType))
  | brIf (l : LabelIdx)

/-- The silmaril instruction. -/
def NInstr.lower : NInstr → Instr
  | .const t k => .intConst t k
  | .un t op => .intUnOp t op
  | .bin t op => .intBinOp t op
  | .test t op => .intTestOp t op
  | .rel t op => .intRelOp t op
  | .drop => .drop
  | .nop => .nop
  | .select ts => .select ts
  | .brIf l => .brIf l

/-- The silmaril instruction sequence. -/
def lower (c : List NInstr) : List Instr := c.map NInstr.lower

/-- Constants (values, not redexes, in silmaril's administrative syntax). -/
def NInstr.isConst : NInstr → Bool
  | .const _ _ => true
  | _ => false

/-- The value of a constant. -/
def NInstr.cval : NInstr → Val
  | .const t k => .num ⟨.int t, k⟩
  | _ => .num ⟨.int .i32, 0⟩

/-- The outcome of one instruction: a new stack, or a stop below a `trap` or a `br`. -/
inductive Out1 where
  | ok (st : List Val)
  | stop (st : List Val) (k : Admin)

/-- The outcome of a run: the final stack, or a stop with the code still after it. -/
inductive Out where
  | ok (st : List Val)
  | stop (st : List Val) (k : Admin) (c : List NInstr)

/-- One instruction on a **top-first** operand stack; `none` when the machine is stuck. -/
def nstep : NInstr → List Val → Option Out1
  | .const t k, st => some (.ok (.num ⟨.int t, k⟩ :: st))
  | .un t op, v :: st => (asInt t v).map fun x => .ok (.num ⟨.int t, intUnOp t op x⟩ :: st)
  | .bin t op, y :: x :: st => (asInt t x).bind fun x => (asInt t y).map fun y =>
      match intBinOp t op x y with
      | .ok z => .ok (.num ⟨.int t, z⟩ :: st)
      | .error _ => .stop st .trap
  | .test t op, v :: st => (asInt t v).map fun x => .ok (Val.i32 (intTestOp t op x) :: st)
  | .rel t op, y :: x :: st => (asInt t x).bind fun x => (asInt t y).map fun y =>
      .ok (Val.i32 (intRelOp t op x y) :: st)
  | .drop, _ :: st => some (.ok st)
  | .nop, st => some (.ok st)
  | .select _, c :: b :: a :: st => (asInt .i32 c).map fun c =>
      .ok ((if c = 0 then b else a) :: st)
  | .brIf l, c :: st => (asInt .i32 c).map fun c =>
      if c = 0 then .ok st else .stop st (.plain (.br l))
  | _, _ => none

/-- Straight-line code on a top-first operand stack. -/
def run : List NInstr → List Val → Option Out
  | [], st => some (.ok st)
  | i :: c, st => (nstep i st).bind fun
    | .ok st' => run c st'
    | .stop st' k => some (.stop st' k c)

/-- **Equal outcomes, left-defined.** -/
def RunRef (a b : List NInstr) : Prop :=
  ∀ st o, run a st = some o → run b st = some o

/-- Code containing an instruction that is not a constant. -/
def StkOp (a : List NInstr) : Prop := ∃ i ∈ a, i.isConst = false

/-- The pairs of the bridge. -/
def NGood (a b : List NInstr) : Prop := StkOp a ∧ RunRef a b

/-- Source base pairs: lowered good pairs. -/
def NBI (x y : List Instr) : Prop :=
  ∃ a b, NGood a b ∧ x = lower a ∧ y = lower b

/-- The semantic condition of a runtime pair (`q`, `r`: values already pushed, bottom first). -/
def PairRef (q : List Val) (a : List NInstr) (r : List Val) (b : List NInstr) : Prop :=
  ∀ S o, run a (q.reverse ++ S) = some o → run b (r.reverse ++ S) = some o

/-- Runtime base pairs. -/
def NB (x y : List Admin) : Prop :=
  ∃ q a r b, x = vals q ++ expression (lower a) ∧ y = vals r ++ expression (lower b) ∧
    StkOp a ∧ PairRef q a r b

end Silmaril.Wasm.FnInst.Ground.Num
