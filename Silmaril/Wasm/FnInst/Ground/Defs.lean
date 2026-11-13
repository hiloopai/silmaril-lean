module

public import Silmaril.Wasm.Execution.Core.Sim.Closure.Basic
public import Silmaril.Wasm.Execution.Core.Sim.Rank

@[expose] public section

/-! # Grounding straight-line segments in silmaril-lean's Wasm Core semantics

The opt track's segment institution (`Silmaril.Wasm.FnInst.Opt`) runs a small `i32` fragment
under its own big-step semantics. This module grounds the call-free, global-free part of
that fragment in silmaril-lean's small-step semantics (`Execution.Core.Step`), stated over
silmaril's own instructions, frames and values:

* `GInstr`: `i32.const`, the non-trapping `i32` binary operators (`add`, `sub`, `mul`,
  `and`, `or`, `xor`), `i32.eqz`, `local.get`, `local.set`, `local.tee`, `drop`, `nop`,
  each lowered to one silmaril `Instr` (`GInstr.lower`);
* `run c f st`: a functional straight-line interpreter over a silmaril `Frame` and a
  top-first operand stack of silmaril `Val`s (`none`: the small-step machine is stuck,
  for instance on an `i64` operand of `i32.add` or on a missing local). Its adequacy for
  `Step` is proved in `Silmaril.Proofs.Wasm.FnInst.Ground.Adequacy`;
* `RunRef a b`: **equal runs, left-defined**: from every frame and stack where `a` runs to a
  result, `b` runs to the same result (frame and stack);
* `Good a b`: the pairs the bridge accepts, with `RunRef a b` and a restricted left side:
  stack-only code (no local access) that is not all constants, or one `local.get` followed
  by stack-only code that never gets stuck. The right side is any code of the fragment;
* `GBI`, `GB`: the source and runtime base relations of silmaril's code-simulation closure
  (`Execution.Core.Sim.BaseSim`) for good pairs, and `gRank`, the stuttering rank.

The bridge theorem (`Silmaril.Wasm.FnInst.Ground.Thms`) is `gBaseSim`: `BaseSim` for `GBI`/`GB`
at every numerical profile under the closed host; with silmaril's closure it gives export
equivalence of modules whose bodies differ by good pairs (`exportEquiv_of_good`).
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The non-trapping `i32` binary operators of the grounded fragment. -/
inductive Bin where
  | add | sub | mul | and | or | xor
  deriving DecidableEq, Repr

/-- The silmaril operator. -/
def Bin.op : Bin → IntBinOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .and => .and
  | .or => .or
  | .xor => .xor

/-- The value of the operator (it never traps). -/
def Bin.eval : Bin → BitVec 32 → BitVec 32 → BitVec 32
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b

/-- Instructions of the grounded fragment. -/
inductive GInstr where
  | const (k : BitVec 32)
  | bin (b : Bin)
  | eqz
  | localGet (x : LocalIdx)
  | localSet (x : LocalIdx)
  | localTee (x : LocalIdx)
  | drop
  | nop
  deriving DecidableEq, Repr

/-- The silmaril instruction. -/
def GInstr.lower : GInstr → Instr
  | .const k => .intConst .i32 k
  | .bin b => .intBinOp .i32 b.op
  | .eqz => .intTestOp .i32 .eqz
  | .localGet x => .localGet x
  | .localSet x => .localSet x
  | .localTee x => .localTee x
  | .drop => .drop
  | .nop => .nop

/-- The silmaril instruction sequence. -/
def lower (c : List GInstr) : List Instr := c.map GInstr.lower

/-- Stack-only instructions: they neither read nor write the frame or the store. -/
def GInstr.stk : GInstr → Bool
  | .localGet _ | .localSet _ | .localTee _ => false
  | _ => true

/-- Constants (which are values, not redexes, in silmaril's administrative syntax). -/
def GInstr.isConst : GInstr → Bool
  | .const _ => true
  | _ => false

/-- The payload of an `i32` value. -/
def asI32 : Val → Option (BitVec 32)
  | .num ⟨.int .i32, x⟩ => some x
  | _ => none

/-- A stack-only instruction on a **top-first** operand stack; `none` when the small-step
machine is stuck (an operand of the wrong type, too few operands) or for local access. -/
def stepS : GInstr → List Val → Option (List Val)
  | .const k, st => some (.i32 k :: st)
  | .bin b, y :: x :: st =>
    (asI32 x).bind fun x => (asI32 y).map fun y => .i32 (b.eval x y) :: st
  | .eqz, x :: st => (asI32 x).map fun x => .i32 (Numerics.intTestOp .i32 .eqz x) :: st
  | .drop, _ :: st => some st
  | .nop, st => some st
  | _, _ => none

/-- One instruction on a frame and a top-first operand stack; `none` when the small-step
machine is stuck. -/
def step1 : GInstr → Frame → List Val → Option (Frame × List Val)
  | .localGet x, f, st => (f.local? x).bind fun o => o.map fun v => (f, v :: st)
  | .localSet x, f, v :: st => if x.toNat < f.locals.length then some (f.setLocal x v, st) else none
  | .localTee x, f, v :: st =>
    if x.toNat < f.locals.length then some (f.setLocal x v, v :: st) else none
  | i, f, st => (stepS i st).map fun st' => (f, st')

/-- Straight-line code on a frame and a top-first operand stack. -/
def run : List GInstr → Frame → List Val → Option (Frame × List Val)
  | [], f, st => some (f, st)
  | i :: c, f, st => (step1 i f st).bind fun r => run c r.1 r.2

/-- **Equal runs, left-defined**: wherever `a` runs to a result, `b` runs to the same one. -/
def RunRef (a b : List GInstr) : Prop :=
  ∀ f st r, run a f st = some r → run b f st = some r

/-- Stack-only code containing an instruction that is not a constant. -/
def StkOp (a : List GInstr) : Prop :=
  (∀ i ∈ a, i.stk = true) ∧ ∃ i ∈ a, i.isConst = false

/-- The pairs the bridge accepts. Either the left side is stack-only (`stk`), or it reads one
local and then runs stack-only code that never gets stuck (`read`); in both cases with equal
runs. The right side is any code of the fragment. -/
def Good (a b : List GInstr) : Prop :=
  (StkOp a ∧ RunRef a b) ∨
    ((∃ x L, a = .localGet x :: L ∧ (∀ i ∈ L, i.stk = true) ∧
      ∀ f v X, (run L f (v :: X)).isSome) ∧ RunRef a b)

/-- Source base pairs: lowered good pairs. -/
def GBI (x y : List Instr) : Prop :=
  ∃ a b, Good a b ∧ x = lower a ∧ y = lower b

/-- The semantic condition of a runtime pair: `q` and `r` are the values already pushed
by the left and right sides (bottom first), `a` and `b` the code still to run. -/
def PairRef (q : List Val) (a : List GInstr) (r : List Val) (b : List GInstr) : Prop :=
  ∀ f S res, run a f (q.reverse ++ S) = some res → run b f (r.reverse ++ S) = some res

/-- Runtime base pairs. Either a stack-only left side, after values `q`, against values `r`
and the rest `b` of the right side, with equal runs from every frame and every stack below
(`PairRef`); or a source pair of the `read` kind, before its first step. The pairs do not
depend on the frame: a stack-only step reads nothing from it, and the right side commits to
its whole run at the left's local read. -/
def GB (x y : List Admin) : Prop :=
  (∃ q a r b, x = vals q ++ expression (lower a) ∧ y = vals r ++ expression (lower b) ∧
    StkOp a ∧ PairRef q a r b) ∨
  (∃ a b, x = expression (lower a) ∧ y = expression (lower b) ∧ Good a b)

mutual
  /-- Values weigh `1`, other instructions `2`: every step of a stack-only
  instruction and of `local.get` lowers the rank, including `local.get` (an instruction becomes a value). -/
  def gAdminRank : Admin → Nat
    | .label _ _ b | .handler _ _ b | .frame _ _ b => 1 + gCodeRank b
    | .plain (.intConst _ _) | .plain (.floatConst _ _) | .plain (.vecConst _) | .ref _ => 1
    | _ => 2

  /-- The stuttering rank of the bridge (payload independent). -/
  def gCodeRank : List Admin → Nat
    | [] => 0
    | a :: l => gAdminRank a + gCodeRank l
end

end Silmaril.Wasm.FnInst.Ground
