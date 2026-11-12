module

public import Silmaril.Wasm.Examples.Common.Defs
public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Logic.LinArith.Defs

@[expose] public section

/-!
# A Farkas certificate checker in Wasm: the module and its specification

`farkasMod` is a Core 3.0 module (silmaril-lean `Module`) checking **Farkas certificates of
infeasibility** (`Silmaril.Logic.LinArith`) for systems `A x ≤ b` with integer coefficients,
streamed in through three exports:

```wat
(func (export "row")   (param $y i64) (param $b i64))   ;; new inequality, bound b, multiplier y
(func (export "entry") (param $j i32) (param $a i64))   ;; coefficient a of variable x_j
(func (export "check") (result i32))                    ;; 1 certifies infeasibility; then reset
```

State: globals `bad : i32`, `hasRow : i32`, `y : i64` (the current multiplier), `accB : i64`
(`∑ yᵢ bᵢ`), and one page of memory holding `acc[j] : i64` at `8 j` for `j < nVars = 8192`
(`∑ᵢ yᵢ aᵢⱼ`). Overflow is excluded by **bounds, not bignums**: multipliers, bounds and
coefficients must lie in `[-2³⁰, 2³⁰]` (and `y ≥ 0`), indices satisfy `j < nVars`, and
accumulators lie in `[-2⁶², 2⁶²]`; then each product is at most
`2⁶⁰` in absolute value and each new accumulator value is computed exactly in `i64`. A value
outside these bounds, a negative multiplier, an `entry` before any `row` or a variable index
`j ≥ nVars` sets the sticky flag `bad`. `check` scans (and zeroes) all `nVars` slots and returns
`bad = 0 ∧ ∀ j, acc[j] = 0 ∧ accB < 0`, then resets the state. All three bodies are
straight-line except the scan loop of `check`. From represented machine stores with a page of
memory, the body and total-correctness specifications establish normal typed returns: entry
addresses are masked to the page and the scan counter stays in bounds. This does not assert
safety from arbitrary stores.

Specification (`next`, `Good`): the abstract state is the list of weighted rows
(`Silmaril.Logic.LinArith.WRows`) loaded since the last `check`: `row` and `entry` act as
`Cmd.apply` on the arguments' integer values (`BitVec.toInt`, `BitVec.toNat` for `j`), whatever
they return; `check` empties it. A `check` call answering `1` is `Good` if the rows loaded
before it carry a valid certificate (`WRows.IsCert`), so their system is infeasible over every
ordered field. The loaded system includes every `row`/`entry` call since the last `check`,
including those with out-of-range arguments (they only make `check` fail); entries before the
first row are not part of the system (and make `check` fail).

`farkasI` is the module's scalar instance (instantiated by silmaril-lean's
`instantiateOnce?` against no imports). A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
open Silmaril.Logic.LinArith (WRows Cmd)
open Silmaril.Wasm.Spec.Multi (Call)

/-- Number of variable slots. -/
def nVars : Nat := 8192
/-- Bound on inputs. -/
def cB : Int := 2 ^ 30
/-- Bound on accumulators. -/
def aB : Int := 2 ^ 62

/-- An `i64.const`. -/
def i64c (v : Int) : Instr := .intConst .i64 (BitVec.ofInt 64 v)
/-- An `i32.const`. -/
def i32c (v : Nat) : Instr := .intConst .i32 (BitVec.ofNat 32 v)
/-- The memory argument of the 8-byte accesses. -/
def ma8 : MemArg := ⟨3, 0⟩

/-- Or the flag on the stack with "`local x` is out of `[lo, hi]`" (i64, signed). -/
def orOut (x : LocalIdx) (lo hi : Int) : List Instr :=
  [.localGet x, i64c lo, .intRelOp .i64 (.lt .signed), .intBinOp .i32 .or,
   .localGet x, i64c hi, .intRelOp .i64 (.gt .signed), .intBinOp .i32 .or]

/-- `row(y, b)`: check `0 ≤ y ≤ 2³⁰`, `|b| ≤ 2³⁰`, `|accB + y b| ≤ 2⁶²`; set `y`, `accB`, `hasRow`. -/
def rowBody : List Instr :=
  [.globalGet ⟨0⟩] ++ orOut ⟨0⟩ 0 cB ++ orOut ⟨1⟩ (-cB) cB ++
  [.globalGet ⟨3⟩, .localGet ⟨0⟩, .localGet ⟨1⟩, .intBinOp .i64 .mul, .intBinOp .i64 .add,
   .localSet ⟨2⟩] ++ orOut ⟨2⟩ (-aB) aB ++
  [.globalSet ⟨0⟩, .localGet ⟨2⟩, .globalSet ⟨3⟩, .localGet ⟨0⟩, .globalSet ⟨2⟩,
   i32c 1, .globalSet ⟨1⟩]

/-- `entry(j, a)`: check `hasRow`, `j < nVars`, `|a| ≤ 2³⁰`; add `y a` to `acc[j mod nVars]` and
check `|acc[j]| ≤ 2⁶²`. -/
def entryBody : List Instr :=
  [.globalGet ⟨0⟩, .globalGet ⟨1⟩, .intTestOp .i32 .eqz, .intBinOp .i32 .or,
   .localGet ⟨0⟩, i32c nVars, .intRelOp .i32 (.ge .unsigned), .intBinOp .i32 .or] ++
  orOut ⟨1⟩ (-cB) cB ++
  [.localGet ⟨0⟩, i32c (nVars - 1), .intBinOp .i32 .and, i32c 3, .intBinOp .i32 .shl,
   .localSet ⟨2⟩, .localGet ⟨2⟩,
   .localGet ⟨2⟩, .intLoad .i64 none ⟨0⟩ ma8, .globalGet ⟨2⟩, .localGet ⟨1⟩,
   .intBinOp .i64 .mul, .intBinOp .i64 .add, .localSet ⟨3⟩,
   .localGet ⟨3⟩, .intStore .i64 none ⟨0⟩ ma8] ++ orOut ⟨3⟩ (-aB) aB ++ [.globalSet ⟨0⟩]

/-- The scan loop of `check`: for `i < nVars`, `nz |= acc[i] ≠ 0; acc[i] := 0`. -/
def loopBody : List Instr :=
  [.localGet ⟨0⟩, i32c nVars, .intRelOp .i32 (.ge .unsigned), .brIf ⟨1⟩,
   .localGet ⟨1⟩, .localGet ⟨0⟩, i32c 3, .intBinOp .i32 .shl, .intLoad .i64 none ⟨0⟩ ma8,
   i64c 0, .intRelOp .i64 .ne, .intBinOp .i32 .or, .localSet ⟨1⟩,
   .localGet ⟨0⟩, i32c 3, .intBinOp .i32 .shl, i64c 0, .intStore .i64 none ⟨0⟩ ma8,
   .localGet ⟨0⟩, i32c 1, .intBinOp .i32 .add, .localSet ⟨0⟩, .br ⟨0⟩]

/-- `check()`: scan, compute `bad = 0 ∧ nz = 0 ∧ accB < 0`, reset the globals. -/
def checkBody : List Instr :=
  [.block .empty [.loop .empty loopBody],
   .globalGet ⟨0⟩, .intTestOp .i32 .eqz, .localGet ⟨1⟩, .intTestOp .i32 .eqz, .intBinOp .i32 .and,
   .globalGet ⟨3⟩, i64c 0, .intRelOp .i64 (.lt .signed), .intBinOp .i32 .and,
   i32c 0, .globalSet ⟨0⟩, i32c 0, .globalSet ⟨1⟩, i64c 0, .globalSet ⟨2⟩, i64c 0, .globalSet ⟨3⟩]

/-- **The checker module.** -/
def farkasMod : Module where
  types := [⟨[⟨true, [], .func ⟨[.i64, .i64], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[.i32, .i64], []⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  globals := [⟨⟨.var, .i32⟩, [i32c 0]⟩, ⟨⟨.var, .i32⟩, [i32c 0]⟩, ⟨⟨.var, .i64⟩, [i64c 0]⟩,
    ⟨⟨.var, .i64⟩, [i64c 0]⟩]
  memories := [⟨.i32, ⟨1, some 1⟩⟩]
  funcs := [⟨⟨0⟩, [.i64], rowBody⟩, ⟨⟨1⟩, [.i32, .i64], entryBody⟩, ⟨⟨2⟩, [.i32, .i32], checkBody⟩]
  exports := [⟨"row", .func ⟨0⟩⟩, ⟨"entry", .func ⟨1⟩⟩, ⟨"check", .func ⟨2⟩⟩]

/-- The function types of the exports. -/
def farkasExports : List FnType :=
  [⟨[.num (.int .i64), .num (.int .i64)], []⟩, ⟨[.num (.int .i32), .num (.int .i64)], []⟩,
    ⟨[], [.num (.int .i32)]⟩]

/-- The instantiation of `farkasMod` against no imports. -/
def farkasRun : Option (Store Nat × Frame × Option FuncIdx) :=
  instantiateOnce? (importStore []) farkasMod []

/-- The store after instantiation. -/
def farkasStore : Store Nat :=
  match farkasRun with
  | some (s, _, _) => s
  | none => {}

/-- The module instance. -/
def farkasMI : ModuleInst :=
  match farkasRun with
  | some (_, f, _) => f.module
  | none => {}

/-- **The checker's scalar instance.** -/
def farkasI : ScalarInstance where
  imports := []
  exports := farkasExports
  addrs := [0, 1, 2]
  store := farkasStore

/-! ## The specification -/

/-- The loading command of a call of export `j` on `args` (`row` and `entry` only). -/
def cmdOf : Nat → List Val → Option Cmd
  | 0, [.num ⟨.int .i64, y⟩, .num ⟨.int .i64, b⟩] => some (.row y.toInt b.toInt)
  | 1, [.num ⟨.int .i32, j⟩, .num ⟨.int .i64, a⟩] => some (.entry j.toNat a.toInt)
  | _, _ => none

variable {I : ScalarInstance}

/-- **The abstract transition**: `row`/`entry` load, `check` empties. -/
def next (rs : WRows) (c : Call I) : WRows :=
  if c.1.1.val = 2 then [] else
    match cmdOf c.1.1.val c.1.2.1 with
    | some cmd => cmd.apply rs
    | none => rs

/-- **Safety of a call**: a `check` answering `1` certifies the rows loaded before it. -/
def Good (rs : WRows) (c : Call I) : Prop :=
  c.1.1.val = 2 → Answer.toResult (ft := I.exports.get c.1.1) c.2 = .values [Val.i32 1] → rs.IsCert

/-- The rows loaded by a list of calls, from the empty state. -/
def loaded (l : List (Call I)) : WRows := Silmaril.Wasm.Examples.Common.after next [] l

/-! ## Completeness: the bounds -/

/-- **A command passes the checker's bounds** on the rows `rs` loaded before it: for `row y b`,
`0 ≤ y ≤ 2³⁰`, `|b| ≤ 2³⁰` and the new bound sum within `2⁶²`; for `entry j a`, a row has been
started, `j < nVars`, `|a| ≤ 2³⁰` and the new accumulator of `j` within `2⁶²`. -/
def CmdOk : WRows → Cmd → Prop
  | rs, .row y b => (0 ≤ y ∧ y ≤ cB) ∧ (-cB ≤ b ∧ b ≤ cB) ∧
      (-aB ≤ WRows.combB ((Cmd.row y b).apply rs) ∧ WRows.combB ((Cmd.row y b).apply rs) ≤ aB)
  | rs, .entry j a => rs ≠ [] ∧ j < nVars ∧ (-cB ≤ a ∧ a ≤ cB) ∧
      (-aB ≤ WRows.comb ((Cmd.entry j a).apply rs) j ∧ WRows.comb ((Cmd.entry j a).apply rs) j ≤ aB)

/-- The rows loaded, and whether every `row`/`entry` since the last `check` passed the bounds. -/
def okNext (a : WRows × Prop) (c : Call I) : WRows × Prop :=
  if c.1.1.val = 2 then ([], True) else
    match cmdOf c.1.1.val c.1.2.1 with
    | some cmd => (cmd.apply a.1, a.2 ∧ CmdOk a.1 cmd)
    | none => a

/-- **Every `row`/`entry` call of `l` since its last `check` passed the bounds.** -/
def LoadsOk (l : List (Call I)) : Prop := (Silmaril.Wasm.Examples.Common.after okNext ([], True) l).2

end Silmaril.Wasm.Examples.Farkas
