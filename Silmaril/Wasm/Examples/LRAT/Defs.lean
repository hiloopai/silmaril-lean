module

public import Silmaril.Wasm.Modules
public import Silmaril.Wasm.Logic.Memory.Defs
public import Silmaril.Logic.SAT.CNF.Defs

@[expose] public section

/-!
# The streaming LRAT checker: the Wasm module

A Core 3.0 module (a silmaril-lean `Module`, written as abstract syntax) that checks LRAT
refutations (RUP and RAT steps) of a DIMACS CNF formula, fed one integer per export call. Its safety theorem is
in `Silmaril.Wasm.Examples.LRAT.Thms`.

## Interface

| export | type | effect |
|---|---|---|
| `add_lit(x)` | `[i32] → []` | DIMACS input: `x ≠ 0` is a literal of the current input clause, `x = 0` ends it |
| `end_clause()` | `[] → []` | the same as `add_lit(0)` |
| `step_begin(id)` | `[i32] → []` | start an LRAT addition step for clause `id` (ends the input phase) |
| `step_lit(x)` | `[i32] → []` | a literal of the clause being added |
| `step_hint(h)` | `[i32] → []` | a RUP hint: unit-propagate with clause `h` |
| `step_end()` | `[] → []` | finish the step: if the hints reached a conflict, store the clause (or record the empty clause) |
| `delete(id)` | `[i32] → []` | delete clause `id` (outside a step) |
| `unsat()` | `[] → [i32]` | `1` once the empty clause has been derived (or read), else `0` |
| `rat_begin(j)` | `[i32] → []` | close the current RAT group and start the group of candidate `j` |
| `rat_end()` | `[] → []` | finish a RAT step: store the clause if every candidate was covered |

Input clauses get the ids `1, 2, …` in order (LRAT convention). Ids are below `1024`, literals
`x` satisfy `-1024 < x < 1024`; out-of-range input closes the input phase (`add_lit`), aborts the
step (`step_lit`), or is ignored (`step_begin`, `step_hint`, `delete`). Calls in the wrong phase
are ignored.

## State

Globals (all mutable `i32`): `0` mode (`0` reading input, `1` idle, `2` in a step), `1` `top`
(next free arena byte), `2` `cstart` (start of the clause being built), `3` the step stamp, `4`
the conflict flag of the current step, `5` the id of the current step, `6` the `unsat` flag, `7`
the next input clause id.

One page of memory (`65536` bytes):

* `[4, 8192)`: the **literal values** `val[x]` at `4096 + 4x`: with stamp `S`, `2S` means "`x` is
  false in the current step", `2S + 1` "`x` is true", anything else "unassigned". A new step
  increments the stamp, which unassigns everything at once;
* `[8192, 12288)`: `start[id]` at `8192 + 4·id`, the arena address of clause `id`;
* `[12288, 16384)`: `len[id]` at `12288 + 4·id`, its length in **bytes** (`0`: no clause);
* `[16384, 20480)`: `cov[id]` at `16384 + 4·id`, the tag of the step in which candidate `id`
  was covered by a RAT group;
* `20480`: the current RAT candidate plus one (`0`: none); `20484`: the tag of the current step
  (its first stamp);
* `[24576, 65536)`: the **arena**, an append-only array of literals (`i32` words). Stored clauses
  lie below `cstart`; the clause being built is `[cstart, top)`.

A RUP step `step_begin(id)`, `step_lit(x)…`, `step_hint(h)…`, `step_end()` assigns every literal
of the clause false (`step_lit`); each hint scans clause `h` (a loop over its words) counting the
literals not assigned false: none is a conflict, exactly one is assigned true.

A RAT step on the pivot `p` (the first literal of the clause) is `step_begin(id)`, `step_lit(x)…`,
then for each candidate `j` (a stored clause containing `-p`) `rat_begin(j)` and its hints
`step_hint(h)…`, then `rat_end()`. `rat_begin(j)` marks the previous candidate covered
(`cov := tag`) if its group reached a conflict, takes a fresh stamp and assigns false every literal
of the clause and every literal of clause `j` other than `-p` (two loops). `rat_end()` closes the
last group, scans every stored clause not covered in this step for `-p` (a loop over ids around a
loop over words) and stores the clause if none contains it. Hints shared by all groups are
repeated in each group.

New code (no source).
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Wasm

/-! ## Instruction shorthands -/

/-- `i32.const n`. -/
abbrev c32 (n : Nat) : Instr := .intConst .i32 (BitVec.ofNat 32 n)
/-- `local.get k`. -/
abbrev lget (k : Nat) : Instr := .localGet ⟨⟨k % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩
/-- `local.set k`. -/
abbrev lset (k : Nat) : Instr := .localSet ⟨⟨k % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩
/-- `global.get k`. -/
abbrev gget (k : Nat) : Instr := .globalGet ⟨⟨k % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩
/-- `global.set k`. -/
abbrev gset (k : Nat) : Instr := .globalSet ⟨⟨k % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩
/-- `i32.add`. -/
abbrev iadd : Instr := .intBinOp .i32 .add
/-- `i32.sub`. -/
abbrev isub : Instr := .intBinOp .i32 .sub
/-- `i32.mul`. -/
abbrev imul : Instr := .intBinOp .i32 .mul
/-- `i32.and`. -/
abbrev iand : Instr := .intBinOp .i32 .and
/-- `i32.eq`. -/
abbrev ieq : Instr := .intRelOp .i32 .eq
/-- `i32.ne`. -/
abbrev ine : Instr := .intRelOp .i32 .ne
/-- `i32.lt_u`. -/
abbrev iltu : Instr := .intRelOp .i32 (.lt .unsigned)
/-- `i32.ge_u`. -/
abbrev igeu : Instr := .intRelOp .i32 (.ge .unsigned)
/-- `i32.eqz`. -/
abbrev ieqz : Instr := .intTestOp .i32 .eqz
/-- `i32.load` at offset `0`. -/
abbrev iload : Instr := .intLoad .i32 none ⟨0⟩ ⟨2, 0⟩
/-- `i32.store` at offset `0`. -/
abbrev istore : Instr := .intStore .i32 none ⟨0⟩ ⟨2, 0⟩
/-- `if (then t) end`, of empty block type. -/
abbrev ifThen (t : List Instr) : Instr := .if_ .empty t []

/-! ## Globals and layout -/

/-- Global indices. -/
abbrev gMode : Nat := 0
abbrev gTop : Nat := 1
abbrev gCstart : Nat := 2
abbrev gStamp : Nat := 3
abbrev gConfl : Nat := 4
abbrev gStepId : Nat := 5
abbrev gUnsat : Nat := 6
abbrev gNextId : Nat := 7

/-- Base addresses. -/
abbrev valBase : Nat := 4096
abbrev startBase : Nat := 8192
abbrev lenBase : Nat := 12288
/-- `cov[id]` at `covBase + 4·id`: the tag of the step in which candidate `id` was covered. -/
abbrev covBase : Nat := 16384
/-- The current RAT candidate plus one (`0`: none). -/
abbrev candAddr : Nat := 20480
/-- The tag of the current step (its first stamp). -/
abbrev tagAddr : Nat := 20484
abbrev arenaBase : Nat := 24576
abbrev memSize : Nat := 65536
/-- Clause ids are below `maxId`. -/
abbrev maxId : Nat := 1024
/-- Stamps stay below `maxStamp`. -/
abbrev maxStamp : Nat := 2 ^ 29

/-- Push `1` if the local `k` holds a literal in range (`x ≠ 0`, `-1024 < x < 1024`), else `0`. -/
def validLitCode (k : Nat) : List Instr :=
  [lget k, c32 1023, iadd, c32 2047, iltu, lget k, c32 0, ine, iand]

/-- Push the address `4096 + 4x` of `val[x]`, for the value `x` of local `k`. -/
def valAddrCode (k : Nat) : List Instr := [c32 valBase, lget k, c32 4, imul, iadd]

/-- Push the address `4096 - 4x` of `val[-x]`, for the value `x` of local `k`. -/
def negAddrCode (k : Nat) : List Instr := [c32 valBase, lget k, c32 4, imul, isub]

/-- Push the stamp value `2S`. -/
def stamp2Code : List Instr := [gget gStamp, c32 2, imul]

/-- `val[x] := 2S + b; val[-x] := 2S + (1 - b)` for the literal in local `k`: makes `x` false
(`b = 0`) or true (`b = 1`), together with its negation. -/
def assignCode (k b : Nat) : List Instr :=
  valAddrCode k ++ stamp2Code ++ [c32 b, iadd, istore] ++
  negAddrCode k ++ stamp2Code ++ [c32 (1 - b), iadd, istore]

/-! ## `add_lit` and `end_clause` -/

/-- Locals: `0` the literal `x`; `1` "end the clause"; `2` "append `x`"; `3` "close the input";
`4` "the clause is empty"; `5` "record the clause". -/
def addLitBody : List Instr :=
  -- l1 := mode = 0 ∧ x = 0
  [gget gMode, ieqz, lget 0, ieqz, iand, lset 1] ++
  -- l2 := mode = 0 ∧ valid x ∧ top < 65536
  [gget gMode, ieqz] ++ validLitCode 0 ++ [iand, gget gTop, c32 memSize, iltu, iand, lset 2] ++
  -- l3 := mode = 0 ∧ x ≠ 0 ∧ ¬ l2
  [gget gMode, ieqz, lget 0, c32 0, ine, iand, lget 2, ieqz, iand, lset 3] ++
  -- l4 := l1 ∧ top = cstart; l5 := l1 ∧ top ≠ cstart ∧ nextId < 1024
  [lget 1, gget gTop, gget gCstart, ieq, iand, lset 4] ++
  [lget 1, gget gTop, gget gCstart, ine, iand, gget gNextId, c32 maxId, iltu, iand, lset 5] ++
  -- append
  [lget 2, ifThen [gget gTop, lget 0, istore, gget gTop, c32 4, iadd, gset gTop]] ++
  -- close the input
  [lget 3, ifThen [c32 1, gset gMode]] ++
  -- the empty clause
  [lget 4, ifThen [c32 1, gset gUnsat]] ++
  -- record the clause under the next id
  [lget 5, ifThen [c32 startBase, gget gNextId, c32 4, imul, iadd, gget gCstart, istore,
    c32 lenBase, gget gNextId, c32 4, imul, iadd, gget gTop, gget gCstart, isub, istore,
    gget gNextId, c32 1, iadd, gset gNextId]] ++
  -- start the next clause
  [lget 1, ifThen [gget gTop, gset gCstart]]

/-! ## Steps -/

/-- Locals: `0` the clause id; `1` "start". -/
def stepBeginBody : List Instr :=
  [gget gMode, c32 2, ine, lget 0, c32 maxId, iltu, iand, gget gStamp, c32 maxStamp, iltu,
    iand, lset 1] ++
  [lget 1, ifThen [gget gCstart, gset gTop, gget gStamp, c32 1, iadd, gset gStamp,
    c32 0, gset gConfl, lget 0, gset gStepId, c32 2, gset gMode,
    c32 candAddr, c32 0, istore, c32 tagAddr, gget gStamp, istore]]

/-- Locals: `0` the literal `x`; `1` "add it"; `2` "abort the step". -/
def stepLitBody : List Instr :=
  [gget gMode, c32 2, ieq] ++ validLitCode 0 ++ [iand, gget gTop, c32 memSize, iltu, iand,
    lset 1] ++
  [gget gMode, c32 2, ieq, lget 1, ieqz, iand, lset 2] ++
  [lget 1, ifThen ([gget gTop, lget 0, istore, gget gTop, c32 4, iadd, gset gTop] ++
    assignCode 0 0)] ++
  [lget 2, ifThen [gget gCstart, gset gTop, c32 1, gset gMode]]

/-- The hint loop: while `p < e`, read the literal `x` at `p`; if `val[x] ≠ 2S` count it and
remember it; `p += 4`. Locals: `2` `p`, `3` `e`, `4` the count, `5` the last literal counted,
`6` `x`, `7` "not false". -/
def hintLoopBody : List Instr :=
  [lget 2, lget 3, igeu, .brIf ⟨1⟩,
    lget 2, iload, lset 6] ++
  valAddrCode 6 ++ [iload] ++ stamp2Code ++ [ine, lset 7,
    lget 4, lget 7, iadd, lset 4,
    lget 5, lget 7, lget 6, lget 5, isub, imul, iadd, lset 5,
    lget 2, c32 4, iadd, lset 2, .br ⟨0⟩]

/-- Locals: `0` the hint `h`; `1` "valid hint"; `2` `p`; `3` `e`; `4` count; `5` last;
`6` `x`; `7` "not false"; `8` the masked id `h · l1`. -/
def stepHintBody : List Instr :=
  -- l1 := mode = 2 ∧ h < 1024; l8 := h · l1
  [gget gMode, c32 2, ieq, lget 0, c32 maxId, iltu, iand, lset 1,
    lget 0, lget 1, imul, lset 8] ++
  -- l1 := l1 ∧ len[l8] ≠ 0
  [lget 1, c32 lenBase, lget 8, c32 4, imul, iadd, iload, c32 0, ine, iand, lset 1] ++
  -- p := start[l8] · l1; e := p + len[l8] · l1
  [c32 startBase, lget 8, c32 4, imul, iadd, iload, lget 1, imul, lset 2,
    lget 2, c32 lenBase, lget 8, c32 4, imul, iadd, iload, lget 1, imul, iadd, lset 3,
    c32 0, lset 4, c32 0, lset 5] ++
  [.block .empty [.loop .empty hintLoopBody]] ++
  -- no literal left: conflict
  [lget 1, lget 4, ieqz, iand, ifThen [c32 1, gset gConfl]] ++
  -- one literal left: make it true
  [lget 1, lget 4, c32 1, ieq, iand, ifThen (assignCode 5 1)]

/-- Locals: `0` "in a step"; `1` "conflict and empty"; `2` "conflict and nonempty". A conflict
counts only outside a RAT group (`cand = 0`). -/
def stepEndBody : List Instr :=
  [gget gMode, c32 2, ieq, lset 0,
    lget 0, gget gConfl, c32 0, ine, iand, gget gTop, gget gCstart, ieq, iand,
      c32 candAddr, iload, ieqz, iand, lset 1,
    lget 0, gget gConfl, c32 0, ine, iand, gget gTop, gget gCstart, ine, iand,
      c32 candAddr, iload, ieqz, iand, lset 2] ++
  [lget 1, ifThen [c32 1, gset gUnsat]] ++
  [lget 2, ifThen [c32 startBase, gget gStepId, c32 4, imul, iadd, gget gCstart, istore,
    c32 lenBase, gget gStepId, c32 4, imul, iadd, gget gTop, gget gCstart, isub, istore,
    gget gTop, gset gCstart]] ++
  [lget 0, ifThen [gget gCstart, gset gTop, c32 1, gset gMode]]

/-- Locals: `0` the clause id. Ignored inside a step. -/
def deleteBody : List Instr :=
  [lget 0, c32 maxId, iltu, gget gMode, c32 2, ine, iand,
    ifThen [c32 lenBase, lget 0, c32 4, imul, iadd, c32 0, istore]]

/-! ## RAT steps -/

/-- Mark the current candidate covered (`cov[cand - 1] := tag`), when the local `k` is set. -/
def closeCode (k : Nat) : List Instr :=
  [lget k, ifThen [c32 covBase, c32 candAddr, iload, c32 1, isub, c32 4, imul, iadd,
    c32 tagAddr, iload, istore]]

/-- Assign false every word in `[p, e)` other than `skip`. Locals: `2` `p`, `3` `e`, `4` the word
`x`, `5` `skip`. -/
def assignLoopBody : List Instr :=
  [lget 2, lget 3, igeu, .brIf ⟨1⟩,
    lget 2, iload, lset 4,
    lget 4, lget 5, ine, ifThen (assignCode 4 0),
    lget 2, c32 4, iadd, lset 2, .br ⟨0⟩]

/-- `rat_begin(j)`: close the previous group (marking its candidate covered if it reached a
conflict) and start the group of candidate `j`: a fresh stamp, every literal of the step's clause
false, and every literal of clause `j` other than `-p` false (`p` the first literal of the step's
clause). Locals: `0` `j`; `1` "valid"; `2`–`5` the assignment loop; `6` the masked id `j · l1`;
`7` "close". -/
def ratBeginBody : List Instr :=
  [gget gMode, c32 2, ieq, lget 0, c32 maxId, iltu, iand, lset 1,
    lget 0, lget 1, imul, lset 6,
    lget 1, c32 lenBase, lget 6, c32 4, imul, iadd, iload, c32 0, ine, iand,
      gget gTop, gget gCstart, ine, iand, gget gStamp, c32 maxStamp, iltu, iand, lset 1,
    lget 1, c32 candAddr, iload, c32 0, ine, iand, gget gConfl, c32 0, ine, iand, lset 7] ++
  closeCode 7 ++
  [lget 1, ifThen [gget gStamp, c32 1, iadd, gset gStamp, c32 0, gset gConfl,
    c32 candAddr, lget 0, c32 1, iadd, istore]] ++
  [gget gCstart, lget 1, imul, lset 2, gget gTop, lget 1, imul, lset 3, c32 0, lset 5,
    .block .empty [.loop .empty assignLoopBody]] ++
  [c32 startBase, lget 6, c32 4, imul, iadd, iload, lget 1, imul, lset 2,
    lget 2, c32 lenBase, lget 6, c32 4, imul, iadd, iload, lget 1, imul, iadd, lset 3,
    c32 0, gget gCstart, lget 1, imul, iload, isub, lset 5,
    .block .empty [.loop .empty assignLoopBody]]

/-- Scan the words in `[p, e)` for `skip`, setting `bad`. Locals: `3` `p`, `4` `e`, `5` `skip`,
`6` `bad`, `9` the word. -/
def scanInnerBody : List Instr :=
  [lget 3, lget 4, igeu, .brIf ⟨1⟩,
    lget 3, iload, lset 9,
    lget 9, lget 5, ieq, ifThen [c32 1, lset 6],
    lget 3, c32 4, iadd, lset 3, .br ⟨0⟩]

/-- For each id `i < e₀`: scan clause `i` if it is stored and not covered in this step. Locals:
`1` `i`, `2` `e₀`, `8` "scan clause `i`". -/
def scanOuterBody : List Instr :=
  [lget 1, lget 2, igeu, .brIf ⟨1⟩,
    c32 lenBase, lget 1, c32 4, imul, iadd, iload, c32 0, ine,
      c32 covBase, lget 1, c32 4, imul, iadd, iload, c32 tagAddr, iload, ine, iand, lset 8,
    c32 startBase, lget 1, c32 4, imul, iadd, iload, lget 8, imul, lset 3,
    lget 3, c32 lenBase, lget 1, c32 4, imul, iadd, iload, lget 8, imul, iadd, lset 4,
    .block .empty [.loop .empty scanInnerBody],
    lget 1, c32 1, iadd, lset 1, .br ⟨0⟩]

/-- `rat_end()`: close the last group, check that every stored clause containing `-p` was
covered in this step, and if so store the step's (nonempty) clause under the step id; leave the
step. Locals: `0` "valid"; `1`, `2`, `8` the outer scan; `3`, `4`, `9` the inner scan; `5`
`skip = -p`; `6` `bad`; `7` "close". -/
def ratEndBody : List Instr :=
  [gget gMode, c32 2, ieq, gget gTop, gget gCstart, ine, iand, lset 0,
    lget 0, c32 candAddr, iload, c32 0, ine, iand, gget gConfl, c32 0, ine, iand, lset 7] ++
  closeCode 7 ++
  [c32 maxId, lget 0, imul, lset 2,
    c32 0, gget gCstart, lget 0, imul, iload, isub, lset 5,
    .block .empty [.loop .empty scanOuterBody]] ++
  [lget 0, lget 6, ieqz, iand, ifThen [c32 startBase, gget gStepId, c32 4, imul, iadd,
    gget gCstart, istore, c32 lenBase, gget gStepId, c32 4, imul, iadd, gget gTop, gget gCstart,
    isub, istore, gget gTop, gset gCstart]] ++
  [lget 0, ifThen [gget gCstart, gset gTop, c32 1, gset gMode]]

/-- Read the `unsat` flag. -/
def unsatBody : List Instr := [gget gUnsat]

/-! ## The module -/

/-- `[i32] → []`. -/
def tyLit : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩
/-- `[] → []`. -/
def tyVoid : RecType := ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩
/-- `[] → [i32]`. -/
def tyGet : RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩

/-- A mutable `i32` global with an initial value. -/
def gvar (n : Nat) : Global := ⟨⟨.var, .i32⟩, [c32 n]⟩

/-- **The LRAT checker.** -/
def lratModule : Module where
  types := [tyLit, tyVoid, tyGet]
  globals := [gvar 0, gvar arenaBase, gvar arenaBase, gvar 0, gvar 0, gvar 0, gvar 0, gvar 1]
  memories := [⟨.i32, ⟨1, some 1⟩⟩]
  funcs := [
    ⟨⟨0⟩, [.i32, .i32, .i32, .i32, .i32], addLitBody⟩,
    ⟨⟨1⟩, [.i32, .i32, .i32, .i32, .i32, .i32], addLitBody⟩,
    ⟨⟨0⟩, [.i32], stepBeginBody⟩,
    ⟨⟨0⟩, [.i32, .i32], stepLitBody⟩,
    ⟨⟨0⟩, [.i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32], stepHintBody⟩,
    ⟨⟨1⟩, [.i32, .i32, .i32], stepEndBody⟩,
    ⟨⟨0⟩, [], deleteBody⟩,
    ⟨⟨2⟩, [], unsatBody⟩,
    ⟨⟨0⟩, [.i32, .i32, .i32, .i32, .i32, .i32, .i32], ratBeginBody⟩,
    ⟨⟨1⟩, [.i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32, .i32], ratEndBody⟩]
  exports := [⟨"add_lit", .func ⟨0⟩⟩, ⟨"end_clause", .func ⟨1⟩⟩, ⟨"step_begin", .func ⟨2⟩⟩,
    ⟨"step_lit", .func ⟨3⟩⟩, ⟨"step_hint", .func ⟨4⟩⟩, ⟨"step_end", .func ⟨5⟩⟩,
    ⟨"delete", .func ⟨6⟩⟩, ⟨"unsat", .func ⟨7⟩⟩, ⟨"rat_begin", .func ⟨8⟩⟩,
    ⟨"rat_end", .func ⟨9⟩⟩]

/-! ## The invariant

The meaning of the checker's state, after the DIMACS stream `xs` has been received: the
globals `G` (`gv G k` is global `k`) and the memory `B`. The headline theorem shows that every
export call keeps `Good` (`Silmaril.Wasm.Examples.LRAT.Thms`). -/

open Silmaril.Wasm.Execution Silmaril.Logic.SAT

/-- The `i32` word at byte `a` (`0` out of bounds). -/
def wd (B : ByteArray) (a : Nat) : BitVec 32 := (Memory.load B a 4).getD 0

/-- Write the `i32` word `v` at byte `a`. -/
def wr (B : ByteArray) (a : Nat) (v : BitVec 32) : ByteArray :=
  Silmaril.Wasm.Logic.Core.storeLE B a 4 v.toNat

/-- Global `k` of a list of global values. -/
abbrev gv (G : List (BitVec 32)) (k : Nat) : BitVec 32 := G.getD k 0

/-- A literal in range: `x ≠ 0` and `-1024 < x < 1024` (as the code tests it). -/
def ValidLit (x : BitVec 32) : Prop := x ≠ 0 ∧ (x + 1023#32).toNat < 2047

/-- The address `4096 + 4x` of `val[x]` (computed in `i32`). -/
def litAddr (x : BitVec 32) : Nat := (4096#32 + x * 4#32).toNat

/-- The address `4096 - 4x` of `val[-x]` (computed in `i32`). -/
def negAddr (x : BitVec 32) : Nat := (4096#32 - x * 4#32).toNat

/-- The `n` words from byte `p`. -/
def words (B : ByteArray) (p n : Nat) : List (BitVec 32) :=
  (List.range n).map fun k => wd B (p + 4 * k)

/-- The clause of a list of literal words (signed). -/
def toClause (ws : List (BitVec 32)) : Clause := ws.map BitVec.toInt

/-- `start[id]` and `len[id]`. -/
def entryStart (B : ByteArray) (id : Nat) : Nat := (wd B (startBase + 4 * id)).toNat
def entryLen (B : ByteArray) (id : Nat) : Nat := (wd B (lenBase + 4 * id)).toNat

/-- The words of clause `id`. -/
def entryWords (B : ByteArray) (id : Nat) : List (BitVec 32) :=
  words B (entryStart B id) (entryLen B id / 4)

/-- The words of the clause being built, `[cstart, top)`. -/
def bufWords (G : List (BitVec 32)) (B : ByteArray) : List (BitVec 32) :=
  words B (gv G gCstart).toNat (((gv G gTop).toNat - (gv G gCstart).toNat) / 4)

/-- A stored clause: in the arena below `cstart`, a whole number of words, literals in range. -/
structure EntryOk (B : ByteArray) (cstart id : Nat) : Prop where
  base_le : arenaBase ≤ entryStart B id
  end_le : entryStart B id + entryLen B id ≤ cstart
  dvd : 4 ∣ entryLen B id
  valid : ∀ w ∈ entryWords B id, ValidLit w

/-- The clause of entry `id`. -/
def entryClause (B : ByteArray) (id : Nat) : Clause := toClause (entryWords B id)

/-- **The clause database** of the memory: the clauses of the stored ids (`len ≠ 0`), in id
order. -/
def dbOf (B : ByteArray) : CNF :=
  ((List.range maxId).filter fun id => entryLen B id != 0).map (entryClause B)

/-- `τ` satisfies the clause database. -/
def Models (τ : Assignment) (B : ByteArray) : Prop := (dbOf B).eval τ = true

/-- The total assignment `τ` agrees with the literal values of stamp `S`: `2S` means false,
`2S + 1` true. -/
def Agrees (τ : Assignment) (B : ByteArray) (S : BitVec 32) : Prop :=
  ∀ x, ValidLit x → (wd B (litAddr x) = S * 2 → Lit.eval τ x.toInt = false) ∧
    (wd B (litAddr x) = S * 2 + 1 → Lit.eval τ x.toInt = true)

/-- The current RAT candidate plus one (`0`: none, a RUP step). -/
def candOf (B : ByteArray) : Nat := (wd B candAddr).toNat

/-- The tag of the current step. -/
def tagOf (B : ByteArray) : BitVec 32 := wd B tagAddr

/-- The cover mark of id `id`. -/
def covOf (B : ByteArray) (id : Nat) : BitVec 32 := wd B (covBase + 4 * id)

/-- The pivot: the first word of the step's clause. -/
def pivotOf (G : List (BitVec 32)) (B : ByteArray) : BitVec 32 := wd B (gv G gCstart).toNat

/-- The literals of clause `id` other than `-p`. -/
def resPart (B : ByteArray) (p : BitVec 32) (id : Nat) : Clause :=
  (entryClause B id).filter (· != -p.toInt)

/-- The RAT resolvent of the step's clause with candidate `id`. -/
def resolventOf (G : List (BitVec 32)) (B : ByteArray) (id : Nat) : Clause :=
  toClause (bufWords G B) ++ resPart B (pivotOf G B) id

/-- The clause the current propagation refutes: the step's clause, or in the group of a RAT
candidate its resolvent. -/
def targetOf (G : List (BitVec 32)) (B : ByteArray) : Clause :=
  if candOf B = 0 then toClause (bufWords G B) else resolventOf G B (candOf B - 1)

/-- Inside a step: the step id is in range, the clause's literals are in range, a candidate is a
stored clause and the step's clause is not empty; a recorded conflict means the database implies
the target, every model of the database falsifying the target agrees with the literal values,
and every id covered in this step (`cov = tag`) is a stored clause whose resolvent the database
implies. -/
structure StepOk (G : List (BitVec 32)) (B : ByteArray) : Prop where
  id_lt : (gv G gStepId).toNat < maxId
  valid : ∀ w ∈ bufWords G B, ValidLit w
  cand : candOf B ≠ 0 → candOf B - 1 < maxId ∧ entryLen B (candOf B - 1) ≠ 0 ∧
    gv G gTop ≠ gv G gCstart
  confl : gv G gConfl ≠ 0 → ∀ τ, Models τ B → Clause.eval τ (targetOf G B) = true
  agrees : ∀ τ, Models τ B → Clause.eval τ (targetOf G B) = false → Agrees τ B (gv G gStamp)
  cov : ∀ id < maxId, covOf B id = tagOf B → entryLen B id ≠ 0 ∧ gv G gTop ≠ gv G gCstart ∧
    ∀ τ, Models τ B → Clause.eval τ (resolventOf G B id) = true

/-- **The invariant** of the checker after the DIMACS stream `xs`. The database keeps the
satisfiability of the formula (`sat`); in the input phase every model of the formula is a model
of the database. -/
structure Good (xs : List Int) (G : List (BitVec 32)) (B : ByteArray) : Prop where
  size : B.size = memSize
  mode_le : (gv G gMode).toNat ≤ 2
  base_le : arenaBase ≤ (gv G gCstart).toNat
  cstart_le : (gv G gCstart).toNat ≤ (gv G gTop).toNat
  top_le : (gv G gTop).toNat ≤ memSize
  cstart_dvd : 4 ∣ (gv G gCstart).toNat
  top_dvd : 4 ∣ (gv G gTop).toNat
  stamp_le : (gv G gStamp).toNat ≤ maxStamp
  stale : ∀ x, ValidLit x → (wd B (litAddr x)).toNat ≤ 2 * (gv G gStamp).toNat + 1
  tag_le : (tagOf B).toNat ≤ (gv G gStamp).toNat
  cov_le : ∀ id < maxId, (covOf B id).toNat ≤ (tagOf B).toNat
  entries : ∀ id < maxId, entryLen B id ≠ 0 → EntryOk B (gv G gCstart).toNat id
  sat : (Dimacs.cnf xs).Sat → ∃ τ, Models τ B
  unsat : gv G gUnsat ≠ 0 → (Dimacs.cnf xs).Unsat
  input : gv G gMode = 0 → (∀ w ∈ bufWords G B, ValidLit w) ∧
    toClause (bufWords G B) = Dimacs.pending xs ∧
    ∀ τ, (Dimacs.cnf xs).eval τ = true → Models τ B
  step : gv G gMode = 2 → StepOk G B

end Silmaril.Wasm.Examples.LRAT
