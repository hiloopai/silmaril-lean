module

public import Silmaril.Wasm.Binaryen.InstrUtil
public import Silmaril.Wasm.Binaryen.Exe.Fold
public import Silmaril.Wasm.Binaryen.Pass.UnusedBlocks

@[expose] public section

/-! # CodeFolding: hoist the common tail of the two arms of an `if`

Binaryen's CodeFolding (`src/passes/CodeFolding.cpp`, version_133) merges identical
code at the ends of the arms of an `if` (and at branches to a common block end). This
first version handles the `if` arms:

```
if [] c (t ; x) (e ; x)   ~>   if [] c t e ; x
```

Conditions, all checked syntactically:

* the `if` has the empty block type, and both arms end with the same trees `x`
  (equal lowerings, `instrsEqb`), read from the end (`commonRev`);
* each hoisted `x` is **closed and void**: a complete tree of integer constants and
  operators, `nop`, `drop`, `local.set` and `global.set` (`simpleArity`), whose
  operands are complete single-value trees and whose root produces no value. So `x`
  neither consumes nor produces stack values, has no label, and its typing does not
  depend on the context beyond the indices it names;
* both arms are free of branches out of themselves and of `return`
  (`UnusedBlocks.eligible`): the `if`'s label is never targeted, so where `x` runs,
  inside the label or after it, is unobservable.

The tails are counted on the arms as they are; the arms then fold their own `if`s.
This file contains executable definitions only.
-/

namespace Silmaril.Wasm.Binaryen

namespace CodeFolding

open Exe

/-- Operand and result counts of the flat instructions a hoisted tail may contain. -/
def simpleArity : Instr → Option (Nat × Nat)
  | .intConst .. => some (0, 1)
  | .intUnOp .. | .intTestOp .. => some (1, 1)
  | .intBinOp .. | .intRelOp .. => some (2, 1)
  | .nop => some (0, 0)
  | .drop | .localSet _ | .globalSet _ => some (1, 0)
  | _ => none

mutual
/-- The number of values a closed tree produces (`none` if it is not closed). -/
def closedRes : BExpr → Option Nat
  | .op i args => match simpleArity i with
    | some (n, r) => if args.length == n && closedArgs args then some r else none
    | none => none
  | _ => none
/-- Every tree of the list is closed and produces one value. -/
def closedArgs : List BExpr → Bool
  | [] => true
  | a :: as => closedRes a == some 1 && closedArgs as
end

/-- The number of common closed void trees at the heads of two (reversed) arms. -/
def commonRev : List BExpr → List BExpr → Nat
  | x :: xs, y :: ys =>
    if closedRes x == some 0 && instrsEqb x.lower y.lower then commonRev xs ys + 1 else 0
  | _, _ => 0

/-- How many tails to hoist out of `if bt c t e`. -/
def tailCount (bt : BlockType) (t e : List BExpr) : Nat :=
  if (bt matches .empty) && UnusedBlocks.eligible t && UnusedBlocks.eligible e then
    commonRev t.reverse e.reverse
  else 0

mutual
/-- Fold the `if`s of every body of a tree. -/
def expr : BExpr → BExpr
  | .op i args => .op i (exprs args)
  | .block bt b => .block bt (exprs b)
  | .loop bt b => .loop bt (exprs b)
  | .if_ bt c t e => .if_ bt (exprs c) (exprs t) (exprs e)
  | .tryTable bt cs b => .tryTable bt cs (exprs b)
/-- Fold one tree of a sequence: an `if` loses its common tails, which follow it. -/
def item : BExpr → List BExpr
  | .if_ bt c t e =>
    let k := tailCount bt t e
    let t' := exprs t
    let e' := exprs e
    .if_ bt (exprs c) (t'.take (t'.length - k)) (e'.take (e'.length - k)) :: t.drop (t.length - k)
  | e => [expr e]
/-- Fold in a sequence. -/
def exprs : List BExpr → List BExpr
  | [] => []
  | e :: es => item e ++ exprs es
end

end CodeFolding

/-- **CodeFolding** (first version): hoist identical closed tails out of the arms of
empty-typed `if`s. -/
def codeFolding (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := CodeFolding.exprs f.body } }

end Silmaril.Wasm.Binaryen
