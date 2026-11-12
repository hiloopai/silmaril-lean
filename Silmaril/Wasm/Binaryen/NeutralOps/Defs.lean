module

public import Silmaril.Wasm.Binaryen.Syntax
public import Silmaril.Wasm.Binaryen.Exe.Valid

@[expose] public section

/-! # Neutral-operand elimination (an OptimizeInstructions subrule): run functions

Binaryen's `OptimizeInstructions` (`src/passes/OptimizeInstructions.cpp`) removes
binary operations whose right operand is a constant identity element:
`x + 0`, `x - 0`, `x * 1`, `x | 0`, `x ^ 0`, `x & -1`, and shifts/rotations by `0`,
for `i32` and `i64`. This module implements the restricted form whose exact
equivalence is proved in `Silmaril.Wasm.Binaryen.NeutralOps.Thms`:

  `x; t.const k; t.op; X` ⟶ `x; X`

where `neutral op k` holds and the **consumer** `X` is an integer unary, binary,
test or comparison instruction of type `t` (`topIntType? X = some t`). The
consumer is required because the simulation proofs are untyped: the consumer's
own step forces the top of the stack to be a `t` value, which is what makes the
removed `t.op` executable on the original side. A neutral operation whose result
is consumed by `local.set`, `drop`, `return`, a call, a store, a branch or the end
of a block is left alone. Three syntactic shapes are matched:

* folded: `X (… , op x (t.const k))` with the neutral tree as the *last* operand
  of an arity-one or arity-two consumer;
* flat: the siblings `t.const k; t.op; X` with an operand-free `X`;
* mixed: a folded `op x (t.const k)` tree followed by an operand-free sibling `X`.

The pass recurses into all blocks, loops, ifs and try-tables. It is a run
function only; it is executable-safe (no proof imports). The stage that the
pipelines use is `neutralOpsChecked`, which keeps the rewrite only when the
validator accepts it.
-/

namespace Silmaril.Wasm.Binaryen.NeutralOps

open Silmaril.Wasm Silmaril.Wasm.Binaryen

/-- Does `op` with right operand `k` act as the identity on every value? -/
def neutral {t : IntType} : IntBinOp → BitVec t.width → Bool
  | .add, k | .sub, k | .or, k | .xor, k | .shl, k | .shr _, k | .rotl, k | .rotr, k =>
    k == 0
  | .mul, k => k == 1
  | .and, k => k == BitVec.allOnes t.width
  | _, _ => false

/-- The integer type of the top operand of a consumer instruction: integer unary,
binary, test and comparison operations. -/
def topIntType? : Instr → Option IntType
  | .intUnOp t _ | .intBinOp t _ | .intTestOp t _ | .intRelOp t _ => some t
  | _ => none

/-- The rewrite applies: the consumer `X` takes a `t` operand, the constant has the
operation's type, and `op` with that constant is neutral. -/
def fits (X : Instr) (t : IntType) (op : IntBinOp) (t' : IntType) (k : BitVec t'.width) : Bool :=
  topIntType? X == some t && (if h : t' = t then neutral op (h ▸ k) else false)

mutual
/-- Remove neutral operations consumed by a typed integer consumer, children first. -/
def elimE : BExpr → BExpr
  | .op X [.op (.intBinOp t op) [x, .op (.intConst t' k) []]] =>
    if fits X t op t' k then
      .op X [elimE x]
    else .op X [.op (.intBinOp t op) [elimE x, .op (.intConst t' k) []]]
  | .op X [a, .op (.intBinOp t op) [x, .op (.intConst t' k) []]] =>
    if fits X t op t' k then
      .op X [elimE a, elimE x]
    else .op X [elimE a, .op (.intBinOp t op) [elimE x, .op (.intConst t' k) []]]
  | .op i args => .op i (elimL args)
  | .block bt b => .block bt (elimL b)
  | .loop bt b => .loop bt (elimL b)
  | .if_ bt c t e => .if_ bt (elimL c) (elimL t) (elimL e)
  | .tryTable bt cs b => .tryTable bt cs (elimL b)
termination_by x => sizeOf x

/-- `elimE` on every tree of a sequence, plus the flat and mixed shapes. -/
def elimL : List BExpr → List BExpr
  | .op (.intConst t k) [] :: .op (.intBinOp t' op) [] :: .op X [] :: es =>
    if fits X t' op t k then
      .op X [] :: elimL es
    else .op (.intConst t k) [] :: elimL (.op (.intBinOp t' op) [] :: .op X [] :: es)
  | .op (.intBinOp t op) [x, .op (.intConst t' k) []] :: .op X [] :: es =>
    if fits X t op t' k then
      elimE x :: .op X [] :: elimL es
    else .op (.intBinOp t op) [elimE x, .op (.intConst t' k) []] :: elimL (.op X [] :: es)
  | [] => []
  | e :: es => elimE e :: elimL es
termination_by es => sizeOf es
end

/-- The raw rewrite of every function body. -/
def neutralOps (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := elimL f.body } }

/-- **The neutral-operand stage**: the rewrite, kept when the validator accepts it. -/
def neutralOpsChecked (m : BModule) : BModule :=
  let m' := neutralOps m
  if Exe.validOk m' then m' else m

/-- The source base pairs of the rewrite (the original on the left, the result on the right),
for its soundness proof and for the body relation `neutralOps_bodiesRel`. -/
inductive nBI : List Instr → List Instr → Prop where
  | mk (t : IntType) (op : IntBinOp) (k : BitVec t.width) (X : Instr)
      (hn : neutral op k = true) (hX : topIntType? X = some t) :
      nBI [.intConst t k, .intBinOp t op, X] [X]

end Silmaril.Wasm.Binaryen.NeutralOps
