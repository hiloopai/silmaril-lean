module

public import Silmaril.Wasm.Binaryen.Syntax
public import Silmaril.Wasm.Binaryen.Exe.Valid

@[expose] public section

/-! # Double `i32.eqz` in a boolean context (an OptimizeInstructions subrule): run functions

Binaryen's `OptimizeInstructions` drops `eqz (eqz x)` where only the truth of `x`
matters. `i32.eqz (i32.eqz c)` is `1` if `c ≠ 0` and `0` otherwise, so before a
**boolean consumer** — an instruction whose behaviour depends on its top `i32`
operand only through `c = 0` — the pair is redundant:

  `c; i32.eqz; i32.eqz; X` ⟶ `c; X`     for `X` one of `br_if l`, `select`, `i32.eqz`.

(`if` is not a consumer here: silmaril's arm swap `IfSwap` already removes one
`eqz` from an `if` condition per round.) Shapes matched:

* folded: `X (…, eqz (eqz c))` with the double negation as the last operand tree
  of a consumer;
* flat: the siblings `i32.eqz; i32.eqz; X` with an operand-free `X`;
* mixed: a folded `eqz (eqz c)` followed by an operand-free sibling `X`.

Run functions only (executable-safe). The pipelines use `eqzPairChecked`, kept when
the validator accepts it; soundness is in `Silmaril.Wasm.Binaryen.EqzPair.Thms`.
-/

namespace Silmaril.Wasm.Binaryen.EqzPair

open Silmaril.Wasm Silmaril.Wasm.Binaryen

/-- Instructions whose behaviour depends on their top `i32` operand only through
whether it is zero. -/
def boolConsumer : Instr → Bool
  | .brIf _ | .select _ | .intTestOp .i32 _ => true
  | _ => false

/-- `i32.eqz`. -/
abbrev eqz : Instr := .intTestOp .i32 .eqz


mutual
/-- Drop double negations consumed by a boolean consumer, children first. -/
def elimE : BExpr → BExpr
  | .op i args => if boolConsumer i then .op i (elimArgs args) else .op i (elimL args)
  | .block bt b => .block bt (elimL b)
  | .loop bt b => .loop bt (elimL b)
  | .if_ bt c t e => .if_ bt (elimL c) (elimL t) (elimL e)
  | .tryTable bt cs b => .tryTable bt cs (elimL b)
termination_by x => sizeOf x

/-- The operand trees of a boolean consumer: the last one loses a double negation. -/
def elimArgs : List BExpr → List BExpr
  | [] => []
  | [.op (.intTestOp .i32 .eqz) [.op (.intTestOp .i32 .eqz) [c]]] => [elimE c]
  | e :: es => elimE e :: elimArgs es
termination_by es => sizeOf es

/-- `elimE` on every tree of a sequence, plus the flat and mixed shapes. -/
def elimL : List BExpr → List BExpr
  | .op (.intTestOp .i32 .eqz) [] :: .op (.intTestOp .i32 .eqz) [] :: .op X [] :: es =>
    if boolConsumer X then .op X [] :: elimL es
    else .op eqz [] :: elimL (.op eqz [] :: .op X [] :: es)
  | .op (.intTestOp .i32 .eqz) [.op (.intTestOp .i32 .eqz) [c]] :: .op X [] :: es =>
    if boolConsumer X then elimE c :: .op X [] :: elimL es
    else .op eqz [.op eqz [elimE c]] :: elimL (.op X [] :: es)
  | [] => []
  | e :: es => elimE e :: elimL es
termination_by es => sizeOf es
end

/-- The raw rewrite of every function body. -/
def eqzPair (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := elimL f.body } }

/-- **The double-`eqz` stage**: the rewrite, kept when the validator accepts it. -/
def eqzPairChecked (m : BModule) : BModule :=
  let m' := eqzPair m
  if Exe.validOk m' then m' else m

/-- The source base pairs of the rewrite (the original on the left, the result on the right),
for its soundness proof and for the body relation `eqzPair_bodiesRel`. -/
inductive eBI : List Instr → List Instr → Prop where
  | mk (X : Instr) (hX : boolConsumer X = true) : eBI [eqz, eqz, X] [X]

end Silmaril.Wasm.Binaryen.EqzPair
