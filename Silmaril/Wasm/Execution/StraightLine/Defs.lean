module

public import Silmaril.Wasm.Execution.Core.Step
public import Silmaril.Wasm.Validation.DefTypes
public import Silmaril.Wasm.Execution.Core.Instantiation

/-!
# Straight-line numeric functions

A *straight-line numeric function* of `k` parameters has no declared locals, one result, and
the body `local.get 0 … local.get (k-1); op` where `op` is a scalar numeric instruction
(`NumericStep`: integer or float unary, binary, test or comparison operators, conversions)
of arity `k`. Every function of the spec test files `f32.wast`, `f64.wast`, `f32_bitwise.wast`,
`f64_bitwise.wast`, `f32_cmp.wast`, `f64_cmp.wast` and `conversions.wast` has this form.

`Silmaril.Wasm.Execution.StraightLine.Thms` describes **every** host-free run of the invocation
of such a function, at **any** profile `P` (in particular the specification profile
`Profile.spec`, whose float operators return sets of results): every normal form is
`⟨s, {}, is'⟩` for a numeric step `NumericStep P (vals args ++ [op]) is'`, every such `is'` is
reached, and no run is infinite.

* `numArity op`: the number of operands of a scalar numeric instruction (`none` otherwise);
* `Body k op body`: `body` is `local.get 0 … local.get (k-1); op`;
* `Fn fi k op`: the function instance `fi` is a straight-line numeric function of `k`
  parameters with the operator `op`;
* `fn? fi k`: a checker; `fn?_sound` (`….Thms`) gives `Fn fi k op` from `fn? fi k = some op`.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.StraightLine

open Silmaril.Wasm.Validation

/-- The number of operands of a scalar numeric instruction (the left-hand sides of
`NumericStep`), `none` for every other instruction. -/
def numArity : Instr → Option Nat
  | .intUnOp .. | .floatUnOp .. | .intTestOp .. | .convert _ => some 1
  | .intBinOp .. | .floatBinOp .. | .intRelOp .. | .floatRelOp .. => some 2
  | _ => none

/-- `body` is `local.get 0 … local.get (k-1); op`. -/
def Body (k : Nat) (op : Instr) (body : Expr) : Prop :=
  body.drop k = [op] ∧ ∀ j < k, ∃ x : LocalIdx, body[j]? = some (.localGet x) ∧ x.toNat = j

/-- The function instance `fi` is a straight-line numeric function of `k` parameters: Wasm code
with no declared locals and the body `local.get 0 … local.get (k-1); op`, a function type with
`k` parameters and one result, and `op` a scalar numeric instruction with `k` operands. -/
structure Fn {H : Type} (fi : FuncInst H) (k : Nat) (op : Instr) : Prop where
  code : ∃ c : Func, fi.code = .wasm c ∧ c.locals = [] ∧ Body k op c.body
  type : ∃ ps rs, fi.type.funcType? = some (ps, rs) ∧ ps.length = k ∧ rs.length = 1
  arity : numArity op = some k

/-- `i` is `local.get j`. -/
def isLocalGet (j : Nat) (i : Instr) : Bool :=
  match i with
  | .localGet x => x.toNat == j
  | _ => false

/-- `local.get j, local.get (j+1), …` for `n` instructions at the front of a body. -/
def localGetsB (j : Nat) : Nat → Expr → Bool
  | 0, _ => true
  | n + 1, i :: rest => isLocalGet j i && localGetsB (j + 1) n rest
  | _ + 1, [] => false

/-- The checker of `Fn`: the operator `op` if `fi` is a straight-line numeric function of `k`
parameters. -/
def fn? {H : Type} (fi : FuncInst H) (k : Nat) : Option Instr :=
  match fi.code with
  | .wasm c =>
    match c.body.drop k, fi.type.funcType? with
    | [op], some (ps, rs) =>
      if c.locals.isEmpty && localGetsB 0 k c.body && numArity op == some k && ps.length == k &&
          rs.length == 1 then some op else none
    | _, _ => none
  | .host _ => none

end Silmaril.Wasm.Execution.Core.StraightLine

end
