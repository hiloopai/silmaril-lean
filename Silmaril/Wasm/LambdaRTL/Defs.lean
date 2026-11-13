module

public import Silmaril.SSA.LambdaRTL.Defs
public import Silmaril.Wasm.SSA.Fragment.Defs

/-!
# The loop-free structured Wasm fragment in λRTL

A translation of the numeric Wasm fragment `Silmaril.Wasm.SSA.Expr` (integer `i32`/`i64` code over
locals, folded like Binaryen's `BExpr`) into acyclic λRTL (`Silmaril.SSA.LambdaRTL.Region`), and the
λRTL model in which the translation is read.

## The model

* Registers `WReg`: `loc i` holds Wasm local `i`, `tmp k` is operand-stack slot `k`, `junk`
  receives dead payloads (the parameter of a join, the unit payload of a branch test).
* Labels `WLab`: `ret` is the function's exit; `blk d` is the join label of the Wasm `block`/`if`
  opened at label-nesting depth `d` (one label per depth, so an inner join never captures a branch
  aimed at an outer one).
* Instructions `WOp`: `op o` applies the fragment operator `o` to its operands, packed as a
  right-nested tuple ending in `unit`; `truthy` turns an `i32` condition into `ιₗ ()` (nonzero) or
  `ιᵣ ()` (zero) for a λRTL `case`; `stuck` has no result.
* Values `RVal`: fragment values `val v`, and the tuples and injections of λRTL values.
* The monad is `Except WErr`: `.error .trap` is a Wasm trap (division or remainder by zero, signed
  division overflow, `unreachable`, which is a λRTL `abort`), `.error .stuck` is a configuration
  on which the fragment semantics has no derivation (dynamically ill-typed operands, a non-`i32`
  condition, an out-of-range `local.get`, a missing operand value, a branch beyond the function).
  Operators are silmaril's numerics through `Silmaril.Wasm.SSA.Op.eval`; nothing is redefined.

## The translation

`trE`/`trArgs`/`trSeq` translate in continuation-passing style: `trE … sd e k` evaluates `e` with
operand stack depth `sd`, leaves its value (if any) in `tmp sd`, and continues with the region `k`.
Operands of an operator or branch occupy consecutive slots `sd, sd+1, …`. Locals are λRTL
registers that are overwritten in place, which is the λRTL store reading: no SSA construction or
block parameters are needed. A `block` or `if` becomes `join body (blk d) junk k`; its result
slot is the slot of the construct, and `br`/`br_if` move the carried value there before jumping.
`return` and branches to the function label leave through `ret` with the result value.

Code on which the fragment semantics gets stuck is translated to `stuckR`, whose evaluation is
`.error .stuck`, so stuckness is reproduced exactly. An out-of-range `local.set` writes nothing,
as `List.set` does. `loop` is not translated: `trFunc` returns `none` exactly on bodies containing a
`loop` (`loopFreeL`); loops need λRTL's recursive `where` and an Elgot monad with divergence.

The simulation theorems are in `Silmaril.Wasm.LambdaRTL.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.LambdaRTL

open Silmaril.SSA.LambdaRTL
open Silmaril.Wasm.SSA (WVal Expr FragFunc FOut Res)
open Silmaril.Wasm (IntType)

/-- λRTL registers: Wasm locals, operand-stack slots and a register for dead payloads. -/
inductive WReg where
  | loc (i : Nat)
  | tmp (k : Nat)
  | junk
  deriving DecidableEq, Repr

/-- λRTL labels: the function exit and the join label of the construct at a nesting depth. -/
inductive WLab where
  | ret
  | blk (d : Nat)
  deriving DecidableEq, Repr

/-- λRTL instructions: fragment operators, the branch test and a stuck instruction. -/
inductive WOp where
  | op (o : Silmaril.Wasm.SSA.Op)
  | truthy
  | stuck
  deriving DecidableEq, Repr

/-- λRTL values over fragment values. -/
inductive RVal where
  | val (v : WVal)
  | unit
  | pair (a b : RVal)
  | inl (a : RVal)
  | inr (a : RVal)
  deriving DecidableEq, Repr

/-- The two ways a run can fail to return: a Wasm trap, or no derivation (stuck). -/
inductive WErr where
  | trap
  | stuck
  deriving DecidableEq, Repr

/-- The monad of the model. -/
abbrev WM := Except WErr

/-- λRTL stores of the model. -/
abbrev Store := WReg → RVal

/-- λRTL regions of the translation. -/
abbrev WRegion := Region WReg WLab WOp

/-! ## The model -/

/-- The operand list of an operator, from a right-nested tuple ending in `unit`. -/
def RVal.toList : RVal → Option (List WVal)
  | .unit => some []
  | .pair (.val v) rest => rest.toList.map (v :: ·)
  | _ => none

/-- A list of values as a right-nested tuple ending in `unit`. -/
def RVal.ofList : List WVal → RVal
  | [] => .unit
  | v :: vs => .pair (.val v) (RVal.ofList vs)

/-- The result of a fragment operator in the monad. -/
def ofRes : Option Res → WM RVal
  | some (.val v) => .ok (.val v)
  | some .trap => .error .trap
  | none => .error .stuck

/-- Instruction semantics. -/
def app : WOp → RVal → WM RVal
  | .op o, a =>
      match a.toList with
      | some vs => ofRes (o.eval vs)
      | none => .error .stuck
  | .truthy, .val v =>
      match v.truthy with
      | some true => .ok (.inl .unit)
      | some false => .ok (.inr .unit)
      | none => .error .stuck
  | .truthy, _ => .error .stuck
  | .stuck, _ => .error .stuck

/-- The λRTL model of the fragment. -/
def model : Model WOp WM RVal where
  unit := .unit
  pair := .pair
  inl := .inl
  inr := .inr
  unpair
    | .pair a b => .ok (a, b)
    | _ => .error .stuck
  split
    | .inl a => .ok (.inl a)
    | .inr b => .ok (.inr b)
    | _ => .error .stuck
  app := app
  abort _ := .error .trap

/-! ## The translation -/

/-- A Wasm label that is a `block` or `if`: its λRTL join label depth, its result slot and its
type. The function's own label is the one past the end of the label list. -/
structure Tgt where
  d : Nat
  slot : Nat
  ty : Option IntType
  deriving DecidableEq, Repr

/-- Whether an expression leaves a value when it completes normally (`hasVal_ok` in the proofs:
this is determined by the syntax). -/
def hasVal : Expr → Bool
  | .op .. | .localGet _ | .localTee .. => true
  | .block ty _ | .loop ty _ | .if_ ty .. => ty.isSome
  | .brIf _ args => decide (2 ≤ args.length)
  | _ => false

/-- Whether a body leaves a value, starting from `b` for the empty prefix. -/
def seqVal : Bool → List Expr → Bool
  | b, [] => b
  | _, e :: es => seqVal (hasVal e) es

/-- A region without result. -/
def stuckR : WRegion := .let1 .junk (.app .stuck .unit) (.br .ret .unit)

/-- A register move. -/
def mv (dst src : WReg) (k : WRegion) : WRegion := .let1 dst (.val (.var src)) k

/-- The operand tuple of `n` consecutive slots from `sd`. -/
def pack : Nat → Nat → Val WReg
  | _, 0 => .unit
  | sd, n + 1 => .pair (.var (.tmp sd)) (pack (sd + 1) n)

/-- The exit value of a (possibly absent) result. -/
def encR : Option WVal → RVal
  | none => .unit
  | some v => .val v

/-- Leave the function with result type `res`; `hv` says whether slot `sd` holds a value. -/
def retR (res : Option IntType) (sd : Nat) (hv : Bool) : WRegion :=
  if res.isSome && hv then .br .ret (.var (.tmp sd)) else .br .ret .unit

/-- Branch to Wasm label `l`, carrying the value of slot `sd` when `hv`. -/
def jumpTo (ks : List Tgt) (res : Option IntType) (l sd : Nat) (hv : Bool) : WRegion :=
  match ks[l]? with
  | some t =>
      if t.ty.isSome && !hv then stuckR
      else if hv then mv (.tmp t.slot) (.tmp sd) (.br (.blk t.d) .unit)
      else .br (.blk t.d) .unit
  | none => if l = ks.length then retR res sd hv else stuckR

/-- The end of a body of type `ty`: a typed construct needs a value. -/
def fallR (d : Nat) (ty : Option IntType) (hv : Bool) : WRegion :=
  if ty.isSome && !hv then stuckR else .br (.blk d) .unit

/-- Continue with `k` when a value is present (`hv`), else stuck. -/
def needVal (hv : Bool) (k : WRegion) : WRegion := if hv then k else stuckR

/-- Write slot `sd` to local `i`; nothing when `i` is out of range, as `List.set`. -/
def setLocal (nloc i sd : Nat) (k : WRegion) : WRegion :=
  if i < nloc then mv (.loc i) (.tmp sd) k else k

/-- The join of an `if` at label depth `d`: test slot `sd`, run a branch, then `k`. -/
def ifJoin (d sd : Nat) (rt re k : WRegion) : WRegion :=
  .join (.case (.app .truthy (.var (.tmp sd))) .junk rt .junk re) (.blk d) .junk k

/-- The test of a `br_if` with `n` operands in slots `sd, …`: the last one is the condition. -/
def brIfTest (ks : List Tgt) (res : Option IntType) (l sd : Nat) (k : WRegion) : Nat → WRegion
  | 0 => stuckR
  | m + 1 =>
      .case (.app .truthy (.var (.tmp (sd + m))))
        .junk (jumpTo ks res l sd (decide (1 ≤ m))) .junk k

mutual

/-- Translate an expression at operand-stack depth `sd` under the labels `ks`, continuing with
`k`. `nloc` is the number of locals and `res` the function's result type. -/
def trE (nloc : Nat) (res : Option IntType) : List Tgt → Nat → Expr → WRegion → WRegion
  | ks, sd, .op o args, k =>
      trArgs nloc res ks sd args (.let1 (.tmp sd) (.app (.op o) (pack sd args.length)) k)
  | _, sd, .localGet i, k => if i < nloc then mv (.tmp sd) (.loc i) k else stuckR
  | ks, sd, .localSet i e, k => trE nloc res ks sd e (needVal (hasVal e) (setLocal nloc i sd k))
  | ks, sd, .localTee i e, k => trE nloc res ks sd e (needVal (hasVal e) (setLocal nloc i sd k))
  | ks, sd, .drop e, k => trE nloc res ks sd e k
  | _, _, .nop, k => k
  | _, _, .unreachable, k => .let1 .junk (.abort .unit) k
  | ks, sd, .block ty body, k =>
      .join (trSeq nloc res (⟨ks.length, sd, ty⟩ :: ks) sd body
          (fallR ks.length ty (seqVal false body)))
        (.blk ks.length) .junk k
  | _, _, .loop _ _, _ => stuckR
  | ks, sd, .if_ ty c t el, k =>
      trE nloc res ks sd c (needVal (hasVal c) (ifJoin ks.length sd
        (trSeq nloc res (⟨ks.length, sd, ty⟩ :: ks) sd t (fallR ks.length ty (seqVal false t)))
        (trSeq nloc res (⟨ks.length, sd, ty⟩ :: ks) sd el (fallR ks.length ty (seqVal false el)))
        k))
  | ks, sd, .br l args, _ => trArgs nloc res ks sd args (jumpTo ks res l sd (!args.isEmpty))
  | ks, sd, .brIf l args, k => trArgs nloc res ks sd args (brIfTest ks res l sd k args.length)
  | ks, sd, .return_ args, _ => trArgs nloc res ks sd args (retR res sd (!args.isEmpty))

/-- Translate operands into consecutive slots from `sd`; each must leave a value. -/
def trArgs (nloc : Nat) (res : Option IntType) : List Tgt → Nat → List Expr → WRegion → WRegion
  | _, _, [], k => k
  | ks, sd, e :: es, k =>
      trE nloc res ks sd e (needVal (hasVal e) (trArgs nloc res ks (sd + 1) es k))

/-- Translate a body; every expression runs at depth `sd`, the last value stays in `tmp sd`. -/
def trSeq (nloc : Nat) (res : Option IntType) : List Tgt → Nat → List Expr → WRegion → WRegion
  | _, _, [], k => k
  | ks, sd, e :: es, k => trE nloc res ks sd e (trSeq nloc res ks sd es k)

end

mutual

/-- No `loop` occurs in the expression. -/
def loopFree : Expr → Bool
  | .op _ args => loopFreeL args
  | .localGet _ | .nop | .unreachable => true
  | .localSet _ e | .localTee _ e | .drop e => loopFree e
  | .block _ body => loopFreeL body
  | .loop _ _ => false
  | .if_ _ c t el => loopFree c && loopFreeL t && loopFreeL el
  | .br _ args | .brIf _ args | .return_ args => loopFreeL args

/-- No `loop` occurs in the list. -/
def loopFreeL : List Expr → Bool
  | [] => true
  | e :: es => loopFree e && loopFreeL es

end

/-- The number of locals (parameters first) of a function. -/
def nlocOf (f : FragFunc) : Nat := f.params.length + f.locals.length

/-- The λRTL body of a function: its body at depth `0` under no block labels, leaving through
`ret` (meaningful when the body has no `loop`). -/
def trBody (f : FragFunc) : WRegion :=
  trSeq (nlocOf f) f.result [] 0 f.body (retR f.result 0 (seqVal false f.body))

/-- Translate a function: `none` exactly when its body contains a `loop`. -/
def trFunc (f : FragFunc) : Option WRegion :=
  if loopFreeL f.body then some (trBody f) else none

/-- A λRTL store holding the initial locals of a call (other registers `unit`). -/
def initStore (f : FragFunc) (args : List WVal) : Store
  | .loc i =>
      match (f.initLocals args)[i]? with
      | some v => .val v
      | none => .unit
  | _ => .unit

/-- A λRTL store holds the initial locals of a call (`initStore` is one; other registers are
unconstrained). -/
def InitStore (f : FragFunc) (args : List WVal) (σ : Store) : Prop :=
  ∀ i (h : i < (f.initLocals args).length), σ (.loc i) = .val (f.initLocals args)[i]

/-! ## Observations -/

/-- The λRTL observation of a call outcome. -/
def obsOf : FOut → WM (WLab × RVal)
  | .ret r => .ok (.ret, encR r)
  | .trap => .error .trap

/-- The λRTL observation of an interpreter result (`none`: stuck). -/
def obsOpt : Option FOut → WM (WLab × RVal)
  | some o => obsOf o
  | none => .error .stuck

/-! ## Fuel that suffices for the fragment's interpreter on loop-free code -/

mutual

/-- Fuel for `evalE`. -/
def fuelE : Expr → Nat
  | .op _ args => fuelArgs args + 1
  | .localGet _ | .nop | .unreachable => 1
  | .localSet _ e | .localTee _ e | .drop e => fuelE e + 1
  | .block _ body | .loop _ body => fuelSeq body + 1
  | .if_ _ c t el => max (fuelE c) (max (fuelSeq t) (fuelSeq el)) + 1
  | .br _ args | .brIf _ args | .return_ args => fuelArgs args + 1

/-- Fuel for `evalArgs`. -/
def fuelArgs : List Expr → Nat
  | [] => 1
  | e :: es => max (fuelE e) (fuelArgs es) + 1

/-- Fuel for `evalSeq`. -/
def fuelSeq : List Expr → Nat
  | [] => 1
  | e :: es => max (fuelE e) (fuelSeq es) + 1

end

end Silmaril.Wasm.LambdaRTL
