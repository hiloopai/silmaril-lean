module

public import Silmaril.Wasm.SSA.Pipeline.Defs
public import Silmaril.Wasm.SSA.Bridge.Defs
public import Silmaril.Wasm.SSA.Checked.Defs

/-!
# The fragment and silmaril's native Binaryen interpreter

silmaril's `Binaryen.Eval` (the big-step relation of its fuel interpreter
`Binaryen.run`) evaluates folded trees on a top-first value stack. It agrees
with the fragment semantics only on code whose stack discipline is the
tree's: every operand produces exactly one value, non-final body elements
produce none, a branch carries exactly the target label's arity, and so on.
`FragFunc.native` is a computable **arity check** for that (`tyE`, `tySeq`):
an expression completes with no value (`.none`), one value (`.one`), or never
completes normally (`none` in the outer option, "bottom"; code after it in a
body is not checked). Value *types* are not checked: both semantics check
integer types dynamically in the same way. The interpreter has no conversion
instructions, so `i32.wrap_i64`/`i64.extend_i32_*` are excluded.

`frameOf mi ls` is the interpreter frame for fragment locals `ls`.
`optimizeFuncNative? ft bf` is `optimizeFunc?` guarded by the arity check
on both the recognised source and the optimised function;
`optimizeFuncCertified m g` adds silmaril's module validator as in
`optimizeFuncChecked`.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core

/-- Value arity of a completing expression. -/
inductive Ar where
  | none
  | one
  deriving DecidableEq, Repr

/-- The arity of a construct of result type `ty`. -/
def arOf : Option IntType → Ar
  | none => .none
  | some _ => .one

/-- Operators the native interpreter supports. -/
def Op.native : Op → Bool
  | .un .wrap | .un (.extend _) => false
  | _ => true

/-- `r` is an acceptable outcome for a construct of arity `a`: completes with
`a`, or never completes. -/
def arFits (a : Ar) : Option (Option Ar) → Bool
  | some (some b) => a == b
  | some none => true
  | none => false

mutual

/-- The arity check of an expression, with the label arities `L` (innermost
first), the function's result arity `R` and the number of locals `n`.
`none`: rejected; `some none`: never completes; `some (some a)`: arity `a`. -/
def tyE (L : List Ar) (R : Ar) (n : Nat) : Expr → Option (Option Ar)
  | .op o args =>
      if o.native && args.length == o.arity && tyArgs L R n args then some (some .one) else none
  | .localGet i => if i < n then some (some .one) else none
  | .localSet i e => if i < n && tyE L R n e == some (some .one) then some (some .none) else none
  | .localTee i e => if i < n && tyE L R n e == some (some .one) then some (some .one) else none
  | .drop e => if tyE L R n e == some (some .one) then some (some .none) else none
  | .nop => some (some .none)
  | .unreachable => some none
  | .block ty body =>
      if arFits (arOf ty) (tySeq (arOf ty :: L) R n body) then some (some (arOf ty)) else none
  | .loop ty body =>
      if arFits (arOf ty) (tySeq (.none :: L) R n body) then some (some (arOf ty)) else none
  | .if_ ty c t e =>
      if tyE L R n c == some (some .one) && arFits (arOf ty) (tySeq (arOf ty :: L) R n t) &&
          arFits (arOf ty) (tySeq (arOf ty :: L) R n e) then some (some (arOf ty)) else none
  | .br l args =>
      if tyArgs L R n args && L[l]? == some (if args.length == 1 then .one else .none) &&
          args.length ≤ 1 then some none else none
  | .brIf l args =>
      if tyArgs L R n args && (args.length == 1 || args.length == 2) &&
          L[l]? == some (if args.length == 2 then .one else .none) then
        some (some (if args.length == 2 then .one else .none))
      else none
  | .return_ args =>
      if tyArgs L R n args && args.length ≤ 1 &&
          R == (if args.length == 1 then .one else .none) then some none else none

/-- Every operand produces one value. -/
def tyArgs (L : List Ar) (R : Ar) (n : Nat) : List Expr → Bool
  | [] => true
  | e :: es => tyE L R n e == some (some .one) && tyArgs L R n es

/-- A body: non-final elements produce no value; the arity is the last
element's (`.none` when empty); after a non-completing element the rest is
not checked. -/
def tySeq (L : List Ar) (R : Ar) (n : Nat) : List Expr → Option (Option Ar)
  | [] => some (some .none)
  | e :: es =>
      match tyE L R n e with
      | some none => some none
      | some (some .none) => tySeq L R n es
      | some (some .one) => if es.isEmpty then some (some .one) else none
      | none => none

end

/-- A fragment function the native interpreter runs like the fragment semantics. -/
def FragFunc.native (f : FragFunc) : Bool :=
  arFits (arOf f.result)
    (tySeq [arOf f.result] (arOf f.result) (f.params.length + f.locals.length) f.body)

/-- The interpreter frame of fragment locals. -/
def frameOf (mi : ModuleInst) (ls : List WVal) : Frame :=
  { locals := ls.map (some ∘ WVal.toVal), module := mi }

/-- `optimizeFunc?`, guarded by the arity check of the source and the result. -/
def optimizeFuncNative? (ft : FuncType) (bf : BFunc) : Option BFunc := do
  let f ← ofBFunc? ft bf
  guard f.native
  let g ← optimize? f
  guard g.native
  toBFunc? bf.type g

/-- The arity-guarded optimiser on function `g` of a module, kept only if the
module with the replacement validates. -/
def optimizeFuncCertified (m : BModule) (g : Nat) : Option BFunc := do
  let bf ← m.funcs[g]?
  let ft ← m.funcType? bf.type
  let bf' ← optimizeFuncNative? ft bf
  if validates (m.setFunc g bf') then some bf' else none

end Silmaril.Wasm.SSA
