module

public import Silmaril.Wasm.Auto.EGraph.Defs

@[expose] public section

/-! # The verified rewrite library for straight-line integer Wasm

Each rule is stated at its minimal context, a pattern over typed operand variables;
`Silmaril.Wasm.Auto.Rules.Thms` proves every rule once (`library_sound`), and the
certificate checker (`Silmaril.Wasm.Auto.EGraph`) plugs rules into any context by the
congruence of `Term.set?`. The same list, in the same order, is hard-coded in the
untrusted search `tools/wasm-egraph` (`rules.sexp` is the shared text form;
`Silmaril.Wasm.Auto.Rules.Tests` checks it). Rules are generated for `i32` and `i64`:
index `2 * k` is rule `k` at `i32`, `2 * k + 1` at `i64`.
-/

namespace Silmaril.Wasm.Auto.Rules

open Silmaril.Wasm Silmaril.Wasm.Auto.EGraph

/-- Pattern variable `n` of type `t`. -/
abbrev v (t : IntType) (n : Nat) : Pat := .var t n
/-- A constant. -/
abbrev k (t : IntType) (n : Nat) : Pat := .const t n
/-- Total pattern variable `n` of type `t` (matches only terms that cannot trap). -/
abbrev tv (t : IntType) (n : Nat) : Pat := .tvar t n
/-- Binary operators. -/
abbrev B (t : IntType) (op : IntBinOp) (a b : Pat) : Pat := .bin t op a b

/-- All ones at type `t`. -/
def ones (t : IntType) : Nat := 2 ^ t.width - 1

/-! ## The rule schemas, each at a type `t` -/

/-- `add-comm` -/
def addComm (t : IntType) : Rule :=
  { name := "add-comm", lhs := B t .add (v t 0) (v t 1), rhs := B t .add (v t 1) (v t 0) }

/-- `add-assoc` -/
def addAssoc (t : IntType) : Rule :=
  { name := "add-assoc", lhs := B t .add (B t .add (v t 0) (v t 1)) (v t 2),
    rhs := B t .add (v t 0) (B t .add (v t 1) (v t 2)) }

/-- `mul-comm` -/
def mulComm (t : IntType) : Rule :=
  { name := "mul-comm", lhs := B t .mul (v t 0) (v t 1), rhs := B t .mul (v t 1) (v t 0) }

/-- `mul-assoc` -/
def mulAssoc (t : IntType) : Rule :=
  { name := "mul-assoc", lhs := B t .mul (B t .mul (v t 0) (v t 1)) (v t 2),
    rhs := B t .mul (v t 0) (B t .mul (v t 1) (v t 2)) }

/-- `and-comm` -/
def andComm (t : IntType) : Rule :=
  { name := "and-comm", lhs := B t .and (v t 0) (v t 1), rhs := B t .and (v t 1) (v t 0) }

/-- `and-assoc` -/
def andAssoc (t : IntType) : Rule :=
  { name := "and-assoc", lhs := B t .and (B t .and (v t 0) (v t 1)) (v t 2),
    rhs := B t .and (v t 0) (B t .and (v t 1) (v t 2)) }

/-- `or-comm` -/
def orComm (t : IntType) : Rule :=
  { name := "or-comm", lhs := B t .or (v t 0) (v t 1), rhs := B t .or (v t 1) (v t 0) }

/-- `or-assoc` -/
def orAssoc (t : IntType) : Rule :=
  { name := "or-assoc", lhs := B t .or (B t .or (v t 0) (v t 1)) (v t 2),
    rhs := B t .or (v t 0) (B t .or (v t 1) (v t 2)) }

/-- `xor-comm` -/
def xorComm (t : IntType) : Rule :=
  { name := "xor-comm", lhs := B t .xor (v t 0) (v t 1), rhs := B t .xor (v t 1) (v t 0) }

/-- `xor-assoc` -/
def xorAssoc (t : IntType) : Rule :=
  { name := "xor-assoc", lhs := B t .xor (B t .xor (v t 0) (v t 1)) (v t 2),
    rhs := B t .xor (v t 0) (B t .xor (v t 1) (v t 2)) }

/-- `add-zero` -/
def addZero (t : IntType) : Rule :=
  { name := "add-zero", lhs := B t .add (v t 0) (k t 0), rhs := v t 0 }

/-- `sub-zero` -/
def subZero (t : IntType) : Rule :=
  { name := "sub-zero", lhs := B t .sub (v t 0) (k t 0), rhs := v t 0 }

/-- `mul-one` -/
def mulOne (t : IntType) : Rule :=
  { name := "mul-one", lhs := B t .mul (v t 0) (k t 1), rhs := v t 0 }

/-- `or-zero` -/
def orZero (t : IntType) : Rule :=
  { name := "or-zero", lhs := B t .or (v t 0) (k t 0), rhs := v t 0 }

/-- `xor-zero` -/
def xorZero (t : IntType) : Rule :=
  { name := "xor-zero", lhs := B t .xor (v t 0) (k t 0), rhs := v t 0 }

/-- `and-ones` -/
def andOnes (t : IntType) : Rule :=
  { name := "and-ones", lhs := B t .and (v t 0) (k t (ones t)), rhs := v t 0 }

/-- `shl-zero` -/
def shlZero (t : IntType) : Rule :=
  { name := "shl-zero", lhs := B t .shl (v t 0) (k t 0), rhs := v t 0 }

/-- `shru-zero` -/
def shruZero (t : IntType) : Rule :=
  { name := "shru-zero", lhs := B t (.shr .unsigned) (v t 0) (k t 0), rhs := v t 0 }

/-- `shrs-zero` -/
def shrsZero (t : IntType) : Rule :=
  { name := "shrs-zero", lhs := B t (.shr .signed) (v t 0) (k t 0), rhs := v t 0 }

/-- `rotl-zero` -/
def rotlZero (t : IntType) : Rule :=
  { name := "rotl-zero", lhs := B t .rotl (v t 0) (k t 0), rhs := v t 0 }

/-- `rotr-zero` -/
def rotrZero (t : IntType) : Rule :=
  { name := "rotr-zero", lhs := B t .rotr (v t 0) (k t 0), rhs := v t 0 }

/-- `mul-add-distrib` -/
def mulAddDistrib (t : IntType) : Rule :=
  { name := "mul-add-distrib", lhs := B t .mul (v t 0) (B t .add (v t 1) (v t 2)),
    rhs := B t .add (B t .mul (v t 0) (v t 1)) (B t .mul (v t 0) (v t 2)) }

/-- `sub-add-neg` -/
def subAddNeg (t : IntType) : Rule :=
  { name := "sub-add-neg", lhs := B t .sub (v t 0) (v t 1),
    rhs := B t .add (v t 0) (B t .sub (k t 0) (v t 1)) }

/-- `neg-neg` -/
def negNeg (t : IntType) : Rule :=
  { name := "neg-neg", lhs := B t .sub (k t 0) (B t .sub (k t 0) (v t 0)), rhs := v t 0 }

/-- `add-self` -/
def addSelf (t : IntType) : Rule :=
  { name := "add-self", lhs := B t .add (v t 0) (v t 0), rhs := B t .mul (v t 0) (k t 2) }

/-- `mul-two-shl` -/
def mulTwoShl (t : IntType) : Rule :=
  { name := "mul-two-shl", lhs := B t .mul (v t 0) (k t 2), rhs := B t .shl (v t 0) (k t 1) }

/-- `and-self` -/
def andSelf (t : IntType) : Rule :=
  { name := "and-self", lhs := B t .and (v t 0) (v t 0), rhs := v t 0 }

/-- `or-self` -/
def orSelf (t : IntType) : Rule :=
  { name := "or-self", lhs := B t .or (v t 0) (v t 0), rhs := v t 0 }

/-- `mul-neg-one` -/
def mulNegOne (t : IntType) : Rule :=
  { name := "mul-neg-one", lhs := B t .mul (v t 0) (k t (ones t)), rhs := B t .sub (k t 0) (v t 0) }

/-- `add-sub-assoc` -/
def addSubAssoc (t : IntType) : Rule :=
  { name := "add-sub-assoc", lhs := B t .sub (B t .add (v t 0) (v t 1)) (v t 2),
    rhs := B t .add (v t 0) (B t .sub (v t 1) (v t 2)) }

/-- `eqz-eq` -/
def eqzEq (t : IntType) : Rule :=
  { name := "eqz-eq", lhs := .test t (v t 0), rhs := .rel t .eq (v t 0) (k t 0) }

/-- `eqz-eqz` -/
def eqzEqz (t : IntType) : Rule :=
  { name := "eqz-eqz", lhs := .test .i32 (.test t (v t 0)), rhs := .rel t .ne (v t 0) (k t 0) }

/-- `eqz-ne-zero` -/
def eqzNeZero (t : IntType) : Rule :=
  { name := "eqz-ne-zero", lhs := .rel .i32 .ne (.test t (v t 0)) (k .i32 0),
    rhs := .test t (v t 0) }

/-- `eq-comm` -/
def eqComm (t : IntType) : Rule :=
  { name := "eq-comm", lhs := .rel t .eq (v t 0) (v t 1), rhs := .rel t .eq (v t 1) (v t 0) }

/-- `ne-comm` -/
def neComm (t : IntType) : Rule :=
  { name := "ne-comm", lhs := .rel t .ne (v t 0) (v t 1), rhs := .rel t .ne (v t 1) (v t 0) }

/-- `lts-gts` -/
def ltsGts (t : IntType) : Rule :=
  { name := "lts-gts", lhs := .rel t (.lt .signed) (v t 0) (v t 1),
    rhs := .rel t (.gt .signed) (v t 1) (v t 0) }

/-- `ltu-gtu` -/
def ltuGtu (t : IntType) : Rule :=
  { name := "ltu-gtu", lhs := .rel t (.lt .unsigned) (v t 0) (v t 1),
    rhs := .rel t (.gt .unsigned) (v t 1) (v t 0) }

/-- `les-ges` -/
def lesGes (t : IntType) : Rule :=
  { name := "les-ges", lhs := .rel t (.le .signed) (v t 0) (v t 1),
    rhs := .rel t (.ge .signed) (v t 1) (v t 0) }

/-- `leu-geu` -/
def leuGeu (t : IntType) : Rule :=
  { name := "leu-geu", lhs := .rel t (.le .unsigned) (v t 0) (v t 1),
    rhs := .rel t (.ge .unsigned) (v t 1) (v t 0) }

/-- `sub-self` -/
def subSelf (t : IntType) : Rule :=
  { name := "sub-self", lhs := B t .sub (v t 0) (v t 0), rhs := k t 0, kind := .ref }

/-- `xor-self` -/
def xorSelf (t : IntType) : Rule :=
  { name := "xor-self", lhs := B t .xor (v t 0) (v t 0), rhs := k t 0, kind := .ref }

/-- `mul-zero` -/
def mulZero (t : IntType) : Rule :=
  { name := "mul-zero", lhs := B t .mul (v t 0) (k t 0), rhs := k t 0, kind := .ref }

/-- `and-zero` -/
def andZero (t : IntType) : Rule :=
  { name := "and-zero", lhs := B t .and (v t 0) (k t 0), rhs := k t 0, kind := .ref }

/-- `add-sub-cancel` -/
def addSubCancel (t : IntType) : Rule :=
  { name := "add-sub-cancel", lhs := B t .sub (B t .add (v t 0) (v t 1)) (v t 1),
    rhs := v t 0, kind := .ref }

/-- `div-u-one` -/
def divUOne (t : IntType) : Rule :=
  { name := "div-u-one", lhs := B t (.div .unsigned) (v t 0) (k t 1), rhs := v t 0 }

/-- `div-s-one` -/
def divSOne (t : IntType) : Rule :=
  { name := "div-s-one", lhs := B t (.div .signed) (v t 0) (k t 1), rhs := v t 0 }

/-- `shl-width` -/
def shlWidth (t : IntType) : Rule :=
  { name := "shl-width", lhs := B t .shl (v t 0) (k t t.width), rhs := v t 0 }

/-- `shru-width` -/
def shruWidth (t : IntType) : Rule :=
  { name := "shru-width", lhs := B t (.shr .unsigned) (v t 0) (k t t.width), rhs := v t 0 }

/-- `shrs-width` -/
def shrsWidth (t : IntType) : Rule :=
  { name := "shrs-width", lhs := B t (.shr .signed) (v t 0) (k t t.width), rhs := v t 0 }

/-- `neg-mul` -/
def negMul (t : IntType) : Rule :=
  { name := "neg-mul", lhs := B t .mul (B t .sub (k t 0) (v t 0)) (v t 1),
    rhs := B t .sub (k t 0) (B t .mul (v t 0) (v t 1)) }

/-- `sub-self-t` -/
def subSelfT (t : IntType) : Rule :=
  { name := "sub-self-t", lhs := B t .sub (tv t 0) (tv t 0), rhs := k t 0 }

/-- `xor-self-t` -/
def xorSelfT (t : IntType) : Rule :=
  { name := "xor-self-t", lhs := B t .xor (tv t 0) (tv t 0), rhs := k t 0 }

/-- `mul-zero-t` -/
def mulZeroT (t : IntType) : Rule :=
  { name := "mul-zero-t", lhs := B t .mul (tv t 0) (k t 0), rhs := k t 0 }

/-- `and-zero-t` -/
def andZeroT (t : IntType) : Rule :=
  { name := "and-zero-t", lhs := B t .and (tv t 0) (k t 0), rhs := k t 0 }

/-- `or-ones-t` -/
def orOnesT (t : IntType) : Rule :=
  { name := "or-ones-t", lhs := B t .or (tv t 0) (k t (ones t)), rhs := k t (ones t) }

/-- `zero-shl-t` -/
def zeroShlT (t : IntType) : Rule :=
  { name := "zero-shl-t", lhs := B t .shl (k t 0) (tv t 0), rhs := k t 0 }

/-- `zero-shru-t` -/
def zeroShruT (t : IntType) : Rule :=
  { name := "zero-shru-t", lhs := B t (.shr .unsigned) (k t 0) (tv t 0), rhs := k t 0 }

/-- `zero-shrs-t` -/
def zeroShrsT (t : IntType) : Rule :=
  { name := "zero-shrs-t", lhs := B t (.shr .signed) (k t 0) (tv t 0), rhs := k t 0 }

/-- `rem-u-one-t` -/
def remUOneT (t : IntType) : Rule :=
  { name := "rem-u-one-t", lhs := B t (.rem .unsigned) (tv t 0) (k t 1), rhs := k t 0 }

/-- `eq-self-t` -/
def eqSelfT (t : IntType) : Rule :=
  { name := "eq-self-t", lhs := .rel t .eq (tv t 0) (tv t 0), rhs := k .i32 1 }

/-- `ne-self-t` -/
def neSelfT (t : IntType) : Rule :=
  { name := "ne-self-t", lhs := .rel t .ne (tv t 0) (tv t 0), rhs := k .i32 0 }

/-- `lts-self-t` -/
def ltsSelfT (t : IntType) : Rule :=
  { name := "lts-self-t", lhs := .rel t (.lt .signed) (tv t 0) (tv t 0), rhs := k .i32 0 }

/-- `ltu-self-t` -/
def ltuSelfT (t : IntType) : Rule :=
  { name := "ltu-self-t", lhs := .rel t (.lt .unsigned) (tv t 0) (tv t 0), rhs := k .i32 0 }

/-- `gts-self-t` -/
def gtsSelfT (t : IntType) : Rule :=
  { name := "gts-self-t", lhs := .rel t (.gt .signed) (tv t 0) (tv t 0), rhs := k .i32 0 }

/-- `gtu-self-t` -/
def gtuSelfT (t : IntType) : Rule :=
  { name := "gtu-self-t", lhs := .rel t (.gt .unsigned) (tv t 0) (tv t 0), rhs := k .i32 0 }

/-- `les-self-t` -/
def lesSelfT (t : IntType) : Rule :=
  { name := "les-self-t", lhs := .rel t (.le .signed) (tv t 0) (tv t 0), rhs := k .i32 1 }

/-- `leu-self-t` -/
def leuSelfT (t : IntType) : Rule :=
  { name := "leu-self-t", lhs := .rel t (.le .unsigned) (tv t 0) (tv t 0), rhs := k .i32 1 }

/-- `ges-self-t` -/
def gesSelfT (t : IntType) : Rule :=
  { name := "ges-self-t", lhs := .rel t (.ge .signed) (tv t 0) (tv t 0), rhs := k .i32 1 }

/-- `geu-self-t` -/
def geuSelfT (t : IntType) : Rule :=
  { name := "geu-self-t", lhs := .rel t (.ge .unsigned) (tv t 0) (tv t 0), rhs := k .i32 1 }

/-- `zero-gtu-t` -/
def zeroGtuT (t : IntType) : Rule :=
  { name := "zero-gtu-t", lhs := .rel t (.gt .unsigned) (k t 0) (tv t 0), rhs := k .i32 0 }

/-- `ltu-zero-t` -/
def ltuZeroT (t : IntType) : Rule :=
  { name := "ltu-zero-t", lhs := .rel t (.lt .unsigned) (tv t 0) (k t 0), rhs := k .i32 0 }

/-- `geu-zero-t` -/
def geuZeroT (t : IntType) : Rule :=
  { name := "geu-zero-t", lhs := .rel t (.ge .unsigned) (tv t 0) (k t 0), rhs := k .i32 1 }

/-- `zero-leu-t` -/
def zeroLeuT (t : IntType) : Rule :=
  { name := "zero-leu-t", lhs := .rel t (.le .unsigned) (k t 0) (tv t 0), rhs := k .i32 1 }

/-- `add-sub-cancel-t` -/
def addSubCancelT (t : IntType) : Rule :=
  { name := "add-sub-cancel-t", lhs := B t .sub (B t .add (v t 1) (tv t 0)) (tv t 0),
    rhs := v t 1 }

/-- The rule schemas, in library order. -/
def schemas : List (IntType → Rule) :=
  [addComm,
   addAssoc,
   mulComm,
   mulAssoc,
   andComm,
   andAssoc,
   orComm,
   orAssoc,
   xorComm,
   xorAssoc,
   addZero,
   subZero,
   mulOne,
   orZero,
   xorZero,
   andOnes,
   shlZero,
   shruZero,
   shrsZero,
   rotlZero,
   rotrZero,
   mulAddDistrib,
   subAddNeg,
   negNeg,
   addSelf,
   mulTwoShl,
   andSelf,
   orSelf,
   mulNegOne,
   addSubAssoc,
   eqzEq,
   eqzEqz,
   eqzNeZero,
   eqComm,
   neComm,
   ltsGts,
   ltuGtu,
   lesGes,
   leuGeu,
   subSelf,
   xorSelf,
   mulZero,
   andZero,
   addSubCancel,
   divUOne,
   divSOne,
   shlWidth,
   shruWidth,
   shrsWidth,
   negMul,
   subSelfT,
   xorSelfT,
   mulZeroT,
   andZeroT,
   orOnesT,
   zeroShlT,
   zeroShruT,
   zeroShrsT,
   remUOneT,
   eqSelfT,
   neSelfT,
   ltsSelfT,
   ltuSelfT,
   gtsSelfT,
   gtuSelfT,
   lesSelfT,
   leuSelfT,
   gesSelfT,
   geuSelfT,
   zeroGtuT,
   ltuZeroT,
   geuZeroT,
   zeroLeuT,
   addSubCancelT]

/-- **The library**: every schema at `i32`, then at `i64`, interleaved. -/
def library : List Rule := schemas.flatMap fun r => [r .i32, r .i64]

/-! ## Text form (shared with `wasm-egraph rules`) -/

/-- WAT names of the operators. -/
def tyName : IntType → String
  | .i32 => "i32" | .i64 => "i64"

def unName : IntUnOp → String
  | .clz => "clz" | .ctz => "ctz" | .popcnt => "popcnt"
  | .extend .i8 => "extend8_s" | .extend .i16 => "extend16_s" | .extend .i32 => "extend32_s"
  | .extend .i64 => "extend64_s"

def sxName : Signedness → String
  | .signed => "s" | .unsigned => "u"

def binName : IntBinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div s => "div_" ++ sxName s
  | .rem s => "rem_" ++ sxName s | .and => "and" | .or => "or" | .xor => "xor"
  | .shl => "shl" | .shr s => "shr_" ++ sxName s | .rotl => "rotl" | .rotr => "rotr"

def relName : IntRelOp → String
  | .eq => "eq" | .ne => "ne" | .lt s => "lt_" ++ sxName s | .gt s => "gt_" ++ sxName s
  | .le s => "le_" ++ sxName s | .ge s => "ge_" ++ sxName s

/-- A pattern in WAT folded syntax, variables as `?n`. -/
def patText : Pat → String
  | .var _ n => s!"?{n}"
  | .tvar _ n => s!"?{n}!"
  | .const t n => s!"({tyName t}.const {n})"
  | .un t op a => s!"({tyName t}.{unName op} {patText a})"
  | .test t a => s!"({tyName t}.eqz {patText a})"
  | .bin t op a b => s!"({tyName t}.{binName op} {patText a} {patText b})"
  | .rel t op a b => s!"({tyName t}.{relName op} {patText a} {patText b})"

/-- One line of `wasm-egraph rules` (without the index). -/
def Rule.text (r : Rule) : String :=
  let k := match r.kind with | .eq => "eq" | .ref => "ref"
  s!"{r.name} {k} {patText r.lhs} {patText r.rhs}"

end Silmaril.Wasm.Auto.Rules
