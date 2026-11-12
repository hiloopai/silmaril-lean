module

public import Silmaril.Wasm.SpecTec.Sim.Defs
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecBuiltins
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Floor

/-!
# SpecTec ↔ Core 3.0, integer numerics: the primitives

The integer part of the interpretation `B` of SpecTec's primitives that `Task.wholeStep`
quantifies over. The pinned script declares the bit-level operations of
`3.1-numerics.scalar.spectec` `hint(builtin)` with no clause (`$iclz_`, `$ictz_`, `$ipopcnt_`,
`$iand_`, `$ior_`, `$ixor_`, `$ishl_`, `$ishr_`, `$irotl_`, `$irotr_`) and `$truncz` likewise;
`intCall` interprets them by `Silmaril.Wasm.Numerics` (the `IntegerN` transcription, proved equal
to Core's `intUnOp`/`intBinOp` by `iunop_agree`/`ibinop_agree`).

One more entry is not a primitive: `$irem_`'s signed, non-zero clause binds `j_1`, `j_2` only in an
`if` premise, which the evaluator cannot run, so every clause of `$irem_` definitely fails there
and `callDef` falls back to the builtins (`docs/projects/spectec/README.md`). `intCall` supplies
`IntegerN.irem_` at that name; every other `$irem_` call is answered by its own clauses.

`IntB B` says that `B` extends `intCall`, so the integer facts compose with the other families'
entries of `B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.IntNumeric

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (bvV)
open Silmaril.SpecTec.Equiv.ExecBuiltins (asBits? binBits unBits)

/-- A value of the IL type `sx`, read back. -/
def asSx? : Value → Option Silmaril.Wasm.Signedness
  | .case "U" (.tuple []) => some .unsigned
  | .case "S" (.tuple []) => some .signed
  | _ => none

/-- A value of `u32` (or any `uN(N)`), read back as its natural number. -/
def asPctNat? : Value → Option Nat
  | .case "%" (.tuple [.num (.natN k)]) => some k
  | _ => none

/-- `$truncz`: the integer part of a rational, rounding towards zero (the clause the pinned
script leaves commented out, `3.1-numerics.scalar.spectec:78`). -/
noncomputable def truncQ (q : ℚ) : ℤ := if 0 ≤ q then ⌊q⌋ else ⌈q⌉

/-- A shift primitive `$ish*_(N, i, k)`: `k` is a `u32`, read as its natural number. -/
def shiftBits (N : Nat) (f : BitVec N → Nat → BitVec N) (a b : Value) : Option Value :=
  match asBits? N a, asPctNat? b with
  | some x, some k => some (bvV (f x k))
  | _, _ => none

/-- `$irem_(N, sx, i_1, i_2)`, as `IntegerN.irem_` (an option, so `iN(N)?`). -/
def remBits (N : Nat) (s a b : Value) : Option Value :=
  match asSx? s, asBits? N a, asBits? N b with
  | some sx, some x, some y =>
      some (.opt ((Silmaril.Wasm.Numerics.irem_ N sx x y).map bvV))
  | _, _, _ => none

/-- The integer primitives, at the argument shapes the pinned declarations give them. -/
noncomputable def intCall : IL.Id → List ArgV → Option Value
  | "iclz_", [.val (.num (.natN N)), .val a] => unBits N (Silmaril.Wasm.Numerics.iclz_ N) a
  | "ictz_", [.val (.num (.natN N)), .val a] => unBits N (Silmaril.Wasm.Numerics.ictz_ N) a
  | "ipopcnt_", [.val (.num (.natN N)), .val a] =>
      unBits N (Silmaril.Wasm.Numerics.ipopcnt_ N) a
  | "iand_", [.val (.num (.natN N)), .val a, .val b] =>
      binBits N (Silmaril.Wasm.Numerics.iand_ N) a b
  | "ior_", [.val (.num (.natN N)), .val a, .val b] =>
      binBits N (Silmaril.Wasm.Numerics.ior_ N) a b
  | "ixor_", [.val (.num (.natN N)), .val a, .val b] =>
      binBits N (Silmaril.Wasm.Numerics.ixor_ N) a b
  | "irotl_", [.val (.num (.natN N)), .val a, .val b] =>
      binBits N (Silmaril.Wasm.Numerics.irotl_ N) a b
  | "irotr_", [.val (.num (.natN N)), .val a, .val b] =>
      binBits N (Silmaril.Wasm.Numerics.irotr_ N) a b
  | "ishl_", [.val (.num (.natN N)), .val a, .val b] =>
      shiftBits N (Silmaril.Wasm.Numerics.ishl_ N) a b
  | "ishr_", [.val (.num (.natN N)), .val s, .val a, .val b] =>
      match asSx? s with
      | some sx => shiftBits N (Silmaril.Wasm.Numerics.ishr_ N sx) a b
      | none => none
  | "truncz", [.val (.num (.ratN q))] => some (.num (.intN (truncQ q)))
  | "irem_", [.val (.num (.natN N)), .val s, .val a, .val b] => remBits N s a b
  | _, _ => none

/-- The integer primitives, as an interpretation on their own. -/
noncomputable def intB : Builtins := ⟨intCall⟩

/-- `B` extends the integer primitives: wherever `intCall` answers, `B` gives the same answer.
This is the hypothesis every integer lemma of the family takes about `B`. -/
def IntB (B : Builtins) : Prop := ∀ x ws v, intCall x ws = some v → B.call x ws = some v

theorem intB_intB : IntB intB := fun _ _ _ h => h

/-! ## The operator values of the integer instructions (as `Equiv.instrV` writes them) -/

/-- `Inn` as an IL value: `I32` or `I64`. -/
def ntV (t : Silmaril.Wasm.IntType) : Value :=
  Encode.toValue (Silmaril.Wasm.NumType.int t)

/-- An `unop_(Inn)`. -/
def iunopV : Silmaril.Wasm.IntUnOp → Value
  | .clz => .case "CLZ" (.tuple [])
  | .ctz => .case "CTZ" (.tuple [])
  | .popcnt => .case "POPCNT" (.tuple [])
  | .extend p => .case "EXTEND" (.tuple [.case "%" (.tuple [.num (.natN p.width)])])

/-- A `binop_(Inn)`. -/
def ibinopV : Silmaril.Wasm.IntBinOp → Value
  | .add => .case "ADD" (.tuple [])
  | .sub => .case "SUB" (.tuple [])
  | .mul => .case "MUL" (.tuple [])
  | .div s => .case "DIV" (Equiv.sxV s)
  | .rem s => .case "REM" (Equiv.sxV s)
  | .and => .case "AND" (.tuple [])
  | .or => .case "OR" (.tuple [])
  | .xor => .case "XOR" (.tuple [])
  | .shl => .case "SHL" (.tuple [])
  | .shr s => .case "SHR" (Equiv.sxV s)
  | .rotl => .case "ROTL" (.tuple [])
  | .rotr => .case "ROTR" (.tuple [])

/-- A `testop_(Inn)`. -/
def itestopV : Silmaril.Wasm.IntTestOp → Value
  | .eqz => .case "EQZ" (.tuple [])

/-- A `relop_(Inn)`. -/
def irelopV : Silmaril.Wasm.IntRelOp → Value
  | .eq => .case "EQ" (.tuple [])
  | .ne => .case "NE" (.tuple [])
  | .lt s => .case "LT" (Equiv.sxV s)
  | .gt s => .case "GT" (Equiv.sxV s)
  | .le s => .case "LE" (Equiv.sxV s)
  | .ge s => .case "GE" (Equiv.sxV s)


/-! ## Typing of the quantified values of the integer rules -/

/-- The IL types the integer rules quantify over, inhabited by the encodings of Core's integer
values and operators, in every scope binding term variables only. The type arguments are read
through an expression `e` evaluating to the integer type, as the rules write them (`num_(nt)`
with `nt` bound, or `num_(I32)`). This is the family's typing interface; `intTyping_simEnv`
discharges it. -/
structure IntTyping (env : Env) : Prop where
  /-- `numtype` holds `I32`/`I64`. -/
  numtype : ∀ (ρ : VarEnv) (t : Silmaril.Wasm.IntType), ValsOnly ρ →
    HasTyp env ρ (.varT "numtype" []) (ntV t)
  /-- `num_(Inn)` holds every bit pattern of the width. -/
  num : ∀ (ρ : VarEnv) (e : Exp) (t : Silmaril.Wasm.IntType) (b : BitVec t.width), ValsOnly ρ →
    EvalExp env ρ e (ntV t) → HasTyp env ρ (.varT "num_" [.expA e]) (bvV b)
  /-- `unop_(Inn)` holds every operator valid at the type. -/
  unop : ∀ (ρ : VarEnv) (e : Exp) (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntUnOp),
    op.valid t = true → ValsOnly ρ → EvalExp env ρ e (ntV t) →
    HasTyp env ρ (.varT "unop_" [.expA e]) (iunopV op)
  /-- `binop_(Inn)` holds every integer binary operator. -/
  binop : ∀ (ρ : VarEnv) (e : Exp) (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntBinOp),
    ValsOnly ρ → EvalExp env ρ e (ntV t) → HasTyp env ρ (.varT "binop_" [.expA e]) (ibinopV op)
  /-- `testop_(Inn)` holds `EQZ`. -/
  testop : ∀ (ρ : VarEnv) (e : Exp) (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntTestOp),
    ValsOnly ρ → EvalExp env ρ e (ntV t) → HasTyp env ρ (.varT "testop_" [.expA e]) (itestopV op)
  /-- `relop_(Inn)` holds every integer comparison. -/
  relop : ∀ (ρ : VarEnv) (e : Exp) (t : Silmaril.Wasm.IntType) (op : Silmaril.Wasm.IntRelOp),
    ValsOnly ρ → EvalExp env ρ e (ntV t) → HasTyp env ρ (.varT "relop_" [.expA e]) (irelopV op)


/-! ## The other numeric constructors, as an interface -/

section Other

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type}

/-- The `Forward` obligations of the constructors of `NumericStep` this family does not prove:
the float operators and the conversions (binders copied from `Core/Step/Numeric.lean`). With
them, `fwd_numeric` is the whole `Forward.numeric` field. -/
structure OtherNumericFwd (env : Env) (hn : H → String) (P : Profile) : Prop where
  floatUnOp : ∀ {s : Store H} {f : Frame} {t : FloatType} {op : FloatUnOp}
    {x z : BitVec t.width} (_ : floatUnOpP P t op x z),
    FwdP env hn ⟨s, f, [.plain (.floatConst t x), .plain (.floatUnOp t op)]⟩
      ⟨s, f, [.plain (.floatConst t z)]⟩
  floatBinOp : ∀ {s : Store H} {f : Frame} {t : FloatType} {op : FloatBinOp}
    {x y z : BitVec t.width} (_ : floatBinOpP P t op x y z),
    FwdP env hn ⟨s, f, [.plain (.floatConst t x), .plain (.floatConst t y),
      .plain (.floatBinOp t op)]⟩ ⟨s, f, [.plain (.floatConst t z)]⟩
  floatRelOp : ∀ {s : Store H} {f : Frame} {t : FloatType} {op : FloatRelOp}
    {x y : BitVec t.width},
    FwdP env hn ⟨s, f, [.plain (.floatConst t x), .plain (.floatConst t y),
      .plain (.floatRelOp t op)]⟩ ⟨s, f, [constI32 (floatRelOp t op x y)]⟩
  convert : ∀ {s : Store H} {f : Frame} {op : ConvertOp} {x : BitVec op.source.width}
    {z : BitVec op.target.width} (_ : convertP P op x (.ok z)),
    FwdP env hn ⟨s, f, [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)]⟩
      ⟨s, f, [(Val.num ⟨op.target, z⟩).toAdmin]⟩
  convertTrap : ∀ {s : Store H} {f : Frame} {op : ConvertOp} {x : BitVec op.source.width}
    {e : FloatTrap} (_ : convertP P op x (.error e)),
    FwdP env hn ⟨s, f, [(Val.num ⟨op.source, x⟩).toAdmin, .plain (.convert op)]⟩
      ⟨s, f, [.trap]⟩

end Other

end Silmaril.Wasm.SpecTec.Sim.IntNumeric
