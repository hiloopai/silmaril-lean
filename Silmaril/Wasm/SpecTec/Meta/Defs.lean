module

public import Silmaril.Wasm.SpecTec.Sim.Defs
public import Silmaril.Wasm.SpecTec.Meta.Errata.Defs
public import Silmaril.Raw.Wasm.SpecTec.Scripts.MetaIL.Fixed

/-!
# SpecTec's semantics of its own IL, read by ours

`Wasm-DSL/spectec@3a10283c5b` (branch `meta-theory`) specifies SpecTec's internal language in
SpecTec itself (`spectec/doc/semantics/il/*.spectec`): IL syntax as variant types (`exp`, `typ`,
`val`, …), substitution, environments, primitives (`$numbin`, …), small-step reduction
(`Step_exp`, `Reduce_exp`, …) and typing (`Ok_exp`, …). Its `--ast` stream is vendored as
`specs/spectec/meta-theory-3a10283c5b/meta-il.ast` and generated as
`Scripts.MetaIL.Original.script` (`tools/spectec-gen`). Our IL semantics then gives it a meaning:
its relations are read declaratively (`Sim.DDerives`), its functions by our evaluator.

This header fixes

* the two scripts: `original` and `fixed` (the errata of `Meta/Errata/Defs.lean`);
* the **meta-level encoding** of IL syntax and values as values of their IL types (`con`,
  `encNum`, `encUnOp`, `encBinOp`, `encCmpOp`, `encVal`);
* a **fragment** of IL expressions, `FExp`: Boolean and numeric (`nat`, `int`) literals under
  `UnE`, `BinE` and `CmpE`, with its embedding `FExp.toExp` into our IL and its encoding
  `FExp.enc` into theirs. The encoding erases the operator type annotation, as their `exp` does;
* `FExp.strict`, evaluation without short-circuiting, which is what their reduction computes;
* `MStep`/`MReduce`: their `Step_exp`/`Reduce_exp`, read by `DDerives`.

The agreement theorems are in `Silmaril.Wasm.SpecTec.Meta.Thms`; the comparison is
`docs/projects/wasm-extras.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## The scripts -/

/-- The meta-theory script, as elaborated by SpecTec at `3a10283c5b`. -/
noncomputable abbrev original : Script := Scripts.MetaIL.Original.script

/-- The meta-theory script with errata M1 (`Step_exp`) and M2 (`$numbin`). -/
noncomputable abbrev fixed : Script := Scripts.MetaIL.Fixed.script

/-- `original` as an environment. -/
noncomputable def envO : Env := envOfScript original

/-- `fixed` as an environment. -/
noncomputable def envF : Env := envOfScript fixed

/-! ## IL syntax as values of their IL types

A case `C x₁ … xₙ` of one of their variant types is the value `.case "C" (.tuple [x₁, …, xₙ])`
(every case of their `syntax` declarations carries a tuple). -/

/-- The constructor `c` applied to `vs`. -/
def con (c : MixopS) (vs : List Value) : Value := .case c (.tuple vs)

/-- Their `num`: `NAT n`, `INT i`, `RAT q`, `REAL r`. -/
def encNum : Num → Value
  | .natN n => con "NAT" [.num (.natN n)]
  | .intN i => con "INT" [.num (.intN i)]
  | .ratN q => con "RAT" [.num (.ratN q)]
  | .realN s => con "REAL" [.num (.realN s)]

/-- Their `unop` (`boolunop | numunop`). -/
def encUnOp : UnOp → Value
  | .notOp => con "NOT" []
  | .plusOp => con "PLUS" []
  | .minusOp => con "MINUS" []

/-- Their `binop` (`boolbinop | numbinop`). -/
def encBinOp : BinOp → Value
  | .andOp => con "AND" []
  | .orOp => con "OR" []
  | .implOp => con "IMPL" []
  | .equivOp => con "EQUIV" []
  | .addOp => con "ADD" []
  | .subOp => con "SUB" []
  | .mulOp => con "MUL" []
  | .divOp => con "DIV" []
  | .modOp => con "MOD" []
  | .powOp => con "POW" []

/-- Their `cmpop` (`polycmpop | numcmpop`). -/
def encCmpOp : CmpOp → Value
  | .eqOp => con "EQ" []
  | .neOp => con "NE" []
  | .ltOp => con "LT" []
  | .gtOp => con "GT" []
  | .leOp => con "LE" []
  | .geOp => con "GE" []

/-- A scalar value of ours as a value of their `val` (and so, by subtyping, of their `exp`).
Compound values are not encoded: the theorems only need scalars, and their `mixop` (`atom**`)
has no canonical image of our rendered `MixopS`. -/
def encVal : Value → Value
  | .bool b => con "BOOL" [.bool b]
  | .num n => encNum n
  | .text t => con "TEXT" [.text t]
  | _ => con "TEXT" [.text "<not encoded>"]

/-! ## The fragment -/

/-- Closed Boolean and numeric expressions: literals of type `bool`, `nat` and `int`, and
`UnE`, `BinE`, `CmpE` with any operator and any operator type annotation. -/
inductive FExp where
  | bool (b : Bool)
  | nat (n : Nat)
  | int (i : Int)
  | un (op : UnOp) (t : OpTyp) (e : FExp)
  | bin (op : BinOp) (t : OpTyp) (e₁ e₂ : FExp)
  | cmp (op : CmpOp) (t : OpTyp) (e₁ e₂ : FExp)
  deriving DecidableEq, Repr

namespace FExp

/-- The IL expression. -/
def toExp : FExp → Exp
  | .bool b => .boolE b
  | .nat n => .numE (.natN n)
  | .int i => .numE (.intN i)
  | .un op t e => .unE op t e.toExp
  | .bin op t e₁ e₂ => .binE op t e₁.toExp e₂.toExp
  | .cmp op t e₁ e₂ => .cmpE op t e₁.toExp e₂.toExp

/-- The same expression as a value of their `exp`. -/
def enc : FExp → Value
  | .bool b => con "BOOL" [.bool b]
  | .nat n => con "NAT" [.num (.natN n)]
  | .int i => con "INT" [.num (.intN i)]
  | .un op _ e => con "UN" [encUnOp op, e.enc]
  | .bin op _ e₁ e₂ => con "BIN" [encBinOp op, e₁.enc, e₂.enc]
  | .cmp op _ e₁ e₂ => con "CMP" [encCmpOp op, e₁.enc, e₂.enc]

/-- The value of a `Res`, if any. -/
def resVal : Res Value → Option Value
  | .ok v => some v
  | .error _ => none

/-- Evaluation of every subexpression, without short-circuiting: our operators applied to the
values of both operands. -/
def strict : FExp → Option Value
  | .bool b => some (.bool b)
  | .nat n => some (.num (.natN n))
  | .int i => some (.num (.intN i))
  | .un op _ e => e.strict.bind fun v => resVal (unValue op v)
  | .bin op _ e₁ e₂ =>
      e₁.strict.bind fun v₁ => e₂.strict.bind fun v₂ => resVal (binValues op v₁ v₂)
  | .cmp op _ e₁ e₂ =>
      e₁.strict.bind fun v₁ => e₂.strict.bind fun v₂ => resVal (cmpValues op v₁ v₂)

/-- No `pow` is applied to two `int` values: there SpecTec's own typing (`il/valid.ml`) and
evaluation (`Xl.Num.bin`) of `pow` disagree, and their `$numbin(POW, INT i, INT j)` is undefined
(`docs/projects/wasm-extras.md`, F6). -/
def NoIntPow : FExp → Prop
  | .bool _ | .nat _ | .int _ => True
  | .un _ _ e => e.NoIntPow
  | .bin op _ e₁ e₂ => e₁.NoIntPow ∧ e₂.NoIntPow ∧
      (op = .powOp → ∀ i j : Int, e₁.strict = some (.num (.intN i)) →
        e₂.strict = some (.num (.intN j)) → False)
  | .cmp _ _ e₁ e₂ => e₁.NoIntPow ∧ e₂.NoIntPow

end FExp

/-! ## Their reduction relations, read declaratively -/

/-- Their empty store `{TYP eps, FUN eps, REL eps, GRAM eps}`. -/
def emptyS : Value :=
  .struct [("TYP", .list []), ("FUN", .list []), ("REL", .list []), ("GRAM", .list [])]

/-- `S |- a ~> b` (their `Step_exp`). -/
def MStep (env : Env) (S a b : Value) : Prop :=
  Sim.DDerives env (Sim.otherwise env) "Step_exp" "%|-%~>%" [] (.tuple [S, a, b])

/-- `S |- a ~>* b` (their `Reduce_exp`). -/
def MReduce (env : Env) (S a b : Value) : Prop :=
  Sim.DDerives env (Sim.otherwise env) "Reduce_exp" "%|-%~>*%" [] (.tuple [S, a, b])

end Silmaril.Wasm.SpecTec.Meta
