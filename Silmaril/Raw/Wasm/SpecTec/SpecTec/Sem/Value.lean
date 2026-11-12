module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Ast

/-!
# The universal value domain for SpecTec's internal language

This is step 1 of `docs/projects/spectec/README.md`: the domain in which every IL
expression, premise, rule and grammar production will be interpreted, together
with the projections and the numeric primitives the evaluator of
`Silmaril/SpecTec/Sem/Eval.lean` needs.

Everything is relative to the pin `608711107b7f1edb13efd57b7d79b49477462d36`.

## Why a separate domain

SpecTec's own evaluator (`spectec/src/il/eval.ml`) is a reduction on
expressions, so an IL "value" there is an `Il.Ast.exp` in normal form: it
carries a source region, a type note, and possibly unreduced subterms.  That is
convenient for an interpreter and bad for reasoning.  `Value` below is a
first-order datatype with exactly one constructor per IL type former, so a
value is a value and nothing else.

## The constructors, against `Silmaril/SpecTec/IL/Ast.lean`

`Typ` (`spectec/src/il/ast.ml:29-35`) and `DefTyp` (`ast.ml:38-41`) have
exactly these type formers, and each one gets exactly one constructor.

| IL type former | `ast.ml` | `Value` constructor |
| --- | --- | --- |
| `BoolT` | 31 | `bool` |
| `NumT numtyp` | 32 | `num` |
| `TextT` | 33 | `text` |
| `TupT binds` | 34 | `tuple` |
| `IterT t Opt` | 35, 17 | `opt` |
| `IterT t (List \| List1 \| ListN _)` | 35, 18-20 | `list` |
| `VarT x args` → `StructT fields` | 30, 40 | `struct` |
| `VarT x args` → `VariantT cases` | 30, 41 | `case` |
| `VarT x args` → `AliasT t` | 30, 39 | none: transparent |

`VarT` itself gets no constructor: it is resolved through the environment to a
`DefTyp`.  An `AliasT` (`ast.ml:39`) is transparent, so its values are the
values of the aliased type; a `StructT` (`ast.ml:40`) is a record, whose fields
are keyed by an `atom` (`ast.ml:43`), hence `struct`; a `VariantT`
(`ast.ml:41`) is a sum whose injections are keyed by a `mixop` (`ast.ml:44`),
hence `case`.  `TupT`'s binders are dependent — `(id * typ) list` — but a
binder only affects the *type* of a later component, never the shape of the
tuple, so the value is still a plain `tuple` of components.

`case` carries a single `Value` rather than a list because `typcase` carries a
single `typ` (`ast.ml:44`) and `CaseE` a single `exp` (`ast.ml:65`); an
`n`-ary case is a `case` over a `tuple`.

### Why there is no constructor for functions or grammars

The IL is first order.  `typ'` (`ast.ml:29-35`) has no arrow former at all, so
no well-typed IL expression ever has a function type and no value can be a
closure.  Functions (`DecD`, `ast.ml:135`) and grammars (`GramD`,
`ast.ml:136`) are *definitions*, named at the top level of a `Script`, and
they are passed around by **name**, never by value: the higher-order
parameters `DefP of id * param list * typ` and
`GramP of id * param list * typ` (`ast.ml:126-127`) are instantiated by the
arguments `DefA of id` and `GramA of sym` (`ast.ml:119-120`), which carry an
identifier and a grammar symbol — syntax, not semantics.  So a function
argument is a `Script` lookup and a grammar argument is a piece of `Sym` to be
interpreted later; neither needs a slot in the value domain.  A grammar's
denotation is a *relation* between byte strings and values
(`docs/projects/spectec/README.md`), not itself a value.

## Namespacing of the numeric operations

`spectec/src/xl/num.ml`'s operations act on `Silmaril.SpecTec.IL.Num`, which
is declared in `Silmaril/SpecTec/IL/Ast.lean`.  They are *semantics*, not
syntax, so they live here, in `Silmaril.SpecTec.Sem.Num` rather than in
`Silmaril.SpecTec.IL.Num`; write `Num.bin op n₁ n₂` with
`Silmaril.SpecTec.Sem` open.  The price is that `IL.Num`-valued dot notation
(`n.bin`) does not reach them.

## Reals

`Num.realN` (`ast.ml`'s transcription of `` `Real of real ``,
`spectec/src/xl/num.ml:11`) stores the *rendering* `Printf.sprintf "%.17g" r`
(`num.ml:25`) and nothing else, because that string is all a `--ast` stream
contains.  A rendering cannot be computed with, so **every numeric operation
that would need the float is `none` here**, and `Num.Representable` picks out
the three constructors that are not `realN`.  The only operations on a `realN`
that survive are the two that return their argument unchanged and so need no
arithmetic: `Num.un .plusOp` (`num.ml:129`) and `Num.cvt .realT`
(`num.ml:96`).  No pinned specification in `specs/spectec/` contains a real.
-/

@[expose] public section

namespace Silmaril.SpecTec.Sem

open Silmaril.SpecTec.IL

/-! ## Numeric operations (`spectec/src/xl/num.ml`)

`Xl.Num.unop`, `binop` and `cmpop` (`num.ml:16-18`) are *subsets* of the IL's
`unop`, `binop` and `cmpop` (`spectec/src/il/ast.ml:49-51`), which also
contain `Xl.Bool`'s operators.  The functions below take the IL operator and
return `none` on a boolean one, which is what `eval.ml` does by dispatching on
the `#Num.unop` / `#Num.binop` / `#Num.cmpop` row patterns
(`eval.ml:231,249,264`) and leaving the rest to `Xl.Bool`. -/

namespace Num

/-- `Xl.Num.to_typ` (`spectec/src/xl/num.ml:60-64`): the numeric type of a
numeric literal. -/
def toTyp : Num → NumTyp
  | .natN _ => .natT
  | .intN _ => .intT
  | .ratN _ => .ratT
  | .realN _ => .realT

/-- The three `Num` constructors that carry an actual number.

`realN` carries only `Printf.sprintf "%.17g" r` (`spectec/src/xl/num.ml:25`),
so it is excluded; see the module docstring. -/
def Representable : Num → Prop
  | .natN _ => True
  | .intN _ => True
  | .ratN _ => True
  | .realN _ => False

instance (n : Num) : Decidable (Representable n) :=
  match n with
  | .natN _ => .isTrue trivial
  | .intN _ => .isTrue trivial
  | .ratN _ => .isTrue trivial
  | .realN _ => .isFalse id

@[simp] theorem representable_natN (n : Nat) : Representable (.natN n) := trivial
@[simp] theorem representable_intN (i : Int) : Representable (.intN i) := trivial
@[simp] theorem representable_ratN (q : Rat) : Representable (.ratN q) := trivial
@[simp] theorem not_representable_realN (s : String) :
    ¬ Representable (.realN s) := id

/-- `Representable` is exactly "not of type `real`". -/
theorem representable_iff {n : Num} : Representable n ↔ toTyp n ≠ .realT := by
  cases n <;> simp [Representable, toTyp]

/-- `Xl.Num.sub` (`spectec/src/xl/num.ml:52-57`), the subtyping order on
numeric types: `nat ≤ int ≤ rat ≤ real`, written as a four-clause match in
OCaml. -/
def subTyp : NumTyp → NumTyp → Bool
  | _, .realT => true
  | .natT, _ => true
  | .intT, .ratT => true
  | t₁, t₂ => t₁ == t₂

/-- `Xl.Num.typ_unop` (`spectec/src/xl/num.ml:66-68`): `PlusOp` and `MinusOp`
take `t` to `t` for any `t` above `int`.  A boolean operator is rejected,
since `Xl.Num.unop` is only `` `PlusOp | `MinusOp `` (`num.ml:16`). -/
def typUnOp : UnOp → NumTyp → NumTyp → Bool
  | .notOp, _, _ => false
  | .plusOp, t₁, t₂ | .minusOp, t₁, t₂ => t₁ == t₂ && subTyp .intT t₁

/-- `Xl.Num.typ_binop` (`spectec/src/xl/num.ml:70-76`), for
`op : t₁ × t₂ → t₃`.  Note the OCaml precedence at `num.ml:76`: `&&` binds
tighter than `||`, so `PowOp` is `t₁ = t₃ ∧ (t₂ = nat ∨ (t₂ = int ∧ rat ≤ t₁))`.
A boolean operator is rejected (`num.ml:17`). -/
def typBinOp : BinOp → NumTyp → NumTyp → NumTyp → Bool
  | .andOp, _, _, _ | .orOp, _, _, _ | .implOp, _, _, _ | .equivOp, _, _, _ => false
  | .addOp, t₁, t₂, t₃ | .mulOp, t₁, t₂, t₃ => t₁ == t₂ && t₁ == t₃
  | .subOp, t₁, t₂, t₃ => t₁ == t₂ && subTyp .intT t₃
  | .divOp, t₁, t₂, t₃ => t₁ == t₂ && subTyp .ratT t₃
  | .modOp, t₁, t₂, t₃ => t₁ == t₂ && t₁ == t₃ && subTyp t₁ .intT
  | .powOp, t₁, t₂, t₃ => t₁ == t₃ && (t₂ == .natT || (t₂ == .intT && subTyp .ratT t₁))

/-- `Xl.Num.cvt` (`spectec/src/xl/num.ml:79-96`): coerce a number to a numeric
type, or fail.

Four clauses of the OCaml are `none` here, all of them involving a float:
`num.ml:85,89,93` build a `` `Real `` out of `Z.to_float` / `Q.to_float`, and
`num.ml:94-95` reads one back with `Q.of_float`.  A `realN` stores a rendering,
not a float, so none of those is computable; `num.ml:96` is the identity and
does survive.

`num.ml:90` (`` `Rat `` to `` `NatT ``) routes through `` `IntT ``, which
unfolds to "denominator one and numerator non-negative"; `num.ml:86` is
`Z.sign i >= 0`. -/
def cvt : NumTyp → Num → Option Num
  | .natT, .natN n => some (.natN n)
  | .intT, .natN n => some (.intN n)
  | .ratT, .natN n => some (.ratN n)
  | .realT, .natN _ => none
  | .natT, .intN i => if 0 ≤ i then some (.natN i.toNat) else none
  | .intT, .intN i => some (.intN i)
  | .ratT, .intN i => some (.ratN i)
  | .realT, .intN _ => none
  | .natT, .ratN q => if q.den = 1 ∧ 0 ≤ q.num then some (.natN q.num.toNat) else none
  | .intT, .ratN q => if q.den = 1 then some (.intN q.num) else none
  | .ratT, .ratN q => some (.ratN q)
  | .realT, .ratN _ => none
  | .natT, .realN _ => none
  | .intT, .realN _ => none
  | .ratT, .realN _ => none
  | .realT, .realN s => some (.realN s)

/-- `Xl.Num.un` (`spectec/src/xl/num.ml:122-132`).

`num.ml:128-129` is the identity on every constructor, `realN` included, since
it computes nothing.  `num.ml:130` sends both `` `Nat `` and `` `Int `` to an
`` `Int ``, so unary minus leaves `nat`.  `num.ml:132` negates a float and is
therefore `none` here.  `notOp` is `Xl.Bool`'s (`spectec/src/xl/bool.ml`), not
`Xl.Num`'s (`num.ml:16`), so it is `none` too. -/
def un : UnOp → Num → Option Num
  | .notOp, _ => none
  | .plusOp, .natN n => some (.natN n)
  | .plusOp, .intN i => some (.intN i)
  | .plusOp, .ratN q => some (.ratN q)
  | .plusOp, .realN s => some (.realN s)
  | .minusOp, .natN n => some (.intN (-(n : Int)))
  | .minusOp, .intN i => some (.intN (-i))
  | .minusOp, .ratN q => some (.ratN (-q))
  | .minusOp, .realN _ => none

/-- `Xl.Num.bin` (`spectec/src/xl/num.ml:134-174`).

Both arguments must have the *same* constructor: there is no implicit widening
here, and the catch-all at `num.ml:174` rejects every mixed pair.  Clause by
clause:

* `AddOp` — `num.ml:140-143`; `MulOp` — `num.ml:150-153`.
* `SubOp` — `num.ml:145-148`.  On `nat` the guard `n1 >= n2` (`num.ml:145`)
  means an underflowing subtraction is `none`, *not* an `int`.
* `DivOp` — `num.ml:155-158`.  On `nat` and `int` division must be exact
  (`rem = zero`) as well as by a non-zero divisor; `Z.rem` and `Z.div`
  truncate towards zero, hence `Int.tmod` and `Int.tdiv`.
* `ModOp` — `num.ml:160-161`.  Defined only on `nat` and `int`, and `Z.rem`
  again truncates towards zero, so `Int.tmod`, which is *not* Lean's `%` on
  `Int` (that is `Int.emod`, which rounds the quotient towards `-∞`).
* `PowOp` — `num.ml:163-172`.  `num.ml:165-166` computes
  `(num q₁ ^ k) / (den q₁ ^ k)`, which is `q₁ ^ k`: `Q` normalises, and
  `gcd (num q₁) (den q₁) = 1` gives `gcd (num q₁ ^ k) (den q₁ ^ k) = 1`.
  `num.ml:167-171` handles a negative rational exponent by recursion and then
  `Q.(one / q)`.

Three deliberate divergences, all forced:

* every `realN` clause (`num.ml:143,148,153,158,172`) is `none`;
* `Z.fits_int` (`num.ml:164-165`) and the implicit `Z.to_int` at `num.ml:163`
  bound an exponent by an OCaml machine word and raise otherwise; a Lean `Nat`
  exponent has no such bound, so we compute where OCaml would overflow;
* `num.ml:169` evaluates `Q.(one / q)` with `q = 0` when the base is `0` and
  the exponent negative, which is Zarith's `inf`; `Rat` has no infinity (see
  `Silmaril/SpecTec/IL/Ast.lean`'s module docstring), so that case is `none`. -/
def bin : BinOp → Num → Num → Option Num
  | .andOp, _, _ | .orOp, _, _ | .implOp, _, _ | .equivOp, _, _ => none
  | .addOp, .natN a, .natN b => some (.natN (a + b))
  | .addOp, .intN a, .intN b => some (.intN (a + b))
  | .addOp, .ratN a, .ratN b => some (.ratN (a + b))
  | .subOp, .natN a, .natN b => if b ≤ a then some (.natN (a - b)) else none
  | .subOp, .intN a, .intN b => some (.intN (a - b))
  | .subOp, .ratN a, .ratN b => some (.ratN (a - b))
  | .mulOp, .natN a, .natN b => some (.natN (a * b))
  | .mulOp, .intN a, .intN b => some (.intN (a * b))
  | .mulOp, .ratN a, .ratN b => some (.ratN (a * b))
  | .divOp, .natN a, .natN b =>
      if b = 0 then none else if a % b = 0 then some (.natN (a / b)) else none
  | .divOp, .intN a, .intN b =>
      if b = 0 then none else if a.tmod b = 0 then some (.intN (a.tdiv b)) else none
  | .divOp, .ratN a, .ratN b => if b = 0 then none else some (.ratN (a / b))
  | .modOp, .natN a, .natN b => if b = 0 then none else some (.natN (a % b))
  | .modOp, .intN a, .intN b => if b = 0 then none else some (.intN (a.tmod b))
  | .powOp, .natN a, .natN b => some (.natN (a ^ b))
  | .powOp, .intN a, .intN b => if 0 ≤ b then some (.intN (a ^ b.toNat)) else none
  | .powOp, .ratN a, .ratN b =>
      if b.den ≠ 1 then none
      else if 0 ≤ b then some (.ratN (a ^ b.num.toNat))
      else if a = 0 then none
      else some (.ratN (1 / a ^ (-b.num).toNat))
  | _, _, _ => none

/-- `Xl.Num.cmp` (`spectec/src/xl/num.ml:277-303`).

`Xl.Num.cmpop` is only `` `LtOp | `GtOp | `LeOp | `GeOp `` (`num.ml:18`), so
`eqOp` and `neOp` are `none`: `eval.ml:260-263` settles those by structural
equality of the reduced expressions (`Eq.eq_exp`) before `Num.cmp` is ever
reached.  Mixed constructors are `none` (`num.ml:303`), and so is every
`realN` pair, which would need a float comparison. -/
def cmp : CmpOp → Num → Num → Option Bool
  | .eqOp, _, _ | .neOp, _, _ => none
  | .ltOp, .natN a, .natN b => some (a < b)
  | .ltOp, .intN a, .intN b => some (a < b)
  | .ltOp, .ratN a, .ratN b => some (a < b)
  | .gtOp, .natN a, .natN b => some (a > b)
  | .gtOp, .intN a, .intN b => some (a > b)
  | .gtOp, .ratN a, .ratN b => some (a > b)
  | .leOp, .natN a, .natN b => some (a ≤ b)
  | .leOp, .intN a, .intN b => some (a ≤ b)
  | .leOp, .ratN a, .ratN b => some (a ≤ b)
  | .geOp, .natN a, .natN b => some (a ≥ b)
  | .geOp, .intN a, .intN b => some (a ≥ b)
  | .geOp, .ratN a, .ratN b => some (a ≥ b)
  | _, _, _ => none

/-! ### Metatheory of the numeric operations -/

/-- `un` is a function, hence deterministic. -/
theorem un_deterministic {op : UnOp} {n : Num} {r₁ r₂ : Option Num}
    (h₁ : un op n = r₁) (h₂ : un op n = r₂) : r₁ = r₂ := by
  subst h₁; exact h₂

/-- `bin` is a function, hence deterministic. -/
theorem bin_deterministic {op : BinOp} {m n : Num} {r₁ r₂ : Option Num}
    (h₁ : bin op m n = r₁) (h₂ : bin op m n = r₂) : r₁ = r₂ := by
  subst h₁; exact h₂

/-- `cmp` is a function, hence deterministic. -/
theorem cmp_deterministic {op : CmpOp} {m n : Num} {r₁ r₂ : Option Bool}
    (h₁ : cmp op m n = r₁) (h₂ : cmp op m n = r₂) : r₁ = r₂ := by
  subst h₁; exact h₂

/-- `cmp` is decidable: it is a total function into `Option Bool`, so every
comparison it can make is settled by `Option Bool`'s decidable equality.  A
`def` rather than an `instance`, because `inferInstance` already finds this and
a second copy would only create a duplicate. -/
def decidableCmp (op : CmpOp) (m n : Num) (r : Option Bool) :
    Decidable (cmp op m n = r) := inferInstance

/-- `cmp` is defined exactly when the operator is one of `Xl.Num.cmpop`
(`spectec/src/xl/num.ml:18`) — so neither `eqOp` nor `neOp` — and the two
arguments are the same representable constructor
(`spectec/src/xl/num.ml:283-303`). -/
theorem cmp_isSome_iff {op : CmpOp} {m n : Num} :
    (cmp op m n).isSome ↔
      (op ≠ .eqOp ∧ op ≠ .neOp) ∧ Representable m ∧ toTyp m = toTyp n := by
  cases op <;> cases m <;> cases n <;> simp [cmp, Representable, toTyp]

@[simp] theorem cmp_ltOp_natN (a b : Nat) :
    cmp .ltOp (.natN a) (.natN b) = some (decide (a < b)) := rfl
@[simp] theorem cmp_ltOp_intN (a b : Int) :
    cmp .ltOp (.intN a) (.intN b) = some (decide (a < b)) := rfl
@[simp] theorem cmp_ltOp_ratN (a b : Rat) :
    cmp .ltOp (.ratN a) (.ratN b) = some (decide (a < b)) := rfl
@[simp] theorem cmp_gtOp_natN (a b : Nat) :
    cmp .gtOp (.natN a) (.natN b) = some (decide (b < a)) := rfl
@[simp] theorem cmp_gtOp_intN (a b : Int) :
    cmp .gtOp (.intN a) (.intN b) = some (decide (b < a)) := rfl
@[simp] theorem cmp_gtOp_ratN (a b : Rat) :
    cmp .gtOp (.ratN a) (.ratN b) = some (decide (b < a)) := rfl
@[simp] theorem cmp_leOp_natN (a b : Nat) :
    cmp .leOp (.natN a) (.natN b) = some (decide (a ≤ b)) := rfl
@[simp] theorem cmp_leOp_intN (a b : Int) :
    cmp .leOp (.intN a) (.intN b) = some (decide (a ≤ b)) := rfl
@[simp] theorem cmp_leOp_ratN (a b : Rat) :
    cmp .leOp (.ratN a) (.ratN b) = some (decide (a ≤ b)) := rfl
@[simp] theorem cmp_geOp_natN (a b : Nat) :
    cmp .geOp (.natN a) (.natN b) = some (decide (b ≤ a)) := rfl
@[simp] theorem cmp_geOp_intN (a b : Int) :
    cmp .geOp (.intN a) (.intN b) = some (decide (b ≤ a)) := rfl
@[simp] theorem cmp_geOp_ratN (a b : Rat) :
    cmp .geOp (.ratN a) (.ratN b) = some (decide (b ≤ a)) := rfl

/-- `cmp .ltOp` on `natN` is `<`. -/
theorem cmp_ltOp_natN_iff {a b : Nat} : cmp .ltOp (.natN a) (.natN b) = some true ↔ a < b := by
  simp

/-- `cmp .ltOp` on `intN` is `<`. -/
theorem cmp_ltOp_intN_iff {a b : Int} : cmp .ltOp (.intN a) (.intN b) = some true ↔ a < b := by
  simp

/-- `cmp .ltOp` on `ratN` is `<`. -/
theorem cmp_ltOp_ratN_iff {a b : Rat} : cmp .ltOp (.ratN a) (.ratN b) = some true ↔ a < b := by
  simp

/-- `cmp .leOp` on `natN` is `≤`. -/
theorem cmp_leOp_natN_iff {a b : Nat} : cmp .leOp (.natN a) (.natN b) = some true ↔ a ≤ b := by
  simp

/-- `cmp .leOp` on `intN` is `≤`. -/
theorem cmp_leOp_intN_iff {a b : Int} : cmp .leOp (.intN a) (.intN b) = some true ↔ a ≤ b := by
  simp

/-- `cmp .leOp` on `ratN` is `≤`. -/
theorem cmp_leOp_ratN_iff {a b : Rat} : cmp .leOp (.ratN a) (.ratN b) = some true ↔ a ≤ b := by
  simp

/-- `cmp .ltOp` is irreflexive on the representable constructors: it really is
the strict order. -/
theorem cmp_ltOp_irrefl {n : Num} (h : Representable n) : cmp .ltOp n n = some false := by
  cases n <;> simp_all [Representable]

/-- `cmp .leOp` is reflexive on the representable constructors: it really is
the non-strict order.  Companion to `cmp_ltOp_irrefl`. -/
theorem cmp_leOp_refl {n : Num} (h : Representable n) : cmp .leOp n n = some true := by
  cases n <;> simp_all [Representable]

/-- Division by zero is `none` on `nat` (`spectec/src/xl/num.ml:155`). -/
@[simp] theorem bin_divOp_natN_zero (a : Nat) : bin .divOp (.natN a) (.natN 0) = none := rfl

/-- Division by zero is `none` on `int` (`spectec/src/xl/num.ml:156`). -/
@[simp] theorem bin_divOp_intN_zero (a : Int) : bin .divOp (.intN a) (.intN 0) = none := rfl

/-- Division by zero is `none` on `rat` (`spectec/src/xl/num.ml:157`). -/
@[simp] theorem bin_divOp_ratN_zero (a : Rat) : bin .divOp (.ratN a) (.ratN 0) = none := rfl

/-- Modulo by zero is `none` on `nat` (`spectec/src/xl/num.ml:160`). -/
@[simp] theorem bin_modOp_natN_zero (a : Nat) : bin .modOp (.natN a) (.natN 0) = none := rfl

/-- Modulo by zero is `none` on `int` (`spectec/src/xl/num.ml:161`). -/
@[simp] theorem bin_modOp_intN_zero (a : Int) : bin .modOp (.intN a) (.intN 0) = none := rfl

/-- `modOp` exists only on `nat` and `int` (`spectec/src/xl/num.ml:160-161`);
on `rat` it falls through to the catch-all at `num.ml:174`. -/
@[simp] theorem bin_modOp_ratN (a b : Rat) : bin .modOp (.ratN a) (.ratN b) = none := rfl

/-- No binary operation touches a `realN`. -/
@[simp] theorem bin_realN_left (op : BinOp) (s : String) (n : Num) :
    bin op (.realN s) n = none := by
  cases op <;> cases n <;> rfl

/-- No binary operation touches a `realN`. -/
@[simp] theorem bin_realN_right (op : BinOp) (s : String) (n : Num) :
    bin op n (.realN s) = none := by
  cases op <;> cases n <;> rfl

/-- No comparison touches a `realN`. -/
@[simp] theorem cmp_realN_left (op : CmpOp) (s : String) (n : Num) :
    cmp op (.realN s) n = none := by
  cases op <;> cases n <;> rfl

/-- No comparison touches a `realN`. -/
@[simp] theorem cmp_realN_right (op : CmpOp) (s : String) (n : Num) :
    cmp op n (.realN s) = none := by
  cases op <;> cases n <;> rfl

/-- The one surviving unary operation on a `realN`
(`spectec/src/xl/num.ml:129`). -/
@[simp] theorem un_plusOp_realN (s : String) : un .plusOp (.realN s) = some (.realN s) := rfl

/-- Unary minus on a `realN` needs the float (`spectec/src/xl/num.ml:132`). -/
@[simp] theorem un_minusOp_realN (s : String) : un .minusOp (.realN s) = none := rfl

/-- `bin` and `un` never manufacture a `realN` out of representable
arguments, so the representable part of the domain is closed. -/
theorem representable_of_un {op : UnOp} {m n : Num}
    (hm : Representable m) (h : un op m = some n) : Representable n := by
  rcases n with _ | _ | _ | s
  · trivial
  · trivial
  · trivial
  · exfalso
    cases op <;> cases m <;> simp_all [un, Representable]

/-- Companion to `representable_of_un` for `bin`. -/
theorem representable_of_bin {op : BinOp} {m₁ m₂ n : Num}
    (h : bin op m₁ m₂ = some n) : Representable n := by
  rcases n with _ | _ | _ | s
  · trivial
  · trivial
  · trivial
  · exfalso
    cases op <;> cases m₁ <;> cases m₂ <;> simp only [bin] at h <;>
      (try split_ifs at h) <;> simp_all

/-- `cvt` lands in the requested type (`spectec/src/xl/num.ml:79-96`). -/
theorem toTyp_cvt {t : NumTyp} {m n : Num} (h : cvt t m = some n) : toTyp n = t := by
  cases t <;> cases m <;> simp only [cvt] at h <;> (try split_ifs at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> (try subst h) <;> rfl

end Num

/-! ## The value domain -/

/-- The universal value domain of `docs/projects/spectec/README.md`: one constructor
per type former of `Silmaril.SpecTec.IL.Typ` and
`Silmaril.SpecTec.IL.DefTyp`.  See the module docstring for the table, and for
why there is no constructor for a function or a grammar.

`Repr` and `Inhabited` are derived; `DecidableEq` is `Value.decEq`, written
out by hand because Lean's deriving handler does not apply to a nested
inductive — the recursive occurrences here sit under `List`, `Option` and
`List (AtomS × ·)`. -/
inductive Value where
  /-- `BoolT` (`spectec/src/il/ast.ml:31`). -/
  | bool (b : Bool)
  /-- `NumT of numtyp` (`spectec/src/il/ast.ml:32`).  The `numtyp` is not
  stored: it is recoverable as `Num.toTyp`. -/
  | num (n : Num)
  /-- `TextT` (`spectec/src/il/ast.ml:33`). -/
  | text (t : Text)
  /-- `TupT of (id * typ) list` (`spectec/src/il/ast.ml:34`).  The binders
  constrain the component *types*, not the shape of the tuple. -/
  | tuple (vs : List Value)
  /-- One injection of a `VariantT of typcase list`
  (`spectec/src/il/ast.ml:41,44`), keyed by the rendered `mixop`. -/
  | case (op : MixopS) (v : Value)
  /-- A `StructT of typfield list` (`spectec/src/il/ast.ml:40,43`), keyed by
  rendered `atom`s.  An association list, not a map: `eval.ml` keeps a record
  in declaration order and matches fields positionally
  (`spectec/src/il/eval.ml:948-949`, with `match_expfield` at
  `spectec/src/il/eval.ml:1072-1074` asserting atom equality; `eval.ml:333` is
  the length assertion in `CompE`, not the match). -/
  | struct (fields : List (AtomS × Value))
  /-- `IterT of typ * (List | List1 | ListN _)`
  (`spectec/src/il/ast.ml:35`, `ast.ml:18-20`). -/
  | list (vs : List Value)
  /-- `IterT of typ * Opt` (`spectec/src/il/ast.ml:35,17`). -/
  | opt (v : Option Value)
  deriving Repr, Inhabited

namespace Value

/-! ### Decidable equality -/

mutual

/-- Structural decision procedure for equality of values.  Hand-written
because `Value` is a nested inductive; the style is `SExp.decEq` in
`Silmaril/SpecTec/SExp/Basic.lean`. -/
def decEq : (a b : Value) → Decidable (a = b)
  | .bool x, .bool y => if h : x = y then .isTrue (by rw [h]) else .isFalse (by simp [h])
  | .num x, .num y => if h : x = y then .isTrue (by rw [h]) else .isFalse (by simp [h])
  | .text x, .text y => if h : x = y then .isTrue (by rw [h]) else .isFalse (by simp [h])
  | .tuple xs, .tuple ys =>
      match decEqList xs ys with
      | .isTrue h => .isTrue (by rw [h])
      | .isFalse h => .isFalse (by simp [h])
  | .case o x, .case o' y =>
      if h : o = o' then
        match decEq x y with
        | .isTrue h' => .isTrue (by rw [h, h'])
        | .isFalse h' => .isFalse (by simp [h'])
      else .isFalse (by simp [h])
  | .struct xs, .struct ys =>
      match decEqFields xs ys with
      | .isTrue h => .isTrue (by rw [h])
      | .isFalse h => .isFalse (by simp [h])
  | .list xs, .list ys =>
      match decEqList xs ys with
      | .isTrue h => .isTrue (by rw [h])
      | .isFalse h => .isFalse (by simp [h])
  | .opt x, .opt y =>
      match decEqOpt x y with
      | .isTrue h => .isTrue (by rw [h])
      | .isFalse h => .isFalse (by simp [h])
  | .bool _, .num _ | .bool _, .text _ | .bool _, .tuple _ | .bool _, .case _ _
  | .bool _, .struct _ | .bool _, .list _ | .bool _, .opt _
  | .num _, .bool _ | .num _, .text _ | .num _, .tuple _ | .num _, .case _ _
  | .num _, .struct _ | .num _, .list _ | .num _, .opt _
  | .text _, .bool _ | .text _, .num _ | .text _, .tuple _ | .text _, .case _ _
  | .text _, .struct _ | .text _, .list _ | .text _, .opt _
  | .tuple _, .bool _ | .tuple _, .num _ | .tuple _, .text _ | .tuple _, .case _ _
  | .tuple _, .struct _ | .tuple _, .list _ | .tuple _, .opt _
  | .case _ _, .bool _ | .case _ _, .num _ | .case _ _, .text _ | .case _ _, .tuple _
  | .case _ _, .struct _ | .case _ _, .list _ | .case _ _, .opt _
  | .struct _, .bool _ | .struct _, .num _ | .struct _, .text _ | .struct _, .tuple _
  | .struct _, .case _ _ | .struct _, .list _ | .struct _, .opt _
  | .list _, .bool _ | .list _, .num _ | .list _, .text _ | .list _, .tuple _
  | .list _, .case _ _ | .list _, .struct _ | .list _, .opt _
  | .opt _, .bool _ | .opt _, .num _ | .opt _, .text _ | .opt _, .tuple _
  | .opt _, .case _ _ | .opt _, .struct _ | .opt _, .list _ => .isFalse (by simp)

/-- `decEq` on a list of values. -/
def decEqList : (a b : List Value) → Decidable (a = b)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (by simp)
  | _ :: _, [] => .isFalse (by simp)
  | x :: xs, y :: ys =>
      match decEq x y with
      | .isTrue h =>
        match decEqList xs ys with
        | .isTrue h' => .isTrue (by rw [h, h'])
        | .isFalse h' => .isFalse (by simp [h'])
      | .isFalse h => .isFalse (by simp [h])

/-- `decEq` on a list of named struct fields. -/
def decEqFields : (a b : List (AtomS × Value)) → Decidable (a = b)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (by simp)
  | _ :: _, [] => .isFalse (by simp)
  | (a, x) :: xs, (b, y) :: ys =>
      if hab : a = b then
        match decEq x y with
        | .isTrue h =>
          match decEqFields xs ys with
          | .isTrue h' => .isTrue (by rw [hab, h, h'])
          | .isFalse h' => .isFalse (by simp [h'])
        | .isFalse h => .isFalse (by simp [h])
      else .isFalse (by simp [hab])

/-- `decEq` on an optional value. -/
def decEqOpt : (a b : Option Value) → Decidable (a = b)
  | none, none => .isTrue rfl
  | none, some _ => .isFalse (by simp)
  | some _, none => .isFalse (by simp)
  | some x, some y =>
      match decEq x y with
      | .isTrue h => .isTrue (by rw [h])
      | .isFalse h => .isFalse (by simp [h])

end

instance : DecidableEq Value := decEq

/-! ### Size

A structural measure, used for the termination arguments of the evaluator and
of anything else that recurses through `Value`. -/

mutual

/-- The number of constructors in a value. -/
def size : Value → Nat
  | .bool _ => 1
  | .num _ => 1
  | .text _ => 1
  | .tuple vs => 1 + sizes vs
  | .case _ v => 1 + size v
  | .struct fs => 1 + sizesFields fs
  | .list vs => 1 + sizes vs
  | .opt none => 1
  | .opt (some v) => 1 + size v

/-- Total `size` of a list of values. -/
def sizes : List Value → Nat
  | [] => 0
  | v :: vs => size v + sizes vs

/-- Total `size` of a list of struct fields. -/
def sizesFields : List (AtomS × Value) → Nat
  | [] => 0
  | f :: fs => size f.2 + sizesFields fs

end

@[simp] theorem size_bool (b : Bool) : size (.bool b) = 1 := rfl
@[simp] theorem size_num (n : Num) : size (.num n) = 1 := rfl
@[simp] theorem size_text (t : Text) : size (.text t) = 1 := rfl
@[simp] theorem size_tuple (vs : List Value) : size (.tuple vs) = 1 + sizes vs := rfl
@[simp] theorem size_case (o : MixopS) (v : Value) : size (.case o v) = 1 + size v := rfl
@[simp] theorem size_struct (fs : List (AtomS × Value)) :
    size (.struct fs) = 1 + sizesFields fs := rfl
@[simp] theorem size_list (vs : List Value) : size (.list vs) = 1 + sizes vs := rfl
@[simp] theorem size_opt_none : size (.opt none) = 1 := rfl
@[simp] theorem size_opt_some (v : Value) : size (.opt (some v)) = 1 + size v := rfl
@[simp] theorem sizes_nil : sizes [] = 0 := rfl
@[simp] theorem sizes_cons (v : Value) (vs : List Value) :
    sizes (v :: vs) = size v + sizes vs := rfl
@[simp] theorem sizesFields_nil : sizesFields [] = 0 := rfl
@[simp] theorem sizesFields_cons (f : AtomS × Value) (fs : List (AtomS × Value)) :
    sizesFields (f :: fs) = size f.2 + sizesFields fs := rfl

/-- Every value has at least one constructor. -/
theorem size_pos : ∀ v : Value, 0 < size v
  | .bool _ | .num _ | .text _ | .opt none => Nat.zero_lt_one
  | .tuple _ | .case _ _ | .struct _ | .list _ | .opt (some _) =>
      Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right _ _)

/-- `sizes` is the sum of the sizes. -/
theorem sizes_eq_sum (vs : List Value) : sizes vs = (vs.map size).sum := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [ih]

/-- `sizesFields` is the sum of the sizes of the field values. -/
theorem sizesFields_eq_sum (fs : List (AtomS × Value)) :
    sizesFields fs = (fs.map (size ·.2)).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [ih]

/-- A member of a list of values is smaller than the list. -/
theorem size_le_sizes {v : Value} {vs : List Value} (h : v ∈ vs) : size v ≤ sizes vs := by
  induction vs with
  | nil => cases h
  | cons w ws ih =>
      rcases List.mem_cons.mp h with rfl | hmem
      · exact Nat.le_add_right _ _
      · exact Nat.le_trans (ih hmem) (Nat.le_add_left _ _)

/-- A field value is no larger than the total size of the record's fields. -/
theorem size_le_sizesFields {f : AtomS × Value} {fs : List (AtomS × Value)}
    (h : f ∈ fs) : size f.2 ≤ sizesFields fs := by
  induction fs with
  | nil => cases h
  | cons g gs ih =>
      rcases List.mem_cons.mp h with rfl | hmem
      · exact Nat.le_add_right _ _
      · exact Nat.le_trans (ih hmem) (Nat.le_add_left _ _)

/-- A member of a `list` is strictly smaller than the `list`. -/
theorem size_lt_of_mem_list {v : Value} {vs : List Value} (h : v ∈ vs) :
    size v < size (.list vs) :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (size_le_sizes h)) (Nat.le_of_eq (Nat.add_comm _ 1))

/-- A member of a `tuple` is strictly smaller than the `tuple`. -/
theorem size_lt_of_mem_tuple {v : Value} {vs : List Value} (h : v ∈ vs) :
    size v < size (.tuple vs) :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (size_le_sizes h)) (Nat.le_of_eq (Nat.add_comm _ 1))

/-- A field value of a `struct` is strictly smaller than the `struct`. -/
theorem size_lt_of_mem_struct {a : AtomS} {v : Value} {fs : List (AtomS × Value)}
    (h : (a, v) ∈ fs) : size v < size (.struct fs) := by
  have hle : size v ≤ sizesFields fs := by
    induction fs with
    | nil => cases h
    | cons f fs ih =>
        rcases List.mem_cons.mp h with rfl | hmem
        · exact Nat.le_add_right _ _
        · exact Nat.le_trans (ih hmem) (Nat.le_add_left _ _)
  simpa [Nat.add_comm] using Nat.lt_succ_of_le hle

/-! ### Projections

Each `asX?` is the partial inverse of one constructor.  `eval.ml` performs the
same tests by matching a reduced expression against `ListE`, `OptE`, `StrE`
and friends (`spectec/src/il/eval.ml:271-357`). -/

/-- The underlying `Bool` of a `bool`. -/
def asBool? : Value → Option Bool
  | .bool b => some b
  | _ => none

/-- The underlying `Num` of a `num`. -/
def asNum? : Value → Option Num
  | .num n => some n
  | _ => none

/-- The underlying `Nat` of a `num (natN _)`.  This is the test `eval.ml`
spells `NumE (`Nat i)` at `spectec/src/il/eval.ml:275,284`: an index, a slice
bound and a length are all `nat`s, and an `int`-typed index does not reduce. -/
def asNat? : Value → Option Nat
  | .num (.natN n) => some n
  | _ => none

/-- The underlying `Int` of a `num (intN _)`.  A `natN` is *not* accepted:
`Xl.Num` keeps `` `Nat `` and `` `Int `` apart and never widens implicitly
(`spectec/src/xl/num.ml:174`); use `Num.cvt .intT` for the coercion. -/
def asInt? : Value → Option Int
  | .num (.intN i) => some i
  | _ => none

/-- The underlying `String` of a `text`. -/
def asText? : Value → Option Text
  | .text t => some t
  | _ => none

/-- The components of a `tuple`. -/
def asTuple? : Value → Option (List Value)
  | .tuple vs => some vs
  | _ => none

/-- The elements of a `list`. -/
def asList? : Value → Option (List Value)
  | .list vs => some vs
  | _ => none

/-- The contents of an `opt`. -/
def asOpt? : Value → Option (Option Value)
  | .opt v => some v
  | _ => none

/-- The fields of a `struct`, in declaration order. -/
def asStruct? : Value → Option (List (AtomS × Value))
  | .struct fs => some fs
  | _ => none

/-- The operator and payload of a `case`. -/
def asCase? : Value → Option (MixopS × Value)
  | .case o v => some (o, v)
  | _ => none

@[simp] theorem asBool?_bool (b : Bool) : asBool? (.bool b) = some b := rfl
@[simp] theorem asNum?_num (n : Num) : asNum? (.num n) = some n := rfl
@[simp] theorem asNat?_num_natN (n : Nat) : asNat? (.num (.natN n)) = some n := rfl
@[simp] theorem asInt?_num_intN (i : Int) : asInt? (.num (.intN i)) = some i := rfl
@[simp] theorem asText?_text (t : Text) : asText? (.text t) = some t := rfl
@[simp] theorem asTuple?_tuple (vs : List Value) : asTuple? (.tuple vs) = some vs := rfl
@[simp] theorem asList?_list (vs : List Value) : asList? (.list vs) = some vs := rfl
@[simp] theorem asOpt?_opt (v : Option Value) : asOpt? (.opt v) = some v := rfl
@[simp] theorem asStruct?_struct (fs : List (AtomS × Value)) :
    asStruct? (.struct fs) = some fs := rfl
@[simp] theorem asCase?_case (o : MixopS) (v : Value) : asCase? (.case o v) = some (o, v) := rfl

@[simp] theorem asBool?_eq_some {v : Value} {b : Bool} :
    asBool? v = some b ↔ v = .bool b := by cases v <;> simp [asBool?, eq_comm]

@[simp] theorem asNum?_eq_some {v : Value} {n : Num} :
    asNum? v = some n ↔ v = .num n := by cases v <;> simp [asNum?, eq_comm]

@[simp] theorem asText?_eq_some {v : Value} {t : Text} :
    asText? v = some t ↔ v = .text t := by cases v <;> simp [asText?, eq_comm]

@[simp] theorem asTuple?_eq_some {v : Value} {vs : List Value} :
    asTuple? v = some vs ↔ v = .tuple vs := by cases v <;> simp [asTuple?, eq_comm]

@[simp] theorem asList?_eq_some {v : Value} {vs : List Value} :
    asList? v = some vs ↔ v = .list vs := by cases v <;> simp [asList?, eq_comm]

@[simp] theorem asOpt?_eq_some {v : Value} {o : Option Value} :
    asOpt? v = some o ↔ v = .opt o := by cases v <;> simp [asOpt?, eq_comm]

@[simp] theorem asStruct?_eq_some {v : Value} {fs : List (AtomS × Value)} :
    asStruct? v = some fs ↔ v = .struct fs := by cases v <;> simp [asStruct?, eq_comm]

@[simp] theorem asCase?_eq_some {v : Value} {o : MixopS} {w : Value} :
    asCase? v = some (o, w) ↔ v = .case o w := by cases v <;> simp [asCase?, eq_comm]

theorem asNat?_eq_some {v : Value} {n : Nat} :
    asNat? v = some n ↔ v = .num (.natN n) := by
  cases v with
  | num m => cases m <;> simp [asNat?, eq_comm]
  | bool _ => simp [asNat?]
  | text _ => simp [asNat?]
  | tuple _ => simp [asNat?]
  | case _ _ => simp [asNat?]
  | struct _ => simp [asNat?]
  | list _ => simp [asNat?]
  | opt _ => simp [asNat?]

theorem asInt?_eq_some {v : Value} {i : Int} :
    asInt? v = some i ↔ v = .num (.intN i) := by
  cases v with
  | num m => cases m <;> simp [asInt?, eq_comm]
  | bool _ => simp [asInt?]
  | text _ => simp [asInt?]
  | tuple _ => simp [asInt?]
  | case _ _ => simp [asInt?]
  | struct _ => simp [asInt?]
  | list _ => simp [asInt?]
  | opt _ => simp [asInt?]

/-! ### Structs

`eval.ml` keeps a record as an association list in declaration order and never
sorts it, so field lookup is a linear scan. -/

/-- Field selection, the value side of `DotE` (`spectec/src/il/eval.ml:316`):
`List.find` on the field atoms, so the *first* field with the given atom wins.
`none` when `v` is not a `struct`, or has no such field — `eval.ml:316` would
raise `Not_found`, and `eval.ml:317` leaves the expression stuck when the
record is not a value. -/
def field? (v : Value) (a : AtomS) : Option Value :=
  match v with
  | .struct fs => (fs.find? (·.1 = a)).map Prod.snd
  | _ => none

/-- Field update, the value side of `DotP` (`spectec/src/il/eval.ml:608-625`),
which is what `UpdE`/`ExtE` with a `DotP` path need.

`eval.ml:613-619` *maps* over the fields rather than looking one up, so **every**
field whose atom is `a` is replaced — in contrast to `field?`, which takes the
first.  Well-formed records have distinct atoms (`typfield`,
`spectec/src/il/ast.ml:43`), so the two agree in practice.

A **missing** field is not an error: every field takes the `else Ok ((atomI, eI),
Checked)` branch of `eval.ml:618` and `eval.ml:623` rebuilds the record
unchanged.  So `setField v a w = some v` when `v` is a record without an `a`
field, which is what this transcribes; it is `field?` that raises on a missing
field (`List.find`, `eval.ml:316`), not `DotP`.

The name has no `?` because `docs/projects/spectec/README.md` asks for `setField`, but
the result is still an `Option`: `eval.ml:624-625` falls through to
`k e' (DotP …)` and gets stuck when `e'` is not a record, which is the one case
answered by `none`. -/
def setField (v : Value) (a : AtomS) (w : Value) : Option Value :=
  match v with
  | .struct fs => some (.struct (fs.map fun f => if f.1 = a then (f.1, w) else f))
  | _ => none

@[simp] theorem field?_struct (fs : List (AtomS × Value)) (a : AtomS) :
    field? (.struct fs) a = (fs.find? (·.1 = a)).map Prod.snd := rfl

@[simp] theorem setField_struct (fs : List (AtomS × Value)) (a : AtomS) (w : Value) :
    setField (.struct fs) a w =
      some (.struct (fs.map fun f => if f.1 = a then (f.1, w) else f)) := rfl

/-- `field?` is `none` off the `struct` constructor. -/
@[simp] theorem field?_eq_none_of_asStruct? {v : Value} {a : AtomS}
    (h : asStruct? v = none) : field? v a = none := by
  cases v <;> simp_all [field?, asStruct?]

/-- `setField` is `none` off the `struct` constructor. -/
@[simp] theorem setField_eq_none_of_asStruct? {v : Value} {a : AtomS} {w : Value}
    (h : asStruct? v = none) : setField v a w = none := by
  cases v <;> simp_all [setField, asStruct?]

/-- Lookup after update returns what was written — provided the field was
there to begin with.  The side condition is necessary: `setField` adds
nothing, so updating an absent field leaves the lookup `none`. -/
theorem field?_setField {v : Value} {a : AtomS} {w u : Value}
    (h : setField v a w = some u) (hv : (field? v a).isSome) : field? u a = some w := by
  cases v with
  | struct fs =>
      simp only [setField, Option.some.injEq] at h
      subst h
      have key : ∀ l : List (AtomS × Value), (∃ x ∈ l, x.1 = a) →
          field? (.struct (l.map fun f => if f.1 = a then (f.1, w) else f)) a = some w := by
        intro l
        induction l with
        | nil => intro hl; simp at hl
        | cons f l ih =>
            intro hl
            by_cases hf : f.1 = a
            · simp [field?, hf]
            · have hl' : ∃ x ∈ l, x.1 = a := by
                obtain ⟨x, hx, hx2⟩ := hl
                rcases List.mem_cons.mp hx with rfl | hmem
                · exact absurd hx2 hf
                · exact ⟨x, hmem, hx2⟩
              simpa [field?, hf] using ih hl'
      refine key fs ?_
      simp only [field?, Option.isSome_map, List.find?_isSome] at hv
      obtain ⟨x, hx, hx2⟩ := hv
      exact ⟨x, hx, by simpa using hx2⟩
  | _ => exact absurd h (by simp [setField])

/-- A record without an `a` field comes back unchanged, which is
`eval.ml:614-623` taking the `else` branch for every field. -/
theorem setField_eq_self_of_field?_eq_none {fs : List (AtomS × Value)} {a : AtomS}
    {w : Value} (h : field? (.struct fs) a = none) :
    setField (.struct fs) a w = some (.struct fs) := by
  simp only [field?, Option.map_eq_none_iff, List.find?_eq_none] at h
  simp only [setField, Option.some.injEq, Value.struct.injEq]
  have key : ∀ l : List (AtomS × Value), (∀ x ∈ l, ¬ x.1 = a) →
      (l.map fun f => if f.1 = a then (f.1, w) else f) = l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons f l ih =>
        intro hl
        have hf : (if f.1 = a then (f.1, w) else f) = f := by
          simp [hl f (List.mem_cons_self ..)]
        simp only [List.map_cons, hf, List.cons.injEq, true_and]
        exact ih fun x hx => hl x (List.mem_cons_of_mem f hx)
  exact key fs fun x hx => by simpa using h x hx

/-! ### Lists

The operations `IdxE`, `SliceE`, `LenE`, `UpdE` and `ExtE` need
(`spectec/src/il/eval.ml:271-305,351-357,571-606`). -/

/-- Indexing, the value side of `IdxE` (`spectec/src/il/eval.ml:271-278`).

`eval.ml:275` guards with `i < List.length es` and `eval.ml:277` turns a
failure into `Error`, so an out-of-range index is `none` rather than a stuck
expression.  That is exactly `List.getElem?`. -/
def idx? (v : Value) (i : Nat) : Option Value :=
  match v with
  | .list vs => vs[i]?
  | _ => none

/-- Element update, the value side of `IdxP` (`spectec/src/il/eval.ml:571-588`).

`eval.ml:577-582` maps over the list replacing the `i`-th element, which is
`List.set`; `eval.ml:583-585` turns an out-of-range index into `Error`. -/
def setIdx (v : Value) (i : Nat) (w : Value) : Option Value :=
  match v with
  | .list vs => if i < vs.length then some (.list (vs.set i w)) else none
  | _ => none

/-- Slicing, the value side of `SliceE` (`spectec/src/il/eval.ml:279-287`):
`n` elements starting at `i`.

Note the bound.  `eval.ml:284` guards with `i + n < List.length es`,
**strictly** less, which rejects every slice that runs to the very end of the
list (in particular `slice? (.list vs) 0 vs.length` and every slice of the
empty list).  That is a defect of the interpreter, not the specification's
reading: the `-oob` siblings of every slicing rule (`load-num-oob`,
`array.new_elem-oob`, …) trap only on `i + n > |es|`, so the strict guard left
the accesses ending at the last element with no step at all.  This port uses
the corrected bound `i + n ≤ |es|` (upstream item U2 of
`docs/projects/spectec/README.md`; whether `Lib.List.take`/`drop`,
`spectec/src/util/lib.ml:9-19`, raise at `i + n = |es|` is still to be checked).  The transcription of the strict guard is kept,
as a documented defect, in `Silmaril.Wasm.SpecTec.Broken.sliceEvalMl?`. -/
def slice? (v : Value) (i n : Nat) : Option Value :=
  match v with
  | .list vs => if i + n ≤ vs.length then some (.list ((vs.drop i).take n)) else none
  | _ => none

/-- Slice update, the value side of `SliceP`
(`spectec/src/il/eval.ml:590-606`): replace the `n` elements starting at `i` by
the elements of `w`.

`eval.ml:596-600` splits the list into `take i`, the slice, and `drop (i + n)`,
applies the continuation to the middle, and concatenates; at the root of an
`UpdE` the continuation returns the replacement outright
(`eval.ml:293-294`).  `w` must be a `list`, because `eval.ml:600` concatenates
with `CatE`, which reduces only on two `ListE`s (`eval.ml:462-463`).
`eval.ml:595` repeats `slice?`'s strict bound; this port uses the same
corrected `i + n ≤ length` (upstream item U2). -/
def setSlice (v : Value) (i n : Nat) (w : Value) : Option Value :=
  match v, w with
  | .list vs, .list ws =>
      if i + n ≤ vs.length then some (.list (vs.take i ++ ws ++ vs.drop (i + n)))
      else none
  | _, _ => none

/-- Length, the value side of `LenE` (`spectec/src/il/eval.ml:351-357`).
Defined on `list` only: `LenE` has no clause for an `opt` or a `struct`. -/
def len? (v : Value) : Option Nat :=
  match v with
  | .list vs => some vs.length
  | _ => none

/-- Concatenation, the value side of `CatE`
(`spectec/src/il/eval.ml:459-467`): list append, and for options the one that
can be read as a union of at most one element.  Two `some`s are `Error`
(`eval.ml:466`), hence `none`. -/
def cat? : Value → Value → Option Value
  | .list a, .list b => some (.list (a ++ b))
  | .opt none, .opt o => some (.opt o)
  | .opt o, .opt none => some (.opt o)
  | _, _ => none

mutual

/-- Composition, the value side of `CompE`
(`spectec/src/il/eval.ml:319-338`).

Three shapes compose.  Lists append (`eval.ml:324`); options behave as in
`cat?` (`eval.ml:325-326`); and two records compose **pointwise**
(`eval.ml:327-336`), field by field, in declaration order.  `eval.ml:330`
asserts the atoms match up and `eval.ml:333` that the records have the same
length, so a mismatch on either is `none` here.  Everything else — including
two `some` options — leaves the expression stuck at `eval.ml:337`, i.e.
`none`. -/
def comp? : Value → Value → Option Value
  | .list a, .list b => some (.list (a ++ b))
  | .opt none, .opt o => some (.opt o)
  | .opt o, .opt none => some (.opt o)
  | .struct f₁, .struct f₂ => (compFields? f₁ f₂).map Value.struct
  | _, _ => none

/-- The pointwise part of `comp?` on records
(`spectec/src/il/eval.ml:329-334`). -/
def compFields? :
    List (AtomS × Value) → List (AtomS × Value) → Option (List (AtomS × Value))
  | [], [] => some []
  | (a₁, v₁) :: f₁, (a₂, v₂) :: f₂ =>
      if a₁ = a₂ then
        match comp? v₁ v₂, compFields? f₁ f₂ with
        | some v, some f => some ((a₁, v) :: f)
        | _, _ => none
      else none
  | _, _ => none

end

@[simp] theorem idx?_list (vs : List Value) (i : Nat) : idx? (.list vs) i = vs[i]? := rfl

@[simp] theorem len?_list (vs : List Value) : len? (.list vs) = some vs.length := rfl

@[simp] theorem cat?_list (a b : List Value) :
    cat? (.list a) (.list b) = some (.list (a ++ b)) := rfl

@[simp] theorem comp?_list (a b : List Value) :
    comp? (.list a) (.list b) = some (.list (a ++ b)) := rfl

@[simp] theorem comp?_opt_none_left (o : Option Value) :
    comp? (.opt none) (.opt o) = some (.opt o) := rfl

@[simp] theorem compFields?_nil : compFields? [] [] = some [] := rfl

/-- Indexing out of range is `none` (`spectec/src/il/eval.ml:275,277`). -/
theorem idx?_eq_none_of_le {vs : List Value} {i : Nat} (h : vs.length ≤ i) :
    idx? (.list vs) i = none := by
  simp [List.getElem?_eq_none h]

/-- A slice that reaches the end of the list is defined (the corrected bound of
`spectec/src/il/eval.ml:284`, upstream item U2): the whole list is a slice of itself. -/
theorem slice?_self (vs : List Value) : slice? (.list vs) 0 vs.length = some (.list vs) := by
  simp [slice?]

/-- `len?` agrees with `List.length`. -/
theorem len?_eq_some {v : Value} {n : Nat} :
    len? v = some n ↔ ∃ vs : List Value, v = .list vs ∧ vs.length = n := by
  cases v <;> simp [len?, eq_comm]

/-! ## Examples

Small `rfl` checks that the projections and the numeric primitives compute. -/

/-- The example record `{A 1, B 2}`. -/
def exStruct : Value :=
  .struct [("A", .num (.natN 1)), ("B", .num (.natN 2))]

/-- The example list `[0, 1, 2, 3]`. -/
def exList : Value :=
  .list [.num (.natN 0), .num (.natN 1), .num (.natN 2), .num (.natN 3)]

example : asNat? (.num (.natN 7)) = some 7 := by rfl
example : asNat? (.num (.intN 7)) = none := by rfl
example : asInt? (.num (.intN (-7))) = some (-7) := by rfl
example : asCase? (.case "CONST" exList) = some ("CONST", exList) := by rfl
example : field? exStruct "B" = some (.num (.natN 2)) := by rfl
example : field? exStruct "C" = none := by rfl
example : setField exStruct "A" (.num (.natN 9))
    = some (.struct [("A", .num (.natN 9)), ("B", .num (.natN 2))]) := by rfl
example : setField exStruct "C" (.num (.natN 9)) = some exStruct := by rfl
example : len? exList = some 4 := by rfl
example : idx? exList 2 = some (.num (.natN 2)) := by rfl
example : idx? exList 4 = none := by rfl
example : slice? exList 1 2 = some (.list [.num (.natN 1), .num (.natN 2)]) := by rfl
example : slice? exList 0 4 = some exList := by rfl
example : slice? exList 1 4 = none := by rfl
example : setIdx exList 0 (.num (.natN 9))
    = some (.list [.num (.natN 9), .num (.natN 1), .num (.natN 2), .num (.natN 3)]) := by rfl
example : setSlice exList 1 2 (.list [.num (.natN 9)])
    = some (.list [.num (.natN 0), .num (.natN 9), .num (.natN 3)]) := by rfl
example : cat? (.opt none) (.opt (some (.bool true))) = some (.opt (some (.bool true))) := by rfl
example : cat? (.opt (some (.bool true))) (.opt (some (.bool false))) = none := by rfl
example : comp? exStruct exStruct = none := by rfl
example : comp? (.struct [("A", .list [.bool true])]) (.struct [("A", .list [.bool false])])
    = some (.struct [("A", .list [.bool true, .bool false])]) := by rfl
example : comp? (.struct [("A", .list [])]) (.struct [("B", .list [])]) = none := by rfl

example : Num.bin .addOp (.natN 2) (.natN 3) = some (.natN 5) := by rfl
example : Num.bin .subOp (.natN 2) (.natN 3) = none := by rfl
example : Num.bin .subOp (.intN 2) (.intN 3) = some (.intN (-1)) := by rfl
example : Num.bin .divOp (.natN 7) (.natN 2) = none := by rfl
example : Num.bin .divOp (.natN 6) (.natN 2) = some (.natN 3) := by rfl
example : Num.bin .divOp (.natN 6) (.natN 0) = none := by rfl
example : Num.bin .modOp (.intN (-7)) (.intN 2) = some (.intN (-1)) := by rfl
example : Num.bin .powOp (.natN 2) (.natN 10) = some (.natN 1024) := by rfl
example : Num.bin .powOp (.ratN 3) (.ratN 0) = some (.ratN 1) := by rfl
-- `Rat`'s `/` does not reduce definitionally, so the negative-exponent case
-- needs `simp` rather than `rfl`.
example : Num.bin .powOp (.ratN 2) (.ratN (-1)) = some (.ratN (1 / 2)) := by
  simp [Num.bin]
  exact fun h => absurd h (by decide)
example : Num.bin .powOp (.ratN 0) (.ratN (-1)) = none := by rfl
example : Num.bin .addOp (.natN 1) (.intN 1) = none := by rfl
example : Num.un .minusOp (.natN 3) = some (.intN (-3)) := by rfl
example : Num.un .notOp (.natN 3) = none := by rfl
example : Num.cmp .ltOp (.natN 1) (.natN 2) = some true := by rfl
example : Num.cmp .eqOp (.natN 1) (.natN 1) = none := by rfl
example : Num.cvt .natT (.intN (-1)) = none := by rfl
example : Num.cvt .natT (.ratN 4) = some (.natN 4) := by rfl
example : Num.cvt .intT (.ratN (mkRat 1 2)) = none := by rfl
example : Num.cvt .realT (.natN 0) = none := by rfl
example : Num.subTyp .natT .ratT = true := by rfl
example : Num.subTyp .ratT .intT = false := by rfl

end Value

/-- An `IL.Arg` after evaluation: the value-level counterpart of `arg'`
(`spectec/src/il/ast.ml:116`).

All four forms occur in the pinned corpus (10639 `ExpA`, 316 `TypA`, 69
`DefA`, 119 `GramA`), so all four are kept:

* `ExpA e` is evaluated, giving `val`.  This is `reduce_arg`'s only
  interesting clause (`eval.ml:635`).
* `TypA t`, `DefA x` and `GramA g` are *not* evaluated — `eval.ml:636-638`
  returns the argument unchanged, noting that "types are reduced on demand" —
  so they are carried through as syntax.  `typ` is recorded and, apart from
  being matched against a `TypP` pattern, is irrelevant to an untyped value
  semantics: `SubE e _ _` denotes the denotation of `e` and `CvtE` depends
  only on the first-order `NumTyp`s it names.  `defName` is *not* inert: a
  `CallE` to a `DefP`-bound identifier has to resolve through the
  environment, which is what `VarEnv.defs` is for.  `gram` is carried for
  `Sem/Grammar.lean`, which is where a `GramD` gets its `EncRel` denotation;
  nothing in this file inspects it beyond matching. -/
inductive ArgV where
  /-- `ExpA e`, evaluated. -/
  | val (v : Value)
  /-- `TypA t`, recorded as syntax. -/
  | typ (t : Typ)
  /-- `DefA x`, the name of a global definition. -/
  | defName (x : IL.Id)
  /-- `GramA g`, recorded as syntax. -/
  | gram (g : Sym)
  deriving Repr, Inhabited

end Silmaril.SpecTec.Sem
