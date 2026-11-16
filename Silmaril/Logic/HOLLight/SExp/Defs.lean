module

public import Silmaril.Logic.HOLLight.Term
public import Silmaril.Logic.Smt.SExpr.Writer.Defs
public import Silmaril.Logic.Concrete.SExp.Defs

/-!
# HOL Light types and terms as S-expressions

A concrete syntax for the abstract syntax of `Silmaril.Logic.HOLLight` (`Ty`, `Const`, `Tm`),
over the S-expressions of `Silmaril.Logic.Smt.SE` and their ASCII reader and writer.

**Grammar.** A numeral `n` is the decimal atom `Nat.repr n` (no sign, no leading zeros;
`Silmaril.Logic.Concrete.SExp.num`).

```
ty ::= bool | ind | (tyvar n) | (-> ty ty) | (tyapp n ty*)
tm ::= (bvar n) | (fvar n ty) | (= ty) | (@ ty) | (const n ty*) | (app tm tm) | (lam ty tm)
```

`(= A)` and `(@ A)` are the equality and choice constants at type `A`, `(const n A*)` a user
constant with its type arguments, `(bvar i)` a de Bruijn index and `(fvar n A)` a free variable
with its type.

**The relation to the abstract syntax.** `e` *denotes* `t` when `encodeTm t = e`. Encoding is
injective (`Thms`: `decodeTm_encodeTm`), so each well-formed S-expression denotes exactly one
term, and every term has exactly one concrete form.

**Decoding.** `decodeTm` accepts exactly the canonical forms. It reads the grammar
(`readTm?`), then keeps the result only when encoding gives back the input. So `decodeTm e = some t`
iff `e` denotes `t` (`Thms`: `decodeTm_eq_some_iff`). Ill-formed input is `none`: an unknown
keyword, a wrong number of arguments, a non-canonical numeral such as `007`.

**Bytes.** `printTm t := render (encodeTm t)`; `parseTm` reads exactly one S-expression and
decodes it. Every atom the encoder emits is legal ASCII, so `parseTm (printTm t) = some t`
(`Thms`: `parseTm_printTm`).
-/

@[expose] public section

namespace Silmaril.Logic.HOLLight.SExp

open Silmaril.Logic.Smt (SE readForms)
open Silmaril.Logic.Smt.SExpr.Writer (render)
open Silmaril.Logic.Concrete.SExp (num num?)

mutual
/-- The concrete form of a type. -/
def encodeTy : Ty → SE
  | .var n => .list [.atom "tyvar", num n]
  | .bool => .atom "bool"
  | .ind => .atom "ind"
  | .arr a b => .list [.atom "->", encodeTy a, encodeTy b]
  | .app k as => .list (.atom "tyapp" :: num k :: encodeTys as)
/-- The concrete forms of a list of types. -/
def encodeTys : List Ty → List SE
  | [] => []
  | a :: as => encodeTy a :: encodeTys as
end

mutual
/-- Read the grammar of types (not yet checked to be canonical). -/
def readTy? : SE → Option Ty
  | .atom "bool" => some .bool
  | .atom "ind" => some .ind
  | .list [.atom "tyvar", n] => (num? n).map .var
  | .list [.atom "->", a, b] => do return .arr (← readTy? a) (← readTy? b)
  | .list (.atom "tyapp" :: k :: as) => do return .app (← num? k) (← readTys? as)
  | _ => none
/-- Read a list of types. -/
def readTys? : List SE → Option (List Ty)
  | [] => some []
  | a :: as => do return (← readTy? a) :: (← readTys? as)
end

/-- The concrete form of a term. -/
def encodeTm : Tm → SE
  | .bvar i => .list [.atom "bvar", num i]
  | .fvar n A => .list [.atom "fvar", num n, encodeTy A]
  | .const (.eq A) => .list [.atom "=", encodeTy A]
  | .const (.select A) => .list [.atom "@", encodeTy A]
  | .const (.user n As) => .list (.atom "const" :: num n :: encodeTys As)
  | .app f x => .list [.atom "app", encodeTm f, encodeTm x]
  | .lam A b => .list [.atom "lam", encodeTy A, encodeTm b]

/-- Read the grammar of terms (not yet checked to be canonical). -/
def readTm? : SE → Option Tm
  | .list [.atom "bvar", i] => (num? i).map .bvar
  | .list [.atom "fvar", n, A] => do return .fvar (← num? n) (← readTy? A)
  | .list [.atom "=", A] => (readTy? A).map fun A => .const (.eq A)
  | .list [.atom "@", A] => (readTy? A).map fun A => .const (.select A)
  | .list (.atom "const" :: n :: As) => do return .const (.user (← num? n) (← readTys? As))
  | .list [.atom "app", f, x] => do return .app (← readTm? f) (← readTm? x)
  | .list [.atom "lam", A, b] => do return .lam (← readTy? A) (← readTm? b)
  | _ => none

/-- **Decode a type**: the type a canonical concrete form denotes. -/
def decodeTy (e : SE) : Option Ty :=
  (readTy? e).bind fun t => if encodeTy t = e then some t else none

/-- **Decode a term**: the term a canonical concrete form denotes. -/
def decodeTm (e : SE) : Option Tm :=
  (readTm? e).bind fun t => if encodeTm t = e then some t else none

/-- `e` denotes the term `t`. -/
def Denotes (e : SE) (t : Tm) : Prop := encodeTm t = e

/-- Print a term as ASCII bytes. -/
def printTm (t : Tm) : List UInt8 := render (encodeTm t)

/-- Parse exactly one S-expression and decode it. -/
def parseTm (bytes : List UInt8) : Option Tm :=
  match readForms bytes with
  | some [e] => decodeTm e
  | _ => none

end Silmaril.Logic.HOLLight.SExp
