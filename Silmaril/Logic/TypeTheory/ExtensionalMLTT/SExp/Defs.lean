module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Defs
public import Silmaril.Logic.Concrete.SExp.Defs

/-!
# Extensional MLTT terms, contexts and judgments as S-expressions

A concrete syntax for the abstract syntax of extensional MLTT (`ETm k`, terms with `k` bound
variables in scope; `ECtx`; `EJdg`, the judgments `Γ ⊢ a ≡ b : A`), over the S-expressions of
`Silmaril.Logic.Smt.SE`.

**Grammar.** `n` is a canonical numeral (`Silmaril.Logic.Concrete.SExp.num`), `x` an atom.

```
tm  ::= (fv x) | (bv n) | (univ n) | empty | unit | star | nat | zero | (succ tm)
      | (natrec tm tm tm tm) | (pi tm tm) | (sigma tm tm) | (lam tm tm) | (app tm tm)
      | (pair tm tm) | (fst tm) | (snd tm) | (id tm tm tm) | (refl tm) | (absurd tm tm)
ctx ::= (ctx (x tm)*)              -- oldest declaration first
jdg ::= (jdg ctx tm tm tm)         -- (jdg Γ A a b) is Γ ⊢ a ≡ b : A
```

`natrec C s z n`, `pi A B`, `sigma A B` and `lam A b` bind one variable in their first,
second, second and second argument (the motive `C` and step `s` of `natrec`, the codomain `B`, the
body `b`): those arguments are read with one more variable in scope. A bound variable `(bv i)` is
well formed only when `i` is below the number of variables in scope.

**The relation to the abstract syntax.** `e` *denotes* the judgment `J` when `encodeJdg J = e`.
Encoding is injective, and `decodeJdg` accepts exactly the canonical forms (`Thms`).

**Names.** A free variable `x` (`fv x`, or a context declaration) is the atom `x`. At the level of
S-expressions every name round-trips. The ASCII reader accepts only *legal* atoms: non-empty, no
whitespace, no `(`, `)`, `;`, `"` or `|`, ASCII only. So the byte round trip
`parseJdg (printJdg J) = some J` holds exactly for the judgments whose names are legal
(`LegalNames`, `Thms`). Every judgment that `parseJdg` returns has legal names.
-/

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp

open Silmaril.Logic.Smt (SE readForms)
open Silmaril.Logic.Smt.SExpr.Writer (render LegalAtom)
open Silmaril.Logic.Concrete.SExp (num num?)

/-- The concrete form of a term with `k` variables in scope. -/
def encodeTm : {k : ℕ} → ETm k → SE
  | _, .fv x => .list [.atom "fv", .atom x]
  | _, .bv i => .list [.atom "bv", num i.val]
  | _, .univ n => .list [.atom "univ", num n]
  | _, .empty => .atom "empty"
  | _, .unit => .atom "unit"
  | _, .star => .atom "star"
  | _, .nats => .atom "nat"
  | _, .zero => .atom "zero"
  | _, .succ n => .list [.atom "succ", encodeTm n]
  | _, .natrec C s z n => .list [.atom "natrec", encodeTm C, encodeTm s, encodeTm z, encodeTm n]
  | _, .pi A B => .list [.atom "pi", encodeTm A, encodeTm B]
  | _, .sigma A B => .list [.atom "sigma", encodeTm A, encodeTm B]
  | _, .abs A b => .list [.atom "lam", encodeTm A, encodeTm b]
  | _, .app f a => .list [.atom "app", encodeTm f, encodeTm a]
  | _, .pair a b => .list [.atom "pair", encodeTm a, encodeTm b]
  | _, .fst p => .list [.atom "fst", encodeTm p]
  | _, .snd p => .list [.atom "snd", encodeTm p]
  | _, .id A a b => .list [.atom "id", encodeTm A, encodeTm a, encodeTm b]
  | _, .refl a => .list [.atom "refl", encodeTm a]
  | _, .absurd C e => .list [.atom "absurd", encodeTm C, encodeTm e]

/-- Read the grammar of terms with `k` variables in scope (not yet checked to be canonical). -/
def readTm? : (k : ℕ) → SE → Option (ETm k)
  | _, .list [.atom "fv", .atom x] => some (.fv x)
  | k, .list [.atom "bv", i] => (num? i).bind fun n => if h : n < k then some (.bv ⟨n, h⟩) else none
  | _, .list [.atom "univ", n] => (num? n).map .univ
  | _, .atom "empty" => some .empty
  | _, .atom "unit" => some .unit
  | _, .atom "star" => some .star
  | _, .atom "nat" => some .nats
  | _, .atom "zero" => some .zero
  | k, .list [.atom "succ", n] => (readTm? k n).map .succ
  | k, .list [.atom "natrec", C, s, z, n] =>
      do return .natrec (← readTm? (k + 1) C) (← readTm? (k + 1) s) (← readTm? k z) (← readTm? k n)
  | k, .list [.atom "pi", A, B] => do return .pi (← readTm? k A) (← readTm? (k + 1) B)
  | k, .list [.atom "sigma", A, B] => do return .sigma (← readTm? k A) (← readTm? (k + 1) B)
  | k, .list [.atom "lam", A, b] => do return .abs (← readTm? k A) (← readTm? (k + 1) b)
  | k, .list [.atom "app", f, a] => do return .app (← readTm? k f) (← readTm? k a)
  | k, .list [.atom "pair", a, b] => do return .pair (← readTm? k a) (← readTm? k b)
  | k, .list [.atom "fst", p] => (readTm? k p).map .fst
  | k, .list [.atom "snd", p] => (readTm? k p).map .snd
  | k, .list [.atom "id", A, a, b] => do return .id (← readTm? k A) (← readTm? k a) (← readTm? k b)
  | k, .list [.atom "refl", a] => (readTm? k a).map .refl
  | k, .list [.atom "absurd", C, e] => do return .absurd (← readTm? k C) (← readTm? k e)
  | _, _ => none

/-- The declarations of a context, oldest first. -/
def ctxDecls : ECtx → List (String × ETm 0)
  | .nil => []
  | .cons Γ x A => ctxDecls Γ ++ [(x, A)]

/-- The context of declarations given oldest first. -/
def ctxOfDecls (ds : List (String × ETm 0)) : ECtx :=
  ds.foldl (fun Γ d => .cons Γ d.1 d.2) .nil

/-- The concrete form of a context. -/
def encodeCtx (Γ : ECtx) : SE :=
  .list (.atom "ctx" :: (ctxDecls Γ).map fun d => .list [.atom d.1, encodeTm d.2])

/-- Read the declarations of a context. -/
def readDecls? : List SE → Option (List (String × ETm 0))
  | [] => some []
  | .list [.atom x, A] :: ds => do return (x, ← readTm? 0 A) :: (← readDecls? ds)
  | _ => none

/-- Read the grammar of contexts. -/
def readCtx? : SE → Option ECtx
  | .list (.atom "ctx" :: ds) => (readDecls? ds).map ctxOfDecls
  | _ => none

/-- The concrete form of a judgment `Γ ⊢ a ≡ b : A`: `(jdg Γ A a b)`. -/
def encodeJdg (J : EJdg) : SE :=
  .list [.atom "jdg", encodeCtx J.Γ, encodeTm J.A, encodeTm J.a, encodeTm J.b]

/-- Read the grammar of judgments (not yet checked to be canonical). -/
def readJdg? : SE → Option EJdg
  | .list [.atom "jdg", Γ, A, a, b] =>
      do return ⟨← readCtx? Γ, ← readTm? 0 A, ← readTm? 0 a, ← readTm? 0 b⟩
  | _ => none

/-- **Decode a judgment**: the judgment a canonical concrete form denotes. -/
def decodeJdg (e : SE) : Option EJdg :=
  (readJdg? e).bind fun J => if encodeJdg J = e then some J else none

/-- `e` denotes the judgment `J`. -/
def Denotes (e : SE) (J : EJdg) : Prop := encodeJdg J = e

/-- The free-variable names of a term. -/
def names : {k : ℕ} → ETm k → List String
  | _, .fv x => [x]
  | _, .bv _ | _, .univ _ | _, .empty | _, .unit | _, .star | _, .nats | _, .zero => []
  | _, .succ n | _, .fst n | _, .snd n | _, .refl n => names n
  | _, .natrec C s z n => names C ++ names s ++ names z ++ names n
  | _, .pi A B | _, .sigma A B | _, .abs A B | _, .app A B | _, .pair A B | _, .absurd A B =>
      names A ++ names B
  | _, .id A a b => names A ++ names a ++ names b

/-- Every name of a judgment (in its context, its type and its terms) is a legal atom. -/
def LegalNames (J : EJdg) : Prop :=
  ∀ x ∈ (ctxDecls J.Γ).flatMap (fun d => d.1 :: names d.2) ++ names J.A ++ names J.a ++ names J.b,
    LegalAtom x

/-- Print a judgment as ASCII bytes. -/
def printJdg (J : EJdg) : List UInt8 := render (encodeJdg J)

/-- Parse exactly one S-expression and decode it as a judgment. -/
def parseJdg (bytes : List UInt8) : Option EJdg :=
  match readForms bytes with
  | some [e] => decodeJdg e
  | _ => none

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp
