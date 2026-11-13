module

public import Silmaril.Compiler.Core.Verified.Return.Defs

/-! # Folding closed effectful integer expressions

Cerberus elaborates a C operator applied to its operands as effectful glue around pure guards:
`let weak (a, b) = unseq(e₁, e₂) in pure(guard)`, a comparison's effectful `case` over the
operand tuple, a cast `let weak a = e in pure(conv)`. `value file env e = some w` folds such an
expression when it reads no object: its leaves are `pure(p)` that `Fold.eval` folds, glued by
`let weak`/`let strong`, `unseq` and an effectful `case` whose scrutinee folds. It has no
memory actions, no calls of procedures and no control transfers: this is constant folding of a
closed pure integer expression, not an execution of the program. A `case` must hold no call in
any branch, so that every folded expression is a task of an enclosing `unseq`.

`lit file e = some n` when `e` folds to `Specified n` with `n` an `int`; `StateExpr.term` reads
such an expression as the literal `n`, so `x = 6 / 2 - 3`, `(long) 1 << 3` or `-1 < 0xFFFFFFFF`
inside a statement compile to the constant they denote.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ClosedEff

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Fold

abbrev EExp := Expr Codec.wireModel Unit Unit Sym

/-- Whether `e` holds a procedure call, in a branch or a later sequence part too: the syntactic
check of the dynamics (`Dynamics.hasCCall`, equal by `calls_eq`), restated here so the compiler
reads no definition of the dynamics. -/
def calls : EExp → Bool
  | .mk _ e => match e with
    | .ccall .. => true
    | .case_ _ bs => bs.attach.any fun b => calls b.val.2
    | .let_ _ _ e | .bound e | .save _ _ e | .annot _ e => calls e
    | .if_ _ a b | .wseq _ a b | .sseq _ a b => calls a || calls b
    | .unseq es | .nd es => es.attach.any fun e => calls e.val
    | _ => false
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | (rcases b with ⟨⟨p, e⟩, member⟩; have h := List.sizeOf_lt_of_mem member; simp_all; omega)
    | (have h := List.sizeOf_lt_of_mem e.property; simp_all; omega)
    | (simp_all; omega)

theorem calls_eq : (e : EExp) → calls e = Dynamics.hasCCall e
  | .mk a e => by
    rw [calls.eq_def, Dynamics.hasCCall.eq_def]
    cases e with
    | case_ p bs =>
      dsimp only
      congr 1
      funext b
      exact calls_eq b.val.2
    | unseq es =>
      dsimp only
      congr 1
      funext x
      exact calls_eq x.val
    | nd es =>
      dsimp only
      congr 1
      funext x
      exact calls_eq x.val
    | let_ _ _ e => exact calls_eq e
    | bound e => exact calls_eq e
    | save _ _ e => exact calls_eq e
    | annot _ e => exact calls_eq e
    | if_ _ x y => dsimp only; rw [calls_eq x, calls_eq y]
    | wseq _ x y => dsimp only; rw [calls_eq x, calls_eq y]
    | sseq _ x y => dsimp only; rw [calls_eq x, calls_eq y]
    | _ => rfl
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | (rcases b with ⟨⟨p, e⟩, member⟩; have h := List.sizeOf_lt_of_mem member; simp_all; omega)
    | (have h := List.sizeOf_lt_of_mem x.property; simp_all; omega)
    | (simp_all; omega)

mutual
/-- Fold a closed effectful expression in `env`. -/
def value (file : Doc) (env : WEnv) : EExp → Option WVal
  | .mk _ (.pure p) => eval file Return.fuel env p
  | .mk _ (.wseq pat a b) | .mk _ (.sseq pat a b) =>
      match value file env a with
      | some v => match matchP pat v with
        | some xs => value file (extend xs env) b
        | none => none
      | none => none
  | .mk _ (.unseq es) => (values file env es).map .tuple
  | .mk a (.case_ p bs) =>
      if calls (.mk a (.case_ p bs)) then none else
      match eval file Return.fuel env p with
      | some v => branch file env v bs
      | none => none
  | _ => none

/-- Fold each task of an `unseq`. -/
def values (file : Doc) (env : WEnv) : List EExp → Option (List WVal)
  | [] => some []
  | e :: es => match value file env e, values file env es with
    | some w, some ws => some (w :: ws)
    | _, _ => none

/-- The first branch whose pattern matches `v`, folded. -/
def branch (file : Doc) (env : WEnv) (v : WVal) : List (Pattern Sym × EExp) → Option WVal
  | [] => none
  | (p, body) :: rest => match matchP p v with
    | some xs => value file (extend xs env) body
    | none => branch file env v rest
end

/-- A closed expression folding to `Specified n`, `n` an `int`. -/
def lit (file : Doc) (e : EExp) : Option Int :=
  match value file ∅ e with
  | some (.loaded (.specified (.integer n))) =>
      if -2147483648 ≤ n ∧ n ≤ 2147483647 then some n else none
  | _ => none

end Silmaril.Compile.Core.Verified.ClosedEff
