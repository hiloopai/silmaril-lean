module

public import Silmaril.Wasm.Models.FunLang.Defs

/-!
# FunClo: FunLang with first-class closures and recursion

`FunClo` extends FunLang (`Silmaril.Wasm.Models.FunLang`) with recursive first-class functions. It
is a call-by-value functional language: 31-bit integers, booleans, products, sums and
functions. It reuses FunLang's integer operations and comparisons (`Arith`, `Cmp`).

* `Ty`: FunLang's types and the function type `arr σ τ`.
* `Tm`: FunLang's terms, plus `fix b`, a recursive function, and `app f a`. In `fix b` the body
  `b` sees the argument as `var 0`, the function itself as `var 1` and the enclosing variables
  from `var 2` on. A non-recursive `λ` is a `fix` whose body ignores `var 1` (`Tm.lam`).
* `Val`: FunLang's values, plus closures `clo b ρ`: the body of a `fix` and the environment it
  was created in.
* `eval k ρ e : Option Val`: the big-step semantics with **fuel** `k`, decreased at every
  evaluation step. `none` means stuck or out of fuel; `Thms.eval_mono` proves that more fuel
  gives the same result, so `Prog.Eval p n v := ∃ k, eval k [int n] p.body = some v` is a
  deterministic big-step relation.
* `HasTy`: the typing judgement; `ValTy`/`EnvTy`: typed values and environments (a closure is
  typed by a typing of its body in the type of its environment).
* `Tm.fixes d e`: the `fix` subterms of `e` with the binder depth at which they occur, in
  pre-order. `Prog.table p` is the **closure table** of a program. The compiler gives a
  closure the index of its code in this table (`Silmaril.Wasm.Models.FunCloCompile`).
* `funCloModel : WasmModel`: FunClo as a model of the Wasm model graph. Calls are 31-bit
  arguments and the observations of a call are the words returned. A program may diverge, so
  the domain of the model is the accepted programs that terminate on every argument
  (`Prog.Terminates`).

`Tm.ofFun`, `Val.ofFun`: FunLang terms and values as FunClo terms and values
(`Thms.eval_ofFun`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunClo

open Silmaril.Wasm (Behaviour)
open Silmaril.Wasm.Models.FunLang (Arith Cmp)

/-- FunClo types. -/
inductive Ty where
  | int
  | bool
  | prod (a b : Ty)
  | sum (a b : Ty)
  /-- Functions. -/
  | arr (a b : Ty)
  deriving DecidableEq, Repr

/-- The ground types, at which programs are observed. -/
def Ty.Ground : Ty → Prop
  | .int | .bool => True
  | _ => False

/-- FunClo terms, with de Bruijn variables (`var 0` is the innermost binder). -/
inductive Tm where
  | var (i : Nat)
  | int (n : BitVec 31)
  | bool (b : Bool)
  | arith (op : Arith) (a b : Tm)
  | cmp (op : Cmp) (a b : Tm)
  | ite (c t e : Tm)
  /-- `let x = a in b`: `b` sees `a` as `var 0`. -/
  | let_ (a b : Tm)
  | pair (a b : Tm)
  | fst (e : Tm)
  | snd (e : Tm)
  | inl (e : Tm)
  | inr (e : Tm)
  /-- `case e of inl x => l | inr x => r`: the branches see the payload as `var 0`. -/
  | case (e l r : Tm)
  /-- `fix f x. b`: `b` sees the argument `x` as `var 0` and the function `f` as `var 1`. -/
  | fix (b : Tm)
  /-- Application. -/
  | app (f a : Tm)
  deriving DecidableEq, Repr

/-- FunClo values. -/
inductive Val where
  | int (n : BitVec 31)
  | bool (b : Bool)
  | pair (a b : Val)
  | inl (v : Val)
  | inr (v : Val)
  /-- A closure: the body of a `fix` and its environment. -/
  | clo (b : Tm) (ρ : List Val)
  deriving Repr

/-- **The big-step semantics with fuel** `k` in the environment `ρ` (`ρ[0]` is the value of
`var 0`). Every step uses one unit of fuel; `none` is a stuck term or exhausted fuel. -/
def eval : Nat → List Val → Tm → Option Val
  | 0, _, _ => none
  | _ + 1, ρ, .var i => ρ[i]?
  | _ + 1, _, .int n => some (.int n)
  | _ + 1, _, .bool b => some (.bool b)
  | k + 1, ρ, .arith op a b =>
      match eval k ρ a, eval k ρ b with
      | some (.int x), some (.int y) => some (.int (op.eval x y))
      | _, _ => none
  | k + 1, ρ, .cmp op a b =>
      match eval k ρ a, eval k ρ b with
      | some (.int x), some (.int y) => some (.bool (op.eval x y))
      | _, _ => none
  | k + 1, ρ, .ite c t e =>
      match eval k ρ c with
      | some (.bool true) => eval k ρ t
      | some (.bool false) => eval k ρ e
      | _ => none
  | k + 1, ρ, .let_ a b =>
      match eval k ρ a with
      | some v => eval k (v :: ρ) b
      | none => none
  | k + 1, ρ, .pair a b =>
      match eval k ρ a, eval k ρ b with
      | some x, some y => some (.pair x y)
      | _, _ => none
  | k + 1, ρ, .fst e =>
      match eval k ρ e with
      | some (.pair x _) => some x
      | _ => none
  | k + 1, ρ, .snd e =>
      match eval k ρ e with
      | some (.pair _ y) => some y
      | _ => none
  | k + 1, ρ, .inl e => (eval k ρ e).map .inl
  | k + 1, ρ, .inr e => (eval k ρ e).map .inr
  | k + 1, ρ, .case e l r =>
      match eval k ρ e with
      | some (.inl v) => eval k (v :: ρ) l
      | some (.inr v) => eval k (v :: ρ) r
      | _ => none
  | _ + 1, ρ, .fix b => some (.clo b ρ)
  | k + 1, ρ, .app f a =>
      match eval k ρ f, eval k ρ a with
      | some (.clo b ρ'), some u => eval k (u :: .clo b ρ' :: ρ') b
      | _, _ => none

/-- The typing judgement `Γ ⊢ e : τ` (`Γ[0]` is the type of `var 0`). -/
inductive HasTy : List Ty → Tm → Ty → Prop where
  | var {Γ i τ} : Γ[i]? = some τ → HasTy Γ (.var i) τ
  | int {Γ} (n : BitVec 31) : HasTy Γ (.int n) .int
  | bool {Γ} (b : Bool) : HasTy Γ (.bool b) .bool
  | arith {Γ a b} (op : Arith) : HasTy Γ a .int → HasTy Γ b .int → HasTy Γ (.arith op a b) .int
  | cmp {Γ a b} (op : Cmp) : HasTy Γ a .int → HasTy Γ b .int → HasTy Γ (.cmp op a b) .bool
  | ite {Γ c t e τ} : HasTy Γ c .bool → HasTy Γ t τ → HasTy Γ e τ → HasTy Γ (.ite c t e) τ
  | let_ {Γ a b σ τ} : HasTy Γ a σ → HasTy (σ :: Γ) b τ → HasTy Γ (.let_ a b) τ
  | pair {Γ a b σ τ} : HasTy Γ a σ → HasTy Γ b τ → HasTy Γ (.pair a b) (.prod σ τ)
  | fst {Γ e σ τ} : HasTy Γ e (.prod σ τ) → HasTy Γ (.fst e) σ
  | snd {Γ e σ τ} : HasTy Γ e (.prod σ τ) → HasTy Γ (.snd e) τ
  | inl {Γ e σ} (τ : Ty) : HasTy Γ e σ → HasTy Γ (.inl e) (.sum σ τ)
  | inr {Γ e τ} (σ : Ty) : HasTy Γ e τ → HasTy Γ (.inr e) (.sum σ τ)
  | case {Γ e l r σ τ υ} : HasTy Γ e (.sum σ τ) → HasTy (σ :: Γ) l υ → HasTy (τ :: Γ) r υ →
      HasTy Γ (.case e l r) υ
  | fix {Γ b σ τ} : HasTy (σ :: .arr σ τ :: Γ) b τ → HasTy Γ (.fix b) (.arr σ τ)
  | app {Γ f a σ τ} : HasTy Γ f (.arr σ τ) → HasTy Γ a σ → HasTy Γ (.app f a) τ

mutual
/-- Typed values. -/
inductive ValTy : Val → Ty → Prop where
  | int (n : BitVec 31) : ValTy (.int n) .int
  | bool (b : Bool) : ValTy (.bool b) .bool
  | pair {a b σ τ} : ValTy a σ → ValTy b τ → ValTy (.pair a b) (.prod σ τ)
  | inl {v σ} (τ : Ty) : ValTy v σ → ValTy (.inl v) (.sum σ τ)
  | inr {v τ} (σ : Ty) : ValTy v τ → ValTy (.inr v) (.sum σ τ)
  | clo {b ρ Γ σ τ} : EnvTy ρ Γ → HasTy (σ :: .arr σ τ :: Γ) b τ → ValTy (.clo b ρ) (.arr σ τ)

/-- Typed environments. -/
inductive EnvTy : List Val → List Ty → Prop where
  | nil : EnvTy [] []
  | cons {v ρ τ Γ} : ValTy v τ → EnvTy ρ Γ → EnvTy (v :: ρ) (τ :: Γ)
end

/-- The binder depth of a term: the number of nested `let` and `case` binders. A `fix` body
runs in its own frame, so it does not count. -/
def Tm.depth : Tm → Nat
  | .var _ | .int _ | .bool _ | .fix _ => 0
  | .arith _ a b | .cmp _ a b | .pair a b | .app a b => max a.depth b.depth
  | .ite c t e => max c.depth (max t.depth e.depth)
  | .let_ a b => max a.depth (b.depth + 1)
  | .fst e | .snd e | .inl e | .inr e => e.depth
  | .case e l r => max e.depth (max l.depth r.depth + 1)

/-- The `fix` subterms of a term at binder depth `d`, with the depth at which they occur, in
pre-order (a `fix` body is at depth `d + 2`: the enclosing variables, the function, the
argument). -/
def Tm.fixes (d : Nat) : Tm → List (Nat × Tm)
  | .var _ | .int _ | .bool _ => []
  | .arith _ a b | .cmp _ a b | .pair a b | .app a b => a.fixes d ++ b.fixes d
  | .ite c t e => c.fixes d ++ t.fixes d ++ e.fixes d
  | .let_ a b => a.fixes d ++ b.fixes (d + 1)
  | .fst e | .snd e | .inl e | .inr e => e.fixes d
  | .case e l r => e.fixes d ++ l.fixes (d + 1) ++ r.fixes (d + 1)
  | .fix b => (d, b) :: b.fixes (d + 2)

/-- A non-recursive function `λ x. b`: `b` sees `x` as `var 0` and the enclosing variables from
`var 1` on; it becomes a `fix` whose body skips `var 1` (the function itself). -/
def Tm.lift (c : Nat) : Tm → Tm
  | .var i => .var (if i < c then i else i + 1)
  | .int n => .int n
  | .bool b => .bool b
  | .arith op a b => .arith op (a.lift c) (b.lift c)
  | .cmp op a b => .cmp op (a.lift c) (b.lift c)
  | .ite x t e => .ite (x.lift c) (t.lift c) (e.lift c)
  | .let_ a b => .let_ (a.lift c) (b.lift (c + 1))
  | .pair a b => .pair (a.lift c) (b.lift c)
  | .fst e => .fst (e.lift c)
  | .snd e => .snd (e.lift c)
  | .inl e => .inl (e.lift c)
  | .inr e => .inr (e.lift c)
  | .case e l r => .case (e.lift c) (l.lift (c + 1)) (r.lift (c + 1))
  | .fix b => .fix (b.lift (c + 2))
  | .app f a => .app (f.lift c) (a.lift c)

/-- `λ x. b`. -/
def Tm.lam (b : Tm) : Tm := .fix (b.lift 1)

/-! ## FunLang inside FunClo -/

/-- A FunLang term as a FunClo term. -/
def Tm.ofFun : FunLang.Tm → Tm
  | .var i => .var i
  | .int n => .int n
  | .bool b => .bool b
  | .arith op a b => .arith op (Tm.ofFun a) (Tm.ofFun b)
  | .cmp op a b => .cmp op (Tm.ofFun a) (Tm.ofFun b)
  | .ite c t e => .ite (Tm.ofFun c) (Tm.ofFun t) (Tm.ofFun e)
  | .let_ a b => .let_ (Tm.ofFun a) (Tm.ofFun b)
  | .pair a b => .pair (Tm.ofFun a) (Tm.ofFun b)
  | .fst e => .fst (Tm.ofFun e)
  | .snd e => .snd (Tm.ofFun e)
  | .inl e => .inl (Tm.ofFun e)
  | .inr e => .inr (Tm.ofFun e)
  | .case e l r => .case (Tm.ofFun e) (Tm.ofFun l) (Tm.ofFun r)

/-- A FunLang value as a FunClo value. -/
def Val.ofFun : FunLang.Val → Val
  | .int n => .int n
  | .bool b => .bool b
  | .pair a b => .pair (Val.ofFun a) (Val.ofFun b)
  | .inl v => .inl (Val.ofFun v)
  | .inr v => .inr (Val.ofFun v)

/-! ## Programs and their model -/

/-- A program: a term over one integer argument (`var 0`) with a result type. -/
structure Prog where
  /-- The body. -/
  body : Tm
  /-- The result type. -/
  res : Ty
  deriving DecidableEq, Repr

/-- A well-typed program: its body has its result type in `[int]`, which is ground. -/
def Prog.WellTyped (p : Prog) : Prop := HasTy [.int] p.body p.res ∧ p.res.Ground

/-- **The closure table** of a program: its `fix` subterms with their depths (`main` runs the
body at depth `1`). -/
def Prog.table (p : Prog) : List (Nat × Tm) := p.body.fixes 1

/-- The number of `anyref` locals of the compiled `apply` function beyond its two parameters:
enough for the entry of every `fix` of the table (its environment, the function, the argument and
the binders of its body). -/
def tableLocals (L : List (Nat × Tm)) : Nat := (L.map fun x => x.1 + x.2.depth + 1).foldr max 0

/-- A program within Wasm's limits: the locals of `main` and `apply` are below `2^32`, and the
table indices are 31-bit (closures carry their table index as an `i31`). -/
def Prog.Fits (p : Prog) : Prop :=
  p.body.depth + 2 < 2 ^ 32 ∧ tableLocals p.table + 2 ≤ 2 ^ 32 ∧ p.table.length < 2 ^ 31

/-- A program the compiler accepts: well-typed and within Wasm's limits. -/
def Prog.Ok (p : Prog) : Prop := p.WellTyped ∧ p.Fits

/-- The program returns `v` on `n`, with some fuel. -/
def Prog.Eval (p : Prog) (n : BitVec 31) (v : Val) : Prop := ∃ k, eval k [.int n] p.body = some v

/-- The program terminates on every argument. -/
def Prog.Terminates (p : Prog) : Prop := ∀ n, ∃ v, p.Eval n v

/-- The word observed of a ground value (`true` is `1`, `false` is `0`). -/
def obsWord : Val → BitVec 31
  | .int n => n
  | .bool b => if b then 1 else 0
  | _ => 0

/-- The observations of a program on an argument: it returns the word of its value (none if it
does not terminate). -/
def Prog.obs (p : Prog) (n : BitVec 31) : Set (Behaviour (BitVec 31)) :=
  {b | ∃ v, p.Eval n v ∧ b = .returns [obsWord v]}

/-- **FunClo as a model** of the Wasm model graph: programs, one 31-bit argument per call, the
returned word as observation; the domain is the accepted programs that always terminate. -/
def funCloModel : WasmModel where
  feats := micro functional
  Module := Prog
  Valid := Prog.Ok
  Pt := Prog
  Call := BitVec 31
  Obs := Behaviour (BitVec 31)
  obs := Prog.obs
  dom p := p.Ok ∧ p.Terminates

end Silmaril.Wasm.Models.FunClo
