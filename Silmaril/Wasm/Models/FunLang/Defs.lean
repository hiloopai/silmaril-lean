module

public import Silmaril.Wasm.Models.Model.Defs
public import Silmaril.Wasm.Behaviour.Basic

/-!
# FunLang: a small typed functional language

`FunLang` is a first-order, call-by-value functional language with 31-bit integers, booleans,
products and sums. It is the source language of the compiler to the functional-Wasm profile
(`Silmaril.Wasm.Models.FunCompile`).

* `Ty`: `int`, `bool`, `prod`, `sum`; `Ty.Ground`: `int` and `bool`, the types at which programs
  are observed.
* `Tm`: de Bruijn variables, literals, integer arithmetic (`add`, `sub`, `mul`, modulo `2^31`),
  comparisons (`eq`, unsigned `ltu`), `ite`, `let`, pairs and projections, injections and
  `case` (whose branches bind the payload).
* `HasTy Γ e τ`: the typing judgement; `ValTy v τ`: typed values.
* `Tm.depth`: the binder depth (the compiler allocates one Wasm local per binder level).
* `eval ρ e : Option Val`: the big-step semantics, a structural recursion (there is no recursion
  in the language, so every well-typed term evaluates, `Thms.eval_sound`).
* `Prog`: a program is a term in the context `[int]` (one integer argument) with a ground result
  type; `Prog.run p n` evaluates it on `n`; `obsWord` reads a ground value as a 31-bit word
  (`true` is `1`).
* `funModel : WasmModel`: FunLang as a model of the Wasm model graph (`Silmaril.Wasm.Models.Model`).
  Modules and points are programs; validity and the domain are `Prog.Ok`, well-typed and within
  Wasm's local-index limit (`Prog.Fits`); calls are 31-bit arguments; the
  observations of a call are `Behaviour (BitVec 31)`: the program returns `obsWord` of its value.
  Its game reading (`WasmModel.strat`, `WasmModel.ginst`, `WasmModel.toGInst`) places FunLang in
  the game institution `GInst` like every Wasm model.

There is no `λ`: functions and closures (and so `PCF`, which silmaril has as
`Silmaril.Calculi.PCF`) are not covered.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunLang

open Silmaril.Wasm (Behaviour)


/-- FunLang types. -/
inductive Ty where
  /-- 31-bit integers. -/
  | int
  /-- Booleans. -/
  | bool
  /-- Products. -/
  | prod (a b : Ty)
  /-- Sums. -/
  | sum (a b : Ty)
  deriving DecidableEq, Repr

/-- The ground types, at which programs are observed. -/
def Ty.Ground : Ty → Prop
  | .int | .bool => True
  | _ => False

/-- Integer operations, modulo `2^31`. -/
inductive Arith where
  | add
  | sub
  | mul
  deriving DecidableEq, Repr

/-- Integer comparisons: equality and unsigned less-than. -/
inductive Cmp where
  | eq
  | ltu
  deriving DecidableEq, Repr

/-- FunLang terms, with de Bruijn variables (`var 0` is the innermost binder). -/
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
  deriving DecidableEq, Repr

/-- FunLang values. -/
inductive Val where
  | int (n : BitVec 31)
  | bool (b : Bool)
  | pair (a b : Val)
  | inl (v : Val)
  | inr (v : Val)
  deriving DecidableEq, Repr

/-- The meaning of an integer operation. -/
def Arith.eval : Arith → BitVec 31 → BitVec 31 → BitVec 31
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y

/-- The meaning of a comparison. -/
def Cmp.eval : Cmp → BitVec 31 → BitVec 31 → Bool
  | .eq, x, y => decide (x = y)
  | .ltu, x, y => decide (x < y)

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

/-- Typed values. -/
inductive ValTy : Val → Ty → Prop where
  | int (n : BitVec 31) : ValTy (.int n) .int
  | bool (b : Bool) : ValTy (.bool b) .bool
  | pair {a b σ τ} : ValTy a σ → ValTy b τ → ValTy (.pair a b) (.prod σ τ)
  | inl {v σ} (τ : Ty) : ValTy v σ → ValTy (.inl v) (.sum σ τ)
  | inr {v τ} (σ : Ty) : ValTy v τ → ValTy (.inr v) (.sum σ τ)

/-- **The big-step semantics** in the environment `ρ` (`ρ[0]` is the value of `var 0`). -/
def eval (ρ : List Val) : Tm → Option Val
  | .var i => ρ[i]?
  | .int n => some (.int n)
  | .bool b => some (.bool b)
  | .arith op a b =>
      match eval ρ a, eval ρ b with
      | some (.int x), some (.int y) => some (.int (op.eval x y))
      | _, _ => none
  | .cmp op a b =>
      match eval ρ a, eval ρ b with
      | some (.int x), some (.int y) => some (.bool (op.eval x y))
      | _, _ => none
  | .ite c t e =>
      match eval ρ c with
      | some (.bool true) => eval ρ t
      | some (.bool false) => eval ρ e
      | _ => none
  | .let_ a b =>
      match eval ρ a with
      | some v => eval (v :: ρ) b
      | none => none
  | .pair a b =>
      match eval ρ a, eval ρ b with
      | some x, some y => some (.pair x y)
      | _, _ => none
  | .fst e =>
      match eval ρ e with
      | some (.pair x _) => some x
      | _ => none
  | .snd e =>
      match eval ρ e with
      | some (.pair _ y) => some y
      | _ => none
  | .inl e => (eval ρ e).map .inl
  | .inr e => (eval ρ e).map .inr
  | .case e l r =>
      match eval ρ e with
      | some (.inl v) => eval (v :: ρ) l
      | some (.inr v) => eval (v :: ρ) r
      | _ => none

/-- The binder depth of a term: the number of nested `let` and `case` binders. -/
def Tm.depth : Tm → Nat
  | .var _ | .int _ | .bool _ => 0
  | .arith _ a b | .cmp _ a b | .pair a b => max a.depth b.depth
  | .ite c t e => max c.depth (max t.depth e.depth)
  | .let_ a b => max a.depth (b.depth + 1)
  | .fst e | .snd e | .inl e | .inr e => e.depth
  | .case e l r => max e.depth (max l.depth r.depth + 1)

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

/-- A program within Wasm's local-index limit: its binder depth plus two (the argument and its
boxed copy) is below `2^32`. -/
def Prog.Fits (p : Prog) : Prop := p.body.depth + 2 < 2 ^ 32

/-- A program the compiler accepts: well-typed and within the local-index limit. -/
def Prog.Ok (p : Prog) : Prop := p.WellTyped ∧ p.Fits

/-- Run a program on an argument. -/
def Prog.run (p : Prog) (n : BitVec 31) : Option Val := eval [.int n] p.body

/-- The word observed of a ground value (`true` is `1`, `false` is `0`). -/
def obsWord : Val → BitVec 31
  | .int n => n
  | .bool b => if b then 1 else 0
  | _ => 0

/-- The observations of a program on an argument: it returns the word of its value. -/
def Prog.obs (p : Prog) (n : BitVec 31) : Set (Behaviour (BitVec 31)) :=
  {b | ∃ v, p.run n = some v ∧ b = .returns [obsWord v]}

/-- **FunLang as a model** of the Wasm model graph: programs, well-typedness, one 31-bit
argument per call, and the returned word as observation. -/
def funModel : WasmModel where
  feats := micro functional
  Module := Prog
  Valid := Prog.Ok
  Pt := Prog
  Call := BitVec 31
  Obs := Behaviour (BitVec 31)
  obs := Prog.obs
  dom := Prog.Ok

end Silmaril.Wasm.Models.FunLang
