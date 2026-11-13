module

public import Silmaril.Wasm.Models.FunLang.Defs

/-!
# FunRefClo: first-class recursive closures and references

`FunRefClo` is FunClo (`Silmaril.Wasm.Models.FunClo`, FunLang with recursive first-class closures)
with the ML references of FunRef (`Silmaril.Wasm.Models.FunRef`): `ref e` allocates a cell, `get e`
reads it, `set a b` writes it and returns `true`. Cells may hold closures, so a program can
also recurse through the heap (Landin's knot).

* `Ty`, `Tm`, `Val`: FunClo's, with `ref τ`, `ref`/`get`/`set` and locations `loc l`.
* `eval k σ ρ e : Option (Val × Heap)`: big-step semantics with **fuel** `k` (decreased at every
  step), threading the heap `σ` from left to right. `none` is a stuck term or exhausted fuel.
* `HasTy`; `ValTy Ψ`, `EnvTy Ψ` (mutual) type values and environments under a heap typing `Ψ`;
  `HeapTy Ψ σ`.
* `Tm.fixes`, `Prog.table`, `tableLocals`: the closure table, as for FunClo.
* `funRefCloModel : WasmModel`: FunRefClo as a model of the Wasm model graph, observed at ground
  type, on the accepted programs that terminate on every argument.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunRefClo

open Silmaril.Wasm (Behaviour)
open Silmaril.Wasm.Models.FunLang (Arith Cmp)

/-- FunRefClo types. -/
inductive Ty where
  | int
  | bool
  | prod (a b : Ty)
  | sum (a b : Ty)
  /-- Functions. -/
  | arr (a b : Ty)
  /-- Mutable cells. -/
  | ref (a : Ty)
  deriving DecidableEq, Repr

/-- The ground types, at which programs are observed. -/
def Ty.Ground : Ty → Prop
  | .int | .bool => True
  | _ => False

/-- FunRefClo terms, with de Bruijn variables. -/
inductive Tm where
  | var (i : Nat)
  | int (n : BitVec 31)
  | bool (b : Bool)
  | arith (op : Arith) (a b : Tm)
  | cmp (op : Cmp) (a b : Tm)
  | ite (c t e : Tm)
  | let_ (a b : Tm)
  | pair (a b : Tm)
  | fst (e : Tm)
  | snd (e : Tm)
  | inl (e : Tm)
  | inr (e : Tm)
  | case (e l r : Tm)
  /-- `fix f x. b`: `b` sees `x` as `var 0` and `f` as `var 1`. -/
  | fix (b : Tm)
  | app (f a : Tm)
  /-- Allocate a cell. -/
  | ref (e : Tm)
  /-- Read a cell. -/
  | get (e : Tm)
  /-- Write a cell; the result is `true`. -/
  | set (a b : Tm)
  deriving DecidableEq, Repr

/-- FunRefClo values. -/
inductive Val where
  | int (n : BitVec 31)
  | bool (b : Bool)
  | pair (a b : Val)
  | inl (v : Val)
  | inr (v : Val)
  /-- A closure: the body of a `fix` and its environment. -/
  | clo (b : Tm) (ρ : List Val)
  /-- A location of the heap. -/
  | loc (l : Nat)
  deriving Repr

/-- Heaps: the value of every allocated location. -/
abbrev Heap := List Val

/-- **The big-step semantics with fuel**, left to right, threading the heap. -/
def eval : Nat → Heap → List Val → Tm → Option (Val × Heap)
  | 0, _, _, _ => none
  | _ + 1, σ, ρ, .var i => ρ[i]?.map (·, σ)
  | _ + 1, σ, _, .int n => some (.int n, σ)
  | _ + 1, σ, _, .bool b => some (.bool b, σ)
  | k + 1, σ, ρ, .arith op a b =>
      match eval k σ ρ a with
      | some (.int x, σ₁) =>
        match eval k σ₁ ρ b with
        | some (.int y, σ₂) => some (.int (op.eval x y), σ₂)
        | _ => none
      | _ => none
  | k + 1, σ, ρ, .cmp op a b =>
      match eval k σ ρ a with
      | some (.int x, σ₁) =>
        match eval k σ₁ ρ b with
        | some (.int y, σ₂) => some (.bool (op.eval x y), σ₂)
        | _ => none
      | _ => none
  | k + 1, σ, ρ, .ite c t e =>
      match eval k σ ρ c with
      | some (.bool true, σ₁) => eval k σ₁ ρ t
      | some (.bool false, σ₁) => eval k σ₁ ρ e
      | _ => none
  | k + 1, σ, ρ, .let_ a b =>
      match eval k σ ρ a with
      | some (v, σ₁) => eval k σ₁ (v :: ρ) b
      | none => none
  | k + 1, σ, ρ, .pair a b =>
      match eval k σ ρ a with
      | some (x, σ₁) =>
        match eval k σ₁ ρ b with
        | some (y, σ₂) => some (.pair x y, σ₂)
        | none => none
      | none => none
  | k + 1, σ, ρ, .fst e =>
      match eval k σ ρ e with
      | some (.pair x _, σ₁) => some (x, σ₁)
      | _ => none
  | k + 1, σ, ρ, .snd e =>
      match eval k σ ρ e with
      | some (.pair _ y, σ₁) => some (y, σ₁)
      | _ => none
  | k + 1, σ, ρ, .inl e => (eval k σ ρ e).map fun p => (.inl p.1, p.2)
  | k + 1, σ, ρ, .inr e => (eval k σ ρ e).map fun p => (.inr p.1, p.2)
  | k + 1, σ, ρ, .case e l r =>
      match eval k σ ρ e with
      | some (.inl v, σ₁) => eval k σ₁ (v :: ρ) l
      | some (.inr v, σ₁) => eval k σ₁ (v :: ρ) r
      | _ => none
  | _ + 1, σ, ρ, .fix b => some (.clo b ρ, σ)
  | k + 1, σ, ρ, .app f a =>
      match eval k σ ρ f with
      | some (.clo b ρ', σ₁) =>
        match eval k σ₁ ρ a with
        | some (u, σ₂) => eval k σ₂ (u :: .clo b ρ' :: ρ') b
        | none => none
      | _ => none
  | k + 1, σ, ρ, .ref e =>
      match eval k σ ρ e with
      | some (v, σ₁) => some (.loc σ₁.length, σ₁ ++ [v])
      | none => none
  | k + 1, σ, ρ, .get e =>
      match eval k σ ρ e with
      | some (.loc l, σ₁) => σ₁[l]?.map (·, σ₁)
      | _ => none
  | k + 1, σ, ρ, .set a b =>
      match eval k σ ρ a with
      | some (.loc l, σ₁) =>
        match eval k σ₁ ρ b with
        | some (v, σ₂) => if l < σ₂.length then some (.bool true, σ₂.set l v) else none
        | none => none
      | _ => none

/-- The typing judgement. -/
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
  | ref {Γ e τ} : HasTy Γ e τ → HasTy Γ (.ref e) (.ref τ)
  | get {Γ e τ} : HasTy Γ e (.ref τ) → HasTy Γ (.get e) τ
  | set {Γ a b τ} : HasTy Γ a (.ref τ) → HasTy Γ b τ → HasTy Γ (.set a b) .bool

mutual
/-- Typed values under the heap typing `Ψ`. -/
inductive ValTy (Ψ : List Ty) : Val → Ty → Prop where
  | int (n : BitVec 31) : ValTy Ψ (.int n) .int
  | bool (b : Bool) : ValTy Ψ (.bool b) .bool
  | pair {a b σ τ} : ValTy Ψ a σ → ValTy Ψ b τ → ValTy Ψ (.pair a b) (.prod σ τ)
  | inl {v σ} (τ : Ty) : ValTy Ψ v σ → ValTy Ψ (.inl v) (.sum σ τ)
  | inr {v τ} (σ : Ty) : ValTy Ψ v τ → ValTy Ψ (.inr v) (.sum σ τ)
  | clo {b ρ Γ σ τ} : EnvTy Ψ ρ Γ → HasTy (σ :: .arr σ τ :: Γ) b τ →
      ValTy Ψ (.clo b ρ) (.arr σ τ)
  | loc {l τ} : Ψ[l]? = some τ → ValTy Ψ (.loc l) (.ref τ)

/-- Typed environments under the heap typing `Ψ`. -/
inductive EnvTy (Ψ : List Ty) : List Val → List Ty → Prop where
  | nil : EnvTy Ψ [] []
  | cons {v ρ τ Γ} : ValTy Ψ v τ → EnvTy Ψ ρ Γ → EnvTy Ψ (v :: ρ) (τ :: Γ)
end

/-- A typed heap. -/
def HeapTy (Ψ : List Ty) (σ : Heap) : Prop := List.Forall₂ (ValTy Ψ) σ Ψ

/-- The binder depth of a term (`fix` bodies run in `apply`'s frame). -/
def Tm.depth : Tm → Nat
  | .var _ | .int _ | .bool _ | .fix _ => 0
  | .arith _ a b | .cmp _ a b | .pair a b | .app a b | .set a b => max a.depth b.depth
  | .ite c t e => max c.depth (max t.depth e.depth)
  | .let_ a b => max a.depth (b.depth + 1)
  | .fst e | .snd e | .inl e | .inr e | .ref e | .get e => e.depth
  | .case e l r => max e.depth (max l.depth r.depth + 1)

/-- The `fix` subterms of a term at binder depth `d`, with their depths, in pre-order. -/
def Tm.fixes (d : Nat) : Tm → List (Nat × Tm)
  | .var _ | .int _ | .bool _ => []
  | .arith _ a b | .cmp _ a b | .pair a b | .app a b | .set a b => a.fixes d ++ b.fixes d
  | .ite c t e => c.fixes d ++ t.fixes d ++ e.fixes d
  | .let_ a b => a.fixes d ++ b.fixes (d + 1)
  | .fst e | .snd e | .inl e | .inr e | .ref e | .get e => e.fixes d
  | .case e l r => e.fixes d ++ l.fixes (d + 1) ++ r.fixes (d + 1)
  | .fix b => (d, b) :: b.fixes (d + 2)

/-! ## Programs and their model -/

/-- A program: a term over one integer argument with a result type. -/
structure Prog where
  body : Tm
  res : Ty
  deriving DecidableEq, Repr

/-- A well-typed program. -/
def Prog.WellTyped (p : Prog) : Prop := HasTy [.int] p.body p.res ∧ p.res.Ground

/-- The closure table of a program. -/
def Prog.table (p : Prog) : List (Nat × Tm) := p.body.fixes 1

/-- The `anyref` locals of `apply` beyond its parameters. -/
def tableLocals (L : List (Nat × Tm)) : Nat := (L.map fun x => x.1 + x.2.depth + 1).foldr max 0

/-- A program within Wasm's limits. -/
def Prog.Fits (p : Prog) : Prop :=
  p.body.depth + 2 < 2 ^ 32 ∧ tableLocals p.table + 2 ≤ 2 ^ 32 ∧ p.table.length < 2 ^ 31

/-- A program the compiler accepts. -/
def Prog.Ok (p : Prog) : Prop := p.WellTyped ∧ p.Fits

/-- The program returns `v` on `n`, from the empty heap, with some fuel. -/
def Prog.Eval (p : Prog) (n : BitVec 31) (v : Val) : Prop :=
  ∃ k σ, eval k [] [.int n] p.body = some (v, σ)

/-- The program terminates on every argument. -/
def Prog.Terminates (p : Prog) : Prop := ∀ n, ∃ v, p.Eval n v

/-- The word observed of a ground value. -/
def obsWord : Val → BitVec 31
  | .int n => n
  | .bool b => if b then 1 else 0
  | _ => 0

/-- The observations of a program on an argument. -/
def Prog.obs (p : Prog) (n : BitVec 31) : Set (Behaviour (BitVec 31)) :=
  {b | ∃ v, p.Eval n v ∧ b = .returns [obsWord v]}

/-- **FunRefClo as a model** of the Wasm model graph, on the accepted programs that always
terminate. -/
def funRefCloModel : WasmModel where
  feats := micro functionalMutGC
  Module := Prog
  Valid := Prog.Ok
  Pt := Prog
  Call := BitVec 31
  Obs := Behaviour (BitVec 31)
  obs := Prog.obs
  dom p := p.Ok ∧ p.Terminates

end Silmaril.Wasm.Models.FunRefClo
