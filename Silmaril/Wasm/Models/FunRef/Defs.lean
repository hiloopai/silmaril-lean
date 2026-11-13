module

public import Silmaril.Wasm.Models.FunLang.Defs

/-!
# FunRef: FunLang with mutable references

`FunRef` extends the first-order functional language `FunLang` (`Silmaril.Wasm.Models.FunLang`) with
ML-style references: `ref e` allocates a cell holding the value of `e`, `get e` reads a cell and
`set a b` writes the value of `b` into the cell `a` (and returns `true`, as there is no unit
type). It is the source language of the compiler to the mutable-GC functional profile
(`Silmaril.Wasm.Models.FunRefCompile`).

* `Ty`, `Tm`, `Val` as in FunLang (the integer operations and comparisons are FunLang's), with
  `ref τ`, the three operations and locations `loc ℓ`;
* `eval σ ρ e : Option (Val × Heap)`: big-step, left to right, threading the heap `σ`
  (a list of values; a new cell is at the end);
* `HasTy`, `ValTy Ψ` and `HeapTy Ψ σ`: typing, with a heap typing `Ψ` for locations;
* `Prog`, `Prog.Ok`, `Prog.run` (from the empty heap), `obsWord`, `Prog.obs` and the model
  `funRefModel` as for FunLang: programs are observed at ground type, so the heap is not
  observable.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunRef

open Silmaril.Wasm (Behaviour)
open Silmaril.Wasm.Models.FunLang (Arith Cmp)

/-- FunRef types. -/
inductive Ty where
  | int
  | bool
  | prod (a b : Ty)
  | sum (a b : Ty)
  /-- Mutable cells holding a value of the type. -/
  | ref (a : Ty)
  deriving DecidableEq, Repr

/-- The ground types, at which programs are observed. -/
def Ty.Ground : Ty → Prop
  | .int | .bool => True
  | _ => False

/-- FunRef terms, with de Bruijn variables. -/
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
  /-- Allocate a cell. -/
  | ref (e : Tm)
  /-- Read a cell. -/
  | get (e : Tm)
  /-- Write a cell; the result is `true`. -/
  | set (a b : Tm)
  deriving DecidableEq, Repr

/-- FunRef values. -/
inductive Val where
  | int (n : BitVec 31)
  | bool (b : Bool)
  | pair (a b : Val)
  | inl (v : Val)
  | inr (v : Val)
  /-- A location of the heap. -/
  | loc (l : Nat)
  deriving DecidableEq, Repr

/-- Heaps: the value of every allocated location. -/
abbrev Heap := List Val

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
  | ref {Γ e τ} : HasTy Γ e τ → HasTy Γ (.ref e) (.ref τ)
  | get {Γ e τ} : HasTy Γ e (.ref τ) → HasTy Γ (.get e) τ
  | set {Γ a b τ} : HasTy Γ a (.ref τ) → HasTy Γ b τ → HasTy Γ (.set a b) .bool

/-- Typed values, under a heap typing `Ψ` (`Ψ[ℓ]` is the type of the contents of `ℓ`). -/
inductive ValTy (Ψ : List Ty) : Val → Ty → Prop where
  | int (n : BitVec 31) : ValTy Ψ (.int n) .int
  | bool (b : Bool) : ValTy Ψ (.bool b) .bool
  | pair {a b σ τ} : ValTy Ψ a σ → ValTy Ψ b τ → ValTy Ψ (.pair a b) (.prod σ τ)
  | inl {v σ} (τ : Ty) : ValTy Ψ v σ → ValTy Ψ (.inl v) (.sum σ τ)
  | inr {v τ} (σ : Ty) : ValTy Ψ v τ → ValTy Ψ (.inr v) (.sum σ τ)
  | loc {l τ} : Ψ[l]? = some τ → ValTy Ψ (.loc l) (.ref τ)

/-- A typed heap. -/
def HeapTy (Ψ : List Ty) (σ : Heap) : Prop := List.Forall₂ (ValTy Ψ) σ Ψ

/-- **The big-step semantics**, left to right, threading the heap. -/
def eval (σ : Heap) (ρ : List Val) : Tm → Option (Val × Heap)
  | .var i => ρ[i]?.map (·, σ)
  | .int n => some (.int n, σ)
  | .bool b => some (.bool b, σ)
  | .arith op a b =>
      match eval σ ρ a with
      | some (.int x, σ₁) =>
        match eval σ₁ ρ b with
        | some (.int y, σ₂) => some (.int (op.eval x y), σ₂)
        | _ => none
      | _ => none
  | .cmp op a b =>
      match eval σ ρ a with
      | some (.int x, σ₁) =>
        match eval σ₁ ρ b with
        | some (.int y, σ₂) => some (.bool (op.eval x y), σ₂)
        | _ => none
      | _ => none
  | .ite c t e =>
      match eval σ ρ c with
      | some (.bool true, σ₁) => eval σ₁ ρ t
      | some (.bool false, σ₁) => eval σ₁ ρ e
      | _ => none
  | .let_ a b =>
      match eval σ ρ a with
      | some (v, σ₁) => eval σ₁ (v :: ρ) b
      | none => none
  | .pair a b =>
      match eval σ ρ a with
      | some (x, σ₁) =>
        match eval σ₁ ρ b with
        | some (y, σ₂) => some (.pair x y, σ₂)
        | none => none
      | none => none
  | .fst e =>
      match eval σ ρ e with
      | some (.pair x _, σ₁) => some (x, σ₁)
      | _ => none
  | .snd e =>
      match eval σ ρ e with
      | some (.pair _ y, σ₁) => some (y, σ₁)
      | _ => none
  | .inl e => (eval σ ρ e).map fun p => (.inl p.1, p.2)
  | .inr e => (eval σ ρ e).map fun p => (.inr p.1, p.2)
  | .case e l r =>
      match eval σ ρ e with
      | some (.inl v, σ₁) => eval σ₁ (v :: ρ) l
      | some (.inr v, σ₁) => eval σ₁ (v :: ρ) r
      | _ => none
  | .ref e =>
      match eval σ ρ e with
      | some (v, σ₁) => some (.loc σ₁.length, σ₁ ++ [v])
      | none => none
  | .get e =>
      match eval σ ρ e with
      | some (.loc l, σ₁) => σ₁[l]?.map (·, σ₁)
      | _ => none
  | .set a b =>
      match eval σ ρ a with
      | some (.loc l, σ₁) =>
        match eval σ₁ ρ b with
        | some (v, σ₂) => if l < σ₂.length then some (.bool true, σ₂.set l v) else none
        | none => none
      | _ => none

/-- The binder depth of a term (`set` needs no local). -/
def Tm.depth : Tm → Nat
  | .var _ | .int _ | .bool _ => 0
  | .arith _ a b | .cmp _ a b | .pair a b | .set a b => max a.depth b.depth
  | .ite c t e => max c.depth (max t.depth e.depth)
  | .let_ a b => max a.depth (b.depth + 1)
  | .fst e | .snd e | .inl e | .inr e | .ref e | .get e => e.depth
  | .case e l r => max e.depth (max l.depth r.depth + 1)

/-! ## Programs and their model -/

/-- A program: a term over one integer argument with a result type. -/
structure Prog where
  body : Tm
  res : Ty
  deriving DecidableEq, Repr

def Prog.WellTyped (p : Prog) : Prop := HasTy [.int] p.body p.res ∧ p.res.Ground

def Prog.Fits (p : Prog) : Prop := p.body.depth + 2 < 2 ^ 32

/-- A program the compiler accepts. -/
def Prog.Ok (p : Prog) : Prop := p.WellTyped ∧ p.Fits

/-- Run a program on an argument, from the empty heap. -/
def Prog.run (p : Prog) (n : BitVec 31) : Option (Val × Heap) := eval [] [.int n] p.body

def obsWord : Val → BitVec 31
  | .int n => n
  | .bool b => if b then 1 else 0
  | _ => 0

/-- The observations of a program: it returns the word of its value. -/
def Prog.obs (p : Prog) (n : BitVec 31) : Set (Behaviour (BitVec 31)) :=
  {b | ∃ v σ, p.run n = some (v, σ) ∧ b = .returns [obsWord v]}

/-- **FunRef as a model** of the Wasm model graph. -/
def funRefModel : WasmModel where
  feats := micro functionalMutGC
  Module := Prog
  Valid := Prog.Ok
  Pt := Prog
  Call := BitVec 31
  Obs := Behaviour (BitVec 31)
  obs := Prog.obs
  dom := Prog.Ok

end Silmaril.Wasm.Models.FunRef
