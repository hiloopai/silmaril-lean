module

public import Silmaril.Wasm.Logic.Core.Defs

/-! # Straight-line code with `select`, traps told apart from stuck code

`Silmaril.Wasm.Logic.Core.exec` evaluates straight-line integer code; it has no `select`, and its
`none` conflates a trap (a division by zero, an overflowing signed division) with code that is
stuck (a type error, an out-of-range local). This module adds both, without changing `exec`:

* `exec1S`, `execS`: `exec` with the parametric `select` (on any values; the condition is an
  `i32`). On code without `select`, `execS` is `exec` (`execS_eq_exec`);
* `traps1`, `xexec`, `XRes`: a three-way result, `ok` (a final store, frame and stack),
  `trap` (the store and frame at the trapping instruction) or `stuck`. Only an integer binary
  operator whose `intBinOp` is an error counts as a trap;
* `tstep1`, `tsteps`, `StackOk`: a small validator for these instructions over integer types,
  given the types `Γ` of the locals. Typed code in a typed frame is never `stuck`
  (`xexec_ne_stuck`), so there `execS` failing means trapping.

Soundness (`Silmaril.Wasm.Auto.XExec.Thms`): `execS` runs are runs of the small-step semantics;
in the every-run logic (`Wp`), a run that `xexec` computes, ending normally or at a trap, is
the only continuation (both readings, every profile and host).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.XExec

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core

variable {H : Type}

/-- `select` on a top-first stack: pop the `i32` condition `c`, the second value `v₂` and the
first value `v₁`; push `v₁` if `c ≠ 0`, else `v₂`. -/
def selectV (rs : List Val) : Option (List Val) :=
  match popInt .i32 rs with
  | some (c, v₂ :: v₁ :: rs') => some ((if c = 0 then v₂ else v₁) :: rs')
  | _ => none

/-- One instruction of straight-line code, with `select`. -/
def exec1S (s : Store H) (f : Frame) (rs : List Val) : Instr → Option (Store H × Frame × List Val)
  | .select _ => (selectV rs).map fun rs' => (s, f, rs')
  | i => exec1 s f rs i

/-- Straight-line code with `select`. -/
def execS (s : Store H) (f : Frame) (rs : List Val) : List Instr → Option (Store H × Frame × List Val)
  | [] => some (s, f, rs)
  | i :: is =>
    match exec1S s f rs i with
    | some (s₁, f₁, rs₁) => execS s₁ f₁ rs₁ is
    | none => none

/-- The code contains no `select`. -/
def noSelect : List Instr → Bool
  | [] => true
  | .select _ :: _ => false
  | _ :: is => noSelect is

/-! ## Traps -/

/-- The instruction traps on this stack: an integer binary operator on two integers of its
type whose result is an error (division or remainder by zero, `div_s` overflow). -/
def traps1 (rs : List Val) : Instr → Bool
  | .intBinOp t op =>
    match popInt t rs with
    | some (y, rs₁) =>
      match popInt t rs₁ with
      | some (x, _) =>
        match intBinOp t op x y with
        | .error _ => true
        | .ok _ => false
      | none => false
    | none => false
  | _ => false

/-- The result of straight-line code: it ends normally, traps (with the store and frame at
the trap), or is stuck. -/
inductive XRes (H : Type) where
  | ok (s : Store H) (f : Frame) (rs : List Val)
  | trap (s : Store H) (f : Frame)
  | stuck

/-- Straight-line code with `select`, traps told apart from stuck code. -/
def xexec (s : Store H) (f : Frame) (rs : List Val) : List Instr → XRes H
  | [] => .ok s f rs
  | i :: is =>
    match exec1S s f rs i with
    | some (s₁, f₁, rs₁) => xexec s₁ f₁ rs₁ is
    | none => if traps1 rs i then .trap s f else .stuck

/-! ## A validator over integer types -/

/-- One instruction over a top-first stack of integer types, with locals of types `Γ`. -/
def tstep1 (Γ : List IntType) (st : List IntType) : Instr → Option (List IntType)
  | .nop => some st
  | .drop =>
    match st with
    | _ :: st' => some st'
    | [] => none
  | .intConst t _ => some (t :: st)
  | .localGet x => Γ[x.toNat]?.map (· :: st)
  | .localSet x =>
    match st with
    | t :: st' => if Γ[x.toNat]? = some t then some st' else none
    | [] => none
  | .localTee x =>
    match st with
    | t :: st' => if Γ[x.toNat]? = some t then some (t :: st') else none
    | [] => none
  | .intUnOp t _ =>
    match st with
    | t' :: st' => if t' = t then some (t :: st') else none
    | [] => none
  | .intTestOp t _ =>
    match st with
    | t' :: st' => if t' = t then some (.i32 :: st') else none
    | [] => none
  | .intBinOp t _ =>
    match st with
    | t₂ :: t₁ :: st' => if t₁ = t ∧ t₂ = t then some (t :: st') else none
    | _ => none
  | .intRelOp t _ =>
    match st with
    | t₂ :: t₁ :: st' => if t₁ = t ∧ t₂ = t then some (.i32 :: st') else none
    | _ => none
  | .select _ =>
    match st with
    | c :: t₂ :: t₁ :: st' => if c = .i32 ∧ t₁ = t₂ then some (t₁ :: st') else none
    | _ => none
  | _ => none

/-- A sequence of instructions over integer types. -/
def tsteps (Γ : List IntType) (st : List IntType) : List Instr → Option (List IntType)
  | [] => some st
  | i :: is =>
    match tstep1 Γ st i with
    | some st' => tsteps Γ st' is
    | none => none

/-- The top of the stack `rs` holds integers of the types `st` (top first); anything may lie
below. -/
def StackOk : List IntType → List Val → Prop
  | [], _ => True
  | t :: st, v :: rs => (∃ x : BitVec t.width, v = .num ⟨.int t, x⟩) ∧ StackOk st rs
  | _ :: _, [] => False

/-- The frame holds an integer of type `Γ[i]` in each local `i < Γ.length`. -/
def LocalsOk (Γ : List IntType) (f : Frame) : Prop :=
  Γ.length ≤ f.locals.length ∧
    ∀ (i : Nat) (t : IntType), Γ[i]? = some t →
      ∃ x : BitVec t.width, f.locals[i]? = some (some (Val.num ⟨.int t, x⟩))

end Silmaril.Wasm.Auto.XExec
