module

public import Silmaril.Wasm.Verify.Reach.Defs

@[expose] public section

/-!
# Guarded calls: the invariant behind "assert is never called with `false`"

An *assertion import* `i` may be called, but only at **guarded call sites**: a `call x` naming
(through the module's function list `fs`) a function in `B` (the host functions of import `i`)
must be immediately preceded, in its instruction sequence, by `i32.const c` with `c ≠ 0`.
`return_call` and `ref.func` must never name a function in `B`, so the assertion is never
called through a reference.

Source level:

* `instrRF i`, `instrCalls i`, `instrBodies i` (structural, kernel-reducible): the function
  indices named by `return_call`/`ref.func`, those named by `call`, and the nested instruction
  sequences of `i`;
* `BadI B fs i`: `i` is a call of a function in `B`; `GdI i`: `i` is `i32.const c`, `c ≠ 0`;
* `Guarded B fs b`: every bad call of the sequence `b` is preceded by a guard;
* `GuardPl G B fs i` (the instruction predicate of the invariant `CfgIn G fs (GuardPl G B fs)`):
  `return_call`/`ref.func` targets in `G`, `call` targets in `G` or `B`, nested sequences
  guarded.

Runtime level (administrative code):

* `isBadA`, `isGdA`, `isExA`: a bad call, a guard, an *exit* (`trap` or `throw_ref`, after which
  the rest of the sequence is discarded, never executed);
* `Chain B fs st code`: the guard discipline as a state machine over a sequence (state `gd`
  after a guard, `ex` after an exit, `other` otherwise; a bad call needs state `gd` or `ex`);
* `DeepP B fs code`: every nested `label`/`handler`/`frame` body satisfies `Chain` from `other`,
  and label continuations hold no bad call.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-! ## Source level -/

mutual

/-- The function indices named by `return_call` and `ref.func`, including nested bodies. -/
def instrRF : Instr → List Nat
  | .returnCall x => [x.toNat]
  | .refFunc x => [x.toNat]
  | .block _ b => exprRF b
  | .loop _ b => exprRF b
  | .tryTable _ _ b => exprRF b
  | .if_ _ b₁ b₂ => exprRF b₁ ++ exprRF b₂
  | _ => []

/-- `instrRF` of a sequence. -/
def exprRF : List Instr → List Nat
  | [] => []
  | i :: is => instrRF i ++ exprRF is

end

mutual

/-- The function indices named by `call`, including nested bodies. -/
def instrCalls : Instr → List Nat
  | .call x => [x.toNat]
  | .block _ b => exprCalls b
  | .loop _ b => exprCalls b
  | .tryTable _ _ b => exprCalls b
  | .if_ _ b₁ b₂ => exprCalls b₁ ++ exprCalls b₂
  | _ => []

/-- `instrCalls` of a sequence. -/
def exprCalls : List Instr → List Nat
  | [] => []
  | i :: is => instrCalls i ++ exprCalls is

end

mutual

/-- The nested instruction sequences of an instruction (recursively). -/
def instrBodies : Instr → List (List Instr)
  | .block _ b => b :: exprBodies b
  | .loop _ b => b :: exprBodies b
  | .tryTable _ _ b => b :: exprBodies b
  | .if_ _ b₁ b₂ => b₁ :: b₂ :: (exprBodies b₁ ++ exprBodies b₂)
  | _ => []

/-- The nested instruction sequences of the instructions of a sequence. -/
def exprBodies : List Instr → List (List Instr)
  | [] => []
  | i :: is => instrBodies i ++ exprBodies is

end

/-- A call of a function in `B`. -/
def BadI (B : Nat → Prop) (fs : List Nat) (i : Instr) : Prop :=
  ∃ (y : FuncIdx) (a : Nat), i = .call y ∧ fs[y.toNat]? = some a ∧ B a

/-- A guard: `i32.const c` with `c ≠ 0`. -/
def GdI (i : Instr) : Prop := ∃ c : BitVec IntType.i32.width, i = .intConst .i32 c ∧ c ≠ 0

/-- Every bad call of the sequence is immediately preceded by a guard. -/
def Guarded (B : Nat → Prop) (fs : List Nat) (b : List Instr) : Prop :=
  ∀ l₁ i l₂, b = l₁ ++ i :: l₂ → BadI B fs i → ∃ j, l₁.getLast? = some j ∧ GdI j

/-- The instruction predicate of the guarded-call invariant. -/
def GuardPl (G B : Nat → Prop) (fs : List Nat) (i : Instr) : Prop :=
  (∀ x ∈ instrRF i, ∀ a, fs[x]? = some a → G a) ∧
    (∀ x ∈ instrCalls i, ∀ a, fs[x]? = some a → G a ∨ B a) ∧
    ∀ b ∈ instrBodies i, Guarded B fs b

/-! ## Runtime level -/

/-- A bad call in administrative code. -/
def isBadA (B : Nat → Prop) (fs : List Nat) : Admin → Prop
  | .plain i => BadI B fs i
  | _ => False

/-- A guard in administrative code. -/
def isGdA : Admin → Bool
  | .plain (.intConst .i32 c) => c != 0
  | _ => false

/-- An exit: the rest of the sequence is discarded, never executed. -/
def isExA : Admin → Bool
  | .trap => true
  | .plain .throwRef => true
  | _ => false

/-- The states of the guard discipline. -/
inductive PSt where
  | other
  | gd
  | ex
  deriving DecidableEq, Repr

/-- The state after an element. -/
def nextSt (x : Admin) (st : PSt) : PSt :=
  if st = .ex || isExA x then .ex else if isGdA x then .gd else .other

/-- The guard discipline over a sequence, from a state. -/
def Chain (B : Nat → Prop) (fs : List Nat) : PSt → List Admin → Prop
  | _, [] => True
  | st, x :: l => (isBadA B fs x → st ≠ .other) ∧ Chain B fs (nextSt x st) l

/-- The nested bodies of administrative code (recursively). -/
def codeBodies : List Admin → List (List Admin)
  | [] => []
  | .label _ _ body :: rest => body :: (codeBodies body ++ codeBodies rest)
  | .handler _ _ body :: rest => body :: (codeBodies body ++ codeBodies rest)
  | .frame _ _ body :: rest => body :: (codeBodies body ++ codeBodies rest)
  | _ :: rest => codeBodies rest

/-- The label continuations of administrative code (recursively). -/
def codeConts : List Admin → List (List Instr)
  | [] => []
  | .label _ cont body :: rest => cont :: (codeConts body ++ codeConts rest)
  | .handler _ _ body :: rest => codeConts body ++ codeConts rest
  | .frame _ _ body :: rest => codeConts body ++ codeConts rest
  | _ :: rest => codeConts rest

/-- Nested bodies follow the guard discipline; continuations hold no bad call. -/
def DeepP (B : Nat → Prop) (fs : List Nat) (code : List Admin) : Prop :=
  (∀ b ∈ codeBodies code, Chain B fs .other b) ∧ ∀ k ∈ codeConts code, ∀ i ∈ k, ¬ BadI B fs i

end Silmaril.Wasm.Verify
