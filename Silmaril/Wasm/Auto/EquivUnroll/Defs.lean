module

public import Silmaril.Wasm.Auto.Equiv.Thms

/-!
# Loop unrolling by symbolic execution: definitions

An extension of the symbolic executor of `Silmaril.Wasm.Auto.Equiv` through `do … while` loops
whose trip count the simplifier decides:

* `xsexecU fuel mem S code`: `xstep` on every instruction except `loop .empty (body ++ [br_if 0])`
  entered with an empty operand stack, which is **unrolled**: the straight-line `body` runs
  symbolically, its top value must simplify (`canon`) to a constant, and the loop either exits
  (constant `0`: the values below the condition stay on the stack) or runs again (any other
  constant: the stack is emptied, as the branch to the loop's label does). At most `fuel`
  instructions and iterations in all; otherwise, or if the condition is not a constant, `none` (verdict unknown).
* `checkXU fuel lt st gt mem a b`: `checkX` on the unrolled runs (equal guards with their trap
  states, equal final locals, globals, memory and stack).

* `SegEquivXN`: `SegEquivX` for values below the segment that do not end in a function reference
  (`Equiv.NoFuncTop`, as in `CEquiv`): the label rule's converse needs it.

Soundness: `wp_xsexecU`, `segEquivXN_of_checkXU` (`Silmaril.Wasm.Auto.EquivUnroll.Thms`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivUnroll

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv

/-- The body of a `do … while` loop: `body ++ [br_if 0]`. -/
def whileBody? (b : List Instr) : Option (List Instr) :=
  match b.getLast? with
  | some (.brIf l) => if l.toNat = 0 then some b.dropLast else none
  | _ => none

/-- The constant a simplified `i32` condition denotes. -/
def condConst? (e : XT) : Option Nat :=
  match canon .i32 e with
  | .const k => some (k % 2 ^ 32)
  | _ => none

/-- **Symbolic execution with loop unrolling** (`fuel` bounds the instructions and iterations). -/
def xsexecU (mem : Bool) : Nat → XState → List Instr → Option XState
  | _, S, [] => some S
  | 0, _, _ :: _ => none
  | f + 1, S, i :: is =>
    match i with
    | .loop .empty b =>
      match S.stack, whileBody? b with
      | [], some body =>
        match xsexec mem S body with
        | some S₁ =>
          match S₁.stack with
          | (.i32, e) :: st' =>
            match condConst? e with
            | some 0 => xsexecU mem f { S₁ with stack := st' } is
            | some (_ + 1) => xsexecU mem f { S₁ with stack := [] } (i :: is)
            | none => none
          | _ => none
        | none => none
      | _, _ => none
    | _ =>
      match xstep mem S i with
      | some S' => xsexecU mem f S' is
      | none => none

/-- **The equivalence check with loop unrolling.** -/
def checkXU (fuel : Nat) (lt st gt : List IntType) (mem : Bool) (a b : List Instr) : Bool :=
  match xsexecU mem fuel (initX lt st gt) a, xsexecU mem fuel (initX lt st gt) b with
  | some A, some B =>
    decide (guardKeys A = guardKeys B) && decide (A.key = B.key) &&
      decide (canonSlots A.stack = canonSlots B.stack)
  | _, _ => false

/-- **Segment equivalence** with memory and globals, for values below that do not end in a
function reference. -/
def SegEquivXN (lt st gt : List IntType) (mem : Bool) (a b : List Instr) : Prop :=
  ∀ (m : Silmaril.Wasm.Logic.Hoare.Corr) (P : Profile) {H : Type} (host : HostSemantics H) (c : XCtx H)
    (us : List Val) (rest : List Admin) (Q : Silmaril.Wasm.Logic.Core.Post H), c.Ok lt st gt mem →
    Silmaril.Wasm.Auto.Equiv.NoFuncTop us →
    (Silmaril.Wasm.Logic.Hoare.Wp m P host c.s c.f (c.code lt st gt us a rest) Q ↔
      Silmaril.Wasm.Logic.Hoare.Wp m P host c.s c.f (c.code lt st gt us b rest) Q)

end Silmaril.Wasm.Auto.EquivUnroll
