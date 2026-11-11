module

public import Silmaril.Wasm.Auto.Equiv.Thms

/-!
# Equivalence in context: tests

Every example is decided by the straight-line checker (`decide`) and lifted through the
congruence rules of `Silmaril.Wasm.Auto.Equiv.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.Equiv.CtlTests

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto.Equiv (SegEquiv segEquiv_of_check)
open Silmaril.Wasm.Auto.Equiv

/-- `x + 0` and `x` in a local. -/
def addZero : List Instr := [.localGet ⟨0⟩, .intConst .i32 0, .intBinOp .i32 .add, .localSet ⟨0⟩]

/-- `local.set` of the unchanged local. -/
def same : List Instr := [.localGet ⟨0⟩, .localSet ⟨0⟩]

theorem addZero_cequiv : CEquiv [.i32] [] addZero same :=
  SegEquiv.cequiv (segEquiv_of_check (by decide))

/-- **Under `block`.** -/
example : CEquiv [.i32] [.i64] [.block .empty addZero] [.block .empty same] :=
  CEquiv.block noParams_empty addZero_cequiv

/-- **Under `if`.** -/
example : CEquiv [.i32] [.i32] [.if_ .empty addZero [.nop]] [.if_ .empty same []] :=
  CEquiv.if_ noParams_empty addZero_cequiv (SegEquiv.cequiv (segEquiv_of_check (by decide)))

/-- **Under `br_if`** (and sequencing). -/
example : CEquiv [.i32] [.i32] ([.brIf ⟨0⟩] ++ addZero) ([.brIf ⟨0⟩] ++ same) :=
  CEquiv.prepend (Keeps.brIf [.i32] [] ⟨0⟩) addZero_cequiv

/-- A `do … while (x < 10)` body adding `1 + 1` to `x`. -/
def bodyA : List Instr :=
  [.localGet ⟨0⟩, .intConst .i32 1, .intBinOp .i32 .add, .intConst .i32 1, .intBinOp .i32 .add,
    .localTee ⟨0⟩, .intConst .i32 10, .intRelOp .i32 (.lt .signed)]

/-- The same body adding `2`, with the comparison flipped. -/
def bodyB : List Instr :=
  [.localGet ⟨0⟩, .intConst .i32 2, .intBinOp .i32 .add, .localSet ⟨0⟩, .intConst .i32 10,
    .localGet ⟨0⟩, .intRelOp .i32 (.gt .signed)]

/-- **Under `loop`**, in lockstep (partial correctness, Löb induction). -/
theorem loop_pequiv : PEquiv [.i32] [] [.loop .empty (bodyA ++ [.brIf ⟨0⟩])]
    [.loop .empty (bodyB ++ [.brIf ⟨0⟩])] :=
  CEquiv.loop noParams_empty
    (CEquiv.append (SegEquiv.cequiv (segEquiv_of_check (by decide))) _)
    (KeepsBr0.of_check ⟨0⟩ (by decide))

/-- info: 'Silmaril.Wasm.Auto.Equiv.CEquiv.loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CEquiv.loop

/-- info: 'Silmaril.Wasm.Auto.Equiv.CtlTests.loop_pequiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loop_pequiv

end Silmaril.Wasm.Auto.Equiv.CtlTests
