module

public import Silmaril.Compiler.Mir.FuncPass.Defs
/-! # Load forwarding needs a memory-aware simulation

The frame-only `FuncPass.FSim` cannot justify even the full-width transformation
`store [r0] r1; load r2 [r0]; ret r2` to
`store [r0] r1; move r2 r1; ret r2`.

`FuncPass.InstrSim` quantifies over every memory at each instruction, while its
point relation cannot mention memory. After matching the store it therefore forgets
which memory the store produced. `no_store_forward_fsim` proves the obstruction for
**every** point relation, including relations that allow different frames or indices.
This is a limitation of the proof interface, not a counterexample to load forwarding.
The concrete execution checks below show the successful store and forwarded load.

A useful next interface would relate points, frames and the shared current memory.
Operation obligations would carry the relation from the old to the new memory;
call-return obligations must discard memory facts or hold for every returned memory.
No compiler transformation is installed by this module. -/

@[expose] public section

namespace Silmaril.Compile.Mir.LoadForward.Limit

open Silmaril.Machine
open Silmaril.Compile.Mir.FuncPass

/-- One valid address and the value zero, in distinct registers. -/
def frame : Lir.Frame Nat := (Lir.Frame.empty.set 0 0).set 1 0

/-- Eight bytes with the value one at address zero. -/
def before : Lir.Memory := ⟨8, fun a => if a = 0 then 1 else 0⟩

/-- The memory produced by storing a full-width zero. -/
def after : Lir.Memory := ⟨8, Lir.writeLE before.bytes 0 8 0⟩

def store : Lir.Op Nat := .store .b8 0 0 1

def load : Lir.Op Nat := .load .b8 .zero 2 0 0

def move : Lir.Op Nat := .move 2 1

def sourceBlock : Block := ⟨#[.op store, .op load], .ret [.reg 2]⟩

def targetBlock : Block := ⟨#[.op store, .op move], .ret [.reg 2]⟩

def source : Func := ⟨"load_forward_example", [0, 1], 1, #[sourceBlock], true, false⟩

def target : Func := { source with blocks := #[targetBlock] }

/-- Both functions execute the same successful full-width store. -/
theorem store_exec : store.exec frame before = some (frame, after) := by rfl

/-- A successful store really changes memory, so it cannot be stuttered away. -/
theorem after_ne_before : after ≠ before := by
  intro h
  have hbyte := congrArg (fun m : Lir.Memory => m.bytes 0) h
  change (0 : Lir.Byte) = 1 at hbyte
  exact (by decide : (0 : Lir.Byte) ≠ 1) hbyte

/-- On the actual post-store memory, forwarding produces the exact same frame and memory. -/
theorem load_after_eq_move : load.exec frame after = move.exec frame after := by rfl

/-- Replacing the current memory by the pre-store memory changes the load's value. -/
theorem load_before : load.exec frame before = some (frame.set 2 1, before) := by rfl

theorem move_exec (m : Lir.Memory) : move.exec frame m = some (frame.set 2 0, m) := by rfl

/-- There is no frame-only `FSim` for this store-to-load forwarding example.
The store establishes a related point, but `InstrSim` then requires that point to
simulate a load against the pre-store memory too. Stuttering reaches the input's
terminator too early; matching the move returns a different value. -/
theorem no_store_forward_fsim
    (Q : Nat → Nat → Lir.Frame Nat → Nat → Lir.Frame Nat → Prop) :
    ¬ FSim source target Q := by
  intro h
  have hs := h.instr 0 sourceBlock targetBlock 0 frame 0 frame (.op store)
    rfl rfl (h.entry frame) rfl
  have hs := hs before frame after store_exec
  change (after = before ∧ Q 0 1 frame 0 frame) ∨
    ∃ o : Lir.Op Nat, some (Instr.op store) = some (Instr.op o) ∧ ∃ fr : Lir.Frame Nat,
      o.exec frame before = some (fr, after) ∧ Q 0 1 frame 1 fr at hs
  rcases hs with ⟨hm, _⟩ | ⟨o, ho, fr, he, hq⟩
  · exact after_ne_before hm
  · have ho : o = store := by cases ho; rfl
    subst o
    rw [store_exec] at he
    have he : fr = frame := (Prod.mk.inj (Option.some.inj he)).1.symm
    subst fr
    have hl := h.instr 0 sourceBlock targetBlock 1 frame 1 frame (.op load)
      rfl rfl hq rfl
    have hl := hl before (frame.set 2 1) before load_before
    change (before = before ∧ Q 0 2 (frame.set 2 1) 1 frame) ∨
      (∃ o : Lir.Op Nat, some (Instr.op move) = some (Instr.op o) ∧ ∃ fr : Lir.Frame Nat,
        o.exec frame before = some (fr, before) ∧ Q 0 2 (frame.set 2 1) 2 fr) at hl
    rcases hl with ⟨_, hq⟩ | ⟨o, ho, fr, he, hq⟩
    · have ht := h.term 0 sourceBlock targetBlock 2 (frame.set 2 1) 1 frame
        rfl rfl hq rfl
      have hi : (1 : Nat) = 2 := ht.1
      omega
    · have ho : o = move := by cases ho; rfl
      subst o
      rw [move_exec] at he
      have he : fr = frame.set 2 0 := (Prod.mk.inj (Option.some.inj he)).1.symm
      subst fr
      have ht := h.term 0 sourceBlock targetBlock 2 (frame.set 2 1) 2 (frame.set 2 0)
        rfl rfl hq rfl
      have hn : termOut (frame.set 2 1) sourceBlock.term ≠ .stuck := by decide
      have hv := (ht.2 hn).1
      change TermOut.ret [0] = TermOut.ret [1] at hv
      exact (by decide : TermOut.ret [0] ≠ TermOut.ret [1]) hv

end Silmaril.Compile.Mir.LoadForward.Limit
