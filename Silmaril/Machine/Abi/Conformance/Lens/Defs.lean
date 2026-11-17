module

public import Silmaril.Machine.Abi.Conformance.Defs

/-!
# The machine lens: a laundering store, and a machine with hidden state

Test objects for the three requirements `Mach` meets by construction (`Lens.Thms`):

* `launder`: the store of the lawful laundering lens of the #994 review: the integer state of
  `y` written into `s`, and, whenever the machine state changed, the direction flag cleared and
  x87 mode set, whatever the code did. Under the stage-1 laws it was the `store` of a lawful
  machine; it is the store of no `Mach` now (`Lens.Thms.launder_not_store`);
* `tsc`: a machine with **hidden state a step reads**: its state is an integer state and a
  time-stamp value the FFI state does not hold. At `rip = 0` it executes an `rdtsc`-like step
  (`rax` := the hidden value, `rip` := 1); it is stuck elsewhere. Every hidden value is an
  admissible completion (`Fills`). `tscRef` is the reference that may return any value there.
  Like `LeafArith.Witness.toy`, it is a segment machine given by its step function, with no
  decoder: a schema test, not x86 code.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.Lens

open Silmaril.Machine.SystemV.Abi
open Silmaril.X86 (State MState Word)

/-- **The laundering store** of the #994 review: `s` itself when the machine state is
unchanged; otherwise `y`'s integer state with the direction flag cleared and x87 mode set. -/
noncomputable def launder (s : Ffi.State) (y : MState) : Ffi.State :=
  open Classical in
  if y = s.machine then s else { s with machine := y, direction := false, x87Mode := true }

/-- An FFI state: every register, flag and field zero (x87 mode set), no memory mapped. -/
def blank : Ffi.State :=
  ⟨⟨⟨fun _ => 0, 0, ⟨none, none, none, none, none, none⟩, 0⟩, ⟨[], ∅⟩⟩,
    fun _ => 0, fun _ => 0, false, true, 0, 0, 0⟩

/-- The core after the `rdtsc`-like step: `rax` holds the time-stamp value `v`, `rip` is 1. -/
def tscCore (c : State) (v : Word) : State :=
  { c with rip := 1, regs := Silmaril.Machine.RegisterFile.write c.regs .rax v }

/-- The step of `tsc`: at `rip = 0`, read the hidden value into `rax`; stuck elsewhere. -/
def tscStep (x : MState × Word) : Option (MState × Word) :=
  if x.1.core.rip = 0 then some (⟨tscCore x.1.core x.2, x.1.memory⟩, x.2) else none

/-- `tscStep` as a segment machine on `MState × Word` (no decoder: `step_of` is vacuous). -/
def tscIsa : Silmaril.X86.SegVC.Isa (MState × Word) where
  Instr := Unit
  instDecEq := inferInstance
  decode _ := none
  exec _ _ _ _ := .dataFault
  core x := x.1.core
  mem x := x.1.memory
  upd x c m := (⟨c, m⟩, x.2)
  core_upd _ _ _ := rfl
  mem_upd _ _ _ := rfl
  upd_self _ := rfl
  ok _ _ := True
  live _ := True
  step := tscStep
  live_step _ _ := trivial
  step_of _ _ _ _ hd _ _ := nomatch hd

/-- **A machine with a hidden time-stamp value**: it models `.machine` only, and every hidden
value completes an FFI state. -/
def tsc : Mach where
  σ := MState × Word
  isa := tscIsa
  models
    | .machine => true
    | _ => false
  models_machine := rfl
  view x := { blank with machine := x.1 }
  machine_view _ := rfl
  Fills s x := x.1 = s.machine
  fills_agree h f hf := by
    cases f <;> first | exact h | cases hf
  fills_total s := ⟨(s.machine, 0), rfl⟩

/-- **The reference for `tsc`**: at `rip = 0`, any time-stamp value in `rax` and `rip` at 1,
the rest of the FFI state unchanged; no step elsewhere. -/
def tscRef : Ref where
  Step s t := s.machine.core.rip = 0 ∧
    ∃ v, t = { s with machine := ⟨tscCore s.machine.core v, s.machine.memory⟩ }

end Silmaril.Machine.Abi.Conformance.Lens

end
