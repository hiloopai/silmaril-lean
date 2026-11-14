module

public import Silmaril.Machine.X86.Open.Defs
import Silmaril.Proofs.Machine.X86.Open.Law

/-!
# The open machine as a `SegVC` instance, and the transport of returning runs

* `isa`: the open machine as a `Silmaril.X86.SegVC.Isa` (instructions, decoder and executor
  of `Ext8`; no side condition on `ret`; every state live). Its law is `step_of_listed`.
* `step_of_ext8_stepOpt`, `step_of_ext8_returned`, `ext8_of_step`: the open step agrees with
  `Ext8.step exit` for every designated exit `exit`, up to the reporting of the return.
* `returns_open`, `returns_open_ext`: **a callee proved under `Ext8.Returns R` or
  `Ext.Returns R` is an open run ending at `rip = R`**. This is the generic form of
  `Silmaril.Apps.Sha256sum.X86Sys.rReaches_of_ext_returns`.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Open

open Silmaril.X86 (State MState Word Byte)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run Reaches)

/-- **The listing law.** A listed instruction at the program counter that `decode` reads
and that executes is one open step. -/
theorem step_of_listed {m : MState} {base : Word} {code : List Byte} {o l : Nat}
    {i : Silmaril.X86.Ext8.Instr} {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Ext8.exec i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ :=
  Silmaril.Proofs.Machine.X86.Open.step_of_listed hl hrip hfit hdec hx

/-- **The open machine as a segment-VC instance.** -/
@[reducible] def isa : Silmaril.X86.SegVC.Isa MState where
  Instr := Silmaril.X86.Ext8.Instr
  instDecEq := inferInstance
  decode := decode
  exec := Silmaril.X86.Ext8.exec
  core := MState.core
  mem := MState.memory
  upd := fun _ c m => ⟨c, m⟩
  core_upd := fun _ _ _ => rfl
  mem_upd := fun _ _ _ => rfl
  upd_self := fun _ => rfl
  ok := fun _ _ => True
  live := fun _ => True
  step := step
  live_step := fun _ _ => trivial
  step_of := fun _ hl hrip hfit hdec hx _ => step_of_listed hl hrip hfit hdec hx

@[simp] theorem isa_step : isa.step = step := rfl

/-- A retirement of `Ext8.stepOpt exit` is an open step. -/
theorem step_of_ext8_stepOpt {exit : Word} {m n : MState}
    (h : Silmaril.X86.Ext8.stepOpt exit m = some n) : step m = some n :=
  Silmaril.Proofs.Machine.X86.Open.step_of_ext8_stepOpt h

/-- The `ret` to the designated exit is an open step. -/
theorem step_of_ext8_returned {exit : Word} {m n : MState}
    (h : Silmaril.X86.Ext8.step exit m = .ext (.returned n)) : step m = some n :=
  Silmaril.Proofs.Machine.X86.Open.step_of_ext8_returned h

/-- An open step is, for every designated exit, a retirement or the return to that exit. -/
theorem ext8_of_step {exit : Word} {m n : MState} (h : step m = some n) :
    Silmaril.X86.Ext8.stepOpt exit m = some n ∨
      Silmaril.X86.Ext8.step exit m = .ext (.returned n) :=
  Silmaril.Proofs.Machine.X86.Open.ext8_of_step h

/-- Runs of `Ext8.stepOpt exit` are open runs. -/
theorem reaches_of_ext8 {exit : Word} {a b : MState}
    (h : Reaches (Silmaril.X86.Ext8.stepOpt exit) a b) : Reaches step a b :=
  Silmaril.Proofs.Machine.X86.Open.reaches_of_ext8 h

/-- **Returning runs are open runs** (`Ext8`). -/
theorem returns_open {R : Word} {m m' : MState} (h : Silmaril.X86.Ext8.Returns R m m') :
    Reaches step m m' ∧ m'.core.rip = R :=
  Silmaril.Proofs.Machine.X86.Open.returns_open h

/-- **Returning runs are open runs** (`X86.Ext`). -/
theorem returns_open_ext {R : Word} {m m' : MState} (h : Silmaril.X86.Ext.Returns R m m') :
    Reaches step m m' ∧ m'.core.rip = R :=
  Silmaril.Proofs.Machine.X86.Open.returns_open_ext h

/-- The open machine is deterministic: `Reaches` runs of equal length agree. -/
theorem run_deterministic {n : Nat} {a b c : MState} (h₁ : run step n a = some b)
    (h₂ : run step n a = some c) : b = c := by
  rw [h₁] at h₂; exact Option.some.inj h₂

end Silmaril.Machine.X86.Open
