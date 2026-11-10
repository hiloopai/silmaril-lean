module

public import Silmaril.X86.Open.Defs
public import Silmaril.X86.FnContract.Defs
import Silmaril.Proofs.X86.Open.Law

/-!
# The open machine over `Ext8`: `SegVC` instance, agreement with `Ext8`, contracts

* `isa`: the open machine as a `Silmaril.X86.SegVC.Isa` (instructions, decoder and executor
  of `Ext8`; no side condition on `ret`; every state live). Its law is `step_of_listed`.
* `step_of_ext8_stepOpt`, `step_of_ext8_returned`, `ext8_of_step`: the open step agrees with
  `Ext8.step exit` for every designated exit `exit`, up to the reporting of the return.
* `returns_open`, `returns_open_ext`: **a callee proved under `Ext8.Returns R` or
  `Ext.Returns R` is an open run ending at `rip = R`**.
* `total_of_returns`, `contractOfReturns`: function contracts on `Open.isa` from such runs.
* `Ext.decode_none_append`, `Ext.fetch_undecodable_of`: a rejection by `Ext.decode` whose
  length decoder finished persists whatever bytes follow (used by `Open9`).
-/

@[expose] public section

namespace Silmaril.X86.Open

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Loaded parseRaw)
open Silmaril.X86.FnContract (Spec AbiEntry ReturnsPost retOf)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run Reaches)

/-- **The listing law.** A listed instruction at the program counter that `decode` reads
and that executes is one open step. -/
theorem step_of_listed {m : MState} {base : Word} {code : List Byte} {o l : Nat}
    {i : Ext8.Instr} {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : Ext8.exec i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ :=
  Silmaril.Proofs.X86.Open.step_of_listed hl hrip hfit hdec hx

/-- **The open machine as a segment-VC instance.** -/
@[reducible] def isa : SegVC.Isa MState where
  Instr := Ext8.Instr
  instDecEq := inferInstance
  decode := decode
  exec := Ext8.exec
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
    (h : Ext8.stepOpt exit m = some n) : step m = some n :=
  Silmaril.Proofs.X86.Open.step_of_ext8_stepOpt h

/-- The `ret` to the designated exit is an open step. -/
theorem step_of_ext8_returned {exit : Word} {m n : MState}
    (h : Ext8.step exit m = .ext (.returned n)) : step m = some n :=
  Silmaril.Proofs.X86.Open.step_of_ext8_returned h

/-- An open step is, for every designated exit, a retirement or the return to that exit. -/
theorem ext8_of_step {exit : Word} {m n : MState} (h : step m = some n) :
    Ext8.stepOpt exit m = some n ∨ Ext8.step exit m = .ext (.returned n) :=
  Silmaril.Proofs.X86.Open.ext8_of_step h

/-- Runs of `Ext8.stepOpt exit` are open runs. -/
theorem reaches_of_ext8 {exit : Word} {a b : MState}
    (h : Reaches (Ext8.stepOpt exit) a b) : Reaches step a b :=
  Silmaril.Proofs.X86.Open.reaches_of_ext8 h

/-- **Returning runs are open runs** (`Ext8`). -/
theorem returns_open {R : Word} {m m' : MState} (h : Ext8.Returns R m m') :
    Reaches step m m' ∧ m'.core.rip = R :=
  Silmaril.Proofs.X86.Open.returns_open h

/-- **Returning runs are open runs** (`X86.Ext`). -/
theorem returns_open_ext {R : Word} {m m' : MState} (h : Ext.Returns R m m') :
    Reaches step m m' ∧ m'.core.rip = R :=
  returns_open (Ext8.returns_of_ext h)

/-- The open machine is deterministic: runs of equal length agree. -/
theorem run_deterministic {n : Nat} {a b c : MState} (h₁ : run step n a = some b)
    (h₂ : run step n a = some c) : b = c := by
  rw [h₁] at h₂; exact Option.some.inj h₂

/-! ## Contracts from returning runs -/

/-- A total spec on the open machine from `Ext8.Returns` runs to the entry's return
address. -/
theorem total_of_returns (S : Spec MState)
    (h : ∀ m, AbiEntry m.core m.memory → S.entry m →
      ∃ fin, Ext8.Returns (retOf m.core m.memory) m fin ∧ ReturnsPost S m fin) :
    S.Total isa := fun m _ ha he =>
  let ⟨fin, hret, hp⟩ := h m ha he
  let ⟨hr, hrip⟩ := returns_open hret
  ⟨fin, hr, rfl, ⟨hrip, hp.stack, hp.calleeSaved⟩, hp.frame, hp.post⟩

/-- A contract on the open machine from `Ext8.Returns` runs. -/
def contractOfReturns (S : Spec MState)
    (h : ∀ m, AbiEntry m.core m.memory → S.entry m →
      ∃ fin, Ext8.Returns (retOf m.core m.memory) m fin ∧ ReturnsPost S m fin) :
    FnContract isa :=
  ⟨S, total_of_returns S h⟩

end Silmaril.X86.Open

namespace Silmaril.X86.Ext

open Silmaril.X86 (Byte fetchWindow maxInstrLength)
open Silmaril.Process (Memory)

/-- If the length decoder finishes inside `w` and `w` does not decode, no extension of `w`
decodes. -/
theorem decode_none_append {w : List Byte} (hnone : decode w = none)
    (hne : parseRaw w ≠ .eof) (more : List Byte) : decode (w ++ more) = none :=
  Silmaril.Proofs.X86.Open.decode_none_append hnone hne more

/-- The fetch at an address whose window extends such a slice is undecodable. -/
theorem fetch_undecodable_of {memory : Memory} {address : Nat} {w more : List Byte}
    (hwin : fetchWindow memory maxInstrLength address = w ++ more)
    (hnone : decode w = none) (hne : parseRaw w ≠ .eof) :
    fetch memory address = .undecodable :=
  Silmaril.Proofs.X86.Open.fetch_undecodable_of hwin hnone hne

end Silmaril.X86.Ext
