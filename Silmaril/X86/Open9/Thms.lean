module

public import Silmaril.X86.Open9.Defs
public import Silmaril.X86.Open.Thms
public import Silmaril.X86.Ext9.Thms
public import Silmaril.X86.FnContract.Thms
import Silmaril.Proofs.X86.Open9.Law
import Silmaril.Proofs.X86.Open9.Step

/-!
# The open machine over `Ext9`: `SegVC` instance and transfers

* `isa`: the open machine over `Ext9` as a `Silmaril.X86.SegVC.Isa` (same states, core,
  memory and update as `Open.isa`); its law is `step_of_listed`.
* `step_eq_open`: **where `Ext8` fetches anything but undecodable bytes, `Open9.step` is
  `Open.step`**, so an `Open` proof is an `Open9` proof on `Ext8` code.
* `extendsOpen : Open.isa.Extends Open9.isa`: every open step is an `Open9` step
  (`step_of_open`), hence `run_of_open`, `reaches_of_open`.
* `FnContract.Spec.Total.toOpen9`, `FnContract.toOpen9`: **every contract on `Open.isa` is a
  contract on `Open9.isa`** with the same spec.
* `returns_open9`, `total_of_returns`, `contractOfReturns`: a callee proved under
  `Ext9.Returns R` is an `Open9` run ending at `R`, and a contract.
* `fetch8_undecodable_of`, `step_of_fetch_new`: the fetch form of the law for new forms, for
  machines that extend `Open9` with forms of their own.
-/

@[expose] public section

namespace Silmaril.X86.Open9

open Silmaril.X86 (State MState Word Byte)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.FnContract (Spec AbiEntry ReturnsPost retOf)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run Reaches)

/-- **The listing law.** -/
theorem step_of_listed {m : MState} {base : Word} {code : List Byte} {o l : Nat}
    {i : Ext9.Instr} {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : Ext9.exec i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ :=
  Silmaril.Proofs.X86.Open9.step_of_listed hl hrip hfit hdec hx

/-- A listed `Ext8` instruction is an `Open.decode` listing. -/
theorem decode_ext8 {bytes : List Byte} {i : Ext8.Instr} {n : Nat}
    (h : decode bytes = some (.ext8 i, n)) : Open.decode bytes = some (i, n) :=
  Silmaril.Proofs.X86.Open9.decode_ext8 h

/-- A listed new form: `Ext` rejects the slice, the `Ext8` byte-form parser fails and the
`Ext` length decoder finishes inside it, `decodeNew` reads it, and it is 1 to 15 bytes. -/
theorem decode_new {bytes : List Byte} {i : Ext9.New} {n : Nat}
    (h : decode bytes = some (.new i, n)) :
    Ext.decode bytes = none ∧ newBad bytes = true ∧ rawNotEof bytes = true ∧
      Ext9.decodeNew bytes = some (i, n) ∧ 0 < n ∧ n ≤ maxInstrLength :=
  Silmaril.Proofs.X86.Open9.decode_new h

/-- **The fetch form of the law for a new form**: bytes fetched at the program counter that
decode as a new form and execute are one `Open9` step. -/
theorem step_of_fetch_new {m : MState} {l : Nat} {w : List Byte} {i : Ext9.New} {c : State}
    {mem : Memory} (fetched : m.memory.fetchBytes m.core.rip.toNat l = some w)
    (hdec : decode w = some (.new i, l))
    (hx : Ext9.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ :=
  Silmaril.Proofs.X86.Open9.step_of_fetch_new fetched hdec hx

/-- **The fall-through to bytes no `Ext8` form decodes**: fetched bytes of at most 15 bytes
that `Ext` rejects (its length decoder finishing inside them) and whose `Ext8` new-form parse
fails extend to the fetch window, and `Ext8.fetch` reports `undecodable` there. -/
theorem fetch8_undecodable_of {memory : Memory} {address l : Nat} {w : List Byte}
    (fetched : memory.fetchBytes address l = some w) (hl : l ≤ maxInstrLength)
    (hnone : Ext.decode w = none) (hbad : newBad w = true) (hne : rawNotEof w = true) :
    ∃ more, fetchWindow memory maxInstrLength address = w ++ more ∧
      Ext8.fetch memory address = .inl .undecodable :=
  Silmaril.Proofs.X86.Open9.fetch8_undecodable_of fetched hl hnone hbad hne

/-- **Where `Ext8.fetch` decodes, `Open9` is the open machine.** -/
theorem step_eq_open {m : MState}
    (h : Ext8.fetch m.memory m.core.rip.toNat ≠ .inl .undecodable) :
    step m = Open.step m := by
  unfold step; split
  · rename_i he; exact absurd he h
  · rfl

/-- **The open machine over `Ext9` as a segment-VC instance.** -/
@[reducible] def isa : SegVC.Isa MState where
  Instr := Ext9.Instr
  instDecEq := inferInstance
  decode := decode
  exec := Ext9.exec
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

/-- **Every open step is an `Open9` step.** -/
theorem step_of_open {m n : MState} (h : Open.step m = some n) : step m = some n :=
  Silmaril.Proofs.X86.Open9.step_of_open h

/-- **`Open9` extends `Open`** on the same states (identity lens). -/
@[reducible] def extendsOpen : Open.isa.Extends isa :=
  .ofStep (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ h => h) step_of_open

/-- Every open run is an `Open9` run of the same length. -/
theorem run_of_open (k : Nat) {a b : MState} (h : run Open.step k a = some b) :
    run step k a = some b :=
  extendsOpen.run k h

/-- Every open run is an `Open9` run. -/
theorem reaches_of_open {a b : MState} (h : Reaches Open.step a b) : Reaches step a b :=
  extendsOpen.reaches h

/-- A retirement of `Ext9.stepOpt exit` is an `Open9` step. -/
theorem step_of_ext9_stepOpt {exit : Word} {m n : MState}
    (h : Ext9.stepOpt exit m = some n) : step m = some n :=
  Silmaril.Proofs.X86.Open9.step_of_ext9_stepOpt h

/-- **Returning runs are `Open9` runs** (`Ext9`). -/
theorem returns_open9 {R : Word} {m m' : MState} (h : Ext9.Returns R m m') :
    Reaches step m m' ∧ m'.core.rip = R :=
  Silmaril.Proofs.X86.Open9.returns_open9 h

/-- The `Open9` machine is deterministic. -/
theorem run_deterministic {n : Nat} {a b c : MState} (h₁ : run step n a = some b)
    (h₂ : run step n a = some c) : b = c := by
  rw [h₁] at h₂; exact Option.some.inj h₂

/-! ## Contracts -/

/-- A total spec on `Open9` from `Ext9.Returns` runs to the entry's return address. -/
theorem total_of_returns (S : Spec MState)
    (h : ∀ m, AbiEntry m.core m.memory → S.entry m →
      ∃ fin, Ext9.Returns (retOf m.core m.memory) m fin ∧ ReturnsPost S m fin) :
    S.Total isa := fun m _ ha he =>
  let ⟨fin, hret, hp⟩ := h m ha he
  let ⟨hr, hrip⟩ := returns_open9 hret
  ⟨fin, hr, rfl, ⟨hrip, hp.stack, hp.calleeSaved⟩, hp.frame, hp.post⟩

/-- A contract on `Open9` from `Ext9.Returns` runs. -/
def contractOfReturns (S : Spec MState)
    (h : ∀ m, AbiEntry m.core m.memory → S.entry m →
      ∃ fin, Ext9.Returns (retOf m.core m.memory) m fin ∧ ReturnsPost S m fin) :
    FnContract isa :=
  ⟨S, total_of_returns S h⟩

end Silmaril.X86.Open9

namespace Silmaril.X86.FnContract

open Silmaril.X86 (MState)

/-- **A total spec on the `Ext8` open machine is total on the `Ext9` one.** -/
theorem Spec.Total.toOpen9 {S : Spec MState} (h : S.Total Open.isa) : S.Total Open9.isa :=
  h.lift Open9.extendsOpen

/-- **Every `Ext8` open-machine contract is an `Ext9` open-machine contract.** -/
def toOpen9 (C : FnContract Open.isa) : FnContract Open9.isa :=
  ⟨C.toSpec, C.total.toOpen9⟩

@[simp] theorem toOpen9_toSpec (C : FnContract Open.isa) : C.toOpen9.toSpec = C.toSpec := rfl

end Silmaril.X86.FnContract
