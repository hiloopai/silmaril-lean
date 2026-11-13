module

public import Silmaril.Machine.Abi.SystemV.Thms
public import Silmaril.Machine.Abi.Thunk.Defs
public import Silmaril.X86.FnContract.SystemV.Thms
public import Silmaril.X86.Ladder.LeafArith.Defs
/-! # ABI comorphisms on the open x86 machine

Track C's conventions (`Silmaril.Machine.Abi.Convention`) judge an abstract call relation
`Contracts.Model Ffi.State Ffi.State`. Track A's contracts (`FnContract Open.isa`) are proved on
the decoded open machine `Silmaril.X86.Open.step`. This module supplies the call
relation that joins them.

**The model.** `callModel` is the *first-return* call relation of the open machine: from an
entry state `s`, the outcomes are the states `t` that the machine reaches from `s` without
passing through a returned state on the way (`FirstReturn`), where *returned* is A's
`Open.Returned` for `s`'s stack pointer and return address (`rip` at the return address and
`rsp` popped past it). The FFI-only state (vectors, x87, control state, FS base) is carried
unchanged, as in A's `Open.ffiExecute`. Hence the `Ffi.Return`/`Win64.Returns` obligations
`threadPointer`, `direction`, `x87Mode`, `mxcsrControl`, `x87Control` and `vectorsSaved` hold
**by the model, not by the code** (`Silmaril.Machine.Abi.FsBase.callModel_carried`). The FFI
`fsBase` is a copy, distinct from the `machine.core.fsBase` that `%fs:` operands read; the
entry invariant `FsBase.FsCoherent` and `FsBase.callModel_fsBase` (conditional on
`FsBase.Task.openStepKeepsFs`) relate them. Since `Open.step` is a function, `callModel s` has at
most one element (`Thms.callModel_subsingleton`). So the *demonic* satisfaction of track C
(`Contracts.Sat`: some outcome, and every outcome meets the post) is *not* weakened by
non-determinism, and it is not the angelic `∃ final` of `Realizes`.

**Why not `Reaches`.** `FnContract.Spec.Total` gives *some* reachable returned state. On the
open machine a run continues into the caller after the return, so a later returned state is
also reachable and nothing constrains it. A demonic call relation must stop at the first
return; this is A's known problem 3. `RunsIn P` (runs whose every step is taken from a
state satisfying `P`) and `TotalIn` (A's `Spec.Total` with such a run) close the gap:
`InCode base len` (the program counter lies inside the function's code) is the invariant a
`FunCert` run keeps, and a run inside the code reaches no returned state before its last
step when the return address lies outside the code.

**Frames.** Convention sentences are value-level, so the room assumption of a sentence
(code loaded, entry at the function, return address outside the code) is stated with
`Silmaril.Machine.Abi.within`, as for C2's thunks.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.OpenMachine

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi (Ffi.State)
open Silmaril.X86

/-- Runs of the open machine that take every step from a state satisfying `P` (the final
state is unconstrained).

**Deprecated duplicate** (round 4): this is the generic
`FnContract.RunsIn Open.isa` (`Thms.runsIn_iff`); new code should use the generic one. -/
inductive RunsIn (P : MState → Prop) : MState → MState → Prop
  | refl (m : MState) : RunsIn P m m
  | step {m m' t : MState} : P m → Open.step m = some m' → RunsIn P m' t → RunsIn P m t

/-- The program counter lies inside `len` bytes of code at `base`. -/
def InCode (base : Word) (len : Nat) (m : MState) : Prop :=
  ∃ o, o < len ∧ m.core.rip = base + BitVec.ofNat 64 o

/-- The function entered at `s` has returned in `m` (A's `Open.Returned` for `s`'s entry
stack pointer and return address). -/
def Returned (s m : MState) : Prop :=
  Open.Returned (s.core.read .rsp) (FnContract.retOf s.core s.memory) m

/-- `t` is the first returned state of the run from `s`.

**Deprecated duplicate** of `FnContract.FirstReturn Open.isa` (`Thms.firstReturn_iff`). -/
def FirstReturn (s t : MState) : Prop :=
  RunsIn (fun m => ¬ Returned s m) s t ∧ Returned s t

/-- **The open machine's call relation** on FFI states: the first return, with the FFI-only
state carried unchanged. -/
def callModel : Contracts.Model Ffi.State Ffi.State := fun s =>
  {t | FirstReturn s.machine t.machine ∧ t = { s with machine := t.machine }}

/-- A's `Spec.Total` with the run restricted to steps from states satisfying `P s`.

**Deprecated duplicate** of `FnContract.Spec.TotalIn Open.isa`; first-return contracts
should be stated as `FnContract.Spec.Strict` / `FnContract.Strict`. -/
def TotalIn (S : FnContract.Spec MState) (P : MState → MState → Prop) : Prop :=
  ∀ s, FnContract.AbiEntry s.core s.memory → S.entry s →
    ∃ t, RunsIn (P s) s t ∧ S.Result Open.isa s t

/-- The return address of the entry state lies outside `len` bytes of code at `base`. -/
def RetOutside (base : Word) (len : Nat) (s : MState) : Prop :=
  ∀ o, o < len → FnContract.retOf s.core s.memory ≠ base + BitVec.ofNat 64 o

/-- The room of a function loaded from `code` at `base` and entered at offset `off`: the
code is loaded, the entry is at the function, and the return address lies outside the
code. -/
structure Room (base : Word) (code : List Byte) (off : Nat) (s : Ffi.State) : Prop where
  loaded : Silmaril.X86.Ext.Loaded s.machine.memory base code
  pc : s.machine.core.rip = base + BitVec.ofNat 64 off
  retOutside : RetOutside base code.length s.machine

/-! ## Rung 01 prototypes and C contracts -/

open Silmaril.Machine.Abi.SystemV (Proto vocab)
open Silmaril.X86.Ladder.LeafArith

/-- `int clamp_i32(int, int, int)`. -/
def clampProto : Proto := ⟨sigI3, by decide⟩

/-- `uint32_t sat_add_u32(uint32_t, uint32_t)`. -/
def satProto : Proto := ⟨sigU2, by decide⟩

/-- The exact C contract of `clamp_i32`: every call returns `clampSpec x lo hi`. -/
def clampC : Contracts.Contract (vocab.Args clampProto) (Option (vocab.Ret clampProto)) where
  pre _ := True
  post a r := r = some (clampResult a)

/-- The exact C contract of `sat_add_u32`: every call returns `satAddSpec a b`. -/
def satC : Contracts.Contract (vocab.Args satProto) (Option (vocab.Ret satProto)) where
  pre _ := True
  post a r := r = some (satResult a)

/-- A *mutated* C contract for `clamp_i32` (it returns its first argument), used to show
that the bridge discriminates contracts (`Thms.clamp_i32_rejects_id`). -/
def clampIdC : Contracts.Contract (vocab.Args clampProto) (Option (vocab.Ret clampProto)) where
  pre _ := True
  post a r := match a with | .cons x _ => r = some x

/-- The domain of the typed FFI certificates beyond the ABI: the rung 01 code loaded and the
call entered at offset `off`. -/
def ffiLoadedAt {α : Type} (off : Nat) (_ : α) (call : Silmaril.Machine.SystemV.Abi.Ffi.Call) :
    Prop :=
  Silmaril.X86.Ext.Loaded call.initial.machine.memory base code ∧
    call.entry = base + BitVec.ofNat 64 off

end Silmaril.Machine.Abi.OpenMachine
