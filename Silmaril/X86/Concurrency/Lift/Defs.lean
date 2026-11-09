module

public import Silmaril.X86.Concurrency.Cir.Seq.Defs
public import Silmaril.X86.FnContract.Defs
public import Silmaril.X86.MemEvent.Defs
public import Silmaril.X86.Open.Defs
public import Silmaril.X86.Open9.Defs

/-!
# The single-threaded lift for sequential machines and function contracts: definitions

The existing x86 results
(function contracts, process theorems) are stated over **sequential machines**: a deterministic
`step` on one flat memory. The lift (`Cir.Seq.oneSem_iff`) says one thread cannot tell any model
`SC ⊑ M ⊑ XL` from sequential replay. This module says what it means for a machine's runs to
"read the same under `M`", and states the glue to the x86 machines (`Task.openFlatStep`, `Task.open9FlatStep`, both
proved in `Lift/Thms.lean`).

* `flat`: the byte view of a silmaril memory.
* `FlatStep step mem P`: every step has a list of one-thread memory actions (`ActOk`, and
  satisfying `P`, which ties them to the instruction's access list) whose sequential replay on the pre-state
  memory gives the post-state memory.
* `EvRun step mem P s t acts`: a run from `s` to `t` with the concatenation `acts` of such
  per-step actions.
* `RunUnder M step mem P s t`: some event trace of a run from `s` to `t`, read as **one thread
  under `M`** from `s`'s memory, has `t`'s memory as its **only** behaviour.
* `FnContract.Spec.TotalUnder I P S M`: total correctness of a function contract **under `M`**:
  every entry state reaches a state meeting the contract, by a run that reads the same under
  `M`.
* `Task.openFlatStep` and `Task.open9FlatStep`, the memory-event glue for the `Open` and `Open9`
  machines: the access list of `Silmaril.X86.MemEvent`, filled with the bytes read and
  written, replays sequentially to the step's memory. Both are proved: `Lift.openFlatStep`,
  `Lift.open9FlatStep` in `Lift/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Lift

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.MemoryModel.Litmus (XAct)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86 (MState)

/-- The byte view of a silmaril memory (the backing bytes; permissions are not memory-model
state). -/
def flat (m : Silmaril.Process.Memory) : Cir.Mem := fun a => m.bytes[a]?

variable {σ : Type}

/-- **A step is flat-evented**: it has one thread's memory actions (`ActOk`, satisfying `P`)
whose sequential replay on the pre-state memory gives the post-state memory. -/
def FlatStep (step : σ → Option σ) (mem : σ → Cir.Mem) (P : σ → List XAct → Prop) : Prop :=
  ∀ s s', step s = some s' → ∃ acts : List XAct, P s acts ∧ (∀ a ∈ acts, ActOk a) ∧
    actsReplay (mem s) acts = some (mem s')

/-- A run with its event trace: the concatenation of flat per-step actions. -/
inductive EvRun (step : σ → Option σ) (mem : σ → Cir.Mem) (P : σ → List XAct → Prop) :
    σ → σ → List XAct → Prop
  | refl (s : σ) : EvRun step mem P s s []
  | cons {s s' t : σ} {acts rest : List XAct} (h : step s = some s') (hP : P s acts)
      (hok : ∀ a ∈ acts, ActOk a) (hr : actsReplay (mem s) acts = some (mem s'))
      (tail : EvRun step mem P s' t rest) : EvRun step mem P s t (acts ++ rest)

/-- **The run from `s` to `t` reads the same under `M`**: it has an event trace whose only
behaviour, as one thread under `M` from `s`'s memory, is `t`'s memory. -/
def RunUnder (M : Exec → Prop) (step : σ → Option σ) (mem : σ → Cir.Mem) (P : σ → List XAct → Prop)
    (s t : σ) : Prop :=
  ∃ acts, EvRun step mem P s t acts ∧ ∀ m, OneSem M (mem s) acts m ↔ m = mem t

/-- **Total correctness under `M`** of a function contract: as `Spec.Total`, and the run reads
the same under `M`. -/
def _root_.Silmaril.X86.FnContract.Spec.TotalUnder (I : Silmaril.X86.SegVC.Isa σ)
    (P : σ → List XAct → Prop) (S : Silmaril.X86.FnContract.Spec σ) (M : Exec → Prop) : Prop :=
  ∀ s, I.live s → Silmaril.X86.FnContract.AbiEntry (I.core s) (I.mem s) → S.entry s →
    ∃ t, Silmaril.Machine.Execution.Reaches I.step s t ∧
      Silmaril.X86.FnContract.Spec.Result I S s t ∧
      RunUnder M I.step (fun s => flat (I.mem s)) P s t

/-! ## The x86 glue (PROVED in `Lift/Thms.lean`) -/

/-- The actions of an `Open` step are access list of the fetched instruction. -/
def openActs (m : MState) (acts : List XAct) : Prop :=
  match Silmaril.X86.MemEvent.openFetch m.memory m.core.rip.toNat with
  | some (i, n) => acts.map (·.ev) = Silmaril.X86.MemEvent.ext8Accesses i m.core n
  | none => False

/-- The actions of an `Open9` step are access list of the fetched instruction. -/
def open9Acts (m : MState) (acts : List XAct) : Prop :=
  match Silmaril.X86.MemEvent.open9Fetch m.memory m.core.rip.toNat with
  | some (i, n) => acts.map (·.ev) = Silmaril.X86.MemEvent.ext9Accesses i m.core n
  | none => False

/-- **Memory-event glue for `Open`** (proved: `Lift.openFlatStep`). Every `Open.step` has actions with exactly the access list
(`ext8Accesses`) of its instruction, `ActOk`, whose sequential replay on the flat pre-memory is
the flat post-memory. Proof: from `MemEvent.open_step_sc` (the executor is `Local` for the access
list and the new memory is the old one patched on exactly its write set), fill each read event
with the pre-state bytes and each write event with the post-state bytes; `ActOk` holds because
events have positive sizes and `locked` only on read-modify-writes; the replay succeeds
because, in every access list of the `Ext8` forms, no read follows a write to an overlapping
byte (per-form case analysis, as locality proofs). The proof follows this plan; every access
list has at most two events and the two-event ones (`push r/m`, `call r/m`) load first, so no
read follows any write at all (`Flat.ext9_good`). -/
def Task.openFlatStep : Prop :=
  FlatStep Silmaril.X86.Open.step (fun m => flat m.memory) openActs

/-- **Memory-event glue for `Open9`** (PROVED: `Lift.open9FlatStep`: `Task.openFlatStep` for `Open9.step` and `ext9Accesses`,
with the same plan (from `MemEvent.open9_step_sc`). -/
def Task.open9FlatStep : Prop :=
  FlatStep Silmaril.X86.Open9.step (fun m => flat m.memory) open9Acts

end Silmaril.X86.Concurrency.Lift
