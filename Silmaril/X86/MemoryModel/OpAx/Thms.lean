module

public import Silmaril.X86.MemoryModel.OpAx.Defs
public import Silmaril.X86.MemoryModel.Xl.Thms
import Silmaril.Proofs.X86.MemoryModel.OpAx.Timed
import Silmaril.Proofs.X86.MemoryModel.OpAx.Run
import Silmaril.Proofs.X86.MemoryModel.OpAx.Counter
import Silmaril.Proofs.X86.MemoryModel.OpAx.Paired
import Silmaril.Proofs.X86.MemoryModel.OpAx.Sb
import Silmaril.Proofs.X86.MemoryModel.OpAx.Conv

/-!
# Operational x86-TSO against axiomatic x86-TSO: theorems

PROVED (standard axioms only; proofs in
`Silmaril.Proofs.X86.MemoryModel.OpAx.{Timed,Run,Counter,Paired,Sb,Conv}`), for **every** finite program
`P : List (List (XEvent Nat))` (not per litmus test):

* `tso_of_timedOk`: a candidate with a store-buffer-like timing is x86-TSO-consistent;
* `run_explains_tso` (**op-TSO ⊆ ax-TSO**): every complete run of the store-buffer machine
  (`Litmus.AStep`, i.e. `Tso.XStep`/`Tso.XFlush`) on a program whose events name their thread
  (`ThreadsOk`) and whose threads have cells (`ThreadCells`) is explained by an
  x86-TSO-consistent candidate over the program's units: same reads, same final memory;
* `run_explains_tso_paired`: the same candidate also pairs every locked read-modify-write
  (`RmwPaired`), so its atomicity axiom is not vacuous;
* `run_explains_xl` (**op-TSO ⊆ XL**) and `Explains.mono`;
* `sb_weak_explained`, `sb_weak_not_sc`: a non-vacuity check — on SB's weak outcome the
  hypotheses hold and the theorem yields a TSO candidate, while no SC candidate exists;
* `partialForward_shape`, `partialForward_not_explained`: without `ThreadCells` the inclusion fails — a run with partial store
  forwarding reaches a final state no x86-TSO (or XL) candidate explains.

* `axToOp_holds` (**ax-TSO ⊆ op-TSO**, `Task.axToOp`): every x86-TSO-consistent candidate with
  paired locked read-modify-writes that explains a drained final state of a program whose events
  name their thread, whose `rmw`s are sized and whose initial memory covers its footprints is
  reached by a complete store-buffer run. Mixed-size accesses across threads are allowed; the
  proof does not use `ThreadCells` (it stays a hypothesis of `Task.axToOp` as stated);
* `op_iff_ax` (**op-TSO = ax-TSO**): the two directions together, unconditionally;
  `op_iff_ax_of_task` is kept as the earlier conditional form.

Proof of the converse (`Proofs.Conv`): a clock `κ` on the units extends `ghb` (counting the
`ghb`-earlier read-modify-write blocks; acyclicity of `ghb` makes it strictly monotone) and puts
the write of each locked read-modify-write one tick after its read (atomicity makes the block
order acyclic); then the run performs, at tick `t`, the unit with clock `t` (a load or `rmw`
executes after its thread's pending stores and fences, a store is flushed), with the machine
state in closed form at every tick.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.OpAx

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Tso (XEvent XState Mem)

/-- A candidate with a `TimedOk` timing is x86-TSO-consistent (OSS09's timestamp argument). -/
theorem tso_of_timedOk {x : Exec} {T : Timing} (h : TimedOk x T) : x.Tso := Proofs.tso h

/-- `Explains` is monotone in the model. -/
theorem Explains.mono {M M' : Exec → Prop} (hM : ∀ x, M x → M' x)
    {P : List (List (XEvent Nat))} {init : Tso.Mem} {s : XState Nat} {x : Exec}
    (h : Explains M P init s x) : Explains M' P init s x := by
  obtain ⟨us, h1, h2, h3, h4⟩ := h
  exact ⟨us, h1, h2, hM x h3, h4⟩

/-- **op-TSO ⊆ ax-TSO.** A complete run of the store-buffer machine on a program whose threads
have cells is explained by an x86-TSO-consistent candidate execution. -/
theorem run_explains_tso {P : List (List (XEvent Nat))} (hT : ThreadsOk P) (hC : ThreadCells P)
    {init : Tso.Mem} {s : XState Nat} (h : Run P init s) : ∃ x, Explains Exec.Tso P init s x :=
  Proofs.run_explains hT hC h

/-- **op-TSO ⊆ ax-TSO, with atomicity**: the explaining candidate pairs the two halves of each
locked read-modify-write in `x.rmw` (without this, `x.rmw = []` would satisfy `Explains` and
make the atomicity axiom vacuous). -/
theorem run_explains_tso_paired {P : List (List (XEvent Nat))} (hT : ThreadsOk P)
    (hC : ThreadCells P) {init : Tso.Mem} {s : XState Nat} (h : Run P init s) :
    ∃ x, Explains Exec.Tso P init s x ∧ RmwPaired x :=
  Proofs.run_explains_paired hT hC h

/-- **op-TSO ⊆ XL.** -/
theorem run_explains_xl {P : List (List (XEvent Nat))} (hT : ThreadsOk P) (hC : ThreadCells P)
    {init : Tso.Mem} {s : XState Nat} (h : Run P init s) : ∃ x, Explains Exec.Xl P init s x := by
  obtain ⟨x, hx⟩ := run_explains_tso hT hC h
  exact ⟨x, hx.mono fun x hx => x.xl_of_tso hx⟩

/-! ## Non-vacuity: store buffering -/

/-- SB: thread 0 stores `1` at 0 and loads address 1; thread 1 stores `1` at 1 and loads
address 0; both loads return `0` (the outcome SC forbids). -/
def sbP : List (List (XEvent Nat)) :=
  [[.store 0 0 [1], .load 0 1 [0]], [.store 1 1 [1], .load 1 0 [0]]]

/-- The store-buffer machine completes SB with both loads returning `0`, the hypotheses of the
general theorem hold, and it yields an x86-TSO candidate with paired `rmw`s. -/
theorem sb_weak_explained : ThreadsOk sbP ∧ ThreadCells sbP ∧ ∃ s : XState Nat,
    Run sbP Tso.Litmus.zeroMem s ∧ ∃ x, Explains Exec.Tso sbP Tso.Litmus.zeroMem s x ∧
      RmwPaired x :=
  ⟨Proofs.sb_threadsOk, Proofs.sb_cells, Proofs.sb4, Proofs.sb_run, Proofs.sb_explained⟩

/-- No SC candidate explains that run: the theorem is not secretly an SC result. -/
theorem sb_weak_not_sc : ∃ s : XState Nat, Run sbP Tso.Litmus.zeroMem s ∧
    ∀ x, ¬ Explains Exec.Sc sbP Tso.Litmus.zeroMem s x :=
  ⟨Proofs.sb4, Proofs.sb_run, Proofs.sb_not_sc⟩

/-! ## The cells condition is needed -/

/-- The partial-forwarding program: thread 0 stores the byte `1` at address 0 and loads two
bytes there, thread 1 stores the two bytes `2, 1` there. -/
def partialForwardP : List (List (XEvent Nat)) :=
  [[.store 0 0 [1], .load 0 0 [1, 0]], [.store 1 0 [2, 1]]]

/-- Its threads name themselves, but thread 0 does not have cells. -/
theorem partialForward_shape : ThreadsOk partialForwardP ∧ ¬ ThreadCells partialForwardP :=
  ⟨Proofs.pf_threadsOk, Proofs.pf_not_cells⟩

/-- The store-buffer machine completes a run of it (the load forwards byte 0 from thread 0's
buffer and reads byte 1 from memory), ending with `1` at address 0, and no x86-TSO or XL
candidate explains that run. -/
theorem partialForward_not_explained : ∃ s : XState Nat,
    Run partialForwardP Tso.Litmus.zeroMem s ∧ s.memory 0 = some 1 ∧
      ∀ x, ¬ Explains Exec.Tso partialForwardP Tso.Litmus.zeroMem s x ∧
        ¬ Explains Exec.Xl partialForwardP Tso.Litmus.zeroMem s x :=
  ⟨Proofs.pf5, Proofs.pf_run, Proofs.pf_mem0, fun x => ⟨Proofs.pf_not_tso x, Proofs.pf_not_xl x⟩⟩

/-! ## The converse -/

/-- **ax-TSO ⊆ op-TSO.** Every x86-TSO-consistent candidate that explains a final state
of a well-shaped program (sized `rmw`s, defined initial bytes, paired `rmw` halves, drained
buffers; `ThreadCells` is part of the statement but not used by the proof) is reached by a
complete store-buffer run. Proved below (`axToOp_holds`).

Proof (`Proofs.Conv`): a clock on the units that extends `ghb` and places each locked write one
tick after its read (the docstring plan's `TimedOk` step, done directly on the clock rather than
through `TimedOk`), then one machine action per tick with the state given in closed form.
Per test, the litmus enumerators also prove op = ax outcome sets (`TsoVerdicts.op_eq_ax`). -/
def Task.axToOp : Prop :=
  ∀ (P : List (List (XEvent Nat))) (init : Tso.Mem) (s : XState Nat) (x : Exec),
    ThreadsOk P → ThreadCells P → RmwSized P → InitCovers P init → (∀ t, s.buffer t = []) →
      RmwPaired x → Explains Exec.Tso P init s x → Run P init s

/-- `Task.axToOp` holds. -/
theorem axToOp_holds : Task.axToOp :=
  fun _ _ _ _ hT _ hS hI hd hp hx => Proofs.Conv.axToOp hT hS hI hd hp hx

/-- **ax-TSO ⊆ op-TSO**, without the unused `ThreadCells` hypothesis: mixed-size accesses in
one thread as well as across threads are allowed. -/
theorem ax_explains_run {P : List (List (XEvent Nat))} (hT : ThreadsOk P) (hS : RmwSized P)
    {init : Tso.Mem} (hI : InitCovers P init) {s : XState Nat} (hd : ∀ t, s.buffer t = [])
    {x : Exec} (hp : RmwPaired x) (hx : Explains Exec.Tso P init s x) : Run P init s :=
  Proofs.Conv.axToOp hT hS hI hd hp hx

/-- **op-TSO = ax-TSO, conditional on `Task.axToOp`.** On well-shaped programs, a final state
is reached by a complete store-buffer run iff some x86-TSO candidate with paired `rmw`s
explains it with drained buffers. -/
theorem op_iff_ax_of_task (hTask : Task.axToOp) {P : List (List (XEvent Nat))}
    (hT : ThreadsOk P) (hC : ThreadCells P) (hS : RmwSized P) {init : Tso.Mem}
    (hI : InitCovers P init) (s : XState Nat) :
    Run P init s ↔
      (∀ t, s.buffer t = []) ∧ ∃ x, Explains Exec.Tso P init s x ∧ RmwPaired x := by
  constructor
  · intro h; exact ⟨h.2, run_explains_tso_paired hT hC h⟩
  · rintro ⟨hd, x, hx, hp⟩
    exact hTask P init s x hT hC hS hI hd hp hx

/-- **op-TSO = ax-TSO.** On programs whose events name their thread, whose threads have cells,
whose `rmw`s are sized and whose initial memory covers their footprints, a final state is reached
by a complete store-buffer run iff some x86-TSO candidate with paired `rmw`s explains it with
drained buffers. -/
theorem op_iff_ax {P : List (List (XEvent Nat))} (hT : ThreadsOk P) (hC : ThreadCells P)
    (hS : RmwSized P) {init : Tso.Mem} (hI : InitCovers P init) (s : XState Nat) :
    Run P init s ↔
      (∀ t, s.buffer t = []) ∧ ∃ x, Explains Exec.Tso P init s x ∧ RmwPaired x :=
  op_iff_ax_of_task axToOp_holds hT hC hS hI s

/-! ## Non-vacuity of the converse -/

theorem sb_rmwSized : RmwSized sbP := by
  intro i es h ev hev t a o n he; subst he
  rcases i with _ | _ | i <;> simp [sbP] at h <;> subst h <;> simp at hev

theorem sb_initCovers : InitCovers sbP Tso.Litmus.zeroMem := by
  intro _ _ _ _ _ _ _ _ _ _; rfl

/-- The hypotheses of `Task.axToOp` hold together on a concrete candidate: SB's weak outcome
(both loads `0`, which no SC candidate explains) is explained by a TSO candidate with paired
`rmw`s, and `axToOp_holds` then returns a complete store-buffer run of it. -/
theorem axToOp_nonvacuous : ∃ (s : XState Nat) (x : Exec),
    ThreadsOk sbP ∧ ThreadCells sbP ∧ RmwSized sbP ∧ InitCovers sbP Tso.Litmus.zeroMem ∧
    (∀ t, s.buffer t = []) ∧ RmwPaired x ∧ Explains Exec.Tso sbP Tso.Litmus.zeroMem s x ∧
    (∀ x', ¬ Explains Exec.Sc sbP Tso.Litmus.zeroMem s x') ∧ Run sbP Tso.Litmus.zeroMem s := by
  obtain ⟨x, hx, hp⟩ := Proofs.sb_explained
  have hd := Proofs.sb_run.2
  exact ⟨_, x, Proofs.sb_threadsOk, Proofs.sb_cells, sb_rmwSized, sb_initCovers, hd, hp, hx,
    Proofs.sb_not_sc,
    axToOp_holds _ _ _ _ Proofs.sb_threadsOk Proofs.sb_cells sb_rmwSized sb_initCovers hd hp hx⟩

end Silmaril.X86.MemoryModel.OpAx
