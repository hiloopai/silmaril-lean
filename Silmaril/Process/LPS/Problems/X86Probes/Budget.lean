module

public import Silmaril.Process.LPS.Problems.X86Probes.Basic

/-! # No reachable budget refusal

An agreement statement only speaks about launches on which the plain program is not refused
for budget (`StatementProfile.budgetRefused`): no reachable configuration is an allocation the
classifier refuses or a lazy first touch that cannot be backed. Refuting an agreement
statement therefore needs a launch on which the plain program is *not* budget refused.

`Probe.NoBudget P c`: no configuration reachable from `c` (no refusal filter) is budget
refused. The rules mirror the kit's execution rules (same side conditions, discharged by the
same tactics): an instruction or `syscall` trap step with no lazy mapping is never refused, an
`exit` halts, and a channel `write` keeps the model. The tactics `nb_instr`, `nb_trap`,
`nb_exit` and `nb_write` apply them.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines

namespace Probe

variable (P : Probe)

/-- The native classifier's budget refusal at one configuration of the probe. -/
abbrev BudgetAt (c : Config x86ExtNative) : Prop :=
  BudgetRefusedAtUsing x86ExtNative NativeX86.allocBudgetRefusedB P.segs spec c

/-- No configuration reachable from `c` is budget refused. -/
def NoBudget (c : Config x86ExtNative) : Prop :=
  ∀ trace c', Star P.segs spec noFilter c trace c' → ¬ P.BudgetAt c'

variable {P}

theorem NoBudget.step {c : Config x86ExtNative} (here : ¬ P.BudgetAt c)
    (next : ∀ evs c₁, SStep P.segs spec noFilter c evs (.next c₁) → P.NoBudget c₁) : P.NoBudget c := by
  intro trace c' star
  cases star with
  | refl => exact here
  | step st rest => exact next _ _ st _ _ rest

theorem notBudget_halted {c : Config x86ExtNative} (halted : c.model.halted ≠ none) : ¬ P.BudgetAt c :=
  fun refused => halted refused.1

theorem noBudget_halted {c : Config x86ExtNative} (halted : c.model.halted ≠ none) : P.NoBudget c :=
  NoBudget.step (notBudget_halted halted) fun _ _ st => absurd st.halted_none halted

/-- A configuration with no pending call and no lazy mapping is not budget refused. -/
theorem notBudget_running {memory : Memory} {core : Silmaril.X86.State} {model : Model}
    (lazy : model.vmLazy = []) : ¬ P.BudgetAt (cfgM core memory none model) := by
  rintro ⟨_, ⟨_, report, _, materialized⟩ | ⟨number, pending, _⟩⟩
  · rw [Progress.materializeModelAccesses_noLazy _ _ lazy] at materialized
    cases materialized
  · cases pending

/-- A pending call the classifier does not refuse, whose every outcome either halts or keeps
the process running with no lazy mapping, is not budget refused. -/
theorem notBudget_pending {memory : Memory} {core : Silmaril.X86.State} {n : Word} {model : Model}
    (classify : NativeX86.allocBudgetRefusedB (P.sysInM core memory n) model = false)
    (outcomes : ∀ effect model' events, spec (P.sysInM core memory n) model (.ok effect model' events) →
      model'.halted = none → model'.vmLazy = []) :
    ¬ P.BudgetAt (cfgM core memory (some n) model) := by
  rintro ⟨_, ⟨pending, _⟩ | ⟨number, pending, refused⟩⟩
  · cases pending
  · cases pending
    rcases refused with refusedB | ⟨effect, model', events, outcome, live, materialized⟩
    · change NativeX86.allocBudgetRefusedB (P.sysInM core memory n) model = true at refusedB
      rw [classify] at refusedB
      cases refusedB
    · rw [Progress.materializeModelAccesses_noLazy _ _ (outcomes _ _ _ outcome live)] at materialized
      cases materialized

/-! ## Rules -/

theorem nb_instr {checked : Checked P} {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core P.mem0 len = .ok core' P.mem0)
    (rest : P.NoBudget (P.cfg core' none model)) :
    P.NoBudget (P.cfg core none model) :=
  NoBudget.step (notBudget_running lazy) fun evs c₁ st => by
    obtain ⟨_, same⟩ := (P.sstep_instr_iff running lazy rip fits two notSyscall decoded exec evs _).mp st
    cases same
    exact rest

theorem nb_trap {checked : Checked P} {off : Nat} {core : Silmaril.X86.State} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (defined : (rflagsImage core.flags).isSome = true)
    (rest : P.NoBudget (P.cfg core (some (core.read .rax)) model)) :
    P.NoBudget (P.cfg core none model) :=
  NoBudget.step (notBudget_running lazy) fun evs c₁ st => by
    obtain ⟨_, same⟩ := (P.sstep_trap_iff running lazy rip two isSyscall defined evs _).mp st
    cases same
    exact rest

theorem nb_exit {core : Silmaril.X86.State} {n status : Word} {model : Model} (number : n = 60)
    (_rdi : core.read .rdi = status) (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysIn core n) = false) :
    P.NoBudget (P.cfg core (some n) model) := by
  subst number
  refine NoBudget.step (notBudget_pending (by rfl) fun effect model' events outcome live => ?_) ?_
  · rw [native_exit_iff _ model _ rfl clear] at outcome
    cases outcome
    simp [Model.withHalted, Model.halted] at live
  · intro evs c₁ st
    obtain ⟨_, same⟩ := (P.sstep_exit_iff running clear evs _).mp st
    cases same
    exact noBudget_halted (by simp [Model.withHalted, Model.halted])

theorem nb_write {checked : Checked P} {core : Silmaril.X86.State}
    {n : Word} {model : Model} {off count : Nat} {ch : Word} (number : n = 1)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + off))
    (modeled : modeledRwRangeWith accessOkbX86 (core.read .rsi) (core.read .rdx) = true)
    (nonzeroCount : core.read .rdx ≠ 0)
    (clear : NativeX86.All.boundarySuspect 1 (P.sysIn core n) = false)
    (clamp : rwCountClamp (core.read .rdx) = count) (clampWord : (zw (rwCountClamp (core.read .rdx))).toNat = count)
    (fits : off + count ≤ P.size) (nonempty : (P.bytes.drop off).take count ≠ [])
    (rest : ∀ ds, WritePrefix ((P.bytes.drop off).take count) ds →
      P.NoBudget (P.cfg (resume core (lenWord ds)) none model)) :
    P.NoBudget (P.cfg core (some n) model) := by
  subst number
  refine NoBudget.step (notBudget_pending (by rfl) fun effect model' events outcome _ => ?_) ?_
  · have source : writeSource (P.sysIn core 1).mem ((P.sysIn core 1).arg 1) ((P.sysIn core 1).arg 2) =
        (P.bytes.drop off).take count := by
      change readableBytesAux (viewByte P.mem0 .read) (core.read .rsi)
        (zw (rwCountClamp (core.read .rdx))).toNat = _
      rw [clampWord, buffer]
      exact P.readableBytesAux_mem0 off count fits
    obtain ⟨_, _, same⟩ := (native_write_iff (P.sysIn core 1) model _ rfl clear lookup nonzero modeled
      nonzeroCount source nonempty).mp outcome
    cases same
    exact lazy
  · intro evs c₁ st
    obtain ⟨ds, ⟨delivered, _⟩, _, same⟩ := (P.sstep_write_iff rfl running lazy lookup nonzero buffer modeled
      nonzeroCount clear clamp clampWord fits nonempty evs _).mp st
    cases same
    exact rest ds delivered

end Probe

/-! ## Tactics -/

macro "nb_instr " off:term:max len:term:max instr:term:max : tactic =>
  `(tactic| (apply Probe.nb_instr (off := $off) (len := $len) (instruction := $instr) <;> probe_sides))

macro "nb_trap " off:term:max : tactic =>
  `(tactic| (apply Probe.nb_trap (off := $off) <;> probe_sides))

macro "nb_exit " status:term:max : tactic =>
  `(tactic| (apply Probe.nb_exit (status := $status) <;> probe_sides))

macro "nb_write " off:term:max count:term:max : tactic =>
  `(tactic| (apply Probe.nb_write (off := $off) (count := $count) <;> probe_sides))

end Silmaril.Process.LPS.Probes
