module

public import Silmaril.Process.LPS.Problems.Sha256Cli.ReadStep
public import Silmaril.Process.LPS.Problems.Sha256Cli.Backing

/-! # The descriptor relation and the read obligations (VERIFIED)

`StdRel inp`: LPS keeps the input's file system, descriptor 0 and 1 are channels 0 and 1, the
LPS stdin is the CLI stdin after the cursor, every mapped byte is below `TASK_SIZE`, and every
writable byte is backed. `readObligations`: under `StdRel`, every field of `ReadObligations`
holds. What remains of the bridge is the launch: an LPS launch is related to a CLI `Launch`
(`LaunchSim`).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono

/-- Every mapped byte is below LPS's `TASK_SIZE`. -/
def Below (memory : Silmaril.Process.Memory) : Prop :=
  ∀ (access : Silmaril.Process.Access) (a : Nat), memory.permits access a = true →
    (a : Int) < taskSize

/-- The descriptor relation. -/
structure StdRel (inp : ProcInput) (model : Model) (s : Syscall.State) (_h : List Syscall.Event) :
    Prop where
  fs : model.fs = inp.fs
  fd1 : fdLookup model.fds 1 = some (.channel 1)
  fd0 : fdLookup model.fds 0 = some (.channel 0)
  stdin : ∀ d, s.descriptors 0 = some d → model.stdin = InputStream.drop d.input d.cursor
  below : Below s.memory
  backed : Backed s.memory

theorem permits_of_regions {m m' : Silmaril.Process.Memory} (h : m'.regions = m.regions)
    (access : Silmaril.Process.Access) (a : Nat) : m'.permits access a = m.permits access a := by
  simp [Silmaril.Process.Memory.permits, h]

theorem Below.of_grows {m m' : Silmaril.Process.Memory} (g : Silmaril.X86.Ext.Backing.Grows m m')
    (b : Below m) : Below m' := fun access a p => b access a (by rwa [permits_of_regions g.1] at p)

theorem Backed.of_grows {m m' : Silmaril.Process.Memory} (g : Silmaril.X86.Ext.Backing.Grows m m')
    (b : Backed m) : Backed m' := fun a p => g.2 a (b a (by rwa [permits_of_regions g.1] at p))

theorem grows_of_step {core core' : Silmaril.X86.State} {m m' : Silmaril.Process.Memory}
    (h : CLI.X86Linux.step core m = .retired core' m') : Silmaril.X86.Ext.Backing.Grows m m' := by
  unfold CLI.X86Linux.step at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
    · rename_i instr len _
      unfold CLI.X86Linux.execResult at h
      split at h
      · cases h
        exact Silmaril.X86.Ext.Backing.exec_grows ‹_›
      all_goals cases h

/-- Permitted spans lie below `TASK_SIZE`, so they pass `access_ok`. -/
theorem accessOkb_of_permitted {m : Silmaril.Process.Memory} (below : Below m)
    {access : Silmaril.Process.Access} {buf count : Word}
    (perm : m.Permitted access buf.toNat count.toNat) (pos : 0 < count.toNat) :
    accessOkb buf (uns count) = true := by
  rw [Silmaril.Process.Memory.Permitted, Silmaril.Process.Memory.checkSpan_iff] at perm
  obtain ⟨k, hk⟩ : ∃ k, count.toNat = k + 1 := ⟨count.toNat - 1, by omega⟩
  have last := below access _ (perm.2.2 k (by omega))
  simp only [taskSize] at last
  simp only [accessOkb, accessOkbFor, legacySv48AddressSpace, uns, taskSize, Bool.and_eq_true]
  constructor <;> (apply decide_eq_true; omega)

section Obligations

variable {oracle : Nat → X86FlagChoices.Choice} {refusals : SpuriousCfg} {inp : ProcInput}
  {message : List Byte} {input : CLI.ProcInput}

/-- At a pending `read` that the CLI can complete within the invariant, the descriptor is 0. -/
theorem pend_read_fd {MR : DescRel} {c : Config (machine oracle)} {x : PS} {h : List Syscall.Event}
    (p : PendRel MR c x h) (number : (x.core.read .rax).toNat = 0)
    (safe : Safe CStep (Ok message) (Done input message) x h) :
    ((x.core.read .rdi).setWidth 32).toNat = 0 := by
  obtain ⟨e, y, s⟩ := safe.2.1
  have reads : ReadsOnlyStdin (h ++ e) := by
    rcases safe.2.2 _ _ s with ok | done
    · exact ok.2.2.1
    · exact done.2.2.2
  obtain ⟨d, flags, -, -, -, cases⟩ := cli_read_cases p number s
  rcases cases with ⟨bytes, memory', -, -, -, -, -, rfl, -⟩ | ⟨-, rfl, -⟩
  · exact reads _ bytes (List.mem_append_right _ (List.mem_singleton_self _))
  · exact reads _ [] (List.mem_append_right _ (List.mem_singleton_self _))

/-- `pend_read` under `StdRel`. -/
theorem pend_read_std {c : Config (machine oracle)} {x : PS} {h : List Syscall.Event}
    (p : PendRel (StdRel inp) c x h) (safe : Safe CStep (Ok message) (Done input message) x h)
    (number : (x.core.read .rax).toNat = 0) :
    (∀ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c evs st →
      ∃ c', st = .next c' ∧ ∃ es y, CStep x es y ∧ evs = es.flatMap (evFlat inp.fs) ∧
        Rel (StdRel inp) c' y (h ++ es)) ∧
    (∃ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c evs st) ∧
    (∃ es y, CStep x es y ∧ ∃ c', SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c (es.flatMap (evFlat inp.fs)) (.next c') ∧
        Rel (StdRel inp) c' y (h ++ es)) := by
  have fd0 := pend_read_fd p number safe
  have r := p.model
  obtain ⟨e, y, s₀⟩ := safe.2.1
  obtain ⟨d, flags, -, -, accessible, -⟩ := cli_read_cases p number s₀
  have args : ReadArgs x := safe.1.2.2.2.2.2.2
  have pos : 0 < (x.core.read .rdx).toNat :=
    args { x.core with rip := x.core.rip + 2 } (cli_step_trap p.trap) number
  have ok := accessOkb_of_permitted r.below accessible pos
  refine pend_read p number fd0 r.fd0 r.stdin ok r.backed ?_ ?_ ⟨e, y, s₀⟩
  · intro d bs memory' open0 written
    have g := Silmaril.X86.Ext.Backing.Grows.of_stored
      (Silmaril.X86.Ext.Stored.of_writeBytes written)
    refine ⟨r.fs, r.fd1, r.fd0, ?_, r.below.of_grows g, r.backed.of_grows g⟩
    intro d' open0'
    simp only [Syscall.State.setDescriptor, Function.update_self, Option.some.injEq] at open0'
    subst open0'
    rfl
  · exact ⟨r.fs, r.fd1, r.fd0, r.stdin, r.below, r.backed⟩

/-- **The read obligations hold under `StdRel`.** -/
theorem readObligations : ReadObligations oracle refusals inp message input (StdRel inp) where
  retire := by
    intro model s h core core' memory' r step
    have g := grows_of_step step
    exact { r with below := r.below.of_grows g, backed := r.backed.of_grows g }
  fs := fun r => r.fs
  stdout := fun r => r.fd1
  modeled := by
    intro model s h buf count bytes r read
    unfold modeledRwRangeWith
    by_cases small : uns count ≤ rwBytesMax
    · simp [modeledRwCount, small]
    · have pos : 0 < count.toNat := by
        unfold uns rwBytesMax at small; omega
      have perm := (Silmaril.X86.Memory.readWith_eq_some_iff.mp read).2.1
      simp [accessOkb_of_permitted r.below perm pos]
  keepWrite := by
    intro model s h d bs r open1
    refine ⟨r.fs, r.fd1, r.fd0, ?_, r.below, r.backed⟩
    intro d' open0
    apply r.stdin
    simpa [Syscall.State.setDescriptor] using open0
  step := fun p safe number s => (pend_read_std p safe number).1 _ _ s
  progress := fun p safe number => (pend_read_std p safe number).2.1
  back := fun p safe number => (pend_read_std p safe number).2.2

end Obligations

/-! ## What remains: the launch -/

/-- An LPS launch related to a CLI launch under `StdRel`. -/
def LaunchSim (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) (message : List Byte) : Prop :=
  ∃ (input : CLI.ProcInput) (x₀ : PS), input.stdin = .ofList message ∧ input.Valid ∧
    Launch input x₀ ∧ Rel (StdRel inp) (initial oracle limit en inp) x₀ []

/-- The launch obligation: every admissible LPS launch of the pinned ELF is related to a CLI
launch of the chain's image. -/
def LaunchObligation : Prop :=
  ∀ oracle limit en inp message, Admissible oracle en inp message →
    LaunchSim oracle limit en inp message

/-- **Reduction (VERIFIED).** The launch obligation gives the read obligation. -/
theorem readSim_of_launch (h : LaunchObligation) :
    ∀ oracle refusals limit en inp message, Admissible oracle en inp message →
      ReadSimAt oracle refusals limit en inp message := by
  intro oracle refusals limit en inp message admissible
  obtain ⟨input, x₀, stdin, valid, launch, related⟩ := h oracle limit en inp message admissible
  exact ⟨input, x₀, StdRel inp, stdin, valid, launch, related, readObligations⟩

end Silmaril.Process.LPS.Problems.Sha256Cli
