module

public import Silmaril.Process.LPS.Machines.X86MuslStartup

/-! # Stepping the actual LPS x86 machine over a concrete launch

Tools for proving that the actual `SStep` relation of the flag-oracle Wire+REP
STOSQ option (`x86WireDf0RepStosqWithFlagOracle`) takes a concrete launch
through a long, explicitly listed sequence of states.

The byte memory of a process is a `Std.ExtHashMap`, whose lookups do not
reduce in the kernel. A step is therefore evaluated in two halves:

* Every memory *read* (instruction fetch, data load, `pop`, `ret`) is
  rewritten by `readWith_eq` into `readWithV`, a read through a `View`, an
  ordinary function `Nat → Option Byte` that the kernel computes. `Realizes B v`
  states that the hash map `B` has exactly the bytes of `v`; it is proved once
  for the launch memory and carried across stores by `Realizes.install`.
* Everything else, including stores, is ordinary kernel evaluation: a store
  leaves `Memory.install B address bytes` in the state without inspecting `B`.

Register files are closures; `normCore` rebuilds one as a table of sixteen
values so that a successor state can be compared with an explicit one.
`normCore_eq` shows this changes nothing.

Each lemma below has the actual `stepUsing (X86RepStosq.step platform) oracle`
or `SStep` on its left; nothing here is a separate model of execution.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines.X86MuslRun

open Silmaril.Process (Memory ByteMemory Region Access)
open Silmaril.X86 (Reg)

abbrev Byte := Silmaril.Process.Byte

/-! ## Byte views -/

/-- A byte memory as a computable function. -/
abbrev View := Nat → Option Byte

/-- The view after `Memory.install`. -/
def installView (v : View) (base : Nat) (bytes : List Byte) : View :=
  fun a => if base ≤ a ∧ a < base + bytes.length then bytes[a - base]? else v a

/-- The hash map `B` holds exactly the bytes of `v`. -/
def Realizes (B : ByteMemory) (v : View) : Prop := ∀ a, B.get? a = v a

theorem Realizes.install {B : ByteMemory} {v : View} (h : Realizes B v) (base : Nat)
    (bytes : List Byte) : Realizes (Memory.install B base bytes) (installView v base bytes) := by
  intro a
  unfold installView
  by_cases inside : base ≤ a ∧ a < base + bytes.length
  · rw [ite_eq_left_iff.mpr (fun outside => absurd inside outside)]
    obtain ⟨i, rfl⟩ : ∃ i, a = base + i := ⟨a - base, by omega⟩
    rw [Memory.install_get _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem]
  · rw [ite_eq_right_iff.mpr (fun within => absurd within inside),
      Memory.install_outside _ _ _ _ (by omega)]
    exact h a

/-- `Memory.readBacking` over a view. -/
def readBackingV (v : View) (a : Nat) : Nat → Option (List Byte)
  | 0 => some []
  | n + 1 => do
      let byte ← v a
      let tail ← readBackingV v (a + 1) n
      pure (byte :: tail)

theorem readBacking_eq {B : ByteMemory} {v : View} (h : Realizes B v) (a n : Nat) :
    Memory.readBacking B a n = readBackingV v a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [Memory.readBacking, readBackingV, h a, ih]

/-- `Memory.readWith` over a view; permissions depend only on the regions. -/
def readWithV (R : List Region) (v : View) (access : Access) (a n : Nat) :
    Option (List Byte) :=
  if (Memory.mk R ∅).checkSpan access a n then readBackingV v a n else none

theorem readWith_eq {R : List Region} {B : ByteMemory} {v : View} (h : Realizes B v)
    (access : Access) (a n : Nat) :
    Memory.readWith ⟨R, B⟩ access a n = readWithV R v access a n := by
  simp only [Memory.readWith, readWithV, readBacking_eq h]
  rfl

/-! ## Register tables -/

/-- A register file given as a table of the sixteen general registers. -/
def canonRegs (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Silmaril.X86.Word) :
    Reg → Silmaril.X86.Word
  | .rax => a0 | .rcx => a1 | .rdx => a2 | .rbx => a3 | .rsp => a4 | .rbp => a5 | .rsi => a6
  | .rdi => a7 | .r8 => a8 | .r9 => a9 | .r10 => a10 | .r11 => a11 | .r12 => a12 | .r13 => a13
  | .r14 => a14 | .r15 => a15

def normCore (s : Silmaril.X86.State) : Silmaril.X86.State :=
  { regs := canonRegs (s.regs .rax) (s.regs .rcx) (s.regs .rdx) (s.regs .rbx) (s.regs .rsp)
      (s.regs .rbp) (s.regs .rsi) (s.regs .rdi) (s.regs .r8) (s.regs .r9) (s.regs .r10)
      (s.regs .r11) (s.regs .r12) (s.regs .r13) (s.regs .r14) (s.regs .r15)
    rip := s.rip, flags := s.flags, fsBase := s.fsBase }

theorem normCore_eq (s : Silmaril.X86.State) : normCore s = s := by
  cases s with
  | mk regs rip flags fsBase =>
    simp only [normCore, Silmaril.X86.State.mk.injEq, and_true]
    funext r
    cases r <;> rfl

def normResult : Silmaril.X86.Ext.Result → Silmaril.X86.Ext.Result
  | .ok c m => .ok (normCore c) m
  | r => r

theorem normResult_eq (r : Silmaril.X86.Ext.Result) : normResult r = r := by
  cases r <;> simp [normResult, normCore_eq]

/-- Normalize the successor of a native machine result. -/
def normMachine : MachineResult (AccessReport X86State) → MachineResult (AccessReport X86State)
  | .ok ⟨⟨⟨c, m⟩, p⟩, accesses⟩ => .ok ⟨⟨⟨normCore c, m⟩, p⟩, accesses⟩
  | r => r

theorem normMachine_eq (r : MachineResult (AccessReport X86State)) : normMachine r = r := by
  rcases r with ⟨⟨⟨⟨c, m⟩, p⟩, accesses⟩⟩ | _ | _ <;> simp [normMachine, normCore_eq]

/-! ## Steps of the flag-oracle Wire+REP STOSQ option -/

/-- The option the run is about. -/
abbrev Isa (platform : Silmaril.X86.Ext.Wire.Platform) (oracle : Nat → X86FlagChoices.Choice) :
    UserIsa :=
  x86WireDf0RepStosqWithFlagOracle platform oracle

/-- A configuration of that option. -/
abbrev cfg (platform : Silmaril.X86.Ext.Wire.Platform) (oracle : Nat → X86FlagChoices.Choice)
    (state : X86FlagChoices.State) (model : Model) : Config (Isa platform oracle) :=
  ⟨state, model⟩

/-- A successful machine step, with whatever access report it makes. -/
def Next (isa : UserIsa) (segments : List Segment) (state next : isa.State) : Prop :=
  ∃ accesses, isa.step segments state = .ok ⟨next, accesses⟩

/-- The concrete states used here: no pending syscall. -/
def running (core : Silmaril.X86.State) (R : List Region) (B : ByteMemory) (counter : Nat) :
    X86FlagChoices.State :=
  ⟨⟨⟨core, ⟨R, B⟩⟩, none⟩, counter⟩

open Silmaril.X86 in
/-- An ordinary Wire instruction, fetched and decoded through a view. -/
theorem wire_step {platform : Ext.Wire.Platform} {oracle : Nat → X86FlagChoices.Choice}
    {segments : List Segment} {core core' : State} {R : List Region} {B : ByteMemory}
    {v : View} {c : Nat} {d : Ext.Wire.Decoded} {bytes : List Byte} {mem' : Memory}
    (hv : Realizes B v)
    (f3 : readWithV R v .execute core.rip.toNat 3 ≠ some X86RepStosq.bytes)
    (f2 : readWithV R v .execute core.rip.toNat 2 ≠ some [0x0f, 0x05])
    (fd : readWithV R v .execute core.rip.toNat d.length = some bytes)
    (dec : Ext.Wire.decode bytes = some d)
    (ex : normResult (Ext.Wire.exec platform d core ⟨R, B⟩) = .ok core' mem') :
    Next (x86WireDf0RepStosqWithFlagOracle platform oracle) segments
      (running core R B c) ⟨⟨⟨core', mem'⟩, none⟩, c⟩ := by
  rw [normResult_eq] at ex
  have f2' : Memory.fetchBytes ⟨R, B⟩ core.rip.toNat 2 ≠ some [0x0f, 0x05] := by
    rw [Memory.fetchBytes, readWith_eq hv]; exact f2
  have f3' : Memory.fetchBytes ⟨R, B⟩ core.rip.toNat 3 ≠ some X86RepStosq.bytes := by
    rw [Memory.fetchBytes, readWith_eq hv]; exact f3
  have fetched : Ext.Wire.fetch ⟨R, B⟩ core.rip.toNat = .decoded d :=
    Ext.Wire.fetch_eq_decoded_iff.mpr
      ⟨bytes, by rw [Memory.fetchBytes, readWith_eq hv]; exact fd, dec⟩
  refine ⟨(core.rip, d.length) :: X86Accesses.wire core d, ?_⟩
  change X86FlagOracle.stepUsing (X86RepStosq.step platform) oracle _ = _
  rw [X86FlagOracle.not_syscall _ _ _ f2']
  change X86FlagChoices.lift c (X86RepStosq.step platform ⟨⟨core, ⟨R, B⟩⟩, none⟩) = _
  rw [X86RepStosq.step_eq_wire _ _ f3']
  unfold x86WireStep
  rw [ite_eq_right f2', fetched]
  simp only [ex, x86ExecResult]
  rfl

open Silmaril.X86 in
/-- One DF=0 REP STOSQ microstep, fetched through a view. -/
theorem rep_step {platform : Ext.Wire.Platform} {oracle : Nat → X86FlagChoices.Choice}
    {segments : List Segment} {core core' : State} {R : List Region} {B : ByteMemory}
    {v : View} {c : Nat} {mem' : Memory} {accesses : List (Word × Nat)}
    (hv : Realizes B v)
    (f3 : readWithV R v .execute core.rip.toNat 3 = some X86RepStosq.bytes)
    (ex : normMachine (X86RepStosq.iterate ⟨⟨core, ⟨R, B⟩⟩, none⟩) =
      .ok ⟨⟨⟨core', mem'⟩, none⟩, accesses⟩) :
    Next (x86WireDf0RepStosqWithFlagOracle platform oracle) segments
      (running core R B c) ⟨⟨⟨core', mem'⟩, none⟩, c⟩ := by
  rw [normMachine_eq] at ex
  have f3' : Memory.fetchBytes ⟨R, B⟩ core.rip.toNat 3 = some X86RepStosq.bytes := by
    rw [Memory.fetchBytes, readWith_eq hv]; exact f3
  have f2' : Memory.fetchBytes ⟨R, B⟩ core.rip.toNat 2 ≠ some [0x0f, 0x05] := by
    intro syscall
    exact X86FlagOracle.syscall_not_rep ⟨⟨core, ⟨R, B⟩⟩, none⟩ syscall f3'
  refine ⟨accesses, ?_⟩
  change X86FlagOracle.stepUsing (X86RepStosq.step platform) oracle _ = _
  rw [X86FlagOracle.not_syscall _ _ _ f2']
  change X86FlagChoices.lift c (X86RepStosq.step platform ⟨⟨core, ⟨R, B⟩⟩, none⟩) = _
  rw [X86RepStosq.step_rep _ _ f3', ex]
  rfl

open Silmaril.X86 in
/-- The instruction step at a fetched SYSCALL: the oracle completes undefined
flags and the native number in RAX becomes pending. -/
theorem syscall_step {platform : Ext.Wire.Platform} {oracle : Nat → X86FlagChoices.Choice}
    {segments : List Segment} {core core' : State} {R : List Region} {B : ByteMemory}
    {v : View} {c : Nat} {flags : Flags}
    (hv : Realizes B v)
    (f2 : readWithV R v .execute core.rip.toNat 2 = some [0x0f, 0x05])
    (completed : X86FlagChoices.completeFlags core.flags (oracle c) = flags)
    (ex : normCore { core with flags := flags } = core') :
    Next (x86WireDf0RepStosqWithFlagOracle platform oracle) segments
      (running core R B c) ⟨⟨⟨core', ⟨R, B⟩⟩, some (core.read .rax)⟩, c + 1⟩ := by
  rw [normCore_eq] at ex
  subst ex
  have f2' : Memory.fetchBytes ⟨R, B⟩ core.rip.toNat 2 = some [0x0f, 0x05] := by
    rw [Memory.fetchBytes, readWith_eq hv]; exact f2
  refine ⟨[(core.rip, 2)], ?_⟩
  change X86FlagOracle.stepUsing (X86RepStosq.step platform) oracle (running core R B c) = _
  rw [X86FlagOracle.rep_every_oracle_syscall platform oracle (running core R B c) f2']
  simp only [running, X86FlagChoices.completeState, completed]
  rfl

/-! ## Assembling runs of the actual `SStep` relation -/

section Star

variable {isa : UserIsa} {segments : List Segment} {spec : Sys SyscallEffect}
  {refused : RefusalFilter}

/-- An instruction transition of `SStep`, in front of a run. -/
theorem star_instr {state next : isa.State} {model : Model} {trace : List Event}
    {final : Config isa} (halted : model.halted = none) (lazy : model.vmLazy = [])
    (pending : isa.svcPending state = none) (step : Next isa segments state next)
    (rest : Star segments spec refused ⟨next, model⟩ trace final) :
    Star segments spec refused ⟨state, model⟩ trace final := by
  obtain ⟨accesses, step⟩ := step
  exact Star.step (evs := []) (SStep.instr halted pending
    (Progress.accountStep_of_noLazy _ _ _ _ lazy step)) rest

/-- Runs compose. -/
theorem star_append {first middle last : Config isa} {trace rest : List Event}
    (head : Star segments spec refused first trace middle)
    (tail : Star segments spec refused middle rest last) :
    Star segments spec refused first (trace ++ rest) last := by
  induction head with
  | refl => exact tail
  | step step _ ih => rw [List.append_assoc]; exact Star.step step (ih tail)

end Star

open Silmaril.X86 in
/-- A syscall transition of `SStep` for a pending native number, in front of
a run: the specification's effect is applied and RIP moves past SYSCALL. -/
theorem star_syscall {platform : Ext.Wire.Platform} {oracle : Nat → X86FlagChoices.Choice}
    {segments : List Segment} {spec : Sys SyscallEffect} {refused : RefusalFilter}
    {core core' : State} {R : List Region} {B : ByteMemory} {c : Nat} {x8 : Word}
    {model model' model'' : Model} {eff : SyscallEffect} {events trace : List Event}
    {final : Config (Isa platform oracle)}
    (halted : model.halted = none)
    (specified : spec (sysInput (Isa platform oracle) segments
      ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ x8) model (.ok eff model' events))
    (notRefused : ¬ refused (sysInput (Isa platform oracle) segments
      ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ x8) model eff)
    (halted' : model'.halted = none)
    (materialized : materializeModelAccesses model' (syscallEffectAccesses eff) = some model'')
    (memoryEffect : applyMemoryEffect ⟨R, B⟩ eff = ⟨R, B⟩)
    (next : normCore (x86AdvancePastSvc
      (x86ApplyEffectNative ⟨⟨core, ⟨R, B⟩⟩, some x8⟩ eff)).m.core = core')
    (rest : Star segments spec refused (cfg platform oracle (running core' R B c) model'')
      trace final) :
    Star segments spec refused (cfg platform oracle ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ model)
      (events ++ trace) final := by
  have state : (Isa platform oracle).advancePastSvc ((Isa platform oracle).applyEffect
      ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ eff) = running core' R B c := by
    rw [← next, normCore_eq]
    change (⟨x86AdvancePastSvc (x86ApplyEffectNative ⟨⟨core, ⟨R, B⟩⟩, some x8⟩ eff), c⟩ :
      X86FlagChoices.State) = _
    simp only [x86AdvancePastSvc, x86ApplyEffectNative, memoryEffect, running]
  have step := SStep.syscall (isa := Isa platform oracle) (segs := segments) (spec := spec)
    (refused := refused) halted rfl specified notRefused halted' materialized
  rw [state] at step
  exact Star.step step rest


/-! ## Overlays: a symbolic span over a concrete view

A value the environment chooses (here the thread id `set_tid_address` returns)
is stored in memory as symbolic bytes. `overlay base n bytes v` is the view `v`
with the `n` bytes at `base` replaced by `bytes`; every read that stays away
from those bytes is a read of `v`, which the kernel computes. -/

/-- `v` with the `n` bytes at `base` replaced by `bytes`. -/
def overlay (base n : Nat) (bytes : List Byte) (v : View) : View :=
  fun a => if base ≤ a ∧ a < base + n then bytes[a - base]? else v a

/-- Storing `bytes` over a span the view held as `old`: the memory realizes the
old view with `bytes` overlaid. -/
theorem Realizes.installOverlay {B : ByteMemory} {v : View} {n : Nat} (h : Realizes B v)
    (base : Nat) (old bytes : List Byte) (shorter : old.length ≤ bytes.length)
    (length : bytes.length = n) :
    Realizes (Memory.install B base bytes) (overlay base n bytes (installView v base old)) := by
  subst length
  intro a
  rw [(h.install base bytes) a]
  by_cases inside : base ≤ a ∧ a < base + bytes.length
  · simp only [installView, overlay, inside, and_self, ↓reduceIte]
  · have outside : ¬ (base ≤ a ∧ a < base + old.length) := by omega
    simp only [installView, overlay, inside, outside, ↓reduceIte]

/-- A store away from the overlaid span commutes with the overlay. -/
theorem Realizes.installUnder {B : ByteMemory} {v : View} {a n : Nat} {xs : List Byte}
    (h : Realizes B (overlay a n xs v)) (base : Nat) (bytes : List Byte)
    (apart : base + bytes.length ≤ a ∨ a + n ≤ base) :
    Realizes (Memory.install B base bytes) (overlay a n xs (installView v base bytes)) := by
  intro x
  rw [(h.install base bytes) x]
  by_cases stored : base ≤ x ∧ x < base + bytes.length
  · have away : ¬ (a ≤ x ∧ x < a + n) := by omega
    simp only [installView, overlay, stored, away, ↓reduceIte]
  · simp only [installView, overlay, stored, ↓reduceIte]

theorem readBackingV_overlay (v : View) (base n : Nat) (xs : List Byte) (a k : Nat)
    (apart : a + k ≤ base ∨ base + n ≤ a) :
    readBackingV (overlay base n xs v) a k = readBackingV v a k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    have here : overlay base n xs v a = v a := by
      have away : ¬ (base ≤ a ∧ a < base + n) := by omega
      simp only [overlay, away, ↓reduceIte]
    simp only [readBackingV, here, ih (a + 1) (by omega)]

/-- A read away from the overlaid span is a read of the underlying view. -/
theorem readWithV_overlay (R : List Region) (v : View) (base n : Nat) (xs : List Byte)
    (access : Access) (a k : Nat) (apart : a + k ≤ base ∨ base + n ≤ a) :
    readWithV R (overlay base n xs v) access a k = readWithV R v access a k := by
  simp only [readWithV, readBackingV_overlay v base n xs a k apart]

/-- The four bytes a 32-bit store of a register holding `tid` writes
(`mov %eax, m32`: `Sz.read .d`, then `storeN` of the zero-extended value). -/
def tidBytes (tid : Silmaril.X86.Word) : List Byte :=
  Silmaril.X86.Ext.leBytes ((tid.setWidth 32).setWidth 64) 4

theorem tidBytes_length (tid : Silmaril.X86.Word) : (tidBytes tid).length = 4 :=
  Silmaril.X86.Ext.length_leBytes _ _

open Silmaril.X86 in
/-- `wire_step` with the fetch obligations at a literal RIP, for cores that
hold a symbolic value elsewhere. -/
theorem wire_step_at {platform : Ext.Wire.Platform} {oracle : Nat → X86FlagChoices.Choice}
    {segments : List Segment} {core core' : State} {R : List Region} {B : ByteMemory}
    {v : View} {c : Nat} {d : Ext.Wire.Decoded} {bytes : List Byte} {mem' : Memory}
    (rip : Word) (hrip : core.rip = rip) (hv : Realizes B v)
    (f3 : readWithV R v .execute rip.toNat 3 ≠ some X86RepStosq.bytes)
    (f2 : readWithV R v .execute rip.toNat 2 ≠ some [0x0f, 0x05])
    (fd : readWithV R v .execute rip.toNat d.length = some bytes)
    (dec : Ext.Wire.decode bytes = some d)
    (ex : normResult (Ext.Wire.exec platform d core ⟨R, B⟩) = .ok core' mem') :
    Next (x86WireDf0RepStosqWithFlagOracle platform oracle) segments
      (running core R B c) ⟨⟨⟨core', mem'⟩, none⟩, c⟩ := by
  subst hrip
  exact wire_step hv f3 f2 fd dec ex

open Silmaril.X86 in
/-- `wire_step_at` over a memory with an overlaid symbolic span: the
instruction is fetched from the underlying concrete view, away from the span. -/
theorem wire_stepT {platform : Ext.Wire.Platform} {oracle : Nat → X86FlagChoices.Choice}
    {segments : List Segment} {core core' : State} {R : List Region} {B : ByteMemory}
    {v : View} {base : Nat} {xs : List Byte} {c : Nat} {d : Ext.Wire.Decoded}
    {bytes : List Byte} {mem' : Memory}
    (rip : Word) (hrip : core.rip = rip) (hv : Realizes B (overlay base 4 xs v))
    (far : rip.toNat + 15 ≤ base ∨ base + 4 ≤ rip.toNat) (short : d.length ≤ 15)
    (f3 : readWithV R v .execute rip.toNat 3 ≠ some X86RepStosq.bytes)
    (f2 : readWithV R v .execute rip.toNat 2 ≠ some [0x0f, 0x05])
    (fd : readWithV R v .execute rip.toNat d.length = some bytes)
    (dec : Ext.Wire.decode bytes = some d)
    (ex : normResult (Ext.Wire.exec platform d core ⟨R, B⟩) = .ok core' mem') :
    Next (x86WireDf0RepStosqWithFlagOracle platform oracle) segments
      (running core R B c) ⟨⟨⟨core', mem'⟩, none⟩, c⟩ :=
  wire_step_at rip hrip hv
    (by rw [readWithV_overlay _ _ _ _ _ _ _ _ (by omega)]; exact f3)
    (by rw [readWithV_overlay _ _ _ _ _ _ _ _ (by omega)]; exact f2)
    (by rw [readWithV_overlay _ _ _ _ _ _ _ _ (by omega)]; exact fd) dec ex

/-! ## Funnels: every execution passes through a target set

`Funnel segments spec refused T c`: from `c`, every execution reaches `T`
silently. Until it does, each configuration has a successor, and every
`SStep` from it is silent and goes to a configuration that is again funneled;
none goes to `SError`. The relation is inductive, so there is no infinite
execution that avoids `T` (`Funnel.no_divergence`). `funnel_instr` builds one
from a deterministic instruction step, `funnel_syscall` from a syscall whose
specified outcomes are all enumerated. -/

section Funnel

variable {isa : UserIsa} {segments : List Segment} {spec : Sys SyscallEffect}
  {refused : RefusalFilter}

/-- Every execution from the configuration reaches `T` with no events, and
none before that errors, is stuck or diverges. -/
inductive Funnel (segments : List Segment) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (T : Config isa → Prop) : Config isa → Prop where
  | done {c} : T c → Funnel segments spec refused T c
  | step {c} :
      (∃ evs c', SStep segments spec refused c evs (.next c')) →
      (∀ evs, ¬ SStep segments spec refused c evs .error) →
      (∀ evs c', SStep segments spec refused c evs (.next c') → evs = []) →
      (∀ evs c', SStep segments spec refused c evs (.next c') →
        Funnel segments spec refused T c') →
      Funnel segments spec refused T c

/-- A funneled configuration reaches `T`. -/
theorem Funnel.reaches {T : Config isa → Prop} {c : Config isa}
    (h : Funnel segments spec refused T c) :
    ∃ m, T m ∧ Star segments spec refused c [] m := by
  induction h with
  | done t => exact ⟨_, t, Star.refl _⟩
  | step progress _ silent _ ih =>
    obtain ⟨evs, c', st⟩ := progress
    obtain ⟨m, t, run⟩ := ih evs c' st
    have e := silent evs c' st
    subst e
    exact ⟨m, t, Star.step st run⟩

/-- Every execution from a funneled configuration either is still before `T`
(no events yet, and funneled) or has passed through `T` silently. -/
theorem Funnel.cover {T : Config isa → Prop} {c final : Config isa} {trace : List Event}
    (h : Funnel segments spec refused T c) (run : Star segments spec refused c trace final) :
    (trace = [] ∧ Funnel segments spec refused T final) ∨
      ∃ m, T m ∧ Star segments spec refused c [] m ∧ Star segments spec refused m trace final := by
  induction h generalizing trace final with
  | done t => exact .inr ⟨_, t, Star.refl _, run⟩
  | step progress noError silent rest ih =>
    cases run with
    | refl => exact .inl ⟨rfl, Funnel.step progress noError silent rest⟩
    | step st run' =>
      have e := silent _ _ st
      subst e
      rcases ih _ _ st run' with ⟨empty, funneled⟩ | ⟨m, t, first, second⟩
      · exact .inl ⟨by simp [empty], funneled⟩
      · exact .inr ⟨m, t, Star.step st first, by simpa using second⟩

/-- Every `SError` reachable from a funneled configuration is reached after `T`. -/
theorem Funnel.error_after {T : Config isa → Prop} {c final : Config isa} {trace evs : List Event}
    (h : Funnel segments spec refused T c) (run : Star segments spec refused c trace final)
    (error : SStep segments spec refused final evs .error) :
    ∃ m, T m ∧ Star segments spec refused c [] m ∧ Star segments spec refused m trace final := by
  rcases h.cover run with ⟨empty, funneled⟩ | passed
  · subst empty
    cases funneled with
    | done t => exact ⟨final, t, run, Star.refl _⟩
    | step _ noError _ _ => exact absurd error (noError evs)
  · exact passed

/-- No infinite execution from a funneled configuration avoids `T`. -/
theorem Funnel.no_divergence {T : Config isa → Prop} {c : Config isa}
    (h : Funnel segments spec refused T c) (seq : Nat → Config isa) (start : seq 0 = c)
    (steps : ∀ n, ∃ evs, SStep segments spec refused (seq n) evs (.next (seq (n + 1)))) :
    ∃ n, T (seq n) := by
  induction h generalizing seq with
  | done t => exact ⟨0, start ▸ t⟩
  | step _ _ _ _ ih =>
    obtain ⟨evs, st⟩ := steps 0
    rw [start] at st
    obtain ⟨n, t⟩ := ih evs (seq 1) st (fun n => seq (n + 1)) rfl (fun n => steps (n + 1))
    exact ⟨n + 1, t⟩

/-- A deterministic instruction step in front of a funnel: the only `SStep`
from a running configuration whose machine step succeeds is that step. -/
theorem funnel_instr {T : Config isa → Prop} {state next : isa.State} {model : Model}
    (halted : model.halted = none) (lazy : model.vmLazy = [])
    (pending : isa.svcPending state = none) (step : Next isa segments state next)
    (rest : Funnel segments spec refused T ⟨next, model⟩) :
    Funnel segments spec refused T ⟨state, model⟩ := by
  obtain ⟨accesses, step⟩ := step
  have account := Progress.accountStep_of_noLazy _ _ _ _ lazy step
  refine Funnel.step ⟨[], _, SStep.instr halted pending account⟩ ?_ ?_ ?_
  · intro evs st
    cases st with
    | instrFault _ _ fault => rw [account] at fault; cases fault
    | instrUnmodeled _ _ unmodeled => rw [account] at unmodeled; cases unmodeled
    | syscallMaterializationFault _ p => rw [pending] at p; cases p
    | syscallUnmodeled _ p => rw [pending] at p; cases p
  · intro evs c' st
    cases st with
    | instr => rfl
    | syscall _ p => rw [pending] at p; cases p
    | exit _ p => rw [pending] at p; cases p
    | killed _ p => rw [pending] at p; cases p
  · intro evs c' st
    cases st with
    | instr _ _ other =>
      rw [account] at other
      cases other
      exact rest
    | syscall _ p => rw [pending] at p; cases p
    | exit _ p => rw [pending] at p; cases p
    | killed _ p => rw [pending] at p; cases p

theorem killedBy_of_halted {model : Model} (halted : model.halted = none) :
    model.killedBy = none := by
  unfold Model.killedBy
  split
  · exact halted
  · rfl

/-- A pending syscall in front of funnels: when the specification's outcomes
at this input are all enumerated (each a silent, running, not refused success
with no lazy pages), every `SStep` is the syscall transition to one of them. -/
theorem funnel_syscall {T : Config isa → Prop} {ms : isa.State} {model : Model} {x8 : Word}
    (halted : model.halted = none) (pending : isa.svcPending ms = some x8)
    (exists_ : ∃ o, spec (sysInput isa segments ms x8) model o)
    (outcomes : ∀ o, spec (sysInput isa segments ms x8) model o →
      ∃ eff model', o = .ok eff model' [] ∧ model'.halted = none ∧ model'.vmLazy = [] ∧
        ¬ refused (sysInput isa segments ms x8) model eff ∧
        Funnel segments spec refused T ⟨isa.advancePastSvc (isa.applyEffect ms eff), model'⟩) :
    Funnel segments spec refused T ⟨ms, model⟩ := by
  refine Funnel.step ?_ ?_ ?_ ?_
  · obtain ⟨o, so⟩ := exists_
    obtain ⟨eff, model', rfl, halted', lazy, notRefused, _⟩ := outcomes o so
    exact ⟨[], _, SStep.syscall halted pending so notRefused halted'
      (Progress.materializeModelAccesses_noLazy _ _ lazy)⟩
  · intro evs st
    cases st with
    | instrFault _ p => rw [pending] at p; cases p
    | instrUnmodeled _ p => rw [pending] at p; cases p
    | syscallMaterializationFault _ p so _ _ fault =>
      rw [pending] at p; cases p
      obtain ⟨eff, model', e, _, lazy, _⟩ := outcomes _ so
      cases e
      rw [Progress.materializeModelAccesses_noLazy _ _ lazy] at fault
      cases fault
    | syscallUnmodeled _ p so =>
      rw [pending] at p; cases p
      obtain ⟨eff, model', e, _⟩ := outcomes _ so
      cases e
  · intro evs c' st
    cases st with
    | instr => rfl
    | syscall _ p so _ _ _ =>
      rw [pending] at p; cases p
      obtain ⟨eff, model', e, _⟩ := outcomes _ so
      cases e
      rfl
    | exit _ p so stopped =>
      rw [pending] at p; cases p
      obtain ⟨eff, model', e, running, _⟩ := outcomes _ so
      cases e
      rw [running] at stopped; cases stopped
    | killed _ p so killed =>
      rw [pending] at p; cases p
      obtain ⟨eff, model', e, running, _⟩ := outcomes _ so
      cases e
      rw [killedBy_of_halted running] at killed; cases killed
  · intro evs c' st
    cases st with
    | instr _ p => rw [pending] at p; cases p
    | syscall _ p so _ _ materialized =>
      rw [pending] at p; cases p
      obtain ⟨eff, model', e, _, lazy, _, rest⟩ := outcomes _ so
      cases e
      rw [Progress.materializeModelAccesses_noLazy _ _ lazy] at materialized
      cases materialized
      exact rest
    | exit _ p so stopped =>
      rw [pending] at p; cases p
      obtain ⟨eff, model', e, running, _⟩ := outcomes _ so
      cases e
      rw [running] at stopped; cases stopped
    | killed _ p so killed =>
      rw [pending] at p; cases p
      obtain ⟨eff, model', e, running, _⟩ := outcomes _ so
      cases e
      rw [killedBy_of_halted running] at killed; cases killed

end Funnel

end Silmaril.Process.LPS.Machines.X86MuslRun
