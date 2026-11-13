module

public import Silmaril.Machine.Process.LpsBridge.Defs
public import Silmaril.Machine.X86.RelIsa.Safe.Defs

/-!
# The LPS bridge over relational machines: definitions

LPS's user machine
`UserIsa.step` is a function, so the bridge stays over a *deterministic* step `c`; that step
only has to refine a relational (loose) machine `A` (`Le (ofFun c) A`), on which the program
is proved demonically (`SafeNR A`, `Must A`).

* `NStep`: a native LPS x86 step (`X86State → MachineResult (AccessReport X86State)`), the
  shape of silmaril's `x86NativeStep` and `x86NativeStep8`.
* `flagStep oracle nstep`, `flagMachine oracle nstep`: the flag-oracle LPS user machine over a
  native step. Every field except `step` is `x86WithFlagOracle oracle`'s, and `step` is the
  `X86FlagChoices.step8` pattern with `nstep` for `x86NativeStep8`. So
  `flagMachine oracle x86NativeStep8` is the bridge's `machine oracle` (`x86WithFlagOracle8`)
  by definition (`flagMachine_eight` in `Thms`), and `Lps9`'s `x86WithFlagOracle9` is
  `flagMachine oracle x86NativeStep9`.
* `Agrees nstep c`: **the deterministic machine `c` is what `nstep` does off `syscall`.**
  `c` is stuck at `0F 05`; where `c` steps, `nstep` from the same state with no syscall
  pending is that step (with some access report); at `0F 05` with defined flags, `nstep`
  traps (records `rax` as pending, reports the 2 fetched bytes), as LPS's native step does.
* `AlignedF`, `PSafeF`, `ProcessSafeF`: `Aligned`, `PSafe`, `ProcessSafe` of the bridge
  (`LpsBridge/Defs.lean`) over `flagMachine oracle nstep`. At `nstep := x86NativeStep8` they
  are the original notions by definition.

The theorems are in `Silmaril.Machine.Process.LpsBridge.Rel.Thms`.

**Deviation from the design note.** The note writes `Agrees (M : UserIsa) c`. A bare
`UserIsa` has an opaque state type, so alignment cannot be stated for it; `Agrees` is stated
on the native step `nstep` instead, and `M` is `flagMachine oracle nstep`.

**Trust.** As for `LpsBridge`: statements about silmaril's LPS port with handwritten x86
semantics, not about Linux or hardware.
-/

@[expose] public section

namespace Silmaril.Machine.Process.LpsBridge

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)

/-- A native LPS x86 step. -/
abbrev NStep := X86State → MachineResult (AccessReport X86State)

/-- The flag-oracle step over a native step (the `X86FlagChoices.step8` pattern). -/
def flagStep (oracle : Oracle) (nstep : NStep) (state : X86FlagChoices.State) :
    MachineResult (AccessReport X86FlagChoices.State) :=
  if state.native.m.memory.fetchBytes state.native.m.core.rip.toNat 2 = some [0x0f, 0x05] then
    X86FlagChoices.lift (state.counter + 1)
      (nstep (X86FlagChoices.completeState state.native (oracle state.counter)))
  else X86FlagChoices.lift state.counter (nstep state.native)

/-- **The flag-oracle LPS user machine over a native step.** -/
def flagMachine (oracle : Oracle) (nstep : NStep) : UserIsa :=
  { x86WithFlagOracle oracle with step := fun _ => flagStep oracle nstep }

/-- **`c` is what `nstep` does off `syscall`**, and `nstep` traps at `syscall`. -/
structure Agrees (nstep : NStep) (c : MState → Option MState) : Prop where
  /-- The deterministic machine is stuck at `0F 05`. -/
  stuck : ∀ {m : MState}, AtSyscall m → c m = none
  /-- Where `c` steps, the native step (no syscall pending) is that step. -/
  step : ∀ {m m' : MState}, c m = some m' → ∃ acc, nstep ⟨m, none⟩ = .ok ⟨⟨m', none⟩, acc⟩
  /-- At `0F 05` with defined flags, the native step records `rax` as pending. -/
  trap : ∀ (s : X86State) (w : Silmaril.X86.Word), AtSyscall s.m →
    rflagsImage s.m.core.flags = some w →
    nstep s = .ok ⟨{ s with pending := some (s.m.core.read .rax) }, [(s.m.core.rip, 2)]⟩

/-- `Aligned` over `flagMachine oracle nstep`. -/
structure AlignedF {oracle : Oracle} {nstep : NStep} (c : Config (flagMachine oracle nstep))
    (m : MState) : Prop where
  native : c.ms.native = ⟨m, none⟩
  alive : c.model.halted = none
  lazy : c.model.vmLazy = []

/-- `PSafe` over `flagMachine oracle nstep`. -/
def PSafeF {oracle : Oracle} {nstep : NStep} (segs : List Segment) (refused : RefusalFilter)
    (Allowed : List Event → Prop) (c : Config (flagMachine oracle nstep)) : Prop :=
  (∀ tr c', Star segs spec refused c tr c' → Allowed tr) ∧
    ∀ tr c' evs, Star segs spec refused c tr c' → ¬ SStep segs spec refused c' evs .error

/-- `ProcessSafe` over `flagMachine · nstep`: every oracle. -/
def ProcessSafeF (nstep : NStep) (snapshot : X86Launch.Snapshot) (refusals : SpuriousCfg)
    (limit : Int) (en : ExecEntry) (inp : ProcInput) (Allowed : List Event → Prop) : Prop :=
  ∀ oracle : Oracle,
    PSafeF snapshot.image.segments (NativeX86.defaultRefusalFilter refusals) Allowed
      (X86Launch.init (flagMachine oracle nstep) snapshot en limit inp)

end Silmaril.Machine.Process.LpsBridge
