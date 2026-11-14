module

public import Silmaril.X86.Open.Defs
public import Silmaril.Process.LPS.Machines.X86FlagChoices8
public import Silmaril.Process.LPS.Machines.X86NativeLaunch

/-!
# A program-independent bridge from the open x86 machine to the LPS process semantics

The sha256sum proof in silmaril-lean (`Process/LPS/Problems/GnuSha256sum/{StdRel,Instr,
SysBridge}`, duplicating `Sha256Cli/*`) relates a per-program middle model (`X86Sys`/`GStep`)
to the LPS run by a stuttering simulation, rebuilt for every program. This module states the
bridge **once**, for every ELF image (segment list), every flag oracle, every refusal filter
and every launch, directly against the open machine `Silmaril.X86.Open.step` on which the
function contracts of the ELF tracks are proved (no middle model).

* `machine oracle`: the LPS user machine `x86WithFlagOracle8 oracle` (native x86-64, `Ext8`
  fetch, an explicit oracle for flags that are undefined at a `syscall`), and `spec`, the
  native x86-64 syscall table `NativeX86.extendedSyscallSpec`, as in the sha256sum release
  statement (`GnuSha256sum.Statement.machine`, `X86NativeLaunch.runWith`).
* `AtSyscall m`: the bytes `0F 05` are at `rip`.
* `Aligned c m`: the LPS configuration `c` holds exactly the open state `m` (no syscall
  pending, any oracle counter), the process is alive and has no lazy reservation. There is
  no flag-monotonicity relation (`FlagMono.CoreLe` in silmaril): the bridge re-enters the open
  machine after a `syscall` with the state LPS actually holds, completed flags included, and
  the function contracts quantify over every state anyway.
* `PSafe segs refused Allowed c`: **process safety from `c`**: every finite LPS execution
  from `c` has a trace satisfying `Allowed`, and no execution reaches an error (a fault, an
  unmodelled instruction or syscall, or a failed materialisation).
* `resume s eff`: the open state LPS resumes with after a syscall effect `eff`
  (`advancePastSvc ∘ applyEffect` of the native machine).
* `ProcessSafe`: process safety of a whole launch (`X86Launch.init`), for a behaviour
  predicate on traces. This is the shape of silmaril's `lps-partial` tier.

The theorems (instruction half, the generic syscall half, the `exit` arm, the launch, the
`write` and `read` arms) are in `Silmaril.Process.LpsBridge.Thms`; the two arms are
stated here as `Task.writeArm` and `Task.readArm` and proved there.

**Trust.** This is a statement about silmaril's LPS port (rocq-linux-process-semantics
`f1006fe8`) instantiated with the handwritten `X86.Ext`/`Ext8` semantics. It is not a statement
about Linux or hardware.
-/

@[expose] public section

namespace Silmaril.Process.LpsBridge

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)

/-- An oracle for flags that are undefined at a `syscall`. -/
abbrev Oracle := Nat → X86FlagChoices.Choice

/-- **The LPS user machine** of the bridge (the sha256sum release machine). -/
abbrev machine (oracle : Oracle) : UserIsa := x86WithFlagOracle8 oracle

/-- **The syscall table** of the bridge: LPS's native x86-64 table with `arch_prctl`. -/
abbrev spec : Sys SyscallEffect := NativeX86.extendedSyscallSpec

/-- The syscall instruction `0F 05` is at `rip`. -/
def AtSyscall (m : MState) : Prop :=
  m.memory.fetchBytes m.core.rip.toNat 2 = some [0x0f, 0x05]

/-- **Alignment**: the LPS configuration holds exactly the open state `m`, with no syscall
pending, alive, without lazy reservations. The oracle counter is arbitrary. -/
structure Aligned {oracle : Oracle} (c : Config (machine oracle)) (m : MState) : Prop where
  native : c.ms.native = ⟨m, none⟩
  alive : c.model.halted = none
  lazy : c.model.vmLazy = []

/-- **Process safety** from a configuration: every finite execution's trace satisfies
`Allowed`, and no execution reaches an error. -/
def PSafe {oracle : Oracle} (segs : List Segment) (refused : RefusalFilter)
    (Allowed : List Event → Prop) (c : Config (machine oracle)) : Prop :=
  (∀ tr c', Star segs spec refused c tr c' → Allowed tr) ∧
    ∀ tr c' evs, Star segs spec refused c tr c' → ¬ SStep segs spec refused c' evs .error

/-- The native state at a trap after LPS has completed the flags and recorded the pending
number. -/
def trapped (s : X86State) (choice : X86FlagChoices.Choice) : X86State :=
  { X86FlagChoices.completeState s choice with pending := some (s.m.core.read .rax) }

/-- The open state LPS resumes with after the syscall effect `eff`. -/
def resume (s : X86State) (eff : SyscallEffect) : MState :=
  (x86AdvancePastSvc (x86ApplyEffectNative s eff)).m

/-- The syscall request LPS reads at a trap: number `rax`, arguments `rdi, rsi, rdx, r10, r8,
r9`, and the readable and writable memory views. -/
def request {oracle : Oracle} (segs : List Segment) (s : X86FlagChoices.State) :
    SyscallInput :=
  sysInput (machine oracle) segs s (s.native.m.core.read .rax)

/-- The core LPS launches with: every register zero except `rsp = sp`, `rip = pc`, the status
flags defined and clear (`x86Ext.init`). -/
def launchCore (pc : Nat) (sp : Word) : Silmaril.X86.State :=
  ({ regs := fun _ => 0, rip := BitVec.ofNat 64 pc
     flags := ⟨some false, some false, some false, some false, some false, some false⟩ } :
    Silmaril.X86.State).write .rsp sp

/-- **The open state of a launch**: the launch core, and LPS's initial memory (the image
segments, the 8 MiB stack and the entry block `X86Launch.entryStack`). -/
def launchState (snapshot : X86Launch.Snapshot) (en : ExecEntry) (inp : ProcInput) : MState :=
  ⟨launchCore snapshot.image.initPc en.sp,
    initialMemory snapshot.image.segments en.sp (X86Launch.entryStack snapshot.image en inp)⟩

/-- **Process safety of a launch** (the `lps-partial` shape): for every flag oracle, the
launched configuration of `snapshot` on `en`/`inp` is process-safe for `Allowed` under the
native refusal filter of `refusals`. -/
def ProcessSafe (snapshot : X86Launch.Snapshot) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) (Allowed : List Event → Prop) : Prop :=
  ∀ oracle : Oracle,
    PSafe snapshot.image.segments (NativeX86.defaultRefusalFilter refusals) Allowed
      (X86Launch.init (machine oracle) snapshot en limit inp)

/-! ## The `read` and `write` arms (open)

The generic syscall half (`psafe_syscall` in the `Thms` header) reduces every syscall to the
outcomes of `spec` at the trap. For `exit`/`exit_group` they are characterised
(`psafe_exit`). The two statements below characterise `write` to a live channel and `read`
from stdin: the possible outcomes and their events. Both are proved after correcting their
statements: `Task.writeArm` (`writeArm_holds`) and `Task.readArm`
(`readArm_holds`). -/

/-- **`write(fd, buf, n)` to a live channel** (proved, `writeArm_holds`).

At a request with number `1`, if descriptor `fd32 (arg 0)` is a channel `ch ≠ 0`, the range is
modelled (`modeledRwRangeWith accessOkb`, which holds for every count up to 128 KiB), the count
is nonzero and the readable source `writeSource` is non-empty, then the outcomes of the native
table are exactly the successful partial writes: a non-empty prefix `ds` of the source, at most
the clamped count, `rax = |ds|`, one `writeEv ch` per byte, the copy-in `(buf, |ds|)` recorded,
memory and model unchanged; never `unmodeled`.

**Correction (round 3).** Round 2 stated this Task with `eff.copyins = []`, without `ch ≠ 0`,
and without the modelled-range hypothesis. As stated it was false: LPS records the copy-in
`(buf, |ds|)` on every successful write, returns `EBADF` for channel `0`, and is `unmodeled`
for unmodelled ranges. Nothing depended on the old statement. -/
def Task.writeArm : Prop :=
  ∀ (i : SyscallInput) (model : Model) (ch : Word) (o : Outcome SyscallEffect),
    i.sysno.toNat = 1 → fdLookup model.fds (fd32 (i.arg 0)) = some (.channel ch) →
    wIs0 ch = false → modeledRwRangeWith accessOkb (i.arg 1) (i.arg 2) = true →
    wIs0 (i.arg 2) = false → writeSource i.mem (i.arg 1) (i.arg 2) ≠ [] →
    (spec i model o ↔
      ∃ ds : List Byte, (1 ≤ ds.length ∧ (ds.length : Int) ≤ rwCountClamp (i.arg 2) ∧
        ds = (writeSource i.mem (i.arg 1) (i.arg 2)).take ds.length) ∧
        o = .ok ((mkEffect (lenWord ds) [] []).withCopyins ([(i.arg 1, ds.length)] ++ []))
          model (ds.map (.writeEv ch)))

/-- **`read(fd, buf, n)` from stdin** (proved, `readArm_holds`).

At a request with number `0`, if descriptor `fd32 (arg 0)` is channel `0` (stdin), the buffer
passes `access_ok` (`accessOkb buf count`, as LPS checks it) and the whole requested range
`buf .. buf + count` is writable (`readBytesMap i.wmem buf count`), then the outcomes of the
native table are exactly:

* if the count is `0` or stdin is at end of file: `ret = 0`, no effect, the model and the
  trace unchanged;
* otherwise: a non-empty prefix `bs` of the remaining stdin stream, at most the clamped count
  (`rwCountClamp`), delivered as the single memory write `(buf, bs)`, `ret = |bs|`, stdin
  advanced by `|bs|` (`model.withStdin`), one `readEv 0` per byte.

In particular the outcome is never `unmodeled`.

**Correction.** An earlier statement of this Task was for any channel `ch`, with an
unconditional `eff.writes = [(buf, bs)] ∨ (bs = [] ∧ eff.writes = [])`, `copyins = []` and
"model' alive with the same lazy reservations", from a byte-wise writability hypothesis only.
As stated it was false: LPS returns `EBADF` for a channel other than `0`, `EFAULT` when
`access_ok` fails (a writable range is not enough), and its `bs` is constrained to be a prefix
of stdin, which the old statement dropped (it said nothing about stdin advancing). Nothing
depended on the old statement. -/
def Task.readArm : Prop :=
  ∀ (i : SyscallInput) (model : Model) (o : Outcome SyscallEffect),
    i.sysno.toNat = 0 → fdLookup model.fds (fd32 (i.arg 0)) = some (.channel 0) →
    accessOkb (i.arg 1) (uns (i.arg 2)) = true →
    (readBytesMap i.wmem (i.arg 1) (i.arg 2)).isSome →
    (spec i model o ↔
      ((wIs0 (i.arg 2) || model.stdin.atEof) = true ∧ o = .ok (mkEffect 0 [] []) model []) ∨
      ((wIs0 (i.arg 2) || model.stdin.atEof) = false ∧
        ∃ bs : List Byte, (1 ≤ bs.length ∧ (bs.length : Int) ≤ rwCountClamp (i.arg 2) ∧
          (model.stdin.take bs.length).1 = bs) ∧
          o = .ok (mkEffect (lenWord bs) [(i.arg 1, bs)] [])
            (model.withStdin (model.stdin.take bs.length).2) (bs.map (.readEv 0))))

end Silmaril.Process.LpsBridge
