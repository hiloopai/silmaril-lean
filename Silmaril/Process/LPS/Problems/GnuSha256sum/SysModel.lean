module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.Statement
public import Silmaril.Apps.Sha256sum.X86Sys8

/-! # GNU `sha256sum` over the `X86Sys` process model: the middle statement and its segments

The LPS target (`GnuSha256sum.Statement`) is reached in two moves, as for the `sha256` filter
(`Sha256Cli.Segments`):

```
Launch ──startup──▶ AtDigest ──readLoop──▶ AtEof ──final──▶ Digested
       ──format──▶ Formatted ──exit──▶ Done                              (GStep, Leads with Ok)
SysTotalOn ──bridge──▶ TotalOn                                           (X86Sys ⇒ LPS)
```

**The middle model.** `GStep w` is `Apps.Sha256sum.X86Sys.step8` (the `X86.Ext8` machine with
`syscall` recognised, `Process.CLI.X86Linux8.step`, which adds the 8-bit ALU forms to
`X86.Ext`, and the x86-64 Linux calls `read`,
`write`, `close`, `openat`, `exit`/`exit_group` decoded by `X86Sys.decode`) against the world
kernel `Sys.WorldStep w` (any read chunking, any nonempty partial write), with two changes
that make it a *relation* the LPS bridge can match:

* the value the kernel leaves in `r11` is arbitrary at every return (LPS puts RFLAGS there,
  with undefined flags chosen by the oracle); `X86Sys.x86Machine8 r11Of` fixes one function;
* `exit` is an event and an explicit exited state, so `Done` is a state predicate;
* `brk` is not a step: the stdin tier never calls it (`sha256sum.c`: "hashing needs no heap:
  brk is reached only by error messages, quotef and check mode"), so a `Leads` proof shows it
  is unreachable. The `--check` and error tiers will add it.

The CLI model of the filter (`Process.CLI.X86Linux` with `Syscall.Request`) is not used: it
has no `close`, and GNU `sha256sum` closes descriptors 0, 1 and 2 before it exits.

**Segments.** The cut points are *parameters* (`Cut`): each segment is a `Leads` statement
from one cut predicate to the next, and `sysTotalOn_of_segments` (VERIFIED) composes any
choice. The intended cut points in `sha256sum-min` (from its disassembly; `digest_fd` and
`output_file` are inlined) are:

* `AtDigest`: `cmain` at `call digest_file` (`0x403c7b`) with the operand `"-"`, after
  option scanning (no system call before it);
* `AtEof`: inside `digest_file`, after the `read(0, iobuf, 32768)` that returned 0, with the
  hash state the fold of the full blocks and the tail in the `struct sha` buffer;
* `Digested`: back in `cmain` at `0x403c80`, `eax = 1`, the 32 digest bytes in `bin`;
* `Formatted`: the 68 bytes of the stdin record in `obuf` (`0x412140`, `olen = 68`), before
  `close(0)` (`have_read_stdin`);
* `Done`: after `close(0)`, `close_stdout` (`out_flush` loop of `write(1, …)`, `close(1)`,
  `close(2)`) and `exit_group(0)`.

Status: everything proved in this file is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Apps.Sha256sum (World)
open Silmaril.Apps.Sha256sum.Sys (Call Ret KState WorldStep)
open Silmaril.Apps.Sha256sum.X86Sys (XState)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

/-! ## The relational `X86Sys` process -/

/-- An observable event of the middle model: a system call with its reply, or the exit. -/
inductive Ev where
  | sys (c : Call) (r : Ret)
  | exit (status : Nat)
  deriving DecidableEq

/-- A process: the `X86Sys` program state, the world kernel state, and the exit status. -/
structure GS where
  x : XState
  k : KState
  exited : Option Nat := none

/-- One step of the program against the kernel of world `w`. -/
inductive GStep (w : World) : GS → List Ev → GS → Prop
  | retire {g : GS} {c : Silmaril.Apps.Sha256sum.X86Sys.Core} {m : Silmaril.Process.Memory} :
      g.exited = none → g.x.faulted = false →
      CLI.X86Linux8.step g.x.core g.x.memory = .retired c m →
      GStep w g [] { g with x := { g.x with core := c, memory := m } }
  | call {g : GS} {t : Silmaril.Apps.Sha256sum.X86Sys.Core} {call : Call} {r : Ret} {k' : KState} (r11 : Silmaril.X86.Word) :
      g.exited = none → g.x.faulted = false →
      CLI.X86Linux8.step g.x.core g.x.memory = .syscall t →
      Silmaril.Apps.Sha256sum.X86Sys.decode t g.x.memory = some (.call call) → WorldStep w g.k call r k' →
      GStep w g [.sys call r] ⟨Silmaril.Apps.Sha256sum.X86Sys.resume (fun _ => r11) g.x t call r, k', none⟩
  | exit {g : GS} {t : Silmaril.Apps.Sha256sum.X86Sys.Core} {n : Nat} :
      g.exited = none → g.x.faulted = false →
      CLI.X86Linux8.step g.x.core g.x.memory = .syscall t →
      Silmaril.Apps.Sha256sum.X86Sys.decode t g.x.memory = some (.exit n) →
      GStep w g [.exit (n % 256)] { g with exited := some (n % 256) }

/-! ## What the history shows -/

/-- The bytes an event read from descriptor 0. -/
def readBytes : Ev → List Byte
  | .sys (.read 0 _) (.data b) => b.map UInt8.toBitVec
  | _ => []

/-- The bytes an event wrote to descriptor 1 (the accepted prefix). -/
def outBytes : Ev → List Byte
  | .sys (.write 1 bytes) (.ok n) => (bytes.take n).map UInt8.toBitVec
  | _ => []

/-- Everything read from standard input. -/
def stdinRead (h : List Ev) : List Byte := h.flatMap readBytes

/-- Everything written to standard output. -/
def out (h : List Ev) : List Byte := h.flatMap outBytes

/-- The calls the stdin tier may make: `read(0)`, `write(1)`, `close` of a standard
descriptor. No `openat`, no write to stderr, no exit (an exit is the last event of `Done`). -/
def Allowed : Ev → Prop
  | .sys (.read fd _) _ => fd = 0
  | .sys (.write fd _) _ => fd = 1
  | .sys (.close fd) _ => fd ≤ 2
  | .sys (.openat _) _ => False
  | .exit _ => False

/-- The safety invariant of a running process: only allowed calls, a prefix of the message
read, a prefix of the answer written, nothing written before the whole message was read. -/
def Ok (message : List Byte) (g : GS) (h : List Ev) : Prop :=
  g.exited = none ∧ (∀ e ∈ h, Allowed e) ∧ stdinRead h <+: message ∧
    out h <+: expected message ∧ (out h = [] ∨ stdinRead h = message)

/-- The goal: the whole message read, exactly the answer written, then `exit_group(0)`. -/
def Done (message : List Byte) (g : GS) (h : List Ev) : Prop :=
  g.exited = some 0 ∧ ∃ h', h = h' ++ [.exit 0] ∧ (∀ e ∈ h', Allowed e) ∧
    stdinRead h' = message ∧ out h' = expected message

/-- An exited process takes no step. -/
theorem exited_final {w : World} {g : GS} {n : Nat} (exited : g.exited = some n) :
    ∀ e g', ¬ GStep w g e g' := by
  intro e g' step
  cases step <;> simp_all

theorem done_final (w : World) (message : List Byte) :
    ∀ g h, Done message g h → ∀ e g', ¬ GStep w g e g' :=
  fun _ _ done => exited_final done.1

/-! ## Launch and the middle statement -/

/-- A launch of `sha256sum-min` on world `w`: `Silmaril.Apps.Sha256sum.X86Sys.Init` of the transcribed image (System V
stack with argv and envp, segments mapped, `rip` at `0x401000`, heap above the image), the
initial kernel of `w`, and the stack window above the image (which LPS's `ValidEntry`
supplies: images stay below the stack reservation). -/
def Launch (w : World) (g : GS) : Prop :=
  Silmaril.Apps.Sha256sum.X86Sys.Init Apps.Sha256sum.Binary.Image.image w g.x ∧ g.k = KState.init w ∧
    g.exited = none ∧
    Silmaril.Apps.Sha256sum.X86Sys.imageEnd Apps.Sha256sum.Binary.Image.image + CLI.X86Linux.stackRoom ≤
      (g.x.core.read .rsp).toNat

/-- **The middle statement** (stdin tier): from every launch on every stdin-tier world whose
message is in `domain`, every execution keeps `Ok`, can always move, and ends in `Done`. -/
def SysTotalOn (domain : List Byte → Prop) : Prop :=
  ∀ (prog : List Byte) (posix : Bool) (fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult)
    (message : List Byte) (g : GS), domain message →
    Launch (world [prog] posix fs message) g →
      Leads (GStep (world [prog] posix fs message)) (Ok message) (Done message) g []

/-! ## Segments with parametric cut points -/

/-- A cut predicate: on the world, the message, the process and the history so far. -/
abbrev Cut := World → List Byte → GS → List Ev → Prop

/-- The launch as a cut predicate (empty history). -/
def LaunchCut : Cut := fun w _ g h => Launch w g ∧ h = []

/-- The goal as a cut predicate. -/
def DoneCut : Cut := fun _ message g h => Done message g h

/-- One segment: on every stdin-tier world with message in `domain`, from every state at cut
`Pre`, every execution keeps `Ok` and reaches cut `Post`. -/
def Seg (domain : List Byte → Prop) (Pre Post : Cut) : Prop :=
  ∀ (prog : List Byte) (posix : Bool) (fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult)
    (message : List Byte) (g : GS) (h : List Ev), domain message →
    Pre (world [prog] posix fs message) message g h →
      Leads (GStep (world [prog] posix fs message)) (Ok message)
        (Post (world [prog] posix fs message) message) g h

/-- Segments compose at a cut point (VERIFIED). -/
theorem Seg.trans {domain : List Byte → Prop} {A B C : Cut} (first : Seg domain A B)
    (second : Seg domain B C) : Seg domain A C :=
  fun prog posix fs message g h member start =>
    (first prog posix fs message g h member start).trans fun g' h' mid =>
      second prog posix fs message g' h' member mid

/-- A segment from the launch to the goal is the middle statement (VERIFIED). -/
theorem sysTotalOn_of_seg {domain : List Byte → Prop} (h : Seg domain LaunchCut DoneCut) :
    SysTotalOn domain :=
  fun prog posix fs message g member launch => h prog posix fs message g [] member ⟨launch, rfl⟩

/-- Named segments of the stdin tier (cut points as parameters). -/
def StartupSegment (domain : List Byte → Prop) (AtDigest : Cut) : Prop :=
  Seg domain LaunchCut AtDigest
def ReadLoopSegment (domain : List Byte → Prop) (AtDigest AtEof : Cut) : Prop :=
  Seg domain AtDigest AtEof
def FinalSegment (domain : List Byte → Prop) (AtEof Digested : Cut) : Prop :=
  Seg domain AtEof Digested
def FormatSegment (domain : List Byte → Prop) (Digested Formatted : Cut) : Prop :=
  Seg domain Digested Formatted
def ExitSegment (domain : List Byte → Prop) (Formatted : Cut) : Prop :=
  Seg domain Formatted DoneCut

/-- **Glue (VERIFIED).** The five segments, for any choice of the four inner cut points, give
the middle statement. -/
theorem sysTotalOn_of_segments {domain : List Byte → Prop} {AtDigest AtEof Digested Formatted : Cut}
    (startup : StartupSegment domain AtDigest) (readLoop : ReadLoopSegment domain AtDigest AtEof)
    (final : FinalSegment domain AtEof Digested) (format : FormatSegment domain Digested Formatted)
    (exit : ExitSegment domain Formatted) : SysTotalOn domain :=
  sysTotalOn_of_seg (startup.trans (readLoop.trans (final.trans (format.trans exit))))

/-! ## Consequences of the middle statement (VERIFIED) -/

/-- What a `Leads` proof gives directly: along every run from a launch the invariant or the
goal holds, every non-final reachable state can move, and no run is infinite. -/
theorem SysTotalOn.consequences {domain : List Byte → Prop} (h : SysTotalOn domain)
    {prog : List Byte} {posix : Bool} {fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult}
    {message : List Byte} {g : GS} (member : domain message)
    (launch : Launch (world [prog] posix fs message) g) :
    (∀ es g', Machine.Trace.Runs (GStep (world [prog] posix fs message)) g es g' →
        Ok message g' es ∨ Done message g' es) ∧
      (∀ es g', Machine.Trace.Runs (GStep (world [prog] posix fs message)) g es g' →
        ¬ Done message g' es → ∃ e g'', GStep (world [prog] posix fs message) g' e g'') ∧
      ¬ Machine.Trace.Diverges (GStep (world [prog] posix fs message)) g := by
  have leads := h prog posix fs message g member launch
  refine ⟨fun es g' run => ?_, fun es g' run notDone => ?_, leads.not_diverges (done_final _ _)⟩
  · simpa using leads.runs (done_final _ _) run
  · exact leads.progress (done_final _ _) run (by simpa using notDone)

end Silmaril.Process.LPS.Problems.GnuSha256sum
