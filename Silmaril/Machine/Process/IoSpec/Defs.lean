module

public import Silmaril.Machine.Process.LpsBridge.Rel.Defs

/-!
# `IoSpec`: safety of syscall-performing code over a parametric step

The
function contracts of the ELF tracks (`SafeN`, `FnSpec`) are over a *pure* user machine: a
`syscall` is a stuck state. `read`, `write` and `_Exit` execute `syscall`. This topic states
safety *through* syscalls, for any deterministic step `c` (in practice `Open.step`,
`Open9.step` or `Str9.step`), with the syscalls answered by an environment, and proves it
sound for LPS on every agreeing native machine (`ioSafe_psafe` in `Thms`). It generalises
rung 12's `psafe_exit`/`psafe_write` pattern.

* `reqOf segs s`: the syscall request LPS reads at a trapped native state `s` (number `rax`,
  arguments `rdi, rsi, rdx, r10, r8, r9`, the readable and writable memory views).
* `IoOut`: what an environment may answer at a trap: `resume m' e' evs` (the process
  continues at the open state `m'`, the environment is now `e'`, the syscall emitted `evs`) or
  `halt evs` (the process ends; `evs` is the complete trace segment, exit event included).
* `SysEnv`: an environment model `Model`, its abstraction `Abs` of LPS's model, the traps it
  handles (`Handles`, on the trapped native state, so after flag completion) and its answers
  (`arm`). The answers may be loose (any relation).
* `IoOut.Next k A o`: the obligation after answer `o`, for a continuation `k` and the
  remaining-trace predicate `A`.
* **`IoSafeN step E Q n m e A`**: step-indexed safety of `step` from `m` with environment
  `e`: every finite run (user steps, and at `0F 05` any answer of `E.arm`) keeps the trace
  predicate `A` true and does not get stuck, unless `Q` (a frame exit, e.g. a return) is
  reached. The trace predicate is the *remaining* trace: after an answer emitting `evs`, it
  becomes `fun tr => A (evs ++ tr)`, as in `LpsBridge.OutcomesF`.
* **`Sound E segs refused`**: `E` covers LPS at every trap it handles: the request is not
  `unmodeled`, no outcome kills, a resumed outcome keeps no lazy reservation and (unless
  refused) is an answer of `E` (with an abstraction of the new model), and a halting outcome
  is an answer of `E` with LPS's exit event.
* Arms over LPS's model (`Arm`, `ofArms`, `ArmSound`): `exitArm`, `writeArm segs`,
  `readArm segs`, `lpsArms segs`, and `lpsEnv segs = ofArms (lpsArms segs)`. Each arm's
  soundness is the corresponding `LpsBridge` arm (`psafe_exit`, `writeArm_holds`,
  `readArm_holds`).

**Multi-thread future-proofing** (zlib-binary.md §5.1, direction 5). The environment model
is per process; the fs base is read from `MState.core.fsBase` and never duplicated in
`E.Model`.

**Not here** (see the package note): `IoFnSpec` (an `FnSpec` with environment pre/post) and
its call rule, and the total variant `IoSafeT`.
-/

@[expose] public section

namespace Silmaril.Machine.Process.IoSpec

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge

/-- The syscall request LPS reads at the trapped native state `s`. -/
def reqOf (segs : List Segment) (s : X86State) : SyscallInput :=
  ⟨s.m.core.read .rax, x86ExtNative.syscallArgs s, x86ExtNative.readByte segs s,
    x86ExtNative.writableByte segs s⟩

/-- What an environment may answer at a trap. -/
inductive IoOut (Model : Type) where
  /-- The process continues at the open state `m` with environment `e`, after events `evs`. -/
  | resume (m : MState) (e : Model) (evs : List Event)
  /-- The process ends; `evs` is the complete trace segment, exit event included. -/
  | halt (evs : List Event)

/-- **A syscall environment.** -/
structure SysEnv where
  /-- The environment model. -/
  Model : Type
  /-- How an environment model abstracts LPS's model. -/
  Abs : Model → Silmaril.Process.LPS.Model → Prop
  /-- The traps the environment answers, on the trapped native state. -/
  Handles : X86State → Model → Prop
  /-- Its answers. -/
  arm : X86State → Model → IoOut Model → Prop

/-- The obligation after an answer: continue with `k` (and the remaining trace after `evs`),
or the complete trace segment is allowed. -/
def IoOut.Next {Model : Type} (k : MState → Model → (List Event → Prop) → Prop)
    (A : List Event → Prop) : IoOut Model → Prop
  | .resume m' e' evs => k m' e' (fun tr => A (evs ++ tr))
  | .halt evs => A evs

/-- **Step-indexed safety through syscalls.** -/
def IoSafeN (step : MState → Option MState) (E : SysEnv)
    (Q : MState → E.Model → (List Event → Prop) → Prop) :
    Nat → MState → E.Model → (List Event → Prop) → Prop
  | 0, _, _, _ => True
  | n + 1, m, e, A => A [] ∧
      (Q m e A ∨ (∃ m', step m = some m' ∧ IoSafeN step E Q n m' e A) ∨
        (AtSyscall m ∧ ∀ ch : X86FlagChoices.Choice, E.Handles (trapped ⟨m, none⟩ ch) e ∧
          ∀ o, E.arm (trapped ⟨m, none⟩ ch) e o → o.Next (IoSafeN step E Q n) A))

/-- **Soundness of an environment for LPS** (the native table `spec`, segments `segs`,
refusal filter `refused`). -/
def Sound (E : SysEnv) (segs : List Segment) (refused : RefusalFilter) : Prop :=
  ∀ (m : MState) (ch : X86FlagChoices.Choice) (model : Silmaril.Process.LPS.Model)
    (e : E.Model), E.Abs e model → model.halted = none → model.vmLazy = [] → AtSyscall m →
    E.Handles (trapped ⟨m, none⟩ ch) e →
    ¬ spec (reqOf segs (trapped ⟨m, none⟩ ch)) model .unmodeled ∧
    ∀ eff model' evs, spec (reqOf segs (trapped ⟨m, none⟩ ch)) model (.ok eff model' evs) →
      model'.killedBy = none ∧
      (model'.halted = none → model'.vmLazy = [] ∧
        (¬ refused (reqOf segs (trapped ⟨m, none⟩ ch)) model eff →
          ∃ e', E.Abs e' model' ∧
            E.arm (trapped ⟨m, none⟩ ch) e (.resume (resume (trapped ⟨m, none⟩ ch) eff) e' evs))) ∧
      (∀ code, model'.halted = some code →
        E.arm (trapped ⟨m, none⟩ ch) e (.halt (evs ++ [.exitEv code model'.fs])))

/-! ## Arms over LPS's model -/

/-- One syscall arm over LPS's model: the traps it handles and its answers. -/
structure Arm where
  Handles : X86State → Silmaril.Process.LPS.Model → Prop
  out : X86State → Silmaril.Process.LPS.Model → IoOut Silmaril.Process.LPS.Model → Prop

/-- The environment of a list of arms over LPS's model (abstraction: equality). An answer
is an answer of an arm that handles the trap. -/
def ofArms (arms : List Arm) : SysEnv where
  Model := Silmaril.Process.LPS.Model
  Abs := Eq
  Handles s e := ∃ a ∈ arms, a.Handles s e
  arm s e o := ∃ a ∈ arms, a.Handles s e ∧ a.out s e o

/-- An arm is sound for LPS: `Sound` for the one-arm environment. -/
def ArmSound (segs : List Segment) (refused : RefusalFilter) (a : Arm) : Prop :=
  Sound (ofArms [a]) segs refused

/-- **`exit`/`exit_group`**: the process ends with status `rdi &&& 255`. -/
def exitArm : Arm where
  Handles s _ := (s.m.core.read .rax).toNat = 60 ∨ (s.m.core.read .rax).toNat = 231
  out s e o := o = .halt [.exitEv (s.m.core.read .rdi &&& 255) e.fs]

/-- **`write(fd, buf, n)` to a live channel** (the hypotheses of `Task.writeArm`): a
non-empty prefix `ds` of the readable source, at most the clamped count, is written, with one
`writeEv ch` per byte, and the process resumes with `rax = |ds|`. -/
def writeArm (segs : List Segment) : Arm where
  Handles s e :=
    (reqOf segs s).sysno.toNat = 1 ∧
    ∃ ch, fdLookup e.fds (fd32 ((reqOf segs s).arg 0)) = some (.channel ch) ∧ wIs0 ch = false ∧
      modeledRwRangeWith accessOkb ((reqOf segs s).arg 1) ((reqOf segs s).arg 2) = true ∧
      wIs0 ((reqOf segs s).arg 2) = false ∧
      writeSource (reqOf segs s).mem ((reqOf segs s).arg 1) ((reqOf segs s).arg 2) ≠ []
  out s e o :=
    ∃ ch, fdLookup e.fds (fd32 ((reqOf segs s).arg 0)) = some (.channel ch) ∧
    ∃ ds : List Byte, 1 ≤ ds.length ∧ (ds.length : Int) ≤ rwCountClamp ((reqOf segs s).arg 2) ∧
      ds = (writeSource (reqOf segs s).mem ((reqOf segs s).arg 1)
        ((reqOf segs s).arg 2)).take ds.length ∧
      o = .resume (resume s ((mkEffect (lenWord ds) [] []).withCopyins
        ([((reqOf segs s).arg 1, ds.length)] ++ []))) e (ds.map (.writeEv ch))

/-- **`read(0, buf, n)` from stdin** (the hypotheses of `Task.readArm`): at count `0` or end
of file `rax = 0` and nothing else; otherwise a non-empty prefix `bs` of stdin, at most the
clamped count, is stored at `buf`, stdin advances by `|bs|`, one `readEv 0` per byte, and the
process resumes with `rax = |bs|`. -/
def readArm (segs : List Segment) : Arm where
  Handles s e :=
    (reqOf segs s).sysno.toNat = 0 ∧
    fdLookup e.fds (fd32 ((reqOf segs s).arg 0)) = some (.channel 0) ∧
    accessOkb ((reqOf segs s).arg 1) (uns ((reqOf segs s).arg 2)) = true ∧
    (readBytesMap (reqOf segs s).wmem ((reqOf segs s).arg 1) ((reqOf segs s).arg 2)).isSome
  out s e o :=
    ((wIs0 ((reqOf segs s).arg 2) || e.stdin.atEof) = true ∧
      o = .resume (resume s (mkEffect 0 [] [])) e []) ∨
    ((wIs0 ((reqOf segs s).arg 2) || e.stdin.atEof) = false ∧
      ∃ bs : List Byte, 1 ≤ bs.length ∧ (bs.length : Int) ≤ rwCountClamp ((reqOf segs s).arg 2) ∧
        (e.stdin.take bs.length).1 = bs ∧
        o = .resume (resume s (mkEffect (lenWord bs) [((reqOf segs s).arg 1, bs)] []))
          (e.withStdin (e.stdin.take bs.length).2) (bs.map (.readEv 0)))

/-- The arms proved so far: `exit`/`exit_group`, `write` to a live channel, `read` from
stdin. -/
def lpsArms (segs : List Segment) : List Arm := [exitArm, writeArm segs, readArm segs]

/-- **The LPS environment** of the arms proved so far. -/
def lpsEnv (segs : List Segment) : SysEnv := ofArms (lpsArms segs)

end Silmaril.Machine.Process.IoSpec
