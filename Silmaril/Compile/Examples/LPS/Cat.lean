module

public import Silmaril.Compile.Examples.LPS.Obs

/-! # `cat.c`: copy stdin to stdout

`examples/compilers-on-lps/cat.c` reads stdin in blocks and writes each block, retrying
short writes, until `read` returns 0.

* `catSpec r`, universal over the stdin stream (finite or infinite): stdout is always a prefix
  of stdin and of what has been read so far (nothing is echoed before it is read), and nothing
  goes to stderr; at the end the file system is unchanged and either the status is 0 and
  stdout is **all** of stdin (end of file was reached), or (only when `r`) the startup
  allocation was refused with nothing written. `catReq`: on a finite stdin an unrefused run
  exits. LPS reads
  of channel 0 deliver any non-empty prefix of the rest of the stream (short reads), and
  channel writes never fail, so `cat.c`'s `return 1` paths are not allowed outcomes. On an
  infinite stdin no end is allowed but the startup refusal.
* No compiler in Silmaril reads stdin yet (core-comp's and ccomp's programs make no
  syscalls; C7 excludes `stdin`), so the target is the statement `catTarget compile` for a
  compiler `compile : String → Option ELF.Bytes` of C sources, and the obligation here is the
  spec's realizability.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Compile.Examples.LPS

open Silmaril.Process.LPS
open Silmaril.Formats

/-- The C source. -/
def catSource : String := include_str "../../../../examples/compilers-on-lps/cat.c"

/-- The process specification of `cat.c`. -/
def catSpec : ProcSpec := fun r inp tr =>
  StreamPrefix inp.stdin (stdoutOf tr) ∧ stdoutOf tr <+: stdinOf tr ∧ OnlyStdout tr ∧
    OnEnd tr fun o fs => fs = inp.fs ∧
      ((o = .exit 0 ∧ StreamIs inp.stdin (stdoutOf tr)) ∨
        (r = true ∧ StartupRefused o ∧ stdoutOf tr = []))

instance (r : Bool) (inp : ProcInput) (tr : List Event) : Decidable (catSpec r inp tr) := by
  unfold catSpec; infer_instance

/-- The requirement: `catSpec`, and an unrefused run on a finite stdin exits. -/
def catReq : ProcReq := ⟨catSpec, FiniteStdin⟩

/-- **Target** (no compiler yet): every executable `compile` produces from `cat.c` meets
`catSpec` on every input. -/
def catTarget (compile : String → Option ELF.Bytes) : Prop :=
  CompilerMeets compile catSource anyInput catReq

/-- **Obligation** (realizability): some static executable meets `catSpec` on every input.
Strategy: a read/write loop over a buffer in a writable segment; the hardest lemma is the
loop invariant `stdout = stdin.takeFrom 0 k` over nondeterministic short reads and writes
(each non-empty), with the budget refusing only page faults (an `SError`, allowed by safety;
excluded by `Unrefused` for liveness); `MustExit` by induction on the finite stdin left. -/
def cat_realizable : Prop := ∃ file, LpsMeets anyInput file catReq

end Silmaril.Compile.Examples.LPS
