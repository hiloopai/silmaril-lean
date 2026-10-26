module

public import Silmaril.Problems.Basic
public import Silmaril.Process.LPS.Problems.CoreutilsLite.Spec
public import Silmaril.Compile.Examples.LPS.Cat
public import Silmaril.Process.LPS.Probes.Data.LiteEcho
public import Silmaril.Process.LPS.Probes.Data.LiteEchoNonl
public import Silmaril.Process.LPS.Probes.Data.LiteEchoExit1
public import Silmaril.Process.LPS.Probes.Data.LiteEchoStderr
public import Silmaril.Process.LPS.Probes.Data.LiteCat
public import Silmaril.Process.LPS.Probes.Data.LiteCatDroplast
public import Silmaril.Process.LPS.Probes.Data.LiteCatDup
public import Silmaril.Process.LPS.Probes.Data.LiteCatOnce
public import Silmaril.Process.LPS.Probes.Data.LiteCatExit1

/-! # `echo` and `cat` (GCC -O2, freestanding): specifications (VERIFIED) and open problems

The binaries are `examples/coreutils-lite/{echo,cat}.c` and their mutants, built and recorded
on Linux by the probe harness (`Probes.Data.LiteEcho`, `LiteCat`, …).

* `echoSpec`: on every launch, the only complete trace writes `argv[1..]` joined by single
  spaces and a newline to stdout (`echoOut`, any write chunking: the program retries short
  writes), then exits 0 with the initial file system. LPS's `ValidArgv` excludes NUL bytes in
  arguments (so `strlen` is the argument length), and, in LPS's launch profile, a `/` or `..`
  in `argv[1..]`.
* `catSpec`: the ladder's `catSpec false` (#3543, `Compile.Examples.LPS.Cat`) on every complete
  trace, with exit status 0, on every finite stdin: stdout is a prefix of stdin and of what has
  been read, nothing goes to another channel, and at the exit stdout is **all** of stdin and
  the file system is unchanged. Every read partition and write split is covered, since LPS
  `read`/`write` may move any non-empty prefix. The ideal trace is left empty (`[]`): the
  `allowed` set is strict, and `Total`'s `exec` already says some execution ends in it.

**Status (WIP).** The problems `coreutils-lite/echo`, `coreutils-lite/cat` and their mutant
negative controls are stated here and registered as open. They are not solved: both binaries
store to the stack (`push %rbx`, `call`, the `read` buffer), and the kit's instruction rules
(`Probes.Kit`, `Probes.Oracle`) require the memory to stay the initial memory. What remains is
a memory-general kit (code window intact under stack stores; the `read` effect) and the loop
lemmas of `docs/X86Stencils.md` (byte scan, write-all, read loop) over symbolic values.

The trace-level checks below (VERIFIED) show the specs reject what Linux recorded for the mutants
and accept what it recorded for the originals.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.CoreutilsLite

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Probes

/-! ## `echo` -/

/-- `argv[1..]` joined by single spaces, then a newline. -/
def echoOut (argv : List (List Byte)) : List Byte := [32].intercalate (argv.drop 1) ++ [10]

/-- `echo`: write `echoOut argv` to stdout (in any chunking), then exit 0. -/
abbrev echoSpec : Spec where
  domain _ := True
  allowed inp trace code := code = 0 ∧ trace = (echoOut inp.argv).map (.writeEv 1) ++ [.exitEv 0 inp.fs]
  ideal inp := (echoOut inp.argv).map (.writeEv 1) ++ [.exitEv 0 inp.fs]

/-! ## `cat` -/

/-- `cat`: the ladder's `catSpec` (nothing refusable), exit status 0, on finite stdin. -/
abbrev catSpec : Spec where
  domain := Compile.Examples.LPS.FiniteStdin
  allowed inp trace code := code = 0 ∧ Compile.Examples.LPS.catSpec false inp trace
  ideal _ := []

/-! ## Spec checks against the recorded observations (VERIFIED) -/

theorem echoOut_harness : echoOut harnessInput.argv = [10] := by decide

theorem echoOut_two : echoOut [[46], [97], [98, 99]] = [97, 32, 98, 99, 10] := by decide

/-- The recorded `echo` output on the harness input is what the spec requires. -/
theorem echo_recorded : Data.LiteEcho.observed.stdout = echoOut harnessInput.argv := by decide

/-- The recorded mutant outputs are not. -/
theorem echo_nonl_recorded : Data.LiteEchoNonl.observed.stdout ≠ echoOut harnessInput.argv := by
  decide

theorem echo_stderr_recorded : Data.LiteEchoStderr.observed.stdout ≠ echoOut harnessInput.argv := by
  decide

theorem echo_exit1_recorded : Data.LiteEchoExit1.observed.outcome = .exited 1 := rfl

/-- The trace of a recorded run of a cat-like probe on stdin `l`: read it all, write the
recorded stdout, exit. (The recorded runs read and write in one chunk each.) -/
def catTrace (l out : List Byte) (code : Word) (fs : Fs.FileSystem) : List Event :=
  l.map (.readEv 0) ++ out.map (.writeEv 1) ++ [.exitEv code fs]

def helloLine : List Byte := [104, 101, 108, 108, 111, 10]

theorem cat_input : Data.LiteCat.observed.stdout = helloLine := by decide

/-- The harness launch with stdin `hello\n`, as recorded. -/
def catInput : ProcInput := { harnessInput with stdin := .ofList helloLine }

/-- `cat` on `hello\n`, as recorded (one read, one write, exit 0), meets `catSpec`. -/
theorem cat_recorded :
    catSpec.allowed catInput (catTrace helloLine helloLine 0 catInput.fs) 0 := by
  decide +kernel

/-- `cat_droplast` as recorded (writes `hello`, exits 0) does not. -/
theorem cat_droplast_recorded :
    ¬ catSpec.allowed catInput (catTrace helloLine (helloLine.take 5) 0 catInput.fs) 0 := by
  decide +kernel

/-- `cat_dup` as recorded (writes `hhello\n`, exits 0) does not. -/
theorem cat_dup_recorded :
    ¬ catSpec.allowed catInput (catTrace helloLine (104 :: helloLine) 0 catInput.fs) 0 := by
  decide +kernel

/-- `cat_exit1` as recorded (writes `hello\n`, exits 1) does not. -/
theorem cat_exit1_recorded :
    ¬ catSpec.allowed catInput (catTrace helloLine helloLine 1 catInput.fs) 1 := by
  decide +kernel

/-- `cat_once` on a one-chunk input behaves like `cat`: its refutation needs a run with two
reads (stdin of two bytes, a one-byte first read), which the trace check cannot see. The spec
rejects that run's trace: -/
theorem cat_once_two_chunks :
    ¬ catSpec.allowed { harnessInput with stdin := .ofList [97, 98] }
      ([.readEv 0 97, .writeEv 1 97, .exitEv 0 harnessInput.fs]) 0 := by
  decide +kernel

/-! ## The problems (open, WIP) -/

namespace Registry

/-- Open (expected solvable): `LiteEcho` against `echoSpec`. -/
@[problem "coreutils-lite/echo"]
def echo : Prop := Total Data.LiteEcho.probe.snapshot echoSpec

/-- Negative control (expected refutable): `LiteEchoNonl` against `echoSpec`. -/
@[problem "coreutils-lite/echo/mutant-nonl"]
def echoMutantNonl : Prop := Total Data.LiteEchoNonl.probe.snapshot echoSpec

/-- Negative control (expected refutable): `LiteEchoExit1` against `echoSpec`. -/
@[problem "coreutils-lite/echo/mutant-exit1"]
def echoMutantExit1 : Prop := Total Data.LiteEchoExit1.probe.snapshot echoSpec

/-- Negative control (expected refutable): `LiteEchoStderr` against `echoSpec`. -/
@[problem "coreutils-lite/echo/mutant-stderr"]
def echoMutantStderr : Prop := Total Data.LiteEchoStderr.probe.snapshot echoSpec

/-- Open (expected solvable): `LiteCat` against `catSpec`. -/
@[problem "coreutils-lite/cat"]
def cat : Prop := Total Data.LiteCat.probe.snapshot catSpec

/-- Negative control (expected refutable): `LiteCatDroplast` against `catSpec`. -/
@[problem "coreutils-lite/cat/mutant-droplast"]
def catMutantDroplast : Prop := Total Data.LiteCatDroplast.probe.snapshot catSpec

/-- Negative control (expected refutable): `LiteCatDup` against `catSpec`. -/
@[problem "coreutils-lite/cat/mutant-dup"]
def catMutantDup : Prop := Total Data.LiteCatDup.probe.snapshot catSpec

/-- Negative control (expected refutable): `LiteCatOnce` against `catSpec`. -/
@[problem "coreutils-lite/cat/mutant-once"]
def catMutantOnce : Prop := Total Data.LiteCatOnce.probe.snapshot catSpec

/-- Negative control (expected refutable): `LiteCatExit1` against `catSpec`. -/
@[problem "coreutils-lite/cat/mutant-exit1"]
def catMutantExit1 : Prop := Total Data.LiteCatExit1.probe.snapshot catSpec

end Registry

end Silmaril.Process.LPS.Problems.CoreutilsLite
