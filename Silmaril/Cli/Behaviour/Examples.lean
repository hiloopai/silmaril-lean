module

public import Silmaril.Cli.Behaviour.Thms

/-!
# CLI behaviour: compiled examples

The examples of `docs/projects/cli.md`. Small CLI programs as specs, a Lean
implementation that refines its spec, laws of pipes and `&&`, and subcommand dispatch.
-/

@[expose] public section

namespace Silmaril.Cli.Examples.Behaviour

open Silmaril.Cli Silmaril.Cli.Spec

/-! ## Specs -/

/-- `true`. -/
def trueS : Spec := pure fun _ => {}

/-- `false`. -/
def falseS : Spec := pure fun _ => { exit := 1 }

/-- `echo ARGS…`: the arguments separated by spaces, and a newline. -/
def echo : Spec := pure fun i => { stdout := utf8 (" ".intercalate i.args ++ "\n") }

/-- `cat` (no arguments): stdin to stdout, all of it. -/
def cat : Spec := pure (fun i => { stdout := i.stdin }) ⊓ consumesAll

/-- A loose usage error: nothing on stdout, *some* message on stderr, exit `2`, no file
changed. The message itself is left open. -/
def usageError : Spec := exits 2 ⊓ keepsFiles ⊓ fun _ o => o.stdout = [] ∧ o.stderr ≠ []

/-- `tool echo ARGS…` and `tool cat`; anything else is a usage error. -/
def tool : Spec := dispatch [("echo", echo), ("cat", cat)] usageError

/-! ## An implementation refines its spec -/

/-- A Lean implementation of `echo`: a function from invocations to observations. -/
def echoImpl (i : Input) : Obs :=
  { stdout := utf8 (" ".intercalate i.args ++ "\n"), fs := i.fs }

example : det echoImpl ≤ echo :=
  det_le_iff.2 fun _ => ⟨rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, rfl⟩

/-- `echo` stays inside its footprint: it reads and writes no file. -/
example : echo ≤ confined := pure_le_confined _

/-! ## Laws -/

/-- `false && S` is `false`. -/
example (S : Spec) : andThen falseS S = falseS :=
  andThen_of_fails (fun _ o h => show o.exit ≠ 0 by rw [h.2.2.1]; exact (by decide : (1 : ExitCode) ≠ 0)) S

/-- `cat | cat` refines `cat`. -/
example : pipe cat cat ≤ cat := by
  rintro i o ⟨⟨o₁, o₂, fs₁, fs₂, ⟨⟨h1o, h1e, -, -, h1r, -, h1l⟩, h1all⟩,
    ⟨⟨h2o, h2e, h2x, -, h2r, -, h2l⟩, -⟩, hs, he, hx, hc, hr, hl, -⟩, hcoh⟩
  have hnil : Interleave [] [] o.stderr := by rw [h1e, h2e] at he; exact he
  have hlog : o.log = [] := by rw [h1l, h2l] at hl; exact Interleave.nil_left_eq hl
  have hfs : some i.fs = some o.fs := by
    have h : i.fs.replay o.log = some o.fs := hcoh
    rwa [hlog, Fs.replay_nil] at h
  have hcons : o.consumed = i.stdin.length := hc.trans h1all
  refine ⟨⟨hs.trans (h2o.trans h1o), Interleave.nil_left_eq hnil, hx.trans h2x,
    (Option.some.inj hfs).symm, by rw [hr, h1r, h2r]; rfl, hcons.le, hlog⟩, hcons⟩

/-! ## Shared files: the pipe is exact -/

/-- The file `x` in the current directory. -/
def xPath : FPath := ⟨".", ["x"]⟩

/-- `echo 1 > x` as a spec: write `x`, logged. -/
def writeX : Spec := fun i o =>
  o = { fs := i.fs.set xPath (some [49]), log := [.write xPath (some [49])] }

/-- `cat x` as a spec: print what `x` held when it was read, logged. -/
def catX : Spec := fun i o =>
  o = { stdout := (i.fs xPath).getD [], reads := [xPath], fs := i.fs,
        log := [.read xPath (i.fs xPath)] }

/-- The run of `echo 1 > x | cat x` in which `cat` reads `x` before it is written. -/
def catFirst : Obs :=
  { reads := [xPath], fs := Fs.empty.set xPath (some [49]),
    log := [.read xPath none, .write xPath (some [49])] }

/-- The run in which `cat` reads `x` after it is written. -/
def writeFirst : Obs :=
  { stdout := [49], reads := [xPath], fs := Fs.empty.set xPath (some [49]),
    log := [.write xPath (some [49]), .read xPath (some [49])] }

/-- **`echo 1 > x | cat x` may print the old `x`** (nothing, on an empty directory): `cat`
reads `x` before it is written. The sequential pipe (`pipeSeq`) does not allow this
run; `pipe` does. -/
example : pipe writeX catX {} catFirst :=
  ⟨⟨_, _, Fs.empty, Fs.empty, rfl, rfl, rfl, .nil, rfl, rfl, rfl, .right (.left .nil), rfl⟩, rfl⟩

/-- And it may print the new one, as `pipeSeq` does. -/
example : pipe writeX catX {} writeFirst :=
  ⟨⟨_, _, Fs.empty, Fs.empty.set xPath (some [49]), rfl, rfl, rfl, .nil, rfl, rfl, rfl,
    .left (.right .nil), rfl⟩, rfl⟩

/-- The sequential pipe misses the first run: there `cat` always prints `1`. -/
example (o : Obs) (h : pipeSeq writeX catX {} o) : o.stdout = [49] := by
  obtain ⟨o₁, o₂, rfl, rfl, hs, -⟩ := h
  exact hs

/-! ## Dispatch -/

/-- `tool echo hi` behaves as `echo hi`. -/
example (i : Input) (h : i.args = ["echo", "hi"]) :
    tool i = withArgs ["hi"] echo i :=
  dispatch_cons_self h

/-- Adding a subcommand `wc` to `tool` changes nothing for `tool echo …`. -/
example (wc : Spec) (i : Input) (h : i.args.head? = some "echo") :
    dispatch (("wc", wc) :: [("echo", echo), ("cat", cat)]) usageError i = tool i :=
  dispatch_cons_of_ne (by rw [h]; decide)

end Silmaril.Cli.Examples.Behaviour
