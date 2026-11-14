module

public import Silmaril.Wasi.Cli.Greet.Defs
public import Silmaril.Wasi.Cli.Host2.Thms
public import Silmaril.Wasi.Cli.Host3.Thms
public import Silmaril.Wasi.Cli.Main.Thms

/-!
# `greet` meets its specification for every WASI host

PROVED (standard axioms), namespace `Silmaril.Wasi.Cli.Greet`:

* **`greet3_sat`**: the WASI 0.3 component meets `orFail greetSpec` through `p3CliView` under
  `cliTh3` (exact exit codes: `0` for a greeting, help and version, `2` for a usage error);
* **`greet2_sat`**: the WASI 0.2 component meets `spec2 greetSpec` through `p2View` under
  `cliTh2` (exit codes read as `0`/`1`);
* `greet3_usage`: on an invocation whose arguments do not parse, a run `orFail greetSpec`
  allows writes nothing on stdout and exits nonzero.
* **Not vacuous** (kernel evaluation, `decide +kernel`): `greetTrace argv` runs `greet3`'s `run`
  program against the cooperative host `coopHost3 argv` (it is a play of `greet3`:
  `greetTrace_play`); with `--name x` it prints `hello, x` and exits `0` (`greet_name`), without
  it `hello, world` (`greet_default`), and `-V` prints `greet 1.0.0` (`greet_version`). A
  component that always failed would also satisfy `orFail greetSpec`; these runs show this one
  does not. (The kernel does not reduce the derived usage-error text, so that case is covered by
  `greet3_usage` only.)

A Silmaril addition; `docs/projects/wasm-binaryen-tooling.md`.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Greet

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Cli
open Silmaril.Wasm.Component (Val)

/-- **`greet` over WASI 0.3 meets its spec for every host of `cliTh3`.** -/
theorem greet3_sat : CliSat greet3 cliTh3 p3CliView (Spec.orFail greetSpec) :=
  Host3.printer3_sat greetCmd greetLine

/-- **`greet` over WASI 0.2 meets its spec for every host of `cliTh2`.** -/
theorem greet2_sat : CliSat greet2 cliTh2 p2View (Host2.spec2 greetSpec) :=
  Host2.printer2_sat greetCmd greetLine

/-- On a usage error, a run allowed by `orFail greetSpec` writes nothing on stdout and exits
nonzero. -/
theorem greet3_usage {i : Input} (h : greetCmd.UsageErr i) {o : Obs} (ho : Spec.orFail greetSpec i o) :
    o.stdout = [] ∧ o.exit ≠ 0 := by
  rcases ho with ho | ⟨hx, o', ho', hout⟩
  · have hu := spec_usageError h ho
    exact ⟨hu.2.1, by rw [hu.1]; decide⟩
  · have hu := spec_usageError h ho'
    exact ⟨List.prefix_nil.1 (hu.2.1 ▸ hout), hx⟩

/-! ## Not vacuous: a cooperative host -/

/-- **A cooperative WASI 0.3 host** for the arguments `argv`. -/
def coopHost3 (argv : List String) : FnName → List Val → Option (List Val) := fun f a =>
  if f = W3.getArgs then some [.record (argv.map strV)]
  else if f = W3.getEnv then some [.record []]
  else if f = Versions.P3.cStreamNew then some [.u32 1, .u32 2]
  else if f = Versions.P3.stdoutWrite3 ∨ f = W3.stderrWrite then some [.u32 3]
  else if f = Versions.P3.cStreamWrite then
    match a with
    | [_, buf] => some [Versions.P3.natV (16 * (bytesOf buf).length)]
    | _ => none
  else if f = Versions.P3.cStreamDropW then some []
  else none

/-- The `run` call. -/
def runQ : (nsig p3CliWorld.exports).Op := (⟨Versions.P3.run3, rfl⟩, [])

/-- The events of `greet3`'s `run` on `coopHost3 argv`, with the return. -/
def greetTrace (argv : List String) : List WEv :=
  let r := traceOf (coopHost3 argv)
    (Host3.api3.main greetCmd fun m => Host3.api3.putLine .stdout (greetLine m) >>= fun _ => pure 0)
    64
  runTrace runQ r.1 r.2

/-- It is a play of `greet3`. -/
theorem greetTrace_play (argv : List String) : ∃ s ∈ greet3, wtrace s = greetTrace argv :=
  play_of_run (PRun.traceOf_run _ _ _)

theorem greet_name :
    p3CliView.stdout (greetTrace ["greet", "--name", "x"]) = utf8 "hello, x\n" ∧
      p3CliView.code (greetTrace ["greet", "--name", "x"]) = some 0 := by
  decide +kernel

theorem greet_default :
    p3CliView.stdout (greetTrace ["greet"]) = utf8 "hello, world\n" ∧
      p3CliView.code (greetTrace ["greet"]) = some 0 := by
  decide +kernel

theorem greet_version :
    p3CliView.stdout (greetTrace ["greet", "-V"]) = utf8 "greet 1.0.0\n" ∧
      p3CliView.code (greetTrace ["greet", "-V"]) = some 0 := by
  decide +kernel

end Silmaril.Wasi.Cli.Greet

end
