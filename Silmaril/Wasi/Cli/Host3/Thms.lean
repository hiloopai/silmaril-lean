module

public import Silmaril.Wasi.Cli.Host3.Defs
public import Silmaril.Proofs.Wasi.Cli.Host3.Sat

/-!
# A WASI 0.3 component behind an args grammar meets `Command.spec` for every host

PROVED (standard axioms), namespace `Silmaril.Wasi.Cli.Host3`.

* **`command3_sat`**: the WASI 0.3 component `command3 c run` (the `run` export runs
  `c.mainWith api3.host run` on `get-arguments`) satisfies `orFail (c.spec S)` through
  `p3CliView` under `cliTh3`, as soon as each body satisfies `orFail (S m)` on the invocations
  whose arguments resolve to `m` (stated for `api3.bodyAfter c.envVars (run m)`). Exit codes are
  exact (`exit-with-code`); the help, the version and usage errors (exit `2`) hold by
  construction (`emit3_ok`: the canonical ABI write of the line, `stream.new`,
  `write-via-stream`, `stream.write`, and the wait when the write blocks, read through the
  scan of `p3CliView`, for every answer of the host).
* **`command3_every_host`**: the same in every interaction with every host satisfying
  `cliTh3 i`.
* **`printer3_sat`**: a component whose body prints a line computed from the matches meets
  `orFail (c.spec fun m => lineSpec .stdout (f m) 0)`, with no hypothesis.
* `args3_ok`, `env3_ok`, `emit3_ok`.

A Silmaril addition; `docs/projects/wasm-binaryen-tooling.md`.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Host3

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Cli Silmaril.Games
open Silmaril.Wasi.Versions.P3 (run3)

/-- `orFail` at one invocation depends only on the specification there. -/
theorem orFail_mono_at {S S' : Spec} {i : Input} (h : ∀ o, S i o → S' i o) (o : Obs)
    (hs : Spec.orFail S i o) : Spec.orFail S' i o := by
  rcases hs with hs | ⟨hx, o', ho', hout⟩
  · exact .inl (h _ hs)
  · exact .inr ⟨hx, o', h _ ho', hout⟩

/-- **A WASI 0.3 component behind the grammar `c` meets `Command.spec`** (failures allowed),
given its bodies. -/
theorem command3_sat {c : Command} {run : Matches → CliM I3 UInt32} {S : Matches → Spec}
    (hrun : ∀ i m, c.outcome i = .run m →
      (ag (I := I3) (X := {run3}) (fun t => (cliTh3 i).Accepts (hostView t))
        (p3CliView.Guar (Spec.orFail (S m)) i)).holds (ofBody (api3.bodyAfter c.envVars (run m)))) :
    CliSat (command3 c run) cliTh3 p3CliView (Spec.orFail (c.spec S)) :=
  Api.cliSat_main (V := p3CliView) (F := Spec.orFail) api3 (fun q => q.1.2)
    (fun _ _ _ h => orFail_mono_at h) args3_ok env3_ok emit3_ok hrun

/-- **For every host** satisfying `cliTh3 i`. -/
theorem command3_every_host {c : Command} {run : Matches → CliM I3 UInt32} {S : Matches → Spec}
    (hrun : ∀ i m, c.outcome i = .run m →
      (ag (I := I3) (X := {run3}) (fun t => (cliTh3 i).Accepts (hostView t))
        (p3CliView.Guar (Spec.orFail (S m)) i)).holds (ofBody (api3.bodyAfter c.envVars (run m))))
    (i : Input) {Y : Sig.{0}} (η : Silmaril.Wasi.Host Y I3)
    (hη : (hostSat (cliTh3 i).Accepts).holds η) :
    ∀ p ∈ link η (command3 c run), ∃ t ∈ command3 c run, xtrace p = expView (wtrace t) ∧
      p3CliView.Guar (Spec.orFail (c.spec S)) i (wtrace t) :=
  (command3_sat hrun).every_host i η hη

/-- **A printer**: the component whose body prints `f m` on stdout and exits `0`. -/
theorem printer3_sat (c : Command) (f : Matches → String) :
    CliSat (command3 c fun m => api3.putLine .stdout (f m) >>= fun _ => pure 0) cliTh3 p3CliView
      (Spec.orFail (c.spec fun m => lineSpec .stdout (f m) 0)) :=
  command3_sat fun i m _ => emit3_ok i c.envVars .stdout (f m) 0

end Silmaril.Wasi.Cli.Host3

end
