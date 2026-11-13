module

public import Silmaril.Wasi.Cli.Host2.Defs
public import Silmaril.Proofs.Wasi.Cli.Host2.Sat

/-!
# A WASI 0.2 component behind an args grammar meets `Command.spec` for every host

PROVED (standard axioms), namespace `Silmaril.Wasi.Cli.Host2`.

* **`command2_sat`**: the WASI 0.2 component `command2 c run` (the `run` export runs
  `c.mainWith api2.host run` on `get-arguments`) satisfies `spec2 (c.spec S)` through `p2View`
  under `cliTh2`, as soon as each body satisfies `spec2 (S m)` on the invocations whose
  arguments resolve to `m` (stated for the component that runs `get-arguments`,
  `get-environment` and the body: `api2.bodyAfter c.envVars (run m)`). Help, version and usage
  errors hold by construction: they are printed through the host and read through the view
  (`emit2_ok`).
* **`command2_every_host`**: the same in every interaction with every host satisfying
  `cliTh2 i` (`CliSat.every_host`).
* **`printer2_sat`**: a component whose body prints a line computed from the matches meets
  `spec2 (c.spec fun m => lineSpec .stdout (f m) 0)`, with no hypothesis.
* `args2_ok`, `env2_ok`, `emit2_ok`: the three facts about the WASI 0.2 host that
  `Api.cliSat_main` needs.

`spec2 S = orFail (exit01 S)`: WASI 0.2 reports only success or failure (`exit01`), and a host
may fail a write (`Spec.orFail`: a nonzero exit after a prefix of stdout).

A Silmaril addition; `docs/projects/wasm-binaryen-tooling.md`.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Host2

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Cli Silmaril.Games
open Silmaril.Wasm.Resource (Protocol)

/-- `spec2` at one invocation depends only on the specification there. -/
theorem spec2_mono_at {S S' : Spec} {i : Input} (h : ∀ o, S i o → S' i o) (o : Obs)
    (hs : spec2 S i o) : spec2 S' i o := by
  rcases hs with ⟨o', ho', rfl⟩ | ⟨hx, o', ⟨o'', ho'', rfl⟩, hout, herr⟩
  · exact .inl ⟨o', h _ ho', rfl⟩
  · exact .inr ⟨hx, _, ⟨o'', h _ ho'', rfl⟩, hout, herr⟩

/-- **A WASI 0.2 component behind the grammar `c` meets `Command.spec`** (exit codes read as
`0`/`1`, failures allowed), given its bodies. -/
theorem command2_sat {c : Command} {run : Matches → CliM I2 UInt32} {S : Matches → Spec}
    (hrun : ∀ i m, c.outcome i = .run m →
      (ag (I := I2) (X := {cliRun}) (fun t => (cliTh2 i).Accepts (hostView t))
        (p2View.Guar (spec2 (S m)) i)).holds (ofBody (api2.bodyAfter c.envVars (run m)))) :
    CliSat (command2 c run) cliTh2 p2View (spec2 (c.spec S)) :=
  Api.cliSat_main (V := p2View) (F := spec2) api2 (fun q => q.1.2)
    (fun _ _ _ h => spec2_mono_at h) args2_ok env2_ok emit2_ok hrun

/-- **For every host**: in every interaction with a host satisfying `cliTh2 i`, the play of
the component is seen as a run of `spec2 (c.spec S)` on `i`. -/
theorem command2_every_host {c : Command} {run : Matches → CliM I2 UInt32} {S : Matches → Spec}
    (hrun : ∀ i m, c.outcome i = .run m →
      (ag (I := I2) (X := {cliRun}) (fun t => (cliTh2 i).Accepts (hostView t))
        (p2View.Guar (spec2 (S m)) i)).holds (ofBody (api2.bodyAfter c.envVars (run m))))
    (i : Input) {Y : Sig.{0}} (η : Silmaril.Wasi.Host Y I2)
    (hη : (hostSat (cliTh2 i).Accepts).holds η) :
    ∀ p ∈ link η (command2 c run), ∃ t ∈ command2 c run, xtrace p = expView (wtrace t) ∧
      p2View.Guar (spec2 (c.spec S)) i (wtrace t) :=
  (command2_sat hrun).every_host i η hη

/-- **A printer**: the component whose body prints `f m` on stdout and exits `0`. -/
theorem printer2_sat (c : Command) (f : Matches → String) :
    CliSat (command2 c fun m => api2.putLine .stdout (f m) >>= fun _ => pure 0) cliTh2 p2View
      (spec2 (c.spec fun m => lineSpec .stdout (f m) 0)) :=
  command2_sat fun i m _ => emit2_ok i c.envVars .stdout (f m) 0

end Silmaril.Wasi.Cli.Host2

end
