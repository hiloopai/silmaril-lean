module

public import Silmaril.Wasi.Cli.Main.Defs
public import Silmaril.Proofs.Wasi.Cli.Main.Front

/-!
# `Command.mainWith` on a WASI host: theorems

PROVED (standard axioms), namespace `Silmaril.Wasi.Cli`; proofs in
`Silmaril.Proofs.Wasi.Cli.Main.{Runs,Front}`.

* **Runs and plays.** `PRun` inversion and sequencing (`PRun.call_inv`, `PRun.bind_inv`,
  `PRun.bind_right`, `PRun.bind_mono`); **`plays_run`**: a play of a component built from
  programs (`ofBody h`) that calls its export at most once is empty, or the call followed by a
  run of the program (`runTrace`); **`play_of_run`**: conversely. `guar_of_runs`: a CLI
  guarantee transfers from one component to another whose runs include the first's.
* **The front end.** `Api.close_mainWith`, `Api.after_eq`, `Api.close_putLine`; **`Api.main_sim`**:
  under a theory that pins `get-arguments` and `get-environment` (`Api.ArgsOk`, `Api.EnvOk`),
  every run of `A.main c run` on the invocation `i` is a run of
  `A.after c.envVars (c.finish A.host run (c.outcome i))`: the WASI program runs the front
  end's decision on `i`.
* **`Api.cliSat_main`**: if printing a line is read as printing it (`Api.EmitOk`, a property of
  the version's host, view and failure allowance `F`) and each body satisfies `F (S m)` where
  the arguments resolve to `m`, the component `ofBody (A.body c run)` satisfies
  `F (c.spec S)` for every host of the theory (`CliSat`).

Instances: `Silmaril.Wasi.Cli.Host2.Thms` (WASI 0.2), `Silmaril.Wasi.Cli.Host3.Thms` (WASI 0.3).

A Silmaril addition; `docs/projects/wasm-binaryen-tooling.md`.
-/
