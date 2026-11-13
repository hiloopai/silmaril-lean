module

public import Silmaril.Wasi.Cli.Defs
public import Silmaril.Wasi.Cli.HelloOs.Defs
public import Silmaril.Wasi.Examples.Defs

/-!
# WASI 0.2 components against behaviour specs, with refusals

A worked example of the WASI bridge `Silmaril.Wasi.Cli` with an environment that refuses: the WASI
0.2 component `hello` (`Silmaril.Wasi.Examples.hello`) ignores a failed write, so it is specified
with the behaviour model's `Spec.orRefused` and proved correct for every typed host
(`docs/projects/wasm-binaryen-tooling.md`, behaviour part).

The reading is the bridge's: `p2View` reads a WASI 0.2 trace as a partial observation
(`Silmaril.Cli.Seen`) whose `refused` flag records a write answered with anything but success
(`failedWrite2`), and `CliSat σ T p2View S` asks every play with at most one run to be a
partial view of a run `S` allows (`Spec.Partial`). An earlier step had a separate reading `p2Seen` and a
separate satisfaction `SeenSat` here; both are now the bridge's (`p2View.seen`, `CliSat`).

The theorems are in `Silmaril.Wasi.Cli.Refusal.Thms`, the proofs in
`Silmaril.Proofs.Wasi.Cli.Refusal`.

A Silmaril addition.
-/
