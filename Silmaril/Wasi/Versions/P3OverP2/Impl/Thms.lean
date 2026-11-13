module

public import Silmaril.Wasi.Versions.P3OverP2.Impl.Defs
public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Main

@[expose] public section

/-!
# WASI 0.3 over 0.2: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.Wasi.Versions.P3OverP2.*`, namespace
`Silmaril.Wasi.Versions.P3OverP2`). The component `p3OverP2` (importing the WASI 0.2 command slice,
exporting the WASI 0.3 slice with its `canon` built-ins) is an **implementation morphism** from
WASI 0.3 to WASI 0.2:

* **`p3OverP2_model`**: for every host `η` of `p2ThF F` (the loose 0.2 theory `P2.p2Th .loose`
  with the file contents `F` behind `read-via-stream`, `fsRead2 F`), `link η p3OverP2` is a
  model of `p3Th F` = `typed3 ⊗ clockTh3s ⊗ stdoutTh3w ⊗ fsReadTh3w F`;
  `p3OverP2_loose`: in particular over the loose host of `p2ThF F`.
* Separately, with the hypotheses each needs: `p3OverP2_typed`, `p3OverP2_clock`,
  `p3OverP2_stdout` hold over **every** 0.2 host (any theory `T`); `p3OverP2_read` over every
  host of `fsRead2 F`.
* The component guarantees (`Silmaril.Wasi.Versions.Stateful.ag_of_wpInv`): `typed_sat`,
  `clock_sat`, `stdout_sat` (for every `T`), `read_sat` (under `fsRead2 F`), with the invariants
  `ClockJ`, `OutJ`, `RdJ`.

What the proofs use, and what they do not:

* `typed3`, `clockTh3s`, `stdoutTh3w` do not depend on the 0.2 host: the component builds every
  answer from its own state (the clock is **clamped** to the last answer and to the bound owed by
  `wait-for`, since the 0.2 theory does not relate `subscribe-duration` to `now`; a
  `future.read` reports `ok` only after the component saw the writable end dropped).
* `fsReadTh3w F` uses `fsRead2 F`: the bytes of a 0.3 read are those of the 0.2
  `blocking-read`, and its end is the 0.2 stream's error. The bound `k ≤ n` is checked by the
  component (an answer with more bytes kills the binding), not taken from `P2.ioTh`.
* The 0.3 theories are the corrected ones of `Silmaril.Wasi.Versions.P3OverP2.Theory`; for the
  original `stdoutTh3`, `fsReadTh3 F`, `clockTh3` see the refutations there.

The OS image (the bytes accepted on a 0.3 stdout stream against the bytes written to 0.2) is
related in `Silmaril.Wasi.Versions.P3OverP2.Os.Thms` (`p3OverP2_os`, for runs where the poll loop
finishes). Not proved: liveness of the poll loop, and the guest permit discipline of the
component towards 0.2 (`P2.permitG`).
-/
