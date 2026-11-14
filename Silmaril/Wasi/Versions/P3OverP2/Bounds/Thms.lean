module

public import Silmaril.Wasi.Versions.P3OverP2.Bounds.Defs
public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Weaken
public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Bounds
public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Unclamped

@[expose] public section

/-!
# WASI 0.3 over 0.2: weakening, and why the bounds and the clamp are there (header)

Proofs in `Silmaril.Proofs.Wasi.Versions.P3OverP2.{Weaken,Bounds,Unclamped}` (namespace
`Silmaril.Wasi.Versions.P3OverP2`); standard axioms.

PROVED:

* **`fsReadTh3w_of`**: the corrected read theory is a weakening: every run accepted by
  `fsReadTh3 F` is accepted by `fsReadTh3w F` (`rdStepZ_of_rdStep`: the steps agree on
  well-shaped calls; `rdStep_unshaped`: an ill-shaped call that `rdStep` accepts keeps its
  state).

REFUTED (formal counterexamples):

* **`host3_fsReadTh3w_needs_len`**: the length bound `t.length < 2^31` of `host3_fsReadTh3w`
  is needed. `wrapRun` (`2^31 + 2` answers, files of one byte) follows `host3 wrapFile`; the
  second `read-via-stream` gets the handle `2 · 2^31 + 1 = 1` (as a `u32`), `host3` keeps
  reading the first file on it, and `fsReadTh3w wrapFile` rejects the byte.
* **`host3_fsReadTh3w_needs_file`**: the file bound `(F d).length < 2^28` is needed. `bigRun`
  (two answers, files of exactly `2^28` bytes) follows `host3 bigFile`; `COMPLETED 2^28` is
  packed as `2^32 = 0` (`COMPLETED 0`) with `2^28` items, which `fsReadTh3w bigFile` rejects.
* **`p3OverP2u_not_clock`**: the clamp of `now` is needed. The variant `p3OverP2u` answering the
  0.2 instant as it is satisfies `agP (p2ThF F) (retG clockTh3s)` for no `F`: in `latePlay`,
  `now = 5`, `wait-for 10` (the 0.2 pollable is reported ready), `now = 6` (the loose 0.2
  clock only asks for monotonic instants), and `clockTh3s` owes `now ≥ 15`.
-/
