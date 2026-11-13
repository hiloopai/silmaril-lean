module

public import Silmaril.Wasi.Versions.P3OverP2.Theory.Defs
public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Host3Clock
public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Host3Read

@[expose] public section

/-!
# WASI 0.3 over 0.2: the corrected 0.3 theories and `host3` (header)

Proofs in `Silmaril.Proofs.Wasi.Versions.P3OverP2.{Refute,Host3Clock,Host3Read}` (namespace
`Silmaril.Wasi.Versions.P3OverP2`).

REFUTED (explicit runs):

* `stdoutTh3_rejects_nullary`, `fsReadTh3_rejects_nullary`: the original stdout and read
  theories reject every answer to a `stream.write()` and to a `read-via-stream()`; no host
  answering all calls is a model. `host3_not_stdoutTh3`, `host3_not_fsReadTh3`: runs of `host3`.
* `host3_zero_read`: `host3` completes `stream.read r 0` with `0` items; `fsReadTh3` rejects it.
* `host3_clock_overflow`: `clockTh3` owes `now ≥ 2^64` after `now = 2^64 - 1`, `wait-for 1`, and
  rejects `host3`'s run; the saturated `clockTh3s` accepts it.

PROVED:

* `stdoutTh3w_of`, `clockTh3s_of`: the corrections are weakenings (every run accepted by the
  original is accepted by the corrected theory).
* **`host3_clockTh3s`**: every run of `host3 F` is accepted by `clockTh3s` (all runs, all `F`).
* **`host3_fsReadTh3w`**: every run of `host3 F` with fewer than `2^31` answers is accepted by
  `fsReadTh3w F`, for files shorter than `2^28` bytes. Both bounds come from `host3` as written
  (handles `2 |p| + 1` as `u32`; copy results packed as `16 k` in a `u32`); without them the
  statement is false: `host3_fsReadTh3w_needs_len`, `host3_fsReadTh3w_needs_file` in
  `Silmaril.Wasi.Versions.P3OverP2.Bounds.Thms`, with `fsReadTh3w_of` (the read correction is a
  weakening).
-/
