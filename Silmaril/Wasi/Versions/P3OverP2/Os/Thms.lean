module

public import Silmaril.Wasi.Versions.P3OverP2.Os.Defs
public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Os
public import Silmaril.Proofs.Wasi.Versions.P3OverP2.OsSep

@[expose] public section

/-!
# WASI 0.3 over 0.2: the OS image (header)

Proofs in `Silmaril.Proofs.Wasi.Versions.P3OverP2.{OsStore,OsInv,Os,OsSep}` (namespace
`Silmaril.Wasi.Versions.P3OverP2`); standard axioms.

PROVED:

* **`p3OverP2_os`**: over every 0.2 host `η` whose answers `pointwise P2.p2Ok` accepts, for every
  play `p` of the composite `link η p3OverP2` with `PollDone (htrace p)` (no `stream.write`
  answered `BLOCKED`, fewer than `2^29` answers), there is the host's part `s ∈ η` of `p` with
  `osTrace3 ch (htrace p) <+: P2.osTrace2 ch (htrace s)`, and equality when `settled (xtrace p)`
  (no 0.3 call is running). The bytes the composite accepted on its 0.3 stdout streams are the
  bytes its 0.2 host wrote, in order, as LPS write events on `ch`; with the base WASI theory's bridge
  (`P2.osTrace2 = Silmaril.Wasi.Os.osTrace` on `blocking-write-and-flush`, `P2.osTrace2_eq_osTrace`)
  they are events of the IoSpec OS model.
* `p3OverP2_os_p2Th`, `p3OverP2_os_F`: the same over every host of `P2.p2Th r` and of
  `p2ThF F` (the 0.2 theory of `p3OverP2_model`).
* `os_wpInv`, `play_os`: the invariant (`OsInv`, `Silmaril.Proofs.Wasi.Versions.P3OverP2.OsInv`)
  and the component-level statement.

What `PollDone` excludes, and why:

* A `stream.write` answered `BLOCKED` leaves bytes pending. The component then writes them to
  0.2 by `blocking-write-and-flush` when the writable end is dropped, which the 0.3 image does not
  count: the 0.3 image is then a sublist, not a prefix, of the 0.2 image (not formalized).
* `osTrace3` counts the bytes of a `stream-write` event for every writable end it marked as
  stdout, also for bytes a guest reader took before the readable end was handed to
  `write-via-stream` (a guest `stream.write` answered `BLOCKED`, then read by the guest).
  **REFUTED without `PollDone`: `p3OverP2_os_needs_pollDone`**, a play of `p3OverP2` (`guestPlay`)
  whose 0.2 answers `p2Ok` accepts, whose 0.3 image is the byte `7` on the channel `1`, and whose
  0.2 image is empty.
* `2^29` answers keep the component below `2^32` handles (it allocates at most four per call), so
  that `write-via-stream` always binds.

Not proved: liveness of the poll loop (that `PollDone` runs are the typical ones; a host whose
`check-write` keeps answering `0` makes every write `BLOCKED`).
-/
