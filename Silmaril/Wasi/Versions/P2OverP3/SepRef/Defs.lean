module

public import Silmaril.Wasi.Versions.P2OverP3.Sep.Defs

@[expose] public section

/-!
# WASI 0.2 over 0.3: a sentence of the reference machine about non-empty writes

`refNoZeroW`: a `stream.write(w, xs)` with `xs` non-empty does not answer `COMPLETED 0`. This
is what the reference machine (`definitions.py`, `End.copy`) guarantees:
`Silmaril.Wasm.Component.Async.RefZero.ref_own_progress_pos` proves that `copyCore` posts an event
for the copying end with progress `0` only when its buffer is empty, and the canon
`stream.write` (`definitions.py`, `copy`, L2466-2490) returns either `BLOCKED` or the event
`copyCore` posted for the end itself. (The step from `copyCore` to the canon built-in's return
value is by reading `definitions.py`; the copied machine's canon layer is not used here.)

`refW = pointwise refNoZeroW` is a protocol on host answers; `p3Th` does not contain it, and the
host answers of `sepPlay` violate it (`Silmaril.Wasi.Versions.P2OverP3.SepRef.Thms`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy)
open Silmaril.Wasi.Versions.P3

/-- A non-empty `stream.write` does not complete with `0` items. -/
def refNoZeroW : WEv → Bool
  | .imp f [_, xs] (some [.u32 c]) =>
    if f = cStreamWrite then (bytesOf xs).isEmpty || decide (c ≠ BitVec.ofNat 32 (packCopy .completed 0))
    else true
  | _ => true

/-- **The reference machine's rule for non-empty writes**, as a theory of host answers. -/
def refW : Protocol Unit WEv := pointwise refNoZeroW

end Silmaril.Wasi.Versions.P2OverP3
