module

public import Silmaril.Wasi.Versions.P2.Host.Defs
public import Silmaril.Wasi.Os.Defs
public import Silmaril.Wasi.Comp.Defs

@[expose] public section

/-!
# WASI 0.2 hosts over the OS model of `Silmaril.Machine.Process.IoSpec`

The OS bridge (`Silmaril.Wasi.Os`) maps a successful `blocking-write-and-flush` answer to
LPS write events on a channel (`osEv`, `osTrace`) and replays filesystem answers on LPS's file
system (`fsOs`). This module extends the event map to the non-blocking `wasi:io` writes:

* `osEv2 ch`: a successful `write`, `blocking-write-and-flush` (bytes), `write-zeroes` or
  `blocking-write-zeroes-and-flush` (zero bytes) is the LPS trace of its bytes on `ch`. Like
  the base WASI theory's `osEv`, it does not distinguish streams: every output stream is read as `ch`.
* `osTrace2 ch`: the OS image of an event list.

## A WASI 0.2 component using the non-blocking protocol

`hello2` (world `p2Command`): `run` gets stdout, calls `check-write`; if the permit is at least
`2` it `write`s `hi` and calls `blocking-flush`, otherwise it falls back to
`blocking-write-and-flush`; then it drops the stream and returns `ok`. `hello2Run` is its run
against the concrete host `p2Impl` (`check-write` answers `4096`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2

open Silmaril.Process.LPS
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Games
open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

/-! ## The OS image -/

/-- **The OS events of a WASI 0.2 event** on the channel `ch`. -/
def osEv2 (ch : Word) : WEv → List Event
  | .imp f a (some [.variant 0 none]) =>
    if f = osWrite ∨ f = streamWrite then (contentsOf a).map (.writeEv ch)
    else if f = osWriteZeroes ∨ f = osBwzf then (List.replicate (lenOf a) 0).map (.writeEv ch)
    else []
  | _ => []

/-- **The OS image of a WASI 0.2 event list.** -/
def osTrace2 (ch : Word) (t : List WEv) : List Event := t.flatMap (osEv2 ch)

/-! ## `hello2` -/

/-- `get-stdout ∈ p2Imports`. -/
theorem getStdout_mem : getStdout ∈ p2Command.imports := by
  simp [p2Command, p2Imports, cliImports_eq]

/-- `check-write ∈ p2Imports`. -/
theorem checkWrite_mem : osCheckWrite ∈ p2Command.imports := by
  simp [p2Command, p2Imports, ioImports_eq]

/-- `write ∈ p2Imports`. -/
theorem write_mem : osWrite ∈ p2Command.imports := by
  simp [p2Command, p2Imports, ioImports_eq]

/-- `blocking-flush ∈ p2Imports`. -/
theorem bflush_mem : osBflush ∈ p2Command.imports := by
  simp [p2Command, p2Imports, ioImports_eq]

/-- `blocking-write-and-flush ∈ p2Imports`. -/
theorem bwf_mem : streamWrite ∈ p2Command.imports := by
  simp [p2Command, p2Imports, ioImports_eq]

/-- `[resource-drop]output-stream ∈ p2Imports`. -/
theorem drop_mem : streamDrop ∈ p2Command.imports := by
  simp [p2Command, p2Imports, ioImports_eq]

/-- The bytes of `hi`. -/
abbrev hi2 : List (BitVec 8) := Silmaril.Wasi.Examples.hiBytes

/-- `get-stdout()`. -/
def getOp2 : (nsig p2Command.imports).Op := (⟨getStdout, getStdout_mem⟩, [])
/-- `check-write(s)`. -/
def cwOp (s : BitVec 32) : (nsig p2Command.imports).Op := (⟨osCheckWrite, checkWrite_mem⟩, [.u32 s])
/-- `write(s, "hi")`. -/
def wrOp (s : BitVec 32) : (nsig p2Command.imports).Op :=
  (⟨osWrite, write_mem⟩, [.u32 s, bytesV hi2])
/-- `blocking-flush(s)`. -/
def bfOp (s : BitVec 32) : (nsig p2Command.imports).Op := (⟨osBflush, bflush_mem⟩, [.u32 s])
/-- `blocking-write-and-flush(s, "hi")`. -/
def bwfOp (s : BitVec 32) : (nsig p2Command.imports).Op :=
  (⟨streamWrite, bwf_mem⟩, [.u32 s, bytesV hi2])
/-- `[resource-drop]output-stream(s)`. -/
def dropOp2 (s : BitVec 32) : (nsig p2Command.imports).Op := (⟨streamDrop, drop_mem⟩, [.u32 s])

/-- After the drop: `ok`. -/
def h2Done : Option (List Val) → BProg p2Command.imports := fun _ => .pure (some [okV none])

/-- Drop the stream. -/
def h2Drop (s : BitVec 32) : Option (List Val) → BProg p2Command.imports :=
  fun _ => .call (dropOp2 s) h2Done

/-- After `write`: `blocking-flush`. -/
def h2Flush (s : BitVec 32) : Option (List Val) → BProg p2Command.imports :=
  fun _ => .call (bfOp s) (h2Drop s)

/-- After `check-write`: write within the permit, or fall back to `blocking-write-and-flush`. -/
def h2Write (s : BitVec 32) (r : Option (List Val)) : BProg p2Command.imports :=
  if 2 ≤ okNat r then .call (wrOp s) (h2Flush s) else .call (bwfOp s) (h2Drop s)

/-- After `get-stdout`. -/
def h2Got : Option (List Val) → BProg p2Command.imports
  | some [.u32 s] => .call (cwOp s) (h2Write s)
  | _ => .pure (some [errV none])

/-- **`hello2`**: `hi` on stdout through `check-write`, `write` and `blocking-flush`. -/
def hello2 : Body p2Command.imports p2Command.exports := fun _ => .call getOp2 h2Got

/-- The export call `run`. -/
def runQ2 : (nsig p2Command.exports).Op := (⟨cliRun, rfl⟩, [])

/-- **One run of `hello2`** against `p2Impl`. -/
def hello2Run : List (Move (nsig p2Command.imports) (nsig p2Command.exports)) :=
  [.inr (.ask runQ2), .inl (.ask getOp2), .inl (.ans getOp2 (some [.u32 0])),
   .inl (.ask (cwOp 0)), .inl (.ans (cwOp 0) (some [okV (some (.u64 4096))])),
   .inl (.ask (wrOp 0)), .inl (.ans (wrOp 0) (some [okV none])),
   .inl (.ask (bfOp 0)), .inl (.ans (bfOp 0) (some [okV none])),
   .inl (.ask (dropOp2 0)), .inl (.ans (dropOp2 0) (some [])), .inr (.ans runQ2 (some [okV none]))]

end Silmaril.Wasi.Versions.P2
