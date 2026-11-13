module

public import Silmaril.Wasi.Versions.P2.Os.Defs

@[expose] public section

/-!
# WASI 0.2: a component separating the strict and the loose reading

`trusting` (world `p2Command`) relies on the strict reading of `check-write`: `run` gets stdout
`s`, subscribes to it (pollable `p`), blocks on `p`, calls `check-write(s)` and, on any `ok(_)`,
writes one byte without looking at the permit. Under the strict reading the permit after a ready
pollable is at least `1`, so the write is within it; under the loose reading `check-write` may
answer `ok(0)` and the write exceeds the permit (`Silmaril.Wasi.Versions.P2.Sep.Thms`).

`trustRun`: the play in which the host answers `check-write` with `ok(0)`, ending with the
offending `write` request.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2

open Silmaril.Games
open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

/-- `output-stream.subscribe ∈ p2Imports`. -/
theorem subscribe_mem : osSubscribe ∈ p2Command.imports := by
  simp [p2Command, p2Imports, ioImports_eq]

/-- `pollable.block ∈ p2Imports`. -/
theorem block_mem : pollBlock ∈ p2Command.imports := by
  simp [p2Command, p2Imports, ioImports_eq]

/-- `subscribe(s)`. -/
def subOp (s : BitVec 32) : (nsig p2Command.imports).Op := (⟨osSubscribe, subscribe_mem⟩, [.u32 s])
/-- `block(p)`. -/
def blkOp (p : BitVec 32) : (nsig p2Command.imports).Op := (⟨pollBlock, block_mem⟩, [.u32 p])
/-- `write(s, "h")`: one byte. -/
def wr1Op (s : BitVec 32) : (nsig p2Command.imports).Op :=
  (⟨osWrite, write_mem⟩, [.u32 s, bytesV [0x68]])

/-- After the write: `ok`. -/
def tDone : Option (List Val) → BProg p2Command.imports := fun _ => .pure (some [okV none])

/-- After `check-write`: on `ok(_)`, write one byte without consulting the permit. -/
def tCw (s : BitVec 32) : Option (List Val) → BProg p2Command.imports
  | some [.variant 0 _] => .call (wr1Op s) tDone
  | _ => .pure (some [errV none])

/-- After `block`: `check-write`. -/
def tBlk (s : BitVec 32) : Option (List Val) → BProg p2Command.imports :=
  fun _ => .call (cwOp s) (tCw s)

/-- After `subscribe`: block on the pollable. -/
def tSub (s : BitVec 32) : Option (List Val) → BProg p2Command.imports
  | some [.u32 p] => .call (blkOp p) (tBlk s)
  | _ => .pure (some [errV none])

/-- After `get-stdout`: subscribe. -/
def tGot : Option (List Val) → BProg p2Command.imports
  | some [.u32 s] => .call (subOp s) (tSub s)
  | _ => .pure (some [errV none])

/-- **`trusting`**: trusts that a ready pollable makes `check-write` answer a positive permit. -/
def trusting : Body p2Command.imports p2Command.exports := fun _ => .call getOp2 tGot

/-- The play in which `check-write` answers `ok(0)` after the pollable was ready, ending with the
write request. -/
def trustRun : List (Move (nsig p2Command.imports) (nsig p2Command.exports)) :=
  [.inr (.ask runQ2), .inl (.ask getOp2), .inl (.ans getOp2 (some [.u32 0])),
   .inl (.ask (subOp 0)), .inl (.ans (subOp 0) (some [.u32 1])),
   .inl (.ask (blkOp 1)), .inl (.ans (blkOp 1) (some [])),
   .inl (.ask (cwOp 0)), .inl (.ans (cwOp 0) (some [okV (some (.u64 0))])),
   .inl (.ask (wr1Op 0))]

end Silmaril.Wasi.Versions.P2
