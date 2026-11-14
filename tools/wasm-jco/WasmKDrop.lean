import Silmaril.Wasm.JcoTool.KDrop.Defs
import Silmaril.Wasm.JcoTool.KFitBuf.Defs

/-!
# `wasm-kdrop`

Prints the core module (WebAssembly text) that `Silmaril.Wasm.JcoTool.KDrop.genD` generates from a
byte kernel: the drop-aware variant of `wasm-jco kcore` (see `docs/projects/wasm-wasi.md`, *
asyncmodel*). I/O only.

```
wasm-kdrop NAME KERNEL N     kernels: map, filter, takeN, lines, rechunkN; 1 ≤ N ≤ 256
```
-/

open Silmaril.Wasm.JcoTool

def main (args : List String) : IO UInt32 := do
  match args with
  | [name, k, n] =>
    match KFitBuf.toolKernel k, n.toNat? with
    | some km, some b =>
      if 1 ≤ b ∧ b ≤ 256 then
        IO.print (";; wasm-kdrop: Silmaril.Wasm.JcoTool.KDrop.genD (drop-aware callback)\n" ++
          (KDrop.genD km b).wat name)
        pure 0
      else IO.eprintln "wasm-kdrop: N must be in 1..256"; pure 1
    | _, _ => IO.eprintln s!"wasm-kdrop: unknown kernel {k} or bad N {n}"; pure 1
  | _ => IO.eprintln "usage: wasm-kdrop NAME KERNEL N"; pure 2
