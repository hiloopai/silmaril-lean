import Silmaril.Wasm.JcoTool.KCoreEmit.Defs
import Silmaril.Wasm.JcoTool.KFitBuf.Defs
import Silmaril.Wasm.JcoTool.KDrop.Defs

/-!
# `wasm-wac-kbytes`

Writes the bytes of a generated stream core module, by silmaril's verified encoder
(`Silmaril.Wasm.JcoTool.KCoreEmit.wasmOf`; theorem `KCoreEmit.wasmOf_encodes`: the bytes encode
`KCoreEmit.toModule P NAME` in the Core binary grammar), for the program `P` of either generator:

```
wasm-wac-kbytes gen  NAME KERNEL N -o OUT.wasm    P = KCore.gen KERNEL N (as `wasm-jco kcore -o`)
wasm-wac-kbytes genD NAME KERNEL N -o OUT.wasm    P = KDrop.genD KERNEL N (drop-aware)
```

kernels: map, filter, takeN, lines, rechunkN; 1 ≤ N ≤ 256. Used by `tools/wac/tests/streams.sh`
to compose stages whose core modules are verified encodings through `wasm-wac compose --wasm`
(`EndToEnd.composeText`). I/O only.
-/

open Silmaril.Wasm.JcoTool

def main (args : List String) : IO UInt32 := do
  match args with
  | [g, name, k, n, "-o", out] =>
    match KFitBuf.toolKernel k, n.toNat?, g with
    | some km, some b, "gen" | some km, some b, "genD" =>
      if 1 ≤ b ∧ b ≤ 256 then
        let P := if g == "gen" then KCore.gen km b else KDrop.genD km b
        match KCoreEmit.wasmOf P name with
        | .ok bs => IO.FS.writeBinFile out bs; pure 0
        | .error e => IO.eprintln s!"wasm-wac-kbytes: {e}"; pure 1
      else IO.eprintln "wasm-wac-kbytes: N must be in 1..256"; pure 1
    | _, _, _ => IO.eprintln s!"wasm-wac-kbytes: unknown generator {g}, kernel {k} or bad N {n}"; pure 1
  | _ => IO.eprintln "usage: wasm-wac-kbytes {gen|genD} NAME KERNEL N -o OUT.wasm"; pure 2
