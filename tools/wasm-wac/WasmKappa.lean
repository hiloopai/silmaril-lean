import Silmaril.Wasm.Wac.StreamCore.Defs
import Silmaril.Wasm.JcoTool.KFitBuf.Defs

/-!
# `wasm-kappa`

Applies `StreamCore.kappa`, the `κ` of the generated stream modules, to the stream packages of a
composed binary, as `StreamFn.composeText_fn_equiv` reads them (`StreamFn.binShapes`: each
package's main core module):

```
wasm-kappa OUT.wasm NAME:KERNEL:N ...
```

The table is the generated modules `KDrop.genD KERNEL N` with export `NAME`, in order (the bytes
`wasm-wac-kbytes genD NAME KERNEL N` writes); module `j` stands for the code `TCode.take j` here,
so the printed code names the module `kappa` found. For each package it prints
`package I: kappa J` (the first module of the table whose bytes are the package's core module),
`package I: kappa none`, or `package I: other`. I/O only; `tools/wac/tests/kappa.sh` uses it.
-/

open Silmaril.Wasm.Wac Silmaril.Wasm.Wac.StreamCore Silmaril.Wasm.JcoTool
open Silmaril.Wasm.Component.Streams.Alg (TCode)

/-- The module of a spec `NAME:KERNEL:N`, tagged with its index. -/
def genOf (j : Nat) (spec : String) : Option Gen :=
  match spec.splitOn ":" with
  | [name, k, n] => do
    let km ← KFitBuf.toolKernel k
    let b ← n.toNat?
    some ⟨km, b, name, .take j⟩
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | f :: specs =>
    let some gs := (specs.zipIdx.map fun (s, j) => genOf j s).allSome
      | IO.eprintln "wasm-kappa: bad spec (NAME:KERNEL:N)"; pure 2
    let b ← IO.FS.readBinFile f
    match StreamFn.binShapes b with
    | .error e => IO.eprintln s!"wasm-kappa: {e}"; pure 1
    | .ok l =>
      for (o, i) in l.zipIdx do
        match o with
        | none => IO.println s!"package {i}: other"
        | some s =>
          match kappa gs s.core with
          | some (.take j) => IO.println s!"package {i}: kappa {j}"
          | some _ => IO.println s!"package {i}: kappa ?"
          | none => IO.println s!"package {i}: kappa none"
      pure 0
  | _ => IO.eprintln "usage: wasm-kappa OUT.wasm NAME:KERNEL:N ..."; pure 2
