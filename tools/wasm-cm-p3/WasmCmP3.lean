import Silmaril.Wasm.Component.BinaryP3.Check.Defs

/-!
# `wasm-cm-p3`

Prints `Silmaril.Wasm.Component.BinaryP3.Check.report` for each component binary given:
a line `file <path>`, then the report. See `tools/wasm-tools/README.md`.

```
wasm-cm-p3 FILE.wasm...
```

Exit status: 0 when every file was read (parse failures are reported, not errors), 1 when a
file could not be read, 2 on a usage error.
-/

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: wasm-cm-p3 FILE.wasm..."
    return 2
  let mut status : UInt32 := 0
  for f in args do
    match (← (IO.FS.readBinFile f).toBaseIO) with
    | .error e =>
      IO.eprintln s!"wasm-cm-p3: {f}: {e}"
      status := 1
    | .ok bs =>
      IO.println s!"file {f}"
      for l in Silmaril.Wasm.Component.BinaryP3.Check.report bs do
        IO.println l
  return status
