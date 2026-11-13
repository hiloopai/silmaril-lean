import Silmaril.Cerberus.Elab.Translate.Defs

/-! # `core-elab`: typed Ail → Cerberus Core in Lean

```
core-elab [-o OUT] FILE.tail.sexp     elaborate a `cerb-oracle --level tail` document and print the Core
                                      document (`cerb-oracle --level core`'s format) to OUT or stdout
```

Exit status: 0 document written, 1 not supported (message on stderr), 2 usage or I/O error, 3 the input does
not decode.
-/

open Silmaril.Cerberus

def main (args : List String) : IO UInt32 := do
  let (out, rest) := match args with
    | "-o" :: o :: rest => (some o, rest)
    | rest => (none, rest)
  let [path] := rest | IO.eprintln "usage: core-elab [-o OUT] FILE.tail.sexp"; return 2
  let text ← IO.FS.readFile path
  match Ail.Codec.readTailDocument text with
  | .error e => IO.eprintln s!"core-elab: {path}: not a typed-Ail document: {e}"; return 3
  | .ok tail =>
    match Elab.elaborate tail with
    | .error e => IO.eprintln s!"core-elab: {path}: {e}"; return 1
    | .ok b =>
      let doc := Elab.printDocument b
      match out with
      | some o => IO.FS.writeFile o doc
      | none => IO.print doc
      return 0
