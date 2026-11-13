import Silmaril.Cli.Io.Run.Defs
import Silmaril.Cli.Io.Echon.Defs

/-!
# `cli-io-demo`

The example programs of `Silmaril.Cli.Io.Examples`, run with `Prog.toIO`: the same `Prog` values
that `echo_sat`, `cat_sat` and `copy_sat` are about. See `docs/projects/wasm-binaryen-tooling.md`.

```
cli-io-demo echo ARGS…        print ARGS joined by spaces, then a newline
cli-io-demo cat               copy stdin to stdout
cli-io-demo copy SRC -o DST   copy a file
cli-io-demo echon [-n] [--sep SEP] [WORD]...   a derived front end (Prog.ofCommand)
```
-/

open Silmaril.Cli.Io Silmaril.Cli.Io.Examples

def main : List String → IO UInt32
  | "echo" :: args => Prog.main echoProg args
  | "cat" :: args => Prog.main catProg args
  | "copy" :: args => Prog.main copyProg args
  | "echon" :: args => Prog.main Silmaril.Cli.Io.Echon.echonProg args
  | _ => do
    IO.eprintln "usage: cli-io-demo (echo ARGS… | cat | copy SRC -o DST | echon ARGS…)"
    pure 2
