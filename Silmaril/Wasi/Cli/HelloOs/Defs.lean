module

public import Silmaril.Cli.Behaviour.Defs

/-!
# The CLI spec of `hello`

Track *behaviour* of `docs/projects/wasm-binaryen-tooling.md`, worked example. `hiSpec` is the CLI behaviour of the
`hello` program of `docs/projects/wasm-wasi.md` (the `wasi:cli/stdout` component `Silmaril.Wasi.Examples.hello`
and its hand-written x86 runtime `Silmaril.Wasi.Runtime.helloCode`): whatever the invocation, it
writes `hi` (no newline) to stdout, nothing to stderr, touches no file and exits `0`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli

open Silmaril.Cli

/-- **`hello` as a CLI spec**: print `hi`, exit `0`, touch no file. -/
def hiSpec : Spec := Spec.pure fun _ => { stdout := [0x68, 0x69] }

end Silmaril.Wasi.Cli
