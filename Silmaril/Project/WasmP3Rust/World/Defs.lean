module

public import Silmaril.Wasm.Component.BinaryP3.World.Defs

/-!
# The world `wasi:cli/command@0.3.0` (its `wasi:cli` part) as a `WorldType`

`command` is the component type of the world `command` of package `wasi:cli@0.3.0`, written
the way `wit-component` encodes a world (instance types defined before their imports, `use`d
types brought in by `alias export … (type)` and re-exported inside the using interface by
`alias outer 1 k` and `(export "…" (type (eq 0)))`):

| import / export | interface (WIT of `wasip3` 0.9.0+wasi-0.3.0, `wit/deps/cli.wit`) |
|---|---|
| `wasi:cli/environment@0.3.0` | `get-environment: func() -> list<tuple<string, string>>`, `get-arguments: func() -> list<string>`, `get-initial-cwd: func() -> option<string>` |
| `wasi:cli/exit@0.3.0` | `exit: func(status: result)`, `exit-with-code: func(status-code: u8)` |
| `wasi:cli/types@0.3.0` | `enum error-code { io, illegal-byte-sequence, pipe }` |
| `wasi:cli/stdin@0.3.0` | `read-via-stream: func() -> tuple<stream<u8>, future<result<_, error-code>>>` |
| `wasi:cli/stdout@0.3.0`, `wasi:cli/stderr@0.3.0` | `write-via-stream: func(data: stream<u8>) -> future<result<_, error-code>>` |
| `wasi:cli/terminal-input@0.3.0`, `terminal-output` | `resource terminal-input` / `terminal-output` |
| `wasi:cli/terminal-stdin@0.3.0`, `-stdout`, `-stderr` | `get-terminal-…: func() -> option<terminal-…>` |
| export `wasi:cli/run@0.3.0` | `run: async func() -> result` |

**Omitted**: the imports `command` takes from the worlds it includes outside `wasi:cli`
(`wasi:clocks`, `wasi:filesystem`, `wasi:sockets`, `wasi:random`). `World.targets` asks the
world to provide each import of the component, so a component that targets `command` also
targets any world with more imports; none of the examples imports them. The interfaces above
are those of the WIT that `wasip3` 0.9.0 (the crate the examples are built with) embeds; the
vendored `vendor/wasi/0.3.2/cli` states the same functions, every one `@since(version = 0.3.0)`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.Cli

open Silmaril.Wasm.Component.Binary

/-- `(alias outer 1 k (type))` in an instance type. -/
def outerT (k : Nat) : InstanceDecl := .alias ⟨.type, .outer 1 k⟩

/-- An instance type `(export "n" (type (eq 0)))` after an outer alias, re-exporting a used type. -/
def useT (k : Nat) (n : String) : List InstanceDecl := [outerT k, .export n (.type (.eq 0))]

/-- `wasi:cli/environment`. -/
def environmentT : DefType := .instance
  [.type (.val (.list (.prim .string))),
   .type (.val (.tuple [.prim .string, .prim .string])),
   .type (.val (.list (.idx 1))),
   .type (.func ⟨[], some (.idx 2), false⟩),
   .export "get-environment" (.func 3),
   .type (.func ⟨[], some (.idx 0), false⟩),
   .export "get-arguments" (.func 4),
   .type (.val (.option (.prim .string))),
   .type (.func ⟨[], some (.idx 5), false⟩),
   .export "get-initial-cwd" (.func 6)]

/-- `wasi:cli/exit`. -/
def exitT : DefType := .instance
  [.type (.val (.result none none)),
   .type (.func ⟨[("status", .idx 0)], none, false⟩),
   .export "exit" (.func 1),
   .type (.func ⟨[("status-code", .prim .u8)], none, false⟩),
   .export "exit-with-code" (.func 2)]

/-- `wasi:cli/types`. -/
def typesT : DefType := .instance
  [.type (.val (.enum ["io", "illegal-byte-sequence", "pipe"])),
   .export "error-code" (.type (.eq 0))]

/-- `wasi:cli/stdin`, with `error-code` the outer type `k`. -/
def stdinT (k : Nat) : DefType := .instance (useT k "error-code" ++
  [.type (.val (.stream (some (.prim .u8)))),
   .type (.val (.result none (some (.idx 1)))),
   .type (.val (.future (some (.idx 3)))),
   .type (.val (.tuple [.idx 2, .idx 4])),
   .type (.func ⟨[], some (.idx 5), false⟩),
   .export "read-via-stream" (.func 6)])

/-- `wasi:cli/stdout` and `wasi:cli/stderr`, with `error-code` the outer type `k`. -/
def writeT (k : Nat) : DefType := .instance (useT k "error-code" ++
  [.type (.val (.stream (some (.prim .u8)))),
   .type (.val (.result none (some (.idx 1)))),
   .type (.val (.future (some (.idx 3)))),
   .type (.func ⟨[("data", .idx 2)], some (.idx 4), false⟩),
   .export "write-via-stream" (.func 5)])

/-- `wasi:cli/terminal-input` and `terminal-output`: one resource. -/
def resourceT (n : String) : DefType := .instance [.export n (.type .subResource)]

/-- `wasi:cli/terminal-stdin` and the others: `get-…: func() -> option<r>`, with the resource
`r` the outer type `k`. -/
def terminalT (k : Nat) (r f : String) : DefType := .instance (useT k r ++
  [.type (.val (.own 1)),
   .type (.val (.option (.idx 2))),
   .type (.func ⟨[], some (.idx 3), false⟩),
   .export f (.func 4)])

/-- `wasi:cli/run`. -/
def runT : DefType := .instance
  [.type (.val (.result none none)),
   .type (.func ⟨[], some (.idx 0), true⟩),
   .export "run" (.func 1)]

/-- The interface name `wasi:cli/i@0.3.0`. -/
def cli (i : String) : ExternName := ⟨s!"wasi:cli/{i}@0.3.0", .plain0⟩

/-- **`wasi:cli/command@0.3.0`** (its `wasi:cli` part), as a component type. Type indices:
`0` environment, `1` exit, `2` types, `3` `error-code`, `4` stdin, `5` stdout, `6` stderr,
`7` terminal-input, `8` its resource, `9` terminal-output, `10` its resource, `11`–`13` the
terminal streams, `14` run. -/
def command : Silmaril.Wasm.Wit.Project.WorldType :=
  [.inst (.type environmentT), .import (cli "environment") (.instance 0),
   .inst (.type exitT), .import (cli "exit") (.instance 1),
   .inst (.type typesT), .import (cli "types") (.instance 2),
   .inst (.alias ⟨.type, .export 2 "error-code"⟩),
   .inst (.type (stdinT 3)), .import (cli "stdin") (.instance 4),
   .inst (.type (writeT 3)), .import (cli "stdout") (.instance 5),
   .inst (.type (writeT 3)), .import (cli "stderr") (.instance 6),
   .inst (.type (resourceT "terminal-input")), .import (cli "terminal-input") (.instance 7),
   .inst (.alias ⟨.type, .export 6 "terminal-input"⟩),
   .inst (.type (resourceT "terminal-output")), .import (cli "terminal-output") (.instance 9),
   .inst (.alias ⟨.type, .export 7 "terminal-output"⟩),
   .inst (.type (terminalT 8 "terminal-input" "get-terminal-stdin")),
   .import (cli "terminal-stdin") (.instance 11),
   .inst (.type (terminalT 10 "terminal-output" "get-terminal-stdout")),
   .import (cli "terminal-stdout") (.instance 12),
   .inst (.type (terminalT 10 "terminal-output" "get-terminal-stderr")),
   .import (cli "terminal-stderr") (.instance 13),
   .inst (.type runT), .inst (.export (cli "run") (.instance 14))]

end Silmaril.Project.WasmP3Rust.Cli

end
