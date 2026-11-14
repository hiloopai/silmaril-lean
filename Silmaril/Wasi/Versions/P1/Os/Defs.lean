module

public import Silmaril.Wasi.Versions.P1.Theory.Defs
public import Silmaril.Wasi.Os.Defs

@[expose] public section

/-!
# Preview1 hosts over the OS model of `Silmaril.Machine.Process.IoSpec`

The OS image of preview1 events, in the style of `Silmaril.Wasi.Os` (Part D of `docs/projects/wasm-wasi.md`):

* `osEv ch`: a successful `fd_write(1, ciovecs)` answered `ok(n)` writes the first `n` bytes of
  the ciovecs to the stdout channel `ch` (`bytes.map (.writeEv ch)`); every other event emits
  nothing. `osTrace ch` is the image of an event list.
* `helloP1`: the answers of a preview1 `hello`: `fd_write(1, ["hi"])` answered `ok(2)`, then
  `proc_exit(0)` (no answer).

`Silmaril.Wasi.Versions.P1.Os.Thms` shows that its image is the image of the 0.2 `hello` run of
`Silmaril.Wasi.Os`, so the x86 runtimes of `Silmaril.Wasi.Runtime` refine it too.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P1

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Process.LPS (Event Word)

/-- The bytes of a ciovec list, in order. -/
def iovBytes : Val → List (BitVec 8)
  | .record bs => bs.flatMap bytesOf
  | _ => []

/-- **The OS events of a preview1 event** on the stdout channel `ch`. -/
def osEv (ch : Word) : WEv → List Event
  | .imp f (.u32 fd :: bufs :: _) (some [.variant 0 (some (.u32 n))]) =>
    if f = fn "fd_write" ∧ fd = 1 then ((iovBytes bufs).take n.toNat).map (.writeEv ch) else []
  | _ => []

/-- **The OS image of a preview1 event list.** -/
def osTrace (ch : Word) (t : List WEv) : List Event := t.flatMap (osEv ch)

/-- **The answers of a preview1 `hello`**: `fd_write(1, ["hi"])` writes 2 bytes, then
`proc_exit(0)`. -/
def helloP1 : List WEv :=
  [.imp (fn "fd_write") [.u32 1, .record [bytesV Silmaril.Wasi.Examples.hiBytes]] (okAns (some (.u32 2))),
   .imp (fn "proc_exit") [.u32 0] none]

end Silmaril.Wasi.Versions.P1
