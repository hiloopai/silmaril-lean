module

public import Silmaril.Wasi.Cli.Defs
public import Silmaril.Wasi.Versions.P2.Os.Defs

/-!
# CLI views of the runs of the WASI example components

`hiSpec`: print `hi`, exit `0`, touch no file (`Spec.pure`). `Silmaril.Wasi.Cli.Examples.Thms`
reads the recorded runs of the WASI 0.2 components `hello` (`helloRun`, world `stdoutWorld`) and
`hello2` (`hello2Run`, `p2Command`) through `p2View`, and of the WASI 0.3 component `hello3`
(`hello3Run`) through `p3View`, and checks that each is a finished run `hiSpec` allows: a kernel
test of the views.

`teeRun` is a recorded WASI 0.2 run that reads stdin and writes a file under a preopened
directory; `teeSpec` is its spec: a kernel test of the views' stdin and file readings and of
the theory `cliTh2`.

These are single runs against one concrete host, not every-host statements. `hello` and `hello2`
ignore a failed write and still return `ok`, so they do **not** satisfy `hiSpec.orRefused` over
every host of the loose 0.2 theory, in which a write may fail (a refused write must end in a
nonzero exit there); an every-host 0.2 example needs a theory whose writes succeed, or a spec
allowing an empty stdout.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Examples

open Silmaril.Cli

/-- The bytes of `hi` (written out: the kernel does not evaluate `String.toUTF8` well). -/
def hiOut : Bytes := [104, 105]

/-- Print `hi`, exit `0`, touch no file. -/
def hiSpec : Spec := Spec.pure fun _ => { stdout := hiOut }

/-! ## A run that reads stdin and writes a file under a preopen -/

/-- **A recorded WASI 0.2 run of a `tee`-like command**: `get-directories` answers the preopen
`/work` (descriptor `3`), stdin delivers `hi`, `open-at(3, "out.txt")` gives descriptor `9`,
`write(9, "hi", 0)` writes both bytes, stdout gets `hi`, and `run` returns `ok`. -/
def teeRun : List WEv :=
  [.call cliRun [],
   .imp getDirs [] (some [.record [.record [.u32 3, strV "/work"]]]),
   .imp Versions.P2.getStdin [] (some [.u32 7]),
   .imp Versions.P2.isBread [.u32 7, .u64 100] (some [.variant 0 (some (bytesV [104, 105]))]),
   .imp openAt [.u32 3, strV "out.txt"] (some [.variant 0 (some (.u32 9))]),
   .imp fdWrite [.u32 9, bytesV [104, 105], .u64 0] (some [.variant 0 (some (.u64 2))]),
   .imp getStdout [] (some [.u32 8]),
   .imp streamWrite [.u32 8, bytesV [104, 105]] (some [.variant 0 none]),
   .ret cliRun [] (some [.variant 0 none])]

/-- The file `tee` writes. -/
def teeOut : FPath := ⟨"/work", ["out.txt"]⟩

/-- **`tee out.txt`**: stdin to stdout and to `/work/out.txt`, all of it, nothing else. -/
def teeSpec : Spec := fun i o =>
  o.stdout = i.stdin ∧ o.stderr = [] ∧ o.exit = 0 ∧ o.consumed = i.stdin.length ∧
    o.reads = [] ∧ o.fs = i.fs.set teeOut (some i.stdin)

/-- An invocation of `tee` with stdin `hi` and the root `/work`. -/
def teeIn : Input := { args := ["out.txt"], stdin := hiOut, roots := [{ name := "/work" }] }

end Silmaril.Wasi.Cli.Examples

end
