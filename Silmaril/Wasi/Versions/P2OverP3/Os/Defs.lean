module

public import Silmaril.Wasi.Versions.P2OverP3.Sep.Defs

@[expose] public section

/-!
# WASI 0.2 over 0.3: a `hello` run and its OS image

`helloCalls`: a WASI 0.2 guest's calls `get-stdout()` and `blocking-write-and-flush(0, "hi")`,
served by `p2OverP3 4096` against WASI 0.3 answers of the concrete stdout host `stdout3Impl`
(`stream.new` → `1, 2`; `write-via-stream(1)` → `3`; `stream.write(2, "hi")` → `COMPLETED 2`).
`helloPlay` is the resulting play. Its OS images are compared in
`Silmaril.Wasi.Versions.P2OverP3.Os.Thms`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (packCopy)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2

theorem exp2_bwf : osBwf ∈ exp2 := by simp [exp2, ioImports_eq]

/-- `blocking-write-and-flush(h, bs)`. -/
def xBwf (h : BitVec 32) (bs : List (BitVec 8)) : XOp := (⟨osBwf, exp2_bwf⟩, [.u32 h, bytesV bs])

/-- **The calls of a WASI 0.2 `hello`**, with the answers of `stdout3Impl`. -/
def helloCalls : List (XOp × List (Option (List Val))) :=
  [(xGetStdout, [some [natV 1, natV 2], some [natV 3]]),
   (xBwf 0 Silmaril.Wasi.Examples.hiBytes, [some [natV (packCopy .completed 2)]])]

/-- **The `hello` run of WASI 0.2 over 0.3.** -/
def helloPlay : List (Move (nsig imp3) (nsig exp2)) :=
  ((session (body 4096) St.init helloCalls).map (·.1)).getD []

end Silmaril.Wasi.Versions.P2OverP3
