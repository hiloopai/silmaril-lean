module

public import Silmaril.Wasm.JcoTool.KFit.Defs

/-!
# Buffered kernels: which fit, which cannot, and an unbuffered lines kernel

`KLive.KFits k N` (the generated module never overflows its `CAP`-byte buffers) was proved only
for small kernels (`KFit.Small`: no buffer). The two buffered kernels of the tests differ:

* `kRechunk n` (`1 ≤ n ≤ 255`) keeps at most `n - 1` bytes in its buffer and emits at most `n + 1`
  bytes per chunk: it **fits** (`KFitBuf.Thms`, `rechunk_fits`), so every theorem conditional on
  `KFits` holds for it with no hypothesis.
* `kLines nl` keeps the current line in its buffer, and a line can be longer than any fixed
  region: it **does not fit** (`lines_not_fits`; `CAP` bytes without a newline, then one more
  byte, trap the module by design). No variant of the generator with a fixed memory can do
  better for this kernel's semantics (`(kLines nl).tr.runP` withholds a partial line until its
  newline, so the bytes of the line must be held somewhere; WebAssembly's 32-bit memory bounds
  them).
* `kLinesS nl` is the same transformer **on whole streams** without the buffer: it emits every
  byte at once and remembers only whether the current line is nonempty, so at the end it emits
  the final newline. It is small (`linesS_small`), and `(kLinesS nl).tr.run = (kLines nl).tr.run`
  on byte streams (`linesS_run`); only the chunking of its output differs (it does not withhold a
  partial line).

`toolKernel` is the kernel table of the tools (`wasm-jco kcore`, `wasm-kdrop`, `wasm-kappa`,
`wasm-wac-kbytes`): `KCore.kernelByName` with `lines` generated as `kLinesS 10`. Every kernel it
gives fits (`KFitBuf.Thms`, `toolKernel_fits`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KFitBuf

open Silmaril.Wasm.Component.Streams.Kernel (KExp KStmt KM)

/-- **Lines without a buffer**: emit every byte; the state is `1` inside a nonempty line; at the
end emit `nl` when the last line is nonempty. -/
def kLinesS (nl : Nat) : KM where
  init := 0
  step := .seq (.emit .x) (.set (.eqz (.eq .x (.lit nl))))
  flush := .ite .st (.emit (.lit nl)) .skip

/-- **The tools' kernels**: `KCore.kernelByName`, with `lines` as the unbuffered `kLinesS 10`. -/
def toolKernel (k : String) : Option KM :=
  if k == "lines" then some (kLinesS 10) else Silmaril.Wasm.JcoTool.KCore.kernelByName k

end Silmaril.Wasm.JcoTool.KFitBuf
