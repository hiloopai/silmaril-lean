module

public import Silmaril.Data.IncludeBytes
public import Silmaril.Data.IncludeBytes.Kernel
-- A native run interprets `IncludeBytes.decode`, so its code must be loaded at elaboration time.
public meta import Silmaril.Data.IncludeBytes.Types

/-! # The bytes of the staged example: `examples/dyn/pinned/hello-gcc`

Twice, with a proof that they are the same bytes: `helloRaw`, the raw `ByteArray` that native
leaves read (computable, so a native run can evaluate it), and `hello`, core's kernel bytes of
the same literals that kernel leaves read, with `hello.wf_true` and
`hello.toByteArray_eq : hello.toByteArray = helloRaw` (no byte is decoded to prove it). The
file is pinned by `examples/dyn/pins.txt`.
-/

@[expose] public section

namespace Silmaril.Elf.Staged.Example

/-- `examples/dyn/pinned/hello-gcc` as raw bytes. -/
def helloRaw : ByteArray := include_bytes "../../../../examples/dyn/pinned/hello-gcc"

-- Kernel bytes from the same literals.
kbytes_def hello of_include helloRaw

end Silmaril.Elf.Staged.Example
