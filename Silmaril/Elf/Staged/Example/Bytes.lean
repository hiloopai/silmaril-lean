module

public import Silmaril.Data.IncludeBytes
public import Silmaril.Data.IncludeBytes.Kernel
-- A native run interprets `IncludeBytes.decode`, so its code must be loaded at elaboration time.
public meta import Silmaril.Data.IncludeBytes.Types

/-! # The bytes of the staged example: `examples/dyn/pinned/hello-gcc`

`helloRaw` is the raw `ByteArray` that native leaves read (computable, so a native run can
evaluate it). The kernel leaves read core's kernel bytes of the same literals
(`kbytes_def hello of_include helloRaw`, with `hello.toByteArray_eq : hello.toByteArray =
helloRaw`). That definition sits in each leaf module rather than here, because the body of a
`kbytes_def` constant is not exported to importing modules yet (reported to core). The file
is pinned by `examples/dyn/pins.txt`.
-/

@[expose] public section

namespace Silmaril.Elf.Staged.Example

/-- `examples/dyn/pinned/hello-gcc` as raw bytes. -/
def helloRaw : ByteArray := include_bytes "../../../../examples/dyn/pinned/hello-gcc"

end Silmaril.Elf.Staged.Example
