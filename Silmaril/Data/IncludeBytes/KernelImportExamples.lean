module

public import Silmaril.Prelude.Bytes.Examples
public import Silmaril.Data.IncludeBytes.KernelExamples

/-! # Kernel bytes from another module (regression)

`kbytes_def` and `kbytes_def … of_include` add their declarations directly. Under the module
system they must be exported with their bodies: otherwise importers see opaque axioms, and
reads of imported bytes no longer reduce. These checks run in a module that imports them.
-/

@[expose] public section

namespace Silmaril.IncludeBytes.KernelImportExamples

open Silmaril.KBytes Silmaril.KBytes.Examples

example : hello.len = 15960 := hello.len_eq
example : hello.wf = true := hello.wf_true
example : hello = ofChunks 4096 15960 hello.chunks := hello.eq_ofChunks

/-- A kernel read of bytes defined in another module. -/
theorem importedMagic : hello.readLE 0 4 = some 0x464c457f := by decide +kernel

/-- A kernel `rfl` that unfolds imported trees: the two imports hold the same file. -/
theorem importedSame : Silmaril.IncludeBytes.KernelExamples.helloFile = hello := rfl

example : Silmaril.IncludeBytes.KernelExamples.hello.toByteArray =
    Silmaril.IncludeBytes.KernelExamples.helloRaw :=
  Silmaril.IncludeBytes.KernelExamples.hello.toByteArray_eq

end Silmaril.IncludeBytes.KernelImportExamples
