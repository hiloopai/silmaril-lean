module

public import Silmaril.Elf.Abi.Defs
public import Silmaril.Elf.Asm.Defs

/-!
# ABI conformance over assembly functions: the typed adapter

An assembly function (`Silmaril.Elf.Asm.AsmFunction`: name, extent, exact bytes, symbol, listing,
references) is the code a conformance row is about. `Code.ofAsm f image` is the conformance
`Machine.Abi.Conformance.Code` of `f`: its bytes at its virtual address, entered at offset 0,
the function's extent its size, the image ranges given (a row checks them against the file:
`CodeOf`).

The adapter reads only the function's typed fields, never its listing text or its `abiRef`: the
ABI a row is judged against is a typed `AbiDef`, and `abiRef` stays metadata. `Thms.codeOf_ofAsm`
turns the function's evidence (`BytesAt` in the first executable segment, `SymbolOf` an
`STT_FUNC`) and the binding's lookup into the row's `CodeOf`. A function that tail-calls another
(`adler32` → `adler32_z`) needs a region spanning both: a `Code` with an entry offset, not this
single-function form. `Code.ofAsmWith f data image` also carries read-only data the function reads
(a CRC table), each range checked against the file (`MappedAt`) by `Thms.codeOf_ofAsmWith`.

**The loading relation is an assumption, not a fact about ld.so.** A row binds the file's bytes
to the code (`CodeOf`), shows no dynamic relocation writes them (`Untouched`), and quantifies over
the load bases the file admits (`Placement`). Whether a process's memory holds those bytes at the
rebased addresses is the row's admission hypothesis (`Admit`, `Placed.loaded`): the row is about
every call made from a state where they are loaded. Nothing here proves that ld.so maps the file
that way, or infers it from `Placement`, and code the loader runs (constructors, resolvers) is
outside the statement. A loader model that discharges `Placed.loaded` from the file is a separate
adapter.
-/

@[expose] public section

namespace Silmaril.Elf.Abi

open Silmaril.Machine.Abi.Conformance
open Silmaril.Elf.Asm (AsmFunction)

/-- **The conformance code of an assembly function**: its bytes at its virtual address, entered
at offset 0, its extent's size, the read-only data `data` it reads (address, bytes), and the image
ranges `image`. -/
def Code.ofAsmWith (f : AsmFunction) (data : List (Silmaril.X86.Word × List Silmaril.X86.Byte))
    (image : List (Silmaril.X86.Word × Nat)) : Code where
  base := BitVec.ofNat 64 f.extent.vaddr
  bytes := f.bytes
  off := 0
  len := f.extent.size
  data := data
  image := image

/-- **The conformance code of an assembly function** that reads no read-only data. -/
def Code.ofAsm (f : AsmFunction) (image : List (Silmaril.X86.Word × Nat)) : Code :=
  Code.ofAsmWith f [] image

end Silmaril.Elf.Abi

end
