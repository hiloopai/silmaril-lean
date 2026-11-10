module

public import Silmaril.Project.Defs
public import Silmaril.Project.Formats.Elf.Defs
public import Silmaril.X86.Ladder.Pinned.Defs

/-!
# Standard problem shapes: ELF executables

The shapes of facts about what an executable loads, parametrized by the **loader** (`Loader`:
file bytes to the LPS memory image, its segments with permissions and its entry point). A
project fills in a row for its own file; `Silmaril.Project.Shapes.Elf.Thms` has the transfer
lemmas that prove a row with one kernel-fast check (`Loads.x86_of_blob`, `Entry.x86_of_blob`),
and `blob_of_decode`, the recommended certificate that a registered file is a `Blob` literal.

| name | statement |
|---|---|
| `silmaril.shapes.elf.loads` | `Loads L exe perms addr code`: `L` loads `code` at `addr`, in a segment with permissions `perms` |
| `silmaril.shapes.elf.loads.x86` | the same with the standard x86-64 loader `Loader.x86` |
| `silmaril.shapes.elf.entry` | `Entry L exe addr`: `L` accepts `exe` and its entry point is `addr` |
| `silmaril.shapes.elf.entry.x86` | the same with `Loader.x86` |

The executable is a registered value of any format (`exe : Value V`, `V` implicit): only its
bytes are read. The standard loader `Loader.x86` is `Loader.lps ELFImage.x86Policy`, the
loader of the format `elf.exec-x86` and of the pinned ELF ladder
(`Silmaril.X86.Ladder.Pinned.LoadedAt`).

A row, for the code at address `0x401000` of a registered executable `demo.exe`:

```lean
silmaril instance demo.exe.code := silmaril.shapes.elf.loads.x86
  (exe := demo.exe) (perms := "rx") (addr := 0x401000) (code := Demo.code)
```

Trusted: the LPS ELF loading rules (`ELFImage.parse`, `Records.image`).
-/

@[expose] public section

namespace Silmaril.Project.Shapes

open Silmaril.Process.LPS

/-- An ELF loader: the memory image (segments with permissions, entry point) that a file
loads to, if the loader accepts the file. -/
abbrev Loader := Silmaril.Formats.Bytes → Option Image

/-- The LPS loader with policy `P` (machine, header flags, task size): `ELFImage.parse P`,
then the image of the checked records. -/
def Loader.lps (P : ELFImage.Policy) : Loader := fun b =>
  (ELFImage.parse P (Silmaril.Project.Formats.elfBytes b)).map
    (·.image (Silmaril.Project.Formats.elfBytes b))

/-- **The standard x86-64 loader**: `Loader.lps ELFImage.x86Policy`, as in the format
`elf.exec-x86` and in `Pinned.LoadedAt`. -/
def Loader.x86 : Loader := Loader.lps ELFImage.x86Policy

/-- **`exe` loads `code` at `addr`**: the loader `L` accepts the bytes of `exe`, and one segment
of the image, with permission string `perms` (`"rx"` for code, `"r"` for read-only data),
holds exactly `code` at virtual address `addr`. -/
@[problem "silmaril.shapes.elf.loads"
  (title := "An executable loads given code at an address, in a segment with given permissions")]
def Loads (L : Loader) {V : Type} (exe : Value V) (perms : String) (addr : Nat)
    (code : List (BitVec 8)) : Prop :=
  ∃ img, L exe.bytes = some img ∧ ∃ seg ∈ img.segments,
    seg.perms = perms ∧ Silmaril.X86.Ladder.Pinned.sliceAt seg addr code.length = some code

/-- **The entry point of `exe` is `addr`**: the loader `L` accepts the bytes of `exe`, and the
image starts at `addr`. -/
@[problem "silmaril.shapes.elf.entry"
  (title := "An executable's entry point")]
def Entry (L : Loader) {V : Type} (exe : Value V) (addr : Nat) : Prop :=
  ∃ img, L exe.bytes = some img ∧ img.initPc = addr

/-! ## Included files as `Blob`s -/

/-- The little-endian value of the bytes `Silmaril.IncludeBytes.bytesChunks chunk len cs`
(the `include_bytes` encoding of a file: `cs` holds the file `chunk` bytes at a time, the last
chunk short), computed from the chunk literals, without the bytes. -/
def chunksVal (chunk : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | len, c :: cs =>
    c % 256 ^ min chunk len + 256 ^ min chunk len * chunksVal chunk (len - chunk) cs

/-- The length of `Silmaril.IncludeBytes.bytesChunks chunk len cs`. -/
def chunksLen (chunk : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | len, _ :: cs => min chunk len + chunksLen chunk (len - chunk) cs

end Silmaril.Project.Shapes

end

silmaril instance silmaril.shapes.elf.loads.x86 (title := "loads, with the standard x86-64 loader") :=
  silmaril.shapes.elf.loads (L := Silmaril.Project.Shapes.Loader.x86)
silmaril instance silmaril.shapes.elf.entry.x86 (title := "entry, with the standard x86-64 loader") :=
  silmaril.shapes.elf.entry (L := Silmaril.Project.Shapes.Loader.x86)
