module

public import Silmaril.Process.CLI.Input

/-!
# A loaded `CLI.Image`

`Segment.Loaded mem seg`: a non-writable segment holds its contents (file bytes, then zero
fill) in `mem`, readable when the segment is readable and fetchable when it is executable.
`Image.Loaded img mem` (also `ImageLoaded`): every segment of `img` is loaded.

Writable segments (`.data`, `.bss`) are left unconstrained: a program may have changed them
before the point at which a statement is made (a function call, say). This is the
precondition a function-level statement about a pinned executable needs: the code it runs
and the constant tables it reads are the image's bytes.
-/

@[expose] public section

namespace Silmaril.Process.CLI

/-- A non-writable segment holds its contents: readable if the segment is readable,
fetchable if it is executable. -/
def Segment.Loaded (mem : Memory) (seg : Segment) : Prop :=
  seg.permissions.write = false →
    (seg.permissions.read = true →
      mem.readBytes seg.vaddr seg.contents.length = some seg.contents) ∧
    (seg.permissions.execute = true →
      mem.fetchBytes seg.vaddr seg.contents.length = some seg.contents)

/-- **The image is loaded in `mem`**: every segment satisfies `Segment.Loaded`. -/
def Image.Loaded (img : Image) (mem : Memory) : Prop :=
  ∀ seg ∈ img.segments, Segment.Loaded mem seg

/-- `Image.Loaded`, with the image and the memory as arguments in that order. -/
abbrev ImageLoaded (img : Image) (mem : Memory) : Prop := img.Loaded mem

end Silmaril.Process.CLI
