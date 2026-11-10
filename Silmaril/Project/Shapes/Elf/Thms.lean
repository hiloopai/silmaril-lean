module

public import Silmaril.Project.Shapes.Elf.Defs
public import Silmaril.X86.Ladder.Pinned.Thms
public import Silmaril.X86.Link.Blob.Thms
public import Silmaril.Data.IncludeBytes.Types
public import Silmaril.Project.Formats.Elf.Thms
import Silmaril.Proofs.Project.Shapes.Elf

/-! # Standard problem shapes: ELF executables (transfer lemmas)

* `loads_x86_iff`: `Loads Loader.x86` is the pinned ladder's `Pinned.LoadedAt` on the file as
  a `Blob`, so `Loads.x86_of_check` proves a row by `Pinned.check … = true`, one kernel-fast
  run of the reader `Blob.parseN`.
* `Loads.x86_of_blob`, `Entry.x86_of_blob`: the same, through a certificate `hB` that the file
  is a `Blob` literal (a `Nat` comparison), for files too big to decode in the kernel.
* **Certifying an executable's bytes** (`blob_of_decode`, `ofBytes_decode`): the recommended
  way to prove `hB : Blob.ofBytes (elfBytes X.bytes) = B` for a registered value `X` and a
  `Blob` literal `B`. A `silmaril value` holds its file as `include_bytes`,
  `Silmaril.IncludeBytes.decode` of chunk literals; `ofBytes_decode` computes the `Blob` from
  the chunks (`chunksVal`, `chunksLen`: a few big-number operations per chunk), so the kernel
  compares numbers instead of decoding the file byte by byte. Use it as
  `blob_of_decode rfl (by decide +kernel)` in a theorem that states `B`; a direct
  `decide +kernel` on `Blob.ofBytes` of a file of some kilobytes does not fit in memory.
* `Entry.x86_of_satisfies`: a value of format `elf.exec-x86` whose records have entry `addr`.
* Example rows on `examples/project-formats/example-exec.elf` (`exampleExecValue`): its entry
  point (`exampleExec_entry`) and the 14 code bytes there (`exampleExec_code`), each by
  `blob_of_decode rfl rfl` and one `decide +kernel`.
-/

@[expose] public section

namespace Silmaril.Project.Shapes

open Silmaril.Process.LPS
open Silmaril.X86.Link
open Silmaril.X86.Ladder (Pinned.LoadedAt Pinned.check Pinned.check_sound)

variable {V : Type} {perms : String} {addr : Nat} {code : List (BitVec 8)}

/-- `Loads` with the standard loader is `Pinned.LoadedAt` on the file as a `Blob`. -/
theorem loads_x86_iff (X : Value V) (perms : String) (addr : Nat) (code : List (BitVec 8)) :
    Loads Loader.x86 X perms addr code ↔
      Pinned.LoadedAt (Blob.ofBytes (Silmaril.Project.Formats.elfBytes X.bytes)) perms addr
        code :=
  Silmaril.Proofs.Project.Shapes.Elf.loads_x86_iff X perms addr code

/-- A row of `loads.x86` from one run of the kernel-fast check. -/
theorem Loads.x86_of_check {X : Value V}
    (h : Pinned.check (Blob.ofBytes (Silmaril.Project.Formats.elfBytes X.bytes)) perms addr
      code = true) :
    Loads Loader.x86 X perms addr code :=
  (loads_x86_iff X perms addr code).2 (Pinned.check_sound h)

/-- A row of `loads.x86` through a certificate that the file is the `Blob` literal `B`. -/
theorem Loads.x86_of_blob {X : Value V} {B : Blob}
    (hB : Blob.ofBytes (Silmaril.Project.Formats.elfBytes X.bytes) = B)
    (h : Pinned.check B perms addr code = true) : Loads Loader.x86 X perms addr code :=
  Loads.x86_of_check (hB ▸ h)

/-- A row of `entry.x86` through a certificate that the file is the `Blob` literal `B`, and one
run of the kernel-fast reader `Blob.parseN`. -/
theorem Entry.x86_of_blob {X : Value V} {B : Blob}
    (hB : Blob.ofBytes (Silmaril.Project.Formats.elfBytes X.bytes) = B)
    (h : (Blob.parseN ELFImage.x86Policy B.n B.len).map (·.header.entry) = some addr) :
    Entry Loader.x86 X addr :=
  Silmaril.Proofs.Project.Shapes.Elf.entry_x86_of_blob hB h

/-! ## Certifying an executable's bytes -/

/-- **An included file as a `Blob`**, computed from its chunk literals without decoding its
bytes. -/
theorem ofBytes_decode (chunk len : Nat) (cs : List Nat) :
    Blob.ofBytes (Silmaril.Project.Formats.elfBytes ⟨Silmaril.IncludeBytes.decode chunk len cs⟩) =
      ⟨chunksVal chunk len cs, chunksLen chunk len cs⟩ :=
  Silmaril.Proofs.Project.Shapes.Elf.ofBytes_decode chunk len cs

/-- **The bytes of `b` are the `Blob` literal `B`**, for bytes held as `include_bytes` (every
`silmaril value`): `blob_of_decode rfl (by decide +kernel)`. The `rfl` exposes the chunk
literals; the kernel then compares `B` with `chunksVal`/`chunksLen` of the chunks. -/
theorem blob_of_decode {b : Silmaril.Formats.Bytes} {chunk len : Nat} {cs : List Nat} {B : Blob}
    (hb : b = ⟨Silmaril.IncludeBytes.decode chunk len cs⟩)
    (h : B = ⟨chunksVal chunk len cs, chunksLen chunk len cs⟩) :
    Blob.ofBytes (Silmaril.Project.Formats.elfBytes b) = B :=
  hb ▸ (ofBytes_decode chunk len cs).trans h.symm

/-- A row of `entry.x86` for a value of format `elf.exec-x86`: its records have entry `addr`. -/
theorem Entry.x86_of_satisfies {X : Value ELFImage.Records}
    (hF : X.format = Silmaril.Project.Formats.elfExecX86)
    (h : X.Satisfies fun r => r.header.entry = addr) : Entry Loader.x86 X addr :=
  Silmaril.Proofs.Project.Shapes.Elf.entry_x86_of_satisfies hF h

/-! ## Example rows -/

/-- `examples/project-formats/example-exec.elf` as a value of `elf.exec-x86`. -/
def exampleExecValue : Value ELFImage.Records :=
  ⟨Silmaril.Project.Formats.elfExecX86, Silmaril.Project.Formats.exampleExec⟩

/-- The code at its entry point: `endbr64; mov $60, %eax; xor %edi, %edi; syscall; ret`. -/
def exampleExecCode : List (BitVec 8) :=
  [0xf3, 0x0f, 0x1e, 0xfa, 0xb8, 0x3c, 0x00, 0x00, 0x00, 0x31, 0xff, 0x0f, 0x05, 0xc3]

theorem exampleExec_entry : Entry Loader.x86 exampleExecValue 0x400140 :=
  Entry.x86_of_blob (blob_of_decode rfl rfl) (by decide +kernel)

theorem exampleExec_code : Loads Loader.x86 exampleExecValue "rx" 0x400140 exampleExecCode :=
  Loads.x86_of_blob (blob_of_decode rfl rfl) (by decide +kernel)

end Silmaril.Project.Shapes

end
