module
public import Silmaril.Project.Formats.Elf.Defs
public import Silmaril.Data.IncludeBytes

/-!
# Formats `elf.elf64le` and `elf.exec-x86`: laws and examples

* `elfExecX86_sound` (registered law `sound`), from `ELFImage.parse_sound`.
* Examples on `examples/project-formats/example.o` (from `example.c`) and
  `example-exec.elf` (from `example-exec.c`), built with gcc 13.3.0:

  ```
  gcc -O1 -c -fno-asynchronous-unwind-tables -fno-ident -fno-pic -o example.o example.c
  gcc -O1 -static -nostdlib -fno-pic -no-pie -fno-asynchronous-unwind-tables -fno-ident \
    -Wl,--build-id=none -Wl,-z,max-page-size=4096 -Wl,-z,noseparate-code -Wl,-z,norelro \
    -s -o example-exec.elf example-exec.c
  ```
-/

@[expose] public section
namespace Silmaril.Project.Formats

theorem elfExecX86_sound : elfExecX86.SoundFor ElfExecX86Rel :=
  fun _ _ h => Silmaril.Process.LPS.ELFImage.parse_sound h

/-- `examples/project-formats/example.o`. -/
def exampleObject : Silmaril.Formats.Bytes :=
  ⟨include_bytes "../../../../examples/project-formats/example.o"⟩

theorem exampleObject_parses : (elf.parse exampleObject).isSome = true := by decide +kernel

/-- `examples/project-formats/example-exec.elf`. -/
def exampleExec : Silmaril.Formats.Bytes :=
  ⟨include_bytes "../../../../examples/project-formats/example-exec.elf"⟩

theorem exampleExec_parses : (elfExecX86.parse exampleExec).isSome = true := by decide +kernel

end Silmaril.Project.Formats

silmaril format_law "elf.exec-x86" sound := Silmaril.Project.Formats.elfExecX86_sound (rel := Silmaril.Project.Formats.ElfExecX86Rel)
