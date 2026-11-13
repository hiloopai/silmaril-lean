module

public import Silmaril.Compiler.Core.Spec.Defs
public import Silmaril.Semantics.CPort.Formats.ELF.Write.Defs

/-! # Writing a verified artifact (trusted)

`object a` is the ELF relocatable object of a `Spec.Artifact`, for the startup code
`tools/ccomp/runtime/crt0-x86_64.S`; `ldArgs` the link that places its code at
`a.codeBase` (`ld` reads the address in hexadecimal). Both are part of the trusted base of the `core-comp` campaign
(`Silmaril/Compile/Core/Spec.lean`) and are frozen with it: the evaluator checks this
file's hash.

* `.text`: `a.code`, linked first at `a.codeBase` (`--section-start=.text=…`), with the
  function symbol `__ccomp_start` at `a.entry`;
* `.rodata.ccomp`: `a.image`, symbol `__ccomp_image`;
* absolute symbols `__ccomp_image_base` (`a.imageBase`), `__ccomp_image_size`,
  `__ccomp_lmem_size` (`a.memSize`), `__ccomp_ctl` (`Spec.ctlAddr`), `__ccomp_arg_base` and
  `__ccomp_arg_size` (`a.argBase`, `a.argSize`: where crt0 writes `Spec.argBlock`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Emit

open Silmaril.Formats.ELF
open Spec

def bytes (l : List X86.Byte) : ByteArray := ⟨(l.map fun b => b.toNat.toUInt8).toArray⟩

/-- The object file of an artifact (x86-64, `EM_X86_64` = 62). -/
def object (a : Artifact) : ByteArray :=
  Write.writeRelocatable 62 0
    [ { name := ".text", flags := 6, align := 16, data := bytes a.code },
      { name := ".rodata.ccomp", flags := 2, align := 16, data := a.image } ]
    [ { name := "__ccomp_start", sec := some 0, value := a.entry - a.codeBase,
        size := a.code.length - (a.entry - a.codeBase), kind := 2 },
      { name := "__ccomp_image", sec := some 1, value := 0, size := a.image.size, kind := 1 },
      { name := "__ccomp_image_base", sec := none, value := a.imageBase, size := 0, kind := 0 },
      { name := "__ccomp_image_size", sec := none, value := a.image.size, size := 0, kind := 0 },
      { name := "__ccomp_lmem_size", sec := none, value := a.memSize, size := 0, kind := 0 },
      { name := "__ccomp_ctl", sec := none, value := ctlAddr, size := 0, kind := 0 },
      { name := "__ccomp_arg_base", sec := none, value := a.argBase, size := 0, kind := 0 },
      { name := "__ccomp_arg_size", sec := none, value := a.argSize, size := 0, kind := 0 } ]

/-- `ld` arguments: the program's object first, so that its `.text` starts the output
`.text` at `a.codeBase`; then the startup code. -/
def ldArgs (a : Artifact) (out obj crt0 : String) : Array String :=
  #["-static", "-nostdlib", "-z", "noexecstack",
    s!"--section-start=.text=0x{String.ofList (Nat.toDigits 16 a.codeBase)}",
    "-e", "_start", "-o", out, obj, crt0]

end Silmaril.Compile.Core.Emit
