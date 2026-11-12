module

public import Silmaril.Compiler.Native.Correctness.LiteralLoader.Defs
/-! A size-bounded interface for the existing explicit closed-main loader.
Its code, stack, return word and argv are concrete installed memory; no
assembler, machine execution or source semantics is assumed. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.MainLoader
open Silmaril Silmaril.X86

abbrev image (code : List Byte) : Image := LiteralLoader.image code

end Silmaril.Compiler.Native.Correctness.MainLoader
