module

public import Silmaril.Compiler.Native.Correctness.Literal42.Defs
/-! The existing explicit loader reused for any 83-byte literal code image.
This definition installs actual bytes; no execution or text acceptance is assumed. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralLoader
open Silmaril Silmaril.X86

abbrev image (code : List Byte) : Image := Literal42.loadImage code

end Silmaril.Compiler.Native.Correctness.LiteralLoader
