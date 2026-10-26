module

public import Silmaril.Process.LPS.Table
public import Silmaril.Process.LPS.Shapes
public import Silmaril.Process.LPS.NativeX86All
public import Silmaril.Process.CLI.Sha256Cli.Binary

/-! Public definitions for the reviewed Linux-process promotion.  The detailed
proof files remain under `Silmaril.Process.LPS`; this header is the stable
entry point for downstream imports. -/

namespace Silmaril.Process

abbrev lpsSyscallSpec := LPS.syscallSpec
abbrev lpsTranslatedArms := LPS.translatedArms
abbrev sha256CliImage := CLI.Sha256Cli.Binary.image

end Silmaril.Process
