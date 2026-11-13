module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.CfgPrintSound.Defs
/-! # Fragment: `main` as a control-flow graph that prints

The `cfg` fragment with `printf("…%d…", e)` statements over the string literals of the file
(`CfgPrint.recognize`): loops that print, their output bounded by checked potentials of the labels
(`Cfg.check`). The proof is `Cfg.Seg.run` with the print context of the literals
(`CfgPrint.compile_sound`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

/-- `CfgPrint.compile`: the labels' control-flow graph with print nodes (`LoopLink.link`). -/
def cfgPrint : Fragment where
  compile := CfgPrint.compile
  sound := CfgPrint.compile_sound

end Silmaril.Compile.Core.Verified.Fragments
