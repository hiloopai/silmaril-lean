module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.CfgSound.Defs
/-! # Fragment: `main` as a control-flow graph of its saved labels

`int` locals created at the start of `main`'s block, then `int` statements, statement tests
(`if`/`else`) and Cerberus's saved labels with their jumps: `while`, `for` and `do` loops, `break`,
`continue`, several and nested loops, `return e;` anywhere (`Cfg.recognize`). Each label is a
block of the Lir code and each `run` a jump to it (`Cfg.Plan.blocks`); the proof relates the two
runs at every node and covers divergence (`Cfg.compile_sound`, `LoopSim`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

/-- `Cfg.compile`: the labels' control-flow graph (`LoopLink.link`). -/
def cfg : Fragment where
  compile := Cfg.compile
  sound := Cfg.compile_sound

end Silmaril.Compile.Core.Verified.Fragments
