module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.LoopMainSound.Defs
/-! # Fragment: a `while` loop over `int` locals

`int` locals created at the start of `main`'s block, straight statements `int x;`,
`int x = e;`, `x = e;`, then one `while (c) body` whose label carries one local, then
`return e;` (`LoopMain.recognize`). The code is a Lir control-flow graph over registers with a
back edge (`LoopMain.blocks`); the proof relates the two runs at the loop header and covers
divergence (`LoopMain.compile_sound`, `LoopSim`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

/-- `LoopMain.compile`: the loop's control-flow graph (`LoopLink.link`). -/
def loop : Fragment where
  compile := LoopMain.compile
  sound := LoopMain.compile_sound

end Silmaril.Compile.Core.Verified.Fragments
