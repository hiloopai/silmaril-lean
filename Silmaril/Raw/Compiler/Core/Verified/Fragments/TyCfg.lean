module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.TyCfgSound.Defs
/-! # Fragment: `main` as a control-flow graph over typed integer slots

`Fragments.cfg` with the slots of `Fragments.tyRun`: globals initialised by literals and locals
of type plain, `signed` or `unsigned` `char`, `short`, `int`, `long` or `long long`, assignments
and initialisations converted to the slot's type, statement tests and `do` tests of comparisons,
Cerberus's saved labels with their jumps (`while`, `for`, `do`, `break`, `continue`), `return e;`,
`exit(n)` and `abort()` (`TyCfg.recognize`). Each label is a block of the Lir code and each `run`
a jump to it; the proof relates the two runs at every node and covers divergence
(`TyCfg.compile_sound`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

/-- `TyCfg.compile`: the labels' control-flow graph over typed slots (`LoopLink.link`). -/
def tyCfg : Fragment where
  compile := TyCfg.compile
  sound := TyCfg.compile_sound

end Silmaril.Compile.Core.Verified.Fragments
