module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.CfgArgvSound.Defs
/-! # Fragment: `main(argc, argv)` as a control-flow graph with tests on argument characters

`Cfg`'s machine for `main(argc, argv)` of a file without globals: `argc` is an `int` slot, and a
statement test may read a character `argv[i][x]` (`i ≤ 1`, `x` an `int` local) at run time, as in
`int n = 0; while (argv[1][n]) n++;` (`CfgArgv.recognize`). A local indexing an argument is
written only by `= 0` and by `++` after a test found a character that is not the terminator, so
every read stays within the string; from the null slot (`argc = 1`) Core reaches undefined
behaviour (`CfgArgv.compile_sound`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

/-- `CfgArgv.compile`: the labels' control-flow graph over `argc` and `argv` (`LoopLink.link`). -/
def cfgArgv : Fragment where
  compile := CfgArgv.compile
  sound := CfgArgv.compile_sound

end Silmaril.Compile.Core.Verified.Fragments
