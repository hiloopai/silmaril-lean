module

public import Silmaril.Compiler.Core.Verified.Fragments.StateExit.Defs
public import Silmaril.Compiler.Core.Verified.Fragment.Defs
-- One import per fragment, one per line, in any order.
public import Silmaril.Compiler.Core.Verified.Fragments.ReturnConst.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.ReturnLit.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.Return.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.ExitCall.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.Locals.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.LocalExpr.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.ReturnExpr.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.GlobalExpr.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.Call.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.CallStmt.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.CallComma.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.CallArg.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.CallParam.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.Argc.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.State.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.ArrBlock.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.Printf.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.Loop.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.StateGlobals.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.TyState.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.DoLoop.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.CallState.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.CallCompare.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.StateCallCompare.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.ParamCallCompare.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.ParamCallTail.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.ParamCallChain.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.ArgvAbort.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.Cfg.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.TyRun.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.PrintState.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.CfgArgv.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.CfgPrint.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.TyCfg.Defs
/-! # The fragments of the verified compiler

`Verified.compile` is `Fragment.first fragments`: the first fragment of this list that accepts
the document compiles it. Each fragment carries its own proof, so the order is a matter of
preference only (the first recogniser that accepts wins), never of soundness.

To add a fragment: define `Fragments.<name> : Fragment` in a new file
`Verified/Fragments/<Name>.lean` (`Fragment.ofConst`, `Fragment.ofOps`, or a `Fragment` with its
own `compile` and `sound`), then add one import line above and one `<name> ::` line in the list.

This file is merged with `merge=union` (`Silmaril/Compile/Core/.gitattributes` and the project
checkout's `info/attributes`): branches that add different fragments keep both sides' lines.
So every line stays self-contained: one import per line, one `<name> ::` entry per line, no
other definitions here, and the list's opening line and its closing `[]` are never edited. A
line duplicated by a merge is harmless: a repeated import is a no-op and a repeated entry is
never reached (the first copy already tried the document).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

/-- The proved fragments, tried in order. -/
def fragments : List Fragment :=
  returnConst ::
  returnLit ::
  returnFold ::
  exitCall ::
  locals ::
  localExpr ::
  returnExpr ::
  globalExpr ::
  callReturn ::
  callStmt ::
  callComma ::
  callParam ::
  callArg ::
  argc ::
  state ::
  arrBlock ::
  printf ::
  loop ::
  stateGlobals ::
  tyState ::
  doLoop ::
  callState ::
  callCompare ::
  stateCallCompare ::
  paramCallCompare ::
  paramCallTail ::
  paramCallChain ::
  argvAbort ::
  cfg ::
  tyRun ::
  stateExit ::
  printState ::
  cfgArgv ::
  cfgPrint ::
  tyCfg ::
  []

end Silmaril.Compile.Core.Verified.Fragments
