module

public import Silmaril.Compiler.Native.Optimize.Defs
public import Silmaril.Compiler.Native.Semantics.OpenFrame.Defs
/-! Exact conditional function stages and the actual optimizer's cleanup list.
The localSSA and lambdaSSA gates remain separate from these four Mir stages. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Open.Cleanup
open Silmaril.Compile

def propagate (cfg : Config) (function : Mir.Func) : Mir.Func :=
  if cfg.constantPropagation then Mir.ConstProp.rwFunc function else function

def common (cfg : Config) (function : Mir.Func) : Mir.Func :=
  if cfg.commonSubexpressions then Mir.CSE.rwFunc function else function

def dead (cfg : Config) (function : Mir.Func) : Mir.Func :=
  if cfg.deadCode then Mir.DeadCode.dceFunc function else function

def jumps (cfg : Config) (function : Mir.Func) : Mir.Func :=
  if cfg.jumpThreading then Mir.JumpThread.jtFunc function else function

/-- Exactly the four function stages, in actual cleanupPasses order. -/
def cleanupFunc (cfg : Config) (function : Mir.Func) : Mir.Func :=
  jumps cfg (dead cfg (common cfg (propagate cfg function)))

/-- The actual selected cleanup pass list, without local SSA versioning. -/
def cleanupWith (cfg : Config) (units : Array Mir.Unit) : Array Mir.Unit :=
  Mir.Pass.runAll (cleanupPasses cfg) units

/-- The actual function stage selection, including the localSSA gate.
Versioning retains its own actual lambdaSSA selection/validation/fallback. -/
def optimizeFunc (cfg : Config) (function : Mir.Func) : Mir.Func :=
  cleanupFunc cfg (if cfg.localSSA then versionFunc cfg function else function)

end Silmaril.Compiler.Native.Optimize.Open.Cleanup
