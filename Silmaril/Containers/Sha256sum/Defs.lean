module

public import Silmaril.Containers.Outcome.Defs
public import Silmaril.Elf.LpsCli.Defs
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Statement
public import Silmaril.Process.LPS.Problems.Sha256Cli.Statement

/-! # Experimental finite LPS outcome adapter for the existing SHA executables

This adapter includes fault and unmodeled reports, rather than projecting only successful CLI
observations. It does not yet identify the native-machine `Containers.Lps` runtime with the
release statements' `Ext`/`Ext8` machines or establish clone freedom. Hence this is an actual
finite-report bridge, not a new end-to-end container-machine theorem. -/

@[expose] public section
namespace Silmaril.Containers.Sha256sum
open Silmaril.Process.LPS

inductive Report where
  | ended (trace : List Event) (output : Silmaril.Cli.Institution.Out1)
  | fault
  | unmodeled

/-- Reports of the original execution semantics, including every error/unmodeled report. -/
def Report.Occurs (b : Behavior) : Report → Prop
  | .ended tr out => b.traces tr ∧ Silmaril.Elf.LpsCli.out1Of tr = some out
  | .fault => b.errors
  | .unmodeled => b.unmodeled

def Report.observe : Report → Outcome UB
  | .ended _ out => .exited out.exit
  | .fault => .undefined .memory
  | .unmodeled => .undefined .unmodeled

end Silmaril.Containers.Sha256sum
