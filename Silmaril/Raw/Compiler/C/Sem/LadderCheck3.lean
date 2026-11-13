module

public import Silmaril.Compiler.C.Sem.LadderCheck.Defs
@[expose] public section

/-!
# Checked agreement across the C2/C3 layout gap

C2 and C3 disagree on `float` layout, so their universal ladder law fails.
This per-program check compares completed observations instead: it declines
programs that expose the layout difference, as well as undefined, unsupported
or exhausted executions. It uses the same fuel and comparison as the other
adjacent-rung checks without changing their accepted definitions.
-/

namespace Silmaril.Compile.C.Sem

open Silmaril.Cerberus.Ail

/-- Per-program C2/C3 agreement, including any observable floating-layout effects. -/
def ladderCheck3 : TypedProgram → Bool := ladderCheckWith C2.run C3.run

end Silmaril.Compile.C.Sem
