module

public import Silmaril.Cli.Spec.WasmVerify.Defs

/-!
# The command line of `WasmVerify`: theorems

The grammar is well formed (`Command.WF`, decided by kernel evaluation), so the theorems of
`Silmaril.Cli.Args.Thms` read declaratively for it: the parser is sound and complete, names find
their declarations, and its normal form reads back.
-/

@[expose] public section

namespace Silmaril.Cli.Spec.WasmVerify

open Silmaril.Cli

theorem extraWasmVerify_wf : extraWasmVerify.WF := by decide +kernel

/-- The grammar with its checks and rules is well formed too. -/
theorem tool_wf : tool.grammar.WF := by decide +kernel

/-- The help and version options are flags, so the clap reading agrees with the args front
end wherever clap's pre-pass passes (`Clap.read_agrees`). -/
theorem tool_helpFlags : Clap.HelpFlags tool.grammar := by decide +kernel

end Silmaril.Cli.Spec.WasmVerify
