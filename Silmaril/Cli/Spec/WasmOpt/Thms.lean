module

public import Silmaril.Cli.Spec.WasmOpt.Defs
public import Silmaril.Cli.Clap.Main.Thms

/-!
# The command line of `WasmOpt`: theorems

The grammar is well formed (`Command.WF`, decided by kernel evaluation), so the theorems of
`Silmaril.Cli.Args.Thms` read declaratively for it: the parser is sound and complete, names find
their declarations, and its normal form reads back.

The binary takes its help from the grammar (`tool.helpOr`,
`tools/wasm-opt/WasmOptCompatLean.lean`): `main_help` states that it meets `tool.spec` on
every invocation that asks for help, whatever the driver does on the others.
-/

@[expose] public section

namespace Silmaril.Cli.Spec.WasmOpt

open Silmaril.Cli

theorem extraWasmOpt_wf : extraWasmOpt.WF := by decide +kernel

/-- **`wasm-opt`'s help is the specification's**: on every invocation the reading
answers with help, the program (`tool.helpOr Host.io Driver.runExtraOpt`, read in the
behaviour model with any driver `other`) shows exactly the derived help and exits 0. -/
theorem main_help (other : List String → Beh UInt32) (S : Matches → Spec) {i : Input}
    {p : List String} (hp : tool.outcome i = .help p) {o : Obs}
    (h : Beh.toSpec (Beh.withArgs (tool.helpOr Beh.host other)) i o) : tool.spec S i o :=
  tool.helpOr_help other S hp h

/-- `-h` anywhere asks for help. -/
theorem read_help : tool.read (fun _ => none) ["in.wasm", "-O2", "-h"] = .help ["wasm-opt"] := by
  decide +kernel

/-- The grammar with its checks and rules is well formed too. -/
theorem tool_wf : tool.grammar.WF := by decide +kernel

/-- The help and version options are flags, so the clap reading agrees with the args front
end wherever clap's pre-pass passes (`Clap.read_agrees`). -/
theorem tool_helpFlags : Clap.HelpFlags tool.grammar := by decide +kernel

end Silmaril.Cli.Spec.WasmOpt
