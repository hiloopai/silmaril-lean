module

public import Silmaril.Cli.Spec.Asyncify.Defs
public import Silmaril.Cli.Clap.Main.Thms
public import Silmaril.Cli.Clap.Thms

/-!
# The command line of `Asyncify`: theorems

The grammar is well formed (`Command.WF`, decided by kernel evaluation), so the theorems of
`Silmaril.Cli.Args.Thms` read declaratively for it: the parser is sound and complete, names find
their declarations, and its normal form reads back.

The binary reads its arguments with `tool` (`Silmaril.Cli.Clap.Main`): `main_refines`
and `main_front` state what that gives, `read_*` pin readings the hand-written parser got
differently.
-/

@[expose] public section

namespace Silmaril.Cli.Spec.Asyncify

open Silmaril.Cli

theorem extraAsyncify_wf : extraAsyncify.WF := by decide +kernel

/-- The grammar the program reads with (`-h` on every command) is well formed, so what the
reading runs is a `Valid` invocation (`Clap.read_run_valid`). -/
theorem tool_wf : tool.grammar.WF := by decide +kernel

/-- **`wasm-asyncify` refines its specification.** The binary's `main` is `tool.main run`
(`tools/wasm-asyncify/WasmAsyncify.lean`); read in the behaviour model, the program refines `tool.spec S` as soon as
its commands `run m` refine `S m` (`Clap.Tool.main_refines`). -/
theorem main_refines {run : Matches → Beh UInt32} {S : Matches → Spec}
    (h : ∀ m, Beh.toSpec (run m) ≤ S m) : Beh.toSpec (tool.modelMain run) ≤ tool.spec S :=
  tool.main_refines h

/-- Whatever its commands do, the program meets the front end's specification: exactly the
derived help, usage errors and exit codes. -/
theorem main_front (run : Matches → Beh UInt32) :
    Beh.toSpec (tool.modelMain run) ≤ tool.frontSpec :=
  tool.main_refines_front run

/-- Its usage errors are loose usage errors (exit 2, nothing on stdout, no file touched). -/
theorem spec_usageError {S : Matches → Spec} {i : Input} {o : Obs}
    (herr : (∃ msg, tool.outcome i = .error msg) ∨ ∃ p, tool.outcome i = .needCommand p)
    (hs : tool.spec S i o) : Spec.usageError i o :=
  Clap.Tool.spec_usageError rfl herr hs

/-- The commands receive valid invocations of the grammar. -/
theorem read_run_valid {env : String → Option String} {argv : List String} {fs : Invocation}
    {m : Matches} (h : tool.read env argv = .run fs m) : Valid tool.grammar fs :=
  Clap.read_run_valid tool_wf h

/-- Without arguments: the root's help on stderr, a usage error. -/
theorem read_noArgs : tool.read (fun _ => none) [] = .needCommand ["wasm-asyncify"] := by
  decide +kernel

/-- Options anywhere: `-o` before the input, the default `--pages`. -/
theorem read_asyncify :
    (match tool.read (fun _ => none) ["asyncify", "-o", "out.wasm", "in.wasm"] with
     | .run _ m => m.path == ["asyncify"] && m.str? "-o" == some "out.wasm" &&
         m.str? "in" == some "in.wasm" && m.nat? "pages" == some 1
     | _ => false) = true := by
  decide +kernel

/-- A non-numeric `--fuel` is a usage error (the hand-written reading used the default). -/
theorem read_badFuel :
    (tool.read (fun _ => none) ["run-src", "m.wasm", "f", "", "--fuel", "x"]).exit tool =
      some 2 := by
  decide +kernel

/-- The help and version options are flags, so the clap reading agrees with the args front
end wherever clap's pre-pass passes (`Clap.read_agrees`). -/
theorem tool_helpFlags : Clap.HelpFlags tool.grammar := by decide +kernel

end Silmaril.Cli.Spec.Asyncify
