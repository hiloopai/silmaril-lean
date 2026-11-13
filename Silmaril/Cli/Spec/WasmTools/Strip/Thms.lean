module

public import Silmaril.Cli.Spec.WasmTools.Strip.Defs
public import Silmaril.Cli.Clap.Main.Thms

/-!
# Adopting the CLI spec in `wasm-tools`: `strip`, theorems

* **`main_refines`**: a `wasm-tools` built as `WasmTools.tool.main run` refines `spec f` as
  soon as its `strip` command refines `stripSpec f` (the other commands are unconstrained);
  `main_refines_cmds` for any list of specified subcommands;
* `read_strip`, `read_strip_stdin`, `read_strip_bad`: readings of sample command lines, by
  kernel evaluation (clusters, attached values, repetitions, `-` for stdin, a missing value).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Spec.WasmTools.Strip

open Silmaril.Cli

/-- **A tool behind `WasmTools.tool` refines the specs of the listed subcommands** when each
listed command refines its spec on its path. -/
theorem main_refines_cmds (cs : List (List String × (Matches → Spec)))
    {run : Matches → Beh UInt32}
    (h : ∀ m S, cs.lookup m.path = some S → Beh.toSpec (run m) ≤ S m) :
    Beh.toSpec (WasmTools.tool.modelMain run) ≤ WasmTools.tool.spec (bodySpec cs) := by
  refine WasmTools.tool.main_refines fun m => ?_
  unfold bodySpec
  split
  · next S hS => exact h m S hS
  · exact fun _ _ _ => trivial

/-- **`wasm-tools` refines its spec with `strip` specified** once `strip` does. -/
theorem main_refines {f : StripArgs → Bytes → Except Bytes Bytes} {run : Matches → Beh UInt32}
    (hstrip : ∀ m, m.path = ["strip"] → Beh.toSpec (run m) ≤ stripSpec f m) :
    Beh.toSpec (WasmTools.tool.modelMain run) ≤ spec f :=
  main_refines_cmds (cmds f) fun m S hS => by
    simp only [cmds, List.lookup] at hS
    by_cases hp : m.path = ["strip"]
    · simp only [hp, BEq.rfl, Option.some.injEq] at hS
      subst hS
      exact hstrip m hp
    · have hb : (m.path == ["strip"]) = false := beq_false_of_ne hp
      rw [hb] at hS
      cases hS

/-- Clusters, attached values and repetitions read into the record. -/
theorem read_strip :
    (match WasmTools.tool.read (fun _ => none)
        ["strip", "-at", "-d", "name", "--delete=.debug.*", "in.wasm", "-oout.wat"] with
     | .run _ m => m.path == ["strip"] && StripArgs.ofMatches m ==
         { input := some "in.wasm", output := some "out.wat", all := true,
           delete := ["name", ".debug.*"], wat := true }
     | _ => false) = true := by
  decide +kernel

/-- No input: stdin to stdout. -/
theorem read_strip_stdin :
    (match WasmTools.tool.read (fun _ => none) ["strip"] with
     | .run _ m => StripArgs.ofMatches m ==
         { input := none, output := none, all := false, delete := [], wat := false }
     | _ => false) = true := by
  decide +kernel

/-- A missing value is a usage error (exit 2) with clap's message. -/
theorem read_strip_bad :
    WasmTools.tool.read (fun _ => none) ["strip", "-d"] =
      .error "a value is required for '--delete <REGEX>' but none was supplied" := by
  decide +kernel

end Silmaril.Cli.Spec.WasmTools.Strip
