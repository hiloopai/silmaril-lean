module

public import Silmaril.Cli.Getopt.Defs
public import Silmaril.Cli.Front.Defs

/-!
# The getopt front end on a full invocation

A getopt reading depends on the argument vector **and the environment**: `POSIXLY_CORRECT`
decides the ordering (`Tool.order`). This file reads both from a full invocation
(`Silmaril.Cli.Input`, the input of the `L3` level of the CLI institution):

* `Tool.envVars`: the variables the front end reads, `POSIXLY_CORRECT` first, then the
  grammar's own (`Command.envVars`);
* `Tool.envOf i`: their values in the invocation `i` (`Input.getEnv`: the first binding wins;
  every other variable reads as unset);
* `Tool.outcome i`: what the front end decides, `t.read (t.envOf i) i.args`;
* `Tool.spec S`: the outcome as a behaviour specification, as `Command.spec` is for the args
  dialect: on matches `m` the program behaves as `S m`, otherwise it prints help, version or a
  usage error and exits 0, 0 or 2.

A Silmaril addition; the guide is `docs/projects/cli.md`.
-/

@[expose] public section

namespace Silmaril.Cli.Getopt

open Silmaril.Cli

/-- The environment variables the getopt front end of a tool reads. -/
def Tool.envVars (t : Tool) : List String := "POSIXLY_CORRECT" :: t.grammar.envVars

/-- The environment the getopt front end reads from an invocation. -/
def Tool.envOf (t : Tool) (i : Input) : String → Option String := Beh.envOf t.envVars i

/-- **What the getopt front end decides on an invocation**: a function of its arguments and of
its environment. -/
def Tool.outcome (t : Tool) (i : Input) : Outcome := t.read (t.envOf i) i.args

/-- **The getopt front end as a behaviour specification.** -/
def Tool.spec (t : Tool) (S : Matches → Spec) : Spec := fun i o =>
  match t.outcome i with
  | .run m => S m i o
  | out => o = { Beh.lineObs i (out.text t.grammar) with
      exit := (out.exitCode?.getD 0).toUInt32.toUInt8 }

end Silmaril.Cli.Getopt
