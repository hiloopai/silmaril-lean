module

public import Silmaril.X86.Decompile.Lift.Defs
public meta import Lean.Elab.Tactic.Basic

/-!
# The `lift_block` tactic

`lift_block` closes a goal that states the result of this directory's lifting
checker on concrete data — `checkBlock c blk spec = .ok ()` or
`checkFunc c spec = .ok ()` — by reduction in the kernel, and reports the
rejection when the checker refuses.

The proposal is a term of the goal, exactly as in
`Silmaril.X86.Decompile.recover_cfg` and `Silmaril.Machine.Lift.abstract_stack`:
what the kernel checks is visible in the goal rather than produced inside a
metaprogram. On failure the checker's actual result is reduced and printed, so
the error names the `BlockReject` constructor and its arguments — the label, the
address or the instruction index the proposal got wrong.
`docs/agents/decompile-lift-blocks.md` tabulates what each one means and what to
do about it.

Compiled evaluation (the token the layout check forbids) is not used and must not be: a lifting accepted by the compiler
rather than the kernel is a test, not a proof. The tactic tries `rfl` first,
which reduces `checkBlock` directly, and falls back to `decide`, which also
reduces the `DecidableEq` instances. `maxRecDepth` is raised because the
elaborator's default limit is reached by a few dozen instructions long before
the kernel is troubled.

## There is no block proposer to run

`recover_cfg` is usually applied to a goal whose proposal is
`CfgPropose.ofFunction` applied to concrete data, and `recover_loops` to one
whose proposal is `proposeLoops g`. `lift_block` has no counterpart: **this
directory ships no heuristic that guesses a Lir block from x86 instructions.**
Writing one is a lifting pass in its own right — pattern-matching the backend's
selection sequences backwards — and it is not what this rung is for. The
proposal is written by the agent, which is the arrangement the whole toolkit
is built on: the proposer is untrusted and lives outside the checker, so a
proposer that does not exist costs nothing but typing. The checker is the judge
either way.

## How far it scales

The six Lir blocks of the compiled `RTL.Examples.factorial` are lifted and
checked by the kernel in `Silmaril/X86/Decompile/RoundTrip.lean`, as is the
abstraction of the resulting Lir function to RTL. At 35 instructions the whole
chain reduces comfortably; a function whose bytes `Decompile.Examples` can only
`#guard` will not be liftable by `decide` either, for the same reason.
-/

@[expose] public section

namespace Silmaril.X86.Decompile.Lift

open Lean Elab Tactic Meta

/-- Close the goal by kernel reduction, or report what the checker returned. -/
meta def liftBlockCore : TacticM Unit := do
  let goal ← getMainGoal
  let ty ← goal.getType
  try
    withOptions (fun o => o.set `maxRecDepth (100000 : Nat)) do
      evalTactic (← `(tactic| first | rfl | decide))
  catch _ =>
    let some (_, lhs, _) := ty.eq? |
      throwError "lift_block: the goal is not an equation about a checker"
    let reduced ← withOptions (fun o => o.set `maxRecDepth (100000 : Nat)) (reduce lhs)
    throwError "lift_block: the checker rejected the proposal:{indentExpr reduced}"

/-- Close a goal about `checkBlock` or `checkFunc` on concrete data by kernel
reduction, reporting the `BlockReject` when the checker refuses. -/
scoped syntax "lift_block" : tactic

elab_rules : tactic
  | `(tactic| lift_block) => liftBlockCore

end Silmaril.X86.Decompile.Lift
