module

public import Silmaril.Machine.CBackend.Lift.Propose.Defs
public meta import Lean.Elab.Tactic.Basic

/-!
# The `abstract_stack`, `ssa_construct` and `recover_loops` tactics

Each closes a goal that states the result of one of this directory's checkers on
concrete data — `checkAbstraction L target spec = .ok ()`, `checkSsaProg target
spec = .ok ()`, `checkLoops g spec = .ok ()` — by reduction in the kernel, and
reports the rejection when the checker refuses.

The proposal is a term of the goal, exactly as in
`Silmaril.X86.Decompile.split_functions`: the proposers of `Lift/Propose.lean`
are untrusted and live outside the tactic, so that what the kernel checks is
visible in the goal rather than produced inside a metaprogram. `recover_loops`
is usually applied to a goal whose proposal is `proposeLoops g`; the other two
to a goal whose proposal the agent wrote.

Compiled evaluation (the token the layout check forbids) is not used and must not be: a decompilation accepted by the
compiler rather than the kernel is a test, not a proof. The tactics try `rfl`
first, which reduces the checker directly, and fall back to `decide`, which also
reduces the `DecidableEq` instances. `maxRecDepth` is raised because the
elaborator's default limit is reached by a few dozen blocks long before the
kernel is troubled.

On failure the checker's actual result is reduced and printed, so the error
message names the rejection constructor and its arguments — the node, register,
label or header that the proposal got wrong. `docs/agents/decompile-abstract-and-ssa.md`
tabulates what each one means and what to do about it.
-/

@[expose] public section

namespace Silmaril.Machine.Lift

open Lean Elab Tactic Meta

/-- Close the goal by kernel reduction, or report what the checker returned. -/
meta def closeOrReport (name : String) : TacticM Unit := do
  let goal ← getMainGoal
  let ty ← goal.getType
  try
    withOptions (fun o => o.set `maxRecDepth (100000 : Nat)) do
      evalTactic (← `(tactic| first | rfl | decide))
  catch _ =>
    let some (_, lhs, _) := ty.eq? |
      throwError "{name}: the goal is not an equation about a checker"
    let reduced ← withOptions (fun o => o.set `maxRecDepth (100000 : Nat)) (reduce lhs)
    throwError "{name}: the checker rejected the proposal:{indentExpr reduced}"

/-- Close a goal about `checkAbstraction` on concrete data by kernel
reduction. -/
scoped syntax "abstract_stack" : tactic

/-- Close a goal about `checkSsa` or `checkSsaProg` on concrete data by kernel
reduction. -/
scoped syntax "ssa_construct" : tactic

/-- Close a goal about `checkLoops` on concrete data by kernel reduction. -/
scoped syntax "recover_loops" : tactic

elab_rules : tactic
  | `(tactic| abstract_stack) => closeOrReport "abstract_stack"

elab_rules : tactic
  | `(tactic| ssa_construct) => closeOrReport "ssa_construct"

elab_rules : tactic
  | `(tactic| recover_loops) => closeOrReport "recover_loops"

end Silmaril.Machine.Lift
