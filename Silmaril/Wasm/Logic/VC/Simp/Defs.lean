module

public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# The `wat_vc_simp` simp set

`wat_vc_simp` is the simp set of both passes of the tactic `wat_vc`
(`Silmaril.Wasm.Logic.VC.Thms`): the instructions `Silmaril.Wasm.Logic.VC.wpc` handles itself
(`cvt1`, `tableVC`, `callVC`, `callK`), the evaluation equations of `exec1` (`vc_exec1_*`,
globals by index), frame and value helpers, and the integer comparison and test normal forms.

The generator's own definitions (`wpc`, `ctl`, `loops`, `enterVC`, `labelQ`, `loopQ`, `popI32`,
`popSelect`, …) are not members: `wat_vc` unfolds them by name. A simp attribute on a
definition registers its equation lemmas as rewrite rules, and those of definitions with a
catch-all arm (`ctl`) are conditional; measured on the 25-function `Silmaril.Sim.X86.Max2`
problem, that made one condition exceed the default heartbeat limit.

`wat_vc_core` is the same set without `callVC` and `tableVC`: the tactic `wat_vc_calls` uses it so
that a call is rewritten by a call lemma (`Silmaril.Wasm.Logic.VC.callVC_fn`) and a `br_table` at a
known index by `tableVC_cons_self`/`tableVC_cons_of_ne` instead of being unfolded.

The members are tagged in `Silmaril.Wasm.Logic.VC.Thms`; this module only registers the
attribute, because Lean cannot use an attribute in the module that declares it. Other VC
tactics extend the set (`simp [wat_vc_simp, extra]`) instead of copying lemma lists.
A Silmaril addition.
-/

public meta section

/-- The simp set of both passes of `wat_vc`: `wpc`'s own instructions, the evaluation of
`exec1`, frame and value helpers, integer normal forms. -/
register_simp_attr wat_vc_simp

/-- `wat_vc_simp` without `callVC` and `tableVC` (the first pass of `wat_vc_calls`). -/
register_simp_attr wat_vc_core
