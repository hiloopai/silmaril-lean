module

public import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.AuxLemma

@[expose] public section

/-!
# `kernel_rfl`: equations checked by kernel definitional equality

`kernel_rfl` closes a goal `a = b` with `Eq.refl a`, type-checked by the kernel alone (as
`decide +kernel` does with its `Decidable` instance): the proof is added as an auxiliary lemma,
so the kernel checks that `a` and `b` are definitionally equal. The elaborator does not try the
definitional equality itself.

Unlike `decide +kernel` on an equation, no `DecidableEq` instance runs: the kernel compares the
two sides by reduction and structural comparison. On closed terms with strings this avoids
comparing their UTF-8 byte arrays through `String.decEq`; two strings built from the same
characters (a literal and `String.ofList` of its characters) are compared character by
character.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Lean Meta Elab Tactic

/-- `kernel_rfl`: close `a = b` by `Eq.refl a`, checked by the kernel only. -/
syntax (name := kernelRfl) "kernel_rfl" : tactic

@[tactic kernelRfl] meta def evalKernelRfl : Tactic := fun _ => do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    if t.hasFVar || t.hasMVar then throwError "kernel_rfl: the goal must be closed"
    let some (ty, a, _) := t.eq? | throwError "kernel_rfl: not an equation{indentExpr t}"
    let u ← getLevel ty
    let pf := mkApp2 (mkConst ``Eq.refl [u]) ty a
    let lvls := (collectLevelParams {} t).params.toList
    let n ← withOptions (Elab.async.set · false) <| mkAuxLemma lvls t pf
    g.assign (mkConst n (lvls.map .param))
    replaceMainGoal []

end Silmaril.Wasi.Versions.WitImport
