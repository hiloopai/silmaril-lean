module

public import Silmaril.Raw.Wasm.Auto2.VCInfer.Mod
public import Mathlib.Tactic.Ring

/-!
# Inferred contracts for `vcequiv`: results and the fixed tactics

Proofs in `Silmaril.Raw.Wasm.Auto2.VCInfer.Mod` (unrefined):

* **`modEquiv_of_infer`**: two contracts derived from one `InferFun` (`derives_libEntry`,
  `derives_inferEntry`) that check the two exports (`vcEquivWith`) prove `ModEquiv` at every
  profile, for every reflexive relation.

The **fixed tactics** of the library, used unchanged on every program a certificate states:

* `vc_tri` (`sumI`): `vcgen4`, unfold `sumFns`, split the hypotheses, substitute equations, add
  `triBV x = triBV (x - 1) + x` for each hypothesis `x ≠ 0` and `triBV x = 0` for each `x = 0`
  (`tri_facts`), normalise with `ring_nf` (`BitVec 32` is a commutative ring) and close with
  `bv_omega`. Without `ring_nf`, `bv_omega` did not finish in 45 s on `v3 + (v2 - 1) + 1 + t = u`
  (the `sum-decfirst` back edge);
* `vc_simp` (`maxI`, `addI`: no loop): `vcgen4`, then `intros; simp_all` on each goal.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCInfer

theorem triBV_zero0 : Silmaril.WasmSpec.SumTo.triBV (0 : BitVec 32) = 0 := rfl

theorem triBV_of_eq {x : BitVec 32} (h : x = 0) : Silmaril.WasmSpec.SumTo.triBV x = 0 := by
  subst h; rfl

open Lean in
/-- The arguments `x` of the subterms `triBV x` of an expression. -/
meta partial def triArgs (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
  let acc := if e.isAppOfArity ``Silmaril.WasmSpec.SumTo.triBV 1 && !acc.contains e.appArg! then
    acc.push e.appArg! else acc
  match e with
  | .app f a => triArgs a (triArgs f acc)
  | .lam _ t b _ | .forallE _ t b _ => triArgs b (triArgs t acc)
  | .mdata _ b => triArgs b acc
  | _ => acc

open Lean Elab Tactic Meta in
/-- Add the facts `triBV x = triBV (x - 1) + x` for every hypothesis `¬ x = 0` and for every
`triBV x` of the goal and the hypotheses whose `x ≠ 0` `bv_omega` proves, `triBV x = triBV y`
when `bv_omega` proves `x = y`, `triBV x = 0` for every hypothesis `x = 0`, and `triBV 0 = 0`
(hypotheses are kept, not rewritten). -/
elab "tri_facts" : tactic => withMainContext do
  let mut ts : Array Term := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let h ← Term.exprToSyntax d.toExpr
    if let some p := ty.not? then
      if p.isAppOfArity ``Eq 3 then
        ts := ts.push (← `(Silmaril.Wasm.Auto2.VCLib.triBV_step' $h))
    else if ty.isAppOfArity ``Eq 3 then
      ts := ts.push (← `(Silmaril.Wasm.Auto2.VCInfer.triBV_of_eq $h))
  -- `triBV x` with `x` not a variable and `x ≠ 0` provable by `bv_omega` from the hypotheses
  -- (e.g. `x = i + 1` with `i < n`).
  let g ← getMainGoal
  let mut args : Array Lean.Expr := #[]
  let hyps := (← getLCtx).decls.toList.filterMap id |>.filter (!·.isImplementationDetail)
  for e in (← g.getType) :: hyps.map (·.type) do
    let e ← instantiateMVars e
    args := triArgs e args
  for a in args do
    if a.isFVar then continue
    let x ← Term.exprToSyntax a
    let ty ← Term.elabTerm (← `($x ≠ 0)) none
    let mv ← mkFreshExprMVar ty
    let st ← saveState
    try
      let rest ← Tactic.run mv.mvarId! (Tactic.withoutRecover (evalTactic (← `(tactic| bv_omega))))
      if rest.isEmpty then
        ts := ts.push (← `(Silmaril.Wasm.Auto2.VCLib.triBV_step' $(← Term.exprToSyntax (← instantiateMVars mv))))
      else st.restore
    catch _ => st.restore
  -- `triBV x = triBV y` for variables `x`, `y` when `bv_omega` proves `x = y` (e.g. `i ≤ n` and
  -- `n ≤ i` at a loop exit).
  for a in args do
    for b in args do
      if a == b || !a.isFVar || !b.isFVar || Lean.Expr.lt b a then continue
      let x ← Term.exprToSyntax a
      let y ← Term.exprToSyntax b
      let ty ← Term.elabTerm (← `($x = $y)) none
      let mv ← mkFreshExprMVar ty
      let st ← saveState
      try
        let rest ← Tactic.run mv.mvarId! (Tactic.withoutRecover (evalTactic (← `(tactic| bv_omega))))
        if rest.isEmpty then
          ts := ts.push (← `(congrArg Silmaril.WasmSpec.SumTo.triBV $(← Term.exprToSyntax (← instantiateMVars mv))))
        else st.restore
      catch _ => st.restore
  for t in ts do
    evalTactic (← `(tactic| try have := $t))
  evalTactic (← `(tactic| have := Silmaril.Wasm.Auto2.VCInfer.triBV_zero0))
  evalTactic (← `(tactic| have := Silmaril.Wasm.Auto2.VCLib.triBV_zero'))

/-- The fixed tactic of `sumI`. -/
macro "vc_tri" : tactic => `(tactic| (
  vcgen4 <;> simp only [Silmaril.Wasm.Auto2.VCLib.sumFns] <;>
  (try intro h) <;> (try casesm* _ ∧ _) <;>
  (try simp only [ne_eq, Decidable.not_not] at *) <;> (try subst_vars) <;>
  tri_facts <;> (try ring_nf at *) <;> bv_omega))

/-- The fixed tactic of the loop-free `InferFun`s. -/
macro "vc_simp" : tactic => `(tactic| (vcgen4 <;> (intros; simp_all)))

end Silmaril.Wasm.Auto2.VCInfer

/--
info: 'Silmaril.Wasm.Auto2.VCInfer.modEquiv_of_infer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCInfer.modEquiv_of_infer
