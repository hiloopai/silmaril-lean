module

public import Std.Tactic.BVDecide
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Util.CollectAxioms

/-!
# `bv_decide_kernel`: the kernel-checked subset of `bv_decide`

`bv_decide` runs in two stages. First `bv_normalize` rewrites the goal with
`simp` lemmas, which produces an ordinary proof term that the kernel checks.
If that does not close the goal, the goal is bitblasted and sent to an external
SAT solver. The solver's LRAT certificate is then checked by *compiled* code
through `Lean.Meta.nativeEqTrue`, and the result is asserted as a fresh axiom
named `<decl>._native.bv_decide.ax_<n>`. That axiom is outside the
`propext`/`Classical.choice`/`Quot.sound` policy of this library
(`policy.toml`). Nothing in the build fails when it appears.

`bv_decide_kernel` is fail-closed and restricted to the first stage:

* it runs `bv_normalize` and fails if any goal remains, saying that the goal
  needs the SAT stage;
* it then collects the axioms the proof depends on, transitively, and fails
  unless they are among `propext`, `Classical.choice` and `Quot.sound`.

When it succeeds, the theorem is the same statement `bv_decide` would prove
(both close the given goal) and its proof is checked by the kernel alone. No
external solver, compiled checker or native axiom is in the trusted base. It is
**not** a kernel LRAT checker: goals that need SAT are rejected, not
kernel-checked. The upstream LRAT check cannot be reduced by the kernel on this
toolchain (bitblasting hash-conses through the opaque `mixHash`, and the
certificate parser is `partial`). See `docs/bv-decide-trust.md`.
-/

public meta section

namespace Silmaril.Prelude.BVDecide

open Lean Elab Tactic Meta

/-- The axioms a kernel-only proof may depend on (`policy.toml`'s `standard`). -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The axioms that the constants of `e` depend on, transitively, outside
`standardAxioms`. -/
def nonstandardAxioms (e : Expr) : MetaM (Array Name) := do
  let mut bad : Array Name := #[]
  for c in e.getUsedConstants do
    for ax in ← collectAxioms c do
      unless standardAxioms.contains ax || bad.contains ax do
        bad := bad.push ax
  return bad

/-! ## The native procedure behind `bv_decide`

When `bv_normalize` does not close a goal, `bv_decide` asks
`Lean.Meta.nativeEqTrue` to evaluate `verifyBVExpr e cert` in compiled code,
where `verifyBVExpr e cert = verifyCert (AIG.toCNF e.bitblast.relabelNat) cert`.
The natively evaluated surface is therefore **bitblasting** (hash-consed through
the opaque `mixHash`), **AIG to CNF**, **relabeling**, the **LRAT parser**
(`partial`) and the **LRAT checker**, together with the runtime implementations
they call (GMP, `ByteArray`, `String`). It is not the LRAT checker alone.
Normalization, reification and the soundness lemma below are kernel-checked; the
external SAT solver is untrusted. These names are resolved when this module is
compiled, so a toolchain that renames them fails the build. -/

/-- The constant `bv_decide` evaluates natively. -/
def nativeEvaluatedConst : Name := ``Std.Tactic.BVDecide.Reflect.verifyBVExpr

/-- The kernel-checked lemma that turns `verifyBVExpr e cert = true` into `e.Unsat`. -/
def nativeSoundnessConst : Name := ``Std.Tactic.BVDecide.Reflect.unsat_of_verifyBVExpr_eq_true

/-- Whether `n` has the shape of an axiom that `bv_decide` adds for one native
evaluation, `<decl>._native.bv_decide.ax_<n>` (`Lean.Meta.nativeEqTrue`).

This only recognizes names. It is **not** provenance: any declaration could have
this name. A registry that admits native uses must also inspect the axiom's
statement (an equation `verifyBVExpr e cert = true`, see `nativeEvaluatedConst`),
bind it to a registered entry point and toolchain, and reject other native
axioms. -/
def isBvDecideNativeAxiom (n : Name) : Bool :=
  match n.components.reverse with
  | .str _ last :: .str _ "bv_decide" :: .str _ "_native" :: _ => last.startsWith "ax"
  | _ => false

/-- Whether `ax` is an axiom whose statement is exactly one native evaluation of
`nativeEvaluatedConst`: `verifyBVExpr e cert = true` for closed `e` and `cert`.
This checks the statement, not who added the axiom; binding it to a registered
entry point and toolchain is the registry's job. -/
def isBvDecideNativeStatement (ax : Name) : MetaM Bool := do
  let some (.axiomInfo info) := (← getEnv).find? ax | return false
  let_expr Eq ty lhs rhs := info.type | return false
  unless ty.isConstOf ``Bool && rhs.isConstOf ``Bool.true do return false
  return lhs.isAppOfArity nativeEvaluatedConst 2 && !lhs.hasFVar && !lhs.hasMVar &&
    info.levelParams.isEmpty

/-! ## The kernel-only fallback -/

/-- The outcome of `kernelFallback`. -/
inductive KernelResult where
  /-- The goal is closed by a proof on the standard axioms. -/
  | proved
  /-- `bv_normalize` does not close the goal: proving it needs the SAT stage,
  which has no kernel-checked route on this toolchain. The goal is left
  unassigned, as it was before the call. -/
  | needsSat

/--
Prove `goal` with `bv_normalize` alone, checking that the proof depends on no
axioms beyond `standardAxioms`. Returns `.needsSat`, with every change undone,
when `bv_normalize` leaves a goal; throws when the proof contains `sorry` or a
nonstandard axiom. This is the hook a mode framework calls for its kernel-only
(paranoid) route; it never runs the SAT solver or native code.
-/
def kernelFallback (goal : MVarId)
    (cfg : TSyntax ``Lean.Parser.Tactic.optConfig :=
      ⟨mkNode ``Lean.Parser.Tactic.optConfig #[mkNullNode]⟩) : TermElabM KernelResult := do
  let saved ← saveState
  let rest ← Term.withoutErrToSorry <| Tactic.run goal do
    evalTactic (← `(tactic| bv_normalize $cfg:optConfig))
  unless rest.isEmpty do
    saved.restore
    return .needsSat
  let proof ← instantiateMVars (mkMVar goal)
  if proof.hasSyntheticSorry || proof.hasSorry then
    saved.restore
    throwError "bv_decide_kernel: the proof contains `sorry`"
  let bad ← nonstandardAxioms proof
  unless bad.isEmpty do
    saved.restore
    throwError m!"bv_decide_kernel: the proof depends on axioms outside policy.toml's \
      standard set: {bad.toList}"
  return .proved

/--
`bv_decide_kernel` proves a `BitVec`/`Bool` goal using `bv_normalize` alone and
checks that the proof depends on no axioms beyond `propext`, `Classical.choice`
and `Quot.sound` (`kernelFallback`). It fails on goals that `bv_decide` would
send to the SAT solver (whose proof would rest on a native-evaluation axiom).
Options are passed to `bv_normalize`.
-/
syntax (name := bvDecideKernel) "bv_decide_kernel" Lean.Parser.Tactic.optConfig : tactic

@[tactic bvDecideKernel] def evalBvDecideKernel : Tactic := fun stx => do
  match ← kernelFallback (← getMainGoal) ⟨stx[1]⟩ with
  | .proved => replaceMainGoal []
  | .needsSat =>
    throwError "bv_decide_kernel: `bv_normalize` does not close the goal, so `bv_decide` would \
      need the SAT solver and a native-evaluation axiom; run `bv_normalize` to see what remains"

end Silmaril.Prelude.BVDecide
