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

/--
`bv_decide_kernel` proves a `BitVec`/`Bool` goal using `bv_normalize` alone and
checks that the proof depends on no axioms beyond `propext`, `Classical.choice`
and `Quot.sound`. It fails on goals that `bv_decide` would send to the SAT
solver (whose proof would rest on a native-evaluation axiom). Options are passed
to `bv_normalize`.
-/
syntax (name := bvDecideKernel) "bv_decide_kernel" Lean.Parser.Tactic.optConfig : tactic

@[tactic bvDecideKernel] def evalBvDecideKernel : Tactic := fun stx => do
  let cfg : TSyntax ``Lean.Parser.Tactic.optConfig := ⟨stx[1]⟩
  let goal ← getMainGoal
  let rest ← Term.withoutErrToSorry <| run goal do
    evalTactic (← `(tactic| bv_normalize $cfg:optConfig))
  unless rest.isEmpty do
    throwError "bv_decide_kernel: `bv_normalize` does not close the goal, so `bv_decide` would \
      need the SAT solver and a native-evaluation axiom; run `bv_normalize` to see what remains"
  let proof ← instantiateMVars (mkMVar goal)
  if proof.hasSyntheticSorry || proof.hasSorry then
    throwError "bv_decide_kernel: the proof contains `sorry`"
  let bad ← nonstandardAxioms proof
  unless bad.isEmpty do
    throwError m!"bv_decide_kernel: the proof depends on axioms outside policy.toml's \
      standard set: {bad.toList}"
  replaceMainGoal []

end Silmaril.Prelude.BVDecide
