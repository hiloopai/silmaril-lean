module

public import Silmaril.Project.Core.Defs
public meta import Lean.Elab.Tactic
import Silmaril.Proofs.Project.Core.Value

/-!
# Silmaril projects: lemmas about values, and `silmaril_decide`

The kernel-cost policy: a proof about a value runs the
parser in the kernel once, as a `Bool` computation, and never unifies `parse = some ?v`.
`silmaril_decide` closes `X.parses`, `X.Satisfies P` (decidable `P`) and `X.Agrees Y`
(decidable equality) that way; it is meant for small files. The longer proofs are in
`Silmaril.Proofs.Project.Core.Value`.
-/

@[expose] public section

namespace Silmaril.Project

/-- Two artifacts are equivalent when both parse and the values are equal: one kernel `Bool`
(decidable equality of the value type). -/
theorem equivalent_of_decide {S T : ArtifactType} {V : Type} [DecidableEq V]
    {F : Format S V} {G : Format T V} {a : S.Carrier} {b : T.Carrier}
    (h : (match F.parse a, G.parse b with
      | some u, some v => decide (u = v)
      | _, _ => false) = true) : Equivalent F G a b :=
  Silmaril.Proofs.Project.Core.equivalent_of_decide h

theorem bytes_roundtrip : bytes.RoundTrip := Silmaril.Proofs.Project.Core.bytes_roundtrip

end Silmaril.Project

namespace Silmaril.Project.Value

variable {V : Type} {x y : Value V} {P : V → Prop} {v : V}

theorem parses_of_check (h : x.parse.isSome = true) : x.Parses := h

theorem satisfies_of_any [DecidablePred P] (h : (x.parse.any fun v => decide (P v)) = true) :
    x.Satisfies P :=
  Silmaril.Proofs.Project.Core.satisfies_of_any h

theorem satisfies_of_is (h : x.Is v) (hp : P v) : x.Satisfies P := ⟨v, h, hp⟩

theorem parses_of_satisfies (h : x.Satisfies P) : x.Parses := by
  obtain ⟨w, hw, _⟩ := h
  simp [Parses, hw]

/-- Under a certificate, `x.Satisfies P` is `P v`: prove facts about the certificate and move
them to the value (and back). -/
theorem Is.satisfies_iff (h : x.Is v) : x.Satisfies P ↔ P v :=
  ⟨fun ⟨w, hw, hp⟩ => by cases (show v = w from Option.some.inj (h.symm.trans hw)); exact hp,
    satisfies_of_is h⟩

theorem Satisfies.mono {Q : V → Prop} (h : x.Satisfies P) (hPQ : ∀ v, P v → Q v) :
    x.Satisfies Q :=
  let ⟨w, hw, hp⟩ := h; ⟨w, hw, hPQ w hp⟩

/-- A certificate discharges the parse obligation. -/
theorem parses_of_is (h : x.Is v) : x.Parses :=
  parses_of_satisfies (satisfies_of_is (P := fun _ => True) h trivial)

theorem is_of_decide [DecidableEq V] (h : decide (x.parse = some v) = true) : x.Is v :=
  (of_decide_eq_true h : x.parse = some v)

theorem agrees_of_decide [DecidableEq V]
    (h : (match x.parse, y.parse with
      | some a, some b => decide (a = b)
      | _, _ => false) = true) : x.Agrees y :=
  Silmaril.Proofs.Project.Core.agrees_of_decide h

end Silmaril.Project.Value

public meta section

namespace Silmaril.Project

open Lean Meta Elab Tactic

/-- Which `Value` predicate the goal is, after unfolding the definitions above it (a generated
problem such as `X.is` or `N.sol`'s statement). Only the head is unfolded, so the parser itself
is never evaluated by the elaborator. -/
def valueGoal? (e : Expr) : MetaM (Option (Name × Expr)) := do
  let mut e ← instantiateMVars e
  for _ in [0:64] do
    e ← whnfCore e.consumeMData
    let some n := e.getAppFn.constName? | return none
    if n ∈ [``Value.Satisfies, ``Value.Parses, ``Value.Agrees, ``Value.Is] then return some (n, e)
    let some e' ← unfoldDefinition? e | return none
    e := e'
  return none

def valueGoalKind (e : Expr) : MetaM (Option Name) := return (← valueGoal? e).map (·.1)

/-- A value in a message: its name and doc string (`silmaril value` writes the artifact there). -/
def valueMsg (x : Expr) : MetaM MessageData := do
  let some n := x.consumeMData.constName? | return m!"`{x}`"
  match ← findDocString? (← getEnv) n with
  | some d => return m!"`{n}` ({d})"
  | none => return m!"`{n}`"

/-- Why `silmaril_decide` failed when the kernel evaluated a value goal to `false`: in terms of
the problem, the artifact and the property, not of the `Bool` it evaluated. -/
def falseMsg (target : Expr) (kind : Name) (goal : Expr) : MetaM MessageData := do
  let problem := match target.consumeMData.getAppFn.constName? with
    | some n => m!"\n  problem: `{n}`"
    | none => m!""
  let args := goal.getAppArgs
  let x ← valueMsg args[1]!
  let (head, body) ← match kind with
    | ``Value.Satisfies => pure ("the property is false on this artifact",
        m!"{problem}\n  value: {x}\n  property:{indentExpr args[2]!}\nThe artifact does not \
          parse, or its value does not satisfy the property.")
    | ``Value.Parses => pure ("this artifact does not parse", m!"{problem}\n  value: {x}")
    | ``Value.Is => pure ("this artifact is not the given value",
        m!"{problem}\n  value: {x}\n  expected:{indentExpr args[2]!}")
    | _ => pure ("these artifacts do not agree",
        m!"{problem}\n  values: {x} and {← valueMsg args[2]!}")
  return m!"silmaril_decide: {head}{body}\nThe kernel evaluated the goal to `false`, so no \
    proof exists: fix the artifact or the statement, or refute the problem."

end Silmaril.Project

open Lean Elab Tactic

/-- Close `X.parses`, `X.Satisfies P`, `X.Is v` or `X.Agrees Y` by one kernel `Bool` evaluation
(`decide +kernel` behind the matching lemma), and any other decidable goal by `decide +kernel`.
The lemma is chosen from the goal's head, so a failed attempt never makes the elaborator unfold
a parser. Only for small files. -/
elab "silmaril_decide" : tactic => do
  let target ← getMainTarget
  let goal? ← withMainContext do Silmaril.Project.valueGoal? target
  -- the lemma for the goal's head, then one kernel evaluation of its `Bool` premise
  match goal?.map (·.1) with
    | some ``Silmaril.Project.Value.Satisfies =>
      evalTactic (← `(tactic| refine Silmaril.Project.Value.satisfies_of_any ?_))
    | some ``Silmaril.Project.Value.Parses =>
      evalTactic (← `(tactic| refine Silmaril.Project.Value.parses_of_check ?_))
    | some ``Silmaril.Project.Value.Agrees =>
      evalTactic (← `(tactic| refine Silmaril.Project.Value.agrees_of_decide ?_))
    | some ``Silmaril.Project.Value.Is =>
      evalTactic (← `(tactic| refine Silmaril.Project.Value.is_of_decide ?_))
    | _ => pure ()
  try evalTactic (← `(tactic| decide +kernel))
  catch e =>
    -- `decide` evaluated the goal to `false` (not: it could not evaluate it)
    let some (kind, goal) := goal? | throw e
    unless (← e.toMessageData.toString).contains "proved that the proposition" do throw e
    throwError (← withMainContext do Silmaril.Project.falseMsg target kind goal)

end
