module

public import Silmaril.Prelude.BVDecide.Native.Defs
public meta import Silmaril.Prelude.BVDecide.Native.Defs

public meta import Lean

/-!
# Regression tests for `bv_decide_policy`, including native runs

This module is outside the `Silmaril` library on purpose: it holds native axioms, a plain
`bv_decide` and a test axiom, none of which may appear in the library
(`scripts/check-layout.sh` scans `Silmaril/` only). It loads its own policy
(`tests/trust/policy.toml`), whose `tests.trust` scope allows the bv_decide procedure in
the `local` profile and in no other.
-/

trust_policy "policy.toml" pin "10e11008bc742db5"

public section

namespace Tests.Trust.BVDecideNative

open Lean Silmaril.Prelude.BVDecide Silmaril.Trust

/-- info: none -/
#guard_msgs in
#eval show Lean.CoreM _ from registrationProblem

/-- The modes of the uses recorded for `decl`. -/
meta def modesOf (decl : Lean.Name) : Lean.CoreM (List String) := do
  let uses := (useExt.getState (← Lean.getEnv)).toList.filter (·.decl == decl)
  return uses.map fun u => match u.mode with | .native => "native" | .kernel => "kernel"

/-- For `decl`: whether its non-standard axioms are exactly the axioms its recorded native
uses name, and each states one closed `verifyBVExpr e cert = true`. -/
meta def nativeBound (decl : Lean.Name) : Lean.CoreM (Nat × Bool) := do
  let axs := (← Lean.collectAxioms decl).filter (!standardAxioms.contains ·)
  let recorded := ((useExt.getState (← Lean.getEnv)).toList.filter (·.decl == decl)).filterMap (·.ax)
  let stmts ← axs.toList.allM fun a => (isBvDecideNativeStatement a).run'
  return (axs.size, axs.toList.all recorded.contains && recorded.all axs.contains && stmts)

/-! ## The kernel route, in every profile -/

theorem kern (x y : BitVec 64) : x + y - y = x := by bv_decide_policy

/-- info: ["kernel"] -/
#guard_msgs in
#eval modesOf ``kern

/-- info: (0, true) -/
#guard_msgs in
#eval nativeBound ``kern

/-! ## A goal that needs SAT, in the local profile: native, bound to this invocation -/

set_option silmaril.trust.profile "local" in
theorem sat (x y : BitVec 8) : x * y = y * x := by bv_decide_policy

/-- info: ["native"] -/
#guard_msgs in
#eval modesOf ``sat

/-- info: (1, true) -/
#guard_msgs in
#eval nativeBound ``sat

set_option silmaril.trust.profile "local" in
#guard_msgs (drop info) in
trust_audit sat

/-! ## Default and paranoid: SAT goals fail, there is no kernel route -/

/--
error: bv_decide_policy: the goal needs SAT, which has no kernel-checked route, and lean.std.bv_decide.verifyBVExpr is not allowed natively here (profile default)
-/
#guard_msgs in
example (x y : BitVec 8) : x * y = y * x := by bv_decide_policy

/--
error: bv_decide_policy: the goal needs SAT, which has no kernel-checked route, and lean.std.bv_decide.verifyBVExpr is not allowed natively here (profile paranoid)
-/
#guard_msgs in
set_option silmaril.trust.profile "paranoid" in
example (x y : BitVec 8) : x * y = y * x := by bv_decide_policy

/-! ## Unrecorded and wrong axioms are rejected -/

/-- A plain `bv_decide` outside the framework records no use. -/
theorem rogue (x y : BitVec 8) : x * y = y * x := by bv_decide

/-- An axiom with the native name shape but the wrong statement. -/
axiom wrong._native.bv_decide.ax_9_9 : (1 : Nat) = 1

theorem usesWrong : (1 : Nat) = 1 := wrong._native.bv_decide.ax_9_9

/-- info: (true, false) -/
#guard_msgs in
#eval show Lean.MetaM _ from do
  let a := ``wrong._native.bv_decide.ax_9_9
  return (isBvDecideNativeAxiom a, ← isBvDecideNativeStatement a)

/-- Whether `trust_audit` reports, under `local`, that `decl` uses a native axiom that no
recorded use produced (core's wording aside). -/
meta def unverified (decl : Lean.Name) : Lean.CoreM Bool := do
  let (_, violations) ← auditLine decl
  return violations.any (·.startsWith "unverified native axiom")

/-- For `decl`'s native axioms: the expression and certificate they evaluate, checked as
`bv_decide_policy` checks them (against an empty "before" environment, so only the shape
and types are tested here), and whether the proof uses each through the soundness lemma. -/
meta def argsOk (decl : Lean.Name) : Lean.MetaM (List Bool) := do
  let some info := (← Lean.getEnv).find? decl | return []
  let some proof := info.value? (allowOpaque := true) | return []
  let axs := (← Lean.collectAxioms decl).filter isBvDecideNativeAxiom
  axs.toList.mapM fun a => do
    match ← invocationArgs? (← Lean.mkEmptyEnvironment) a with
    | some (e, c) => return usesSoundness proof e c a
    | none => return false

/-- info: [true] -/
#guard_msgs in
#eval argsOk ``sat

/-- info: [false] -/
#guard_msgs in
#eval argsOk ``usesWrong

/-- info: (true, true, false) -/
#guard_msgs in
set_option silmaril.trust.profile "local" in
#eval return (← unverified ``rogue, ← unverified ``usesWrong, ← unverified ``sat)

end Tests.Trust.BVDecideNative
