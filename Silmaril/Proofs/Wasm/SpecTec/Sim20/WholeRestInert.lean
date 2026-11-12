module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestVar

/-!
# The rules the scalar builtins leave inert

The wasm-2.0 script declares `$nbytes_`, `$ibytes_`, `$vbytes_`, `$lanes_` and `$inv_lanes_`
`hint(builtin)` with no clause, and `Sim.Floats.floatIntB` answers none of them
(`floatIntB_inert`). A rule with an `if` premise comparing a call to one of them can therefore never
fire there (`not_body_inert`). This covers, checked against the script (`inertRead20_ok`,
`inertStep20_ok`, kernel computations):

* `Step_read` 23, 25, 27, 29, 31, 33, 35: `load-num-val`, `load-pack-val`, `vload-val`,
  `vload-shape-val`, `vload-splat-val`, `vload-zero-val`, `vload_lane-val`;
* `Step` 12, 14, 16, 18: `store-num-val`, `store-pack-val`, `vstore-val`, `vstore_lane-val`.

Backwards these obligations of `BwdRestW2` hold vacuously (`bwdRestW2_of_rest3`). This is a fact
about `floatIntB`, not about the script: with builtins answering these primitives the rules fire,
and the forward half needs them to.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (Fires RuleBody)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (relRules)

set_option maxRecDepth 100000

variable {H : Type}

/-! ## Inert premises -/

/-- The byte and lane primitives `floatIntB` does not answer. -/
def inertNames : List IL.Id := ["nbytes_", "ibytes_", "vbytes_", "lanes_", "inv_lanes_"]

/-- A call to an inert primitive. -/
def callsInert : Exp → Bool
  | .callE f _ => inertNames.contains f
  | _ => false

/-- An `if` premise comparing a call to an inert primitive. -/
def premInert : Prem → Bool
  | .ifPr (.cmpE _ _ a b) => callsInert a || callsInert b
  | _ => false

/-- A rule with such a premise. -/
def ruleInert : Rule → Bool
  | .ruleD _ _ _ _ prems => prems.any premInert

/-- The environment facts that make the inert primitives denote nothing. -/
def InertEnv (env : Env) : Prop :=
  ∀ f ∈ inertNames, (∃ ps t, env.findDef? f = some (ps, t, [])) ∧
    ∀ ws, env.builtins.call f ws = none

/-- `floatIntB` answers none of the inert primitives. -/
theorem floatIntB_inert (P : Profile) {f : IL.Id} (hf : f ∈ inertNames) (ws : List ArgV) :
    (Sim.Floats.floatIntB P).call f ws = none := by
  simp only [inertNames, List.mem_cons, List.not_mem_nil, or_false] at hf
  have hn : f ∉ Sim.Floats.floatNames := by
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [Sim.Floats.floatIntB, hn, ↓reduceIte]
  rcases hf with rfl | rfl | rfl | rfl | rfl <;>
  · unfold Sim.IntNumeric.intCall
    split <;> simp_all

/-- `simEnv20` at the scalar builtins. -/
theorem inertEnv20 (P : Profile) : InertEnv (simEnv20 (Sim.Floats.floatIntB P)) := by
  intro f hf
  refine ⟨?_, floatIntB_inert P hf⟩
  simp only [inertNames, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩

/-- A call to an inert primitive denotes nothing. -/
theorem not_evalExp_inert {env : Env} (E : InertEnv env) {e : Exp} (he : callsInert e = true)
    {σ : List (IL.Id × Value)} {v : Value} : ¬ EvalExp env (VarEnv.empty.bindVals σ) e v := by
  cases e with
  | callE f args =>
    have hf : f ∈ inertNames := by simpa [callsInert] using he
    obtain ⟨⟨ps, t, hd⟩, hb⟩ := E f hf
    exact fun h => Equiv.ExecBuiltins.not_callDef_of_nil rfl hd hb (evalExp_callE_iff.1 h)
  | _ => simp [callsInert] at he

/-- **A rule with an inert premise never fires.** -/
theorem not_body_inert {env : Env} (E : InertEnv env) {r : Rule} (hr : ruleInert r = true)
    {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {op : MixopS} {v : Value} :
    ¬ RuleBody env D els [] [] op r v := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  intro hb
  obtain ⟨σ, -, -, hp⟩ := Silmaril.Wasm.SpecTec.Sim.ruleBody_scope hb
  obtain ⟨pr, hpr, hi⟩ := List.any_eq_true.1 (by simpa [ruleInert] using hr)
  match pr, hi with
  | .ifPr (.cmpE _ _ a b), hi =>
    obtain ⟨va, vb, ha, hb', -⟩ := evalExp_cmpE_iff.1 (Pure.ifPrem (hp _ hpr))
    rcases Bool.or_eq_true_iff.1 hi with h | h
    · exact not_evalExp_inert E h ha
    · exact not_evalExp_inert E h hb'

/-! ## The inert rules of the 2.0 script -/

/-- The `Step_read` rules with an inert premise. -/
def inertRead20 : List Nat := [23, 25, 27, 29, 31, 33, 35]

/-- The `Step` rules with an inert premise. -/
def inertStep20 : List Nat := [12, 14, 16, 18]

/-- Every listed rule of `x` has an inert premise. -/
noncomputable def inertOk (x : IL.Id) (l : List Nat) : Bool :=
  l.all fun i =>
    match (relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed) x)[i]? with
    | some r => ruleInert r
    | none => false

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- The listed `Step_read` rules have an inert premise (checked against the script). -/
theorem inertRead20_ok : inertOk "Step_read" inertRead20 = true := by
  rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- The listed `Step` rules have an inert premise (checked against the script). -/
theorem inertStep20_ok : inertOk "Step" inertStep20 = true := by
  rfl

/-- **A listed rule does not fire** at the scalar builtins. -/
theorem not_fires_inert {P : Profile} {x : IL.Id} {l : List Nat} (hok : inertOk x l = true)
    {i : Nat} (hi : i ∈ l) {v : Value} :
    ¬ Fires (simEnv20 (Sim.Floats.floatIntB P)) x i v := by
  rintro ⟨t, rules, r, hrel, hr, hb⟩
  have hrules : relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed) x = rules := by
    rw [← relRules_simEnv20 (Sim.Floats.floatIntB P)]
    simp [relRules, hrel]
  have h₁ := List.all_eq_true.1 hok i hi
  rw [hrules, hr] at h₁
  exact not_body_inert (inertEnv20 P) h₁ hb

/-! ## What is left -/

/-- **What is left of `BwdRestW2`** at the scalar builtins: the live `Step_read` rules other than
`local.get`, `global.get` and the inert ones, and the `Step` rules from `table.set` on other than
the inert ones. -/
structure BwdRestW3 (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) :
    Prop where
  read : ∀ (i : Nat), i ∉ deadRead20 → i ∉ [7, 8] → i ∉ inertRead20 → ∀ (c : Config H)
    (w : List Value), GoodW c →
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code'
  step : ∀ (i : Nat), 6 ≤ i → i ∉ inertStep20 → ∀ (c : Config H) (w : Value), GoodW c →
    Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-- `BwdRestW2` at the scalar builtins, from what is left. -/
theorem bwdRestW2_of_rest3 {hn : H → String} {P Q : Profile} {host : HostSemantics H}
    (R : BwdRestW3 (Sim.Floats.floatIntB Q) hn P host) :
    BwdRestW2 (Sim.Floats.floatIntB Q) hn P host where
  read i hd h78 c w hg hc hw hf := by
    by_cases hi : i ∈ inertRead20
    · exact absurd hf (not_fires_inert inertRead20_ok hi)
    · exact R.read i hd h78 hi c w hg hc hw hf
  step i h6 c w hg hf := by
    by_cases hi : i ∈ inertStep20
    · exact absurd hf (not_fires_inert inertStep20_ok hi)
    · exact R.step i h6 hi c w hg hf

/-- **`Task.wholeStepBwdW` from what is left after this pass** (`BwdRestW3`). -/
theorem wholeStepBwdW_of_rest3
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdRestW3 (Sim.Floats.floatIntB (Profile.spec nd r)) hn (Profile.spec nd r) host) :
    Task.wholeStepBwdW :=
  wholeStepBwdW_of_rest2 fun H hn hinj host nd r => bwdRestW2_of_rest3 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim20.Whole
