module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.Utf8

/-!
# Round 5: SpecTec cannot step from an ill-typed frame, so the round-4 target is false

Every one of the 36 rules of SpecTec's `Step` reads its left-hand state either as a quantifier
`z : state` or as `s; f` with a quantifier `f : frame` (`stepRules_guarded`, checked on the
rules of the fixed script by `rfl`). The declarative reading types every quantifier
(`QuantsOk`), so **no `Step` fires on a configuration whose frame is not a typed `frame`**
(`not_sstep_of_frame`).

With `Utf8.lean`, the frame of `expNopCfg` (`nop` over `ConfigOk.exportModule`, which exports a
global as `"g"`) is not typed in any `simEnv B`. The configuration is valid and bounded, and
Core steps from it (`nop`). So the forward conjunct of `Round4.Task.wholeStepValid` fails at it
for every `B`, encoding, host and profile: **`Round4.Task.wholeStepValid` is false**
(`not_wholeStepValid`). The cause is the evaluator's reading of `$utf8` (`Utf8.lean`), not
hosts, so the target restricted to `HostOk` hosts is false too (`not_wholeStepValidOk`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Pos

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

/-! ## Every `Step` rule types its left-hand state -/

/-- `z : state`. -/
def isStateParam (z : IL.Id) : Param → Bool
  | .expP y (.varT "state" []) => y == z
  | _ => false

/-- `f : frame`. -/
def isFrameParam (f : IL.Id) : Param → Bool
  | .expP y (.varT "frame" []) => y == f
  | _ => false

/-- The conclusion reads its left-hand state through a typed quantifier: `z; _ ~> _` with
`z : state`, or `(s; f); _ ~> _` with `f : frame`. -/
def guardQE (qs : List Param) : Exp → Bool
  | .tupE [.caseE "%;%" (.tupE [.varE z, _]), _] => qs.any (isStateParam z)
  | .tupE [.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE _, .varE f]), _]), _] =>
      qs.any (isFrameParam f)
  | _ => false

/-- `guardQE` on a rule. -/
def stateGuard : Rule → Bool
  | .ruleD _ qs _ e _ => guardQE qs e

set_option maxRecDepth 100000 in
/-- **Every rule of `Step` guards its state**, in every `simEnv B`. -/
theorem stepRules_guarded (B : Builtins) : ∃ t rules,
    (simEnv B).findRel? "Step" = some ([], "%~>%", t, rules) ∧ rules.all stateGuard = true :=
  ⟨_, _, rfl, rfl⟩

/-- The state component of a pair conclusion. -/
theorem evalExp_state_of_pair {env : Env} {ρ : VarEnv} {X Y Z : Exp} {a b w : Value}
    (h : EvalExp env ρ (.tupE [.caseE "%;%" (.tupE [X, Y]), Z])
      (.tuple [.case "%;%" (.tuple [a, b]), w])) : EvalExp env ρ X a := by
  obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 h
  obtain ⟨u, us, hu, -, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨rfl, -⟩ := List.cons.inj (Value.tuple.inj hv)
  obtain ⟨p, hp, hpe⟩ := evalExp_caseE_iff.1 hu
  obtain ⟨-, rfl⟩ := Value.case.inj hpe
  obtain ⟨ps, hps, hpv⟩ := evalExp_tupE_iff.1 hp
  obtain ⟨x, xs, hx, -, rfl⟩ := evalExps_cons_iff.1 hps
  obtain ⟨rfl, -⟩ := List.cons.inj (Value.tuple.inj hpv)
  exact hx

/-- A quantifier of a closed named type, bound to `v`, types `v`. -/
theorem typedV_of_quant {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {qs : List Param}
    (hq : QuantsOk (simEnv B) ρ qs) {x y : IL.Id} (hx : Param.expP x (.varT y []) ∈ qs)
    {v : Value} (hv : ρ.findVal? x = some v) : TypedV (simEnv B) (.varT y []) v := by
  obtain ⟨w, hw, ht⟩ := hq x _ hx
  rw [hv] at hw
  obtain rfl := Option.some.inj hw
  exact Typing.typedV_of_hasTyp hρ ht

/-- `any` of a parameter test, as a member. -/
theorem mem_of_any_isState {qs : List Param} {z : IL.Id} (h : qs.any (isStateParam z) = true) :
    Param.expP z (.varT "state" []) ∈ qs := by
  obtain ⟨q, hq, hz⟩ := List.any_eq_true.1 h
  unfold isStateParam at hz
  split at hz
  · obtain rfl := beq_iff_eq.1 hz
    exact hq
  · cases hz

/-- `any` of a parameter test, as a member. -/
theorem mem_of_any_isFrame {qs : List Param} {f : IL.Id} (h : qs.any (isFrameParam f) = true) :
    Param.expP f (.varT "frame" []) ∈ qs := by
  obtain ⟨q, hq, hz⟩ := List.any_eq_true.1 h
  unfold isFrameParam at hz
  split at hz
  · obtain rfl := beq_iff_eq.1 hz
    exact hq
  · cases hz

/-- **A guarded conclusion that evaluates to a configuration's image types its frame.** -/
theorem frame_of_guardQE {B : Builtins} {H : Type} {hn : H → String} {c : Config H}
    {qs : List Param} {e : Exp} {ρ : VarEnv} {w : Value} (hg : guardQE qs e = true)
    (hρ : ValsOnly ρ) (hq : QuantsOk (simEnv B) ρ qs)
    (he : EvalExp (simEnv B) ρ e (.tuple [configV hn c, w])) :
    TypedV (simEnv B) frameT (frameV c.frame) := by
  unfold guardQE at hg
  split at hg
  · have hz := evalExp_varE_iff.1 (evalExp_state_of_pair he)
    have hs := typedV_of_quant hρ hq (mem_of_any_isState hg) hz
    exact (((Typing.typingFacts_simEnv B hn).state c.store c.frame).1 hs).2
  · obtain ⟨u, hu, hue⟩ := evalExp_caseE_iff.1 (evalExp_state_of_pair he)
    obtain ⟨-, rfl⟩ := Value.case.inj hue
    obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 hu
    obtain ⟨x, xs, -, hxs, rfl⟩ := evalExps_cons_iff.1 hvs
    obtain ⟨y, ys, hy, -, rfl⟩ := evalExps_cons_iff.1 hxs
    obtain ⟨-, hyv⟩ := List.cons.inj (Value.tuple.inj hv)
    obtain ⟨rfl, -⟩ := List.cons.inj hyv
    exact typedV_of_quant hρ hq (mem_of_any_isFrame hg) (evalExp_varE_iff.1 hy)
  · cases hg

/-- **SpecTec does not step from a configuration whose frame is not a typed `frame`.** -/
theorem not_sstep_of_frame {B : Builtins} {H : Type} {hn : H → String} {c : Config H}
    (hf : ¬ TypedV (simEnv B) frameT (frameV c.frame)) (w : Value) :
    ¬ SStep (simEnv B) (configV hn c) w := by
  intro h
  cases h with
  | rule hrel hrule hps hq he _ =>
    obtain ⟨t', rules', hrel', hall⟩ := stepRules_guarded B
    rw [hrel'] at hrel
    obtain ⟨rfl, -, -, rfl⟩ : [] = _ ∧ _ ∧ _ ∧ rules' = _ := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using hrel
    have hg := List.all_eq_true.1 hall _ (List.mem_of_getElem? hrule)
    obtain rfl : _ = VarEnv.empty := (Option.some.inj hps).symm
    exact hf (frame_of_guardQE hg (IntNumeric.valsOnly_bindVals _) hq he)

end Silmaril.Wasm.SpecTec.Sim.Round5.Pos
