module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Refute.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Simd.Thms

/-!
# Round 6: the NaN witness is outside `wholeStepValidSel`

Round 5's second argument against `Round5.Task.wholeStepValidSel` was that at
`v128.const nanLane0; f64x2.promote_low_f32x4` under the spec NaN profile Core has two
successors while SpecTec's `vcvtop` has one. The first half holds (`step_promCfg`,
`promDone_ne`). The second does not apply to `wholeStepValidSel`:

* `f64x2.promote_low_f32x4` is a `SimdTy.FloatMissel` instruction (`floatMissel_promoteI`): the
  evaluator types `VCVTOP` through the integer instance of its family, so its image is not a
  typed `instr`. The witness is therefore not `Target.BoundedSel` (`not_boundedSel_promCfg`),
  and `wholeStepValidSel` says nothing about it.
* SpecTec does not step from the witness at all (`not_sstep_promCfg`), by its proof's guard
  read at `VCVTOP` (`stepRules_lastGuardedAt`): every `Step` rule reads the last instruction of
  its code through a typed quantifier or as a literal case other than `VCVTOP`. So SpecTec's
  `Step` is (vacuously) deterministic there, and the forward conjunct already fails for want of
  any SpecTec step, as at `f32x4.sqrt` witness.

Of `$vcvtop__`'s operators only `extend` is not `FloatMissel`, and it is deterministic in Core,
so the single-valued `$vcvtop__` is no obstruction on `BoundedSel` configurations.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Refute

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type} {B : Builtins}

/-! ## Core: two successors -/

/-- The witness's operand is `nanLane0`. -/
theorem promCfg_eq : (promCfg (H := H)).code = [vconst Round5.Simd.nanLane0, .plain promoteI] :=
  rfl

/-- **Core steps from the witness to both NaNs** under the spec NaN profile. -/
theorem step_promCfg (nd : Bool) (r : RelaxedChoice) (host : HostSemantics H) (neg : Bool) :
    Step (Profile.spec nd r) host promCfg (promDone neg) :=
  .vector (.vecConvert (Round5.Simd.promote_two rfl neg))

/-- **The two successors differ.** -/
theorem promDone_ne : (promDone false : Config H) ≠ promDone true := fun h =>
  Round5.Simd.promotedNaN_ne (vconst_injective (List.head_eq_of_cons_eq (congrArg Config.code h)))
where
  /-- `v128.const` is injective. -/
  vconst_injective {a b : V128} (h : vconst a = vconst b) : a = b := by
    simpa [vconst, Val.toAdmin] using h

/-- **The witness is valid**: `⊢ promCfg : v128`. -/
theorem configOk_promCfg : ConfigOk (promCfg (H := H)) [.vec .v128] :=
  ⟨_, ⟨ConfigOk.coreStoreOk_empty, _, [], ConfigOk.moduleInstOk_empty _, .nil, rfl⟩,
    .cons (.plain (.vector (.vecConst _))) (by simp)
      (.single (.plain (.vector (.vecConvert rfl))))⟩

/-- **The witness is bounded and export-free.** -/
theorem boundedNE_promCfg : Round5.Pos.BoundedNE (promCfg (H := H)) :=
  ⟨Round5.Target.bounded_empty (by simp [Round4.AdminsBnd, Round4.AdminBnd, Round4.instrBnd,
      promoteI]),
    Round5.Target.noExports_empty (by simp [Round5.Pos.AdminsNE, Round5.Pos.AdminNE])⟩

/-- **Its successors are bounded, export-free and free of `FloatMissel` code.** -/
theorem boundedSel_promDone (neg : Bool) : Round5.Target.BoundedSel (promDone neg : Config H) :=
  ⟨⟨Round5.Target.bounded_empty (by simp [Round4.AdminsBnd, Round4.AdminBnd, Round4.instrBnd]),
      Round5.Target.noExports_empty (by simp [Round5.Pos.AdminsNE, Round5.Pos.AdminNE])⟩,
    ⟨by simp [promDone, Round5.Target.StoreSel], by
      simp [promDone, Round5.Target.AdminsSel, Round5.Target.AdminSel, Round5.Target.instrSel,
        Round5.SimdTy.FloatMissel]⟩⟩

/-! ## The witness is not `BoundedSel` -/

/-- **`f64x2.promote_low_f32x4` is a `FloatMissel` instruction.** -/
theorem floatMissel_promoteI : Round5.SimdTy.FloatMissel promoteI = true := rfl

/-- **The witness is not `BoundedSel`**, so it is no counterexample to
`Round5.Task.wholeStepValidSel`. -/
theorem not_boundedSel_promCfg : ¬ Round5.Target.BoundedSel (promCfg (H := H)) := fun h => by
  have hc : Round5.Target.AdminsSel (promCfg (H := H)).code := h.2.code
  have hi : Round5.Target.instrSel promoteI = true := hc.2.1
  have hf : Round5.Target.instrSel promoteI = false := rfl
  exact Bool.false_ne_true (hf.symm.trans hi)

/-! ## SpecTec: no step -/

/-- Track target's code guard at the case name `op`. -/
def codeGuardAt (op : MixopS) : Rule → Bool
  | .ruleD _ qs _ e _ => Round5.Target.codeGuardQE qs op e

set_option maxRecDepth 100000 in
/-- **Every rule of `Step` reads the last instruction of its code**, with `VCVTOP` as the
excluded literal case (`stepRules_lastGuarded` checks `VUNOP`). -/
theorem stepRules_lastGuardedAt (B : Builtins) : ∃ t rules,
    (simEnv B).findRel? "Step" = some ([], "%~>%", t, rules) ∧
      rules.all (codeGuardAt "VCVTOP") = true :=
  ⟨_, _, rfl, rfl⟩

/-- **SpecTec does not step from a configuration whose last instruction is not `LastGood`** at
`VCVTOP` (`not_sstep_of_last`, at `VCVTOP`). -/
theorem not_sstep_of_lastVcvtop {hn : H → String} {c : Config H} {u : Value}
    (hu : (adminsToV c.code).getLast? = some u) (hb : ¬ Round5.Target.LastGood B "VCVTOP" u)
    (w : Value) : ¬ SStep (simEnv B) (configV hn c) w := by
  intro h
  cases h with
  | rule hrel hrule hps hq he _ =>
    obtain ⟨t', rules', hrel', hall⟩ := stepRules_lastGuardedAt B
    rw [hrel'] at hrel
    obtain ⟨rfl, -, -, rfl⟩ : [] = _ ∧ _ ∧ _ ∧ rules' = _ := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using hrel
    have hg := List.all_eq_true.1 hall _ (List.mem_of_getElem? hrule)
    obtain rfl : _ = VarEnv.empty := (Option.some.inj hps).symm
    exact hb (Round5.Target.lastGood_of_codeGuardQE hg (IntNumeric.valsOnly_bindVals _) hq he hu)

set_option maxRecDepth 100000 in
/-- No `VCVTOP` is a typed `val`. -/
theorem not_typedV_val_vcvtop (p : Value) :
    ¬ TypedV (simEnv B) (.varT "val" []) (.case "VCVTOP" p) := fun h => by
  obtain ⟨op, w, hc, hf⟩ := IntNumeric.val_tag ConfigOk.valsOnly_empty (h _ ConfigOk.valsOnly_empty)
  obtain ⟨rfl, rfl⟩ := Value.case.inj hc
  exact hf rfl

/-- The image of `f64x2.promote_low_f32x4` is a `VCVTOP`. -/
theorem instrToV_promoteI : ∃ p, instrToV promoteI = .case "VCVTOP" p := ⟨_, rfl⟩

/-- **The image of `f64x2.promote_low_f32x4` is not `LastGood`** at `VCVTOP`. -/
theorem not_lastGood_promoteI : ¬ Round5.Target.LastGood B "VCVTOP" (instrToV promoteI) := by
  obtain ⟨p, hp⟩ := instrToV_promoteI
  rintro (h | h | h)
  · exact h p hp
  · exact Round5.SimdTy.not_typedV_of_floatMissel floatMissel_promoteI h
  · exact not_typedV_val_vcvtop p (hp ▸ h)

/-- **SpecTec does not step from the witness**, in any `simEnv B`. -/
theorem not_sstep_promCfg (hn : H → String) (w : Value) :
    ¬ SStep (simEnv B) (configV hn (promCfg (H := H))) w :=
  not_sstep_of_lastVcvtop (c := promCfg) rfl not_lastGood_promoteI w

/-- **SpecTec's `Step` is deterministic at the witness** (it has no successor). -/
theorem sstep_promCfg_det (hn : H → String) {w₁ w₂ : Value}
    (h₁ : SStep (simEnv B) (configV hn (promCfg (H := H))) w₁)
    (_h₂ : SStep (simEnv B) (configV hn (promCfg (H := H))) w₂) : w₁ = w₂ :=
  absurd h₁ (not_sstep_promCfg hn w₁)

/-- **The forward conjunct of `Round5.Task.wholeStepValidOk` fails at the witness**, for every
`B`, encoding, host and spec NaN profile: Core steps (to either NaN) and SpecTec does not. -/
theorem not_forwardOk_promCfg (B : Builtins) (nd : Bool) (r : RelaxedChoice)
    (host : HostSemantics H) (hn : H → String) :
    ¬ ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Round5.Pos.BoundedNE c →
      Round5.Pos.BoundedNE c' → Step (Profile.spec nd r) host c c' →
      ∃ d', Bwd.ConfigEq c' d' ∧ SStep (simEnv B) (configV hn c) (configV hn d') := fun h => by
  obtain ⟨d', -, hd⟩ := h promCfg (promDone false) _ configOk_promCfg boundedNE_promCfg
    (boundedSel_promDone false).1 (step_promCfg nd r host false)
  exact not_sstep_promCfg hn _ hd

end Silmaril.Wasm.SpecTec.Sim.Round6.Refute
