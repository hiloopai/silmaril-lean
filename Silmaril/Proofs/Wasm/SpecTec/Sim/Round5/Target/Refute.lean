module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Target.Guard

/-!
# Round 5: `Round5.Task.wholeStepValidOk` is false

With `Guard.lean`, no SpecTec `Step` fires on a configuration whose last instruction is a `VUNOP`
that is neither a typed `instr` nor a typed `val` (`not_sstep_of_last`). The image of
`f32x4.sqrt` is such a `VUNOP` in every `simEnv B` (`SimdTy.not_typedV_f32x4Sqrt`; `val` has no
`VUNOP` case, `not_typedV_val_vunop`).

The witness is `sqrtCfg`: `v128.const 0; f32x4.sqrt` on the empty store, in a frame over the
empty module. It is valid (`configOk_sqrtCfg`), bounded and export-free (`boundedNE_sqrtCfg`), and
Core steps from it to `v128.const r` for some `r` (`step_sqrtCfg`), which is bounded and
export-free too. So the forward conjunct of `Round5.Task.wholeStepValidOk` fails at it for every
`B`, at the injective `Pos.hnU`, the finite `HostOk` host `Pos.divHost` and every profile:
**`Round5.Task.wholeStepValidOk` is false** (`not_wholeStepValidOk`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Target

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type} {B : Builtins}

/-! ## No `Step` from a configuration ending in an untyped `VUNOP` -/

/-- The code component of a pair conclusion. -/
theorem evalExp_code_of_pair {env : Env} {ρ : VarEnv} {X Y Z : Exp} {a b w : Value}
    (h : EvalExp env ρ (.tupE [.caseE "%;%" (.tupE [X, Y]), Z])
      (.tuple [.case "%;%" (.tuple [a, b]), w])) : EvalExp env ρ Y b := by
  obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 h
  obtain ⟨u, us, hu, -, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨rfl, -⟩ := List.cons.inj (Value.tuple.inj hv)
  obtain ⟨p, hp, hpe⟩ := evalExp_caseE_iff.1 hu
  obtain ⟨-, rfl⟩ := Value.case.inj hpe
  obtain ⟨ps, hps, hpv⟩ := evalExp_tupE_iff.1 hp
  obtain ⟨x, xs, -, hxs, rfl⟩ := evalExps_cons_iff.1 hps
  obtain ⟨y, ys, hy, -, rfl⟩ := evalExps_cons_iff.1 hxs
  obtain ⟨-, hyv⟩ := List.cons.inj (Value.tuple.inj hpv)
  obtain ⟨rfl, -⟩ := List.cons.inj hyv
  exact hy

/-- **A guarded conclusion that evaluates to a configuration's image reads its last
instruction**: that instruction is `LastGood`. -/
theorem lastGood_of_codeGuardQE {hn : H → String} {c : Config H} {qs : List Param} {op : MixopS}
    {e : Exp} {ρ : VarEnv} {w u : Value} (hg : codeGuardQE qs op e = true) (hρ : ValsOnly ρ)
    (hq : QuantsOk (simEnv B) ρ qs) (he : EvalExp (simEnv B) ρ e (.tuple [configV hn c, w]))
    (hu : (adminsToV c.code).getLast? = some u) : LastGood B op u := by
  unfold codeGuardQE at hg
  split at hg
  · exact lastGood_of_lastOk hρ hq _ hg (evalExp_code_of_pair he) hu
  · cases hg

/-- **SpecTec does not step from a configuration whose last instruction is not `LastGood`** at
`VUNOP`. -/
theorem not_sstep_of_last {hn : H → String} {c : Config H} {u : Value}
    (hu : (adminsToV c.code).getLast? = some u) (hb : ¬ LastGood B "VUNOP" u) (w : Value) :
    ¬ SStep (simEnv B) (configV hn c) w := by
  intro h
  cases h with
  | rule hrel hrule hps hq he _ =>
    obtain ⟨t', rules', hrel', hall⟩ := stepRules_lastGuarded B
    rw [hrel'] at hrel
    obtain ⟨rfl, -, -, rfl⟩ : [] = _ ∧ _ ∧ _ ∧ rules' = _ := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using hrel
    have hg := List.all_eq_true.1 hall _ (List.mem_of_getElem? hrule)
    obtain rfl : _ = VarEnv.empty := (Option.some.inj hps).symm
    exact hb (lastGood_of_codeGuardQE hg (IntNumeric.valsOnly_bindVals _) hq he hu)

set_option maxRecDepth 100000 in
/-- **No `VUNOP` is a typed `val`.** -/
theorem not_typedV_val_vunop (p : Value) :
    ¬ TypedV (simEnv B) (.varT "val" []) (.case "VUNOP" p) := fun h => by
  obtain ⟨op, w, hc, hf⟩ := IntNumeric.val_tag ConfigOk.valsOnly_empty (h _ ConfigOk.valsOnly_empty)
  obtain ⟨rfl, rfl⟩ := Value.case.inj hc
  exact hf rfl

/-- **The image of `f32x4.sqrt` is not `LastGood`** at `VUNOP`, in any `simEnv B`. -/
theorem not_lastGood_f32x4Sqrt : ¬ LastGood B "VUNOP" (instrToV SimdTy.f32x4Sqrt) := by
  rw [SimdTy.instrToV_f32x4Sqrt]
  rintro (h | h | h)
  · exact h _ rfl
  · exact SimdTy.not_typedV_f32x4Sqrt (SimdTy.instrToV_f32x4Sqrt ▸ h)
  · exact not_typedV_val_vunop _ h

/-- **SpecTec does not step from a configuration whose last instruction is `f32x4.sqrt`.** -/
theorem not_sstep_of_last_f32x4Sqrt {hn : H → String} {c : Config H}
    (hu : c.code.getLast? = some (.plain SimdTy.f32x4Sqrt)) (w : Value) :
    ¬ SStep (simEnv B) (configV hn c) w := by
  have hv : (adminsToV c.code).getLast? = some (instrToV SimdTy.f32x4Sqrt) := by
    rw [adminsToV_eq_map, List.getLast?_map, hu]
    rfl
  exact not_sstep_of_last hv not_lastGood_f32x4Sqrt w

/-! ## The witness -/

/-- `v128.const 0; f32x4.sqrt` on the empty store, in a frame over the empty module. -/
def sqrtCfg : Config H := ⟨{}, ⟨[], {}⟩, [vconst 0, .plain SimdTy.f32x4Sqrt]⟩

/-- `v128.const r` on the same state. -/
def sqrtDoneCfg (r : BitVec 128) : Config H := ⟨{}, ⟨[], {}⟩, [vconst r]⟩

/-- **The witness is valid**: `⊢ sqrtCfg : v128`. -/
theorem configOk_sqrtCfg : ConfigOk (sqrtCfg (H := H)) [.vec .v128] :=
  ⟨_, ⟨ConfigOk.coreStoreOk_empty, _, [], ConfigOk.moduleInstOk_empty _, .nil, rfl⟩,
    .cons (.plain (.vector (.vecConst _))) (by simp)
      (.single (.plain (.vector (.vecFloatUnOp _ _))))⟩

/-- The empty store and module are bounded. -/
theorem bounded_empty {code : List Admin} (hc : Round4.AdminsBnd code) :
    Round4.Bounded (⟨{}, ⟨[], {}⟩, code⟩ : Config H) :=
  ⟨Integrate.storeOk_empty, ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩,
    ⟨by simp, by simp⟩, hc⟩

/-- The empty store and module export nothing. -/
theorem noExports_empty {code : List Admin} (hc : Pos.AdminsNE code) :
    Pos.NoExports (⟨{}, ⟨[], {}⟩, code⟩ : Config H) :=
  ⟨by simp [Pos.StoreNE], rfl, hc⟩

/-- **The witness is bounded and export-free.** -/
theorem boundedNE_sqrtCfg : Pos.BoundedNE (sqrtCfg (H := H)) :=
  ⟨bounded_empty (by simp [Round4.AdminsBnd, Round4.AdminBnd, Round4.instrBnd]),
    noExports_empty (by simp [Pos.AdminsNE, Pos.AdminNE])⟩

/-- **Its successor is bounded and export-free.** -/
theorem boundedNE_sqrtDoneCfg (r : BitVec 128) : Pos.BoundedNE (sqrtDoneCfg (H := H) r) :=
  ⟨bounded_empty (by simp [Round4.AdminsBnd, Round4.AdminBnd, Round4.instrBnd]),
    noExports_empty (by simp [Pos.AdminsNE, Pos.AdminNE])⟩

/-- **Core steps from the witness**, under every profile and host. -/
theorem step_sqrtCfg (P : Profile) (host : HostSemantics H) :
    ∃ r, Step P host (sqrtCfg (H := H)) (sqrtDoneCfg r) := by
  obtain ⟨r, hr⟩ := VecFloatUnOpRel_nonempty P FloatShape.f32x4 FloatUnOp.sqrt 0
  exact ⟨r, .vector (.vecFloatUnOp hr)⟩

/-- **SpecTec does not step from the image of the witness**, in any `simEnv B`. -/
theorem not_sstep_sqrtCfg (hn : H → String) (w : Value) :
    ¬ SStep (simEnv B) (configV hn (sqrtCfg (H := H))) w :=
  not_sstep_of_last_f32x4Sqrt rfl w

/-- **The forward one-step simulation of `Round5.Task.wholeStepValidOk` fails at `sqrtCfg`**,
for every `B`, encoding, profile and host. -/
theorem not_forwardOk_sqrtCfg (B : Builtins) (P : Profile) (host : HostSemantics H)
    (hn : H → String) :
    ¬ ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Pos.BoundedNE c →
      Pos.BoundedNE c' → Step P host c c' →
      ∃ d', Bwd.ConfigEq c' d' ∧ SStep (simEnv B) (configV hn c) (configV hn d') := fun h => by
  obtain ⟨r, hs⟩ := step_sqrtCfg (H := H) P host
  obtain ⟨d', -, hd⟩ := h sqrtCfg (sqrtDoneCfg r) _ configOk_sqrtCfg boundedNE_sqrtCfg
    (boundedNE_sqrtDoneCfg r) hs
  exact not_sstep_sqrtCfg hn _ hd

/-- **`Round5.Task.wholeStepValidOk` is false.** -/
theorem not_wholeStepValidOk : ¬ Round5.Task.wholeStepValidOk := fun h => by
  obtain ⟨B, hf, -⟩ := h Unit Pos.hnU Pos.hnU_injective Pos.divHost Pos.hostFinite_divHost
    Pos.hostOk_divHost false {}
  exact not_forwardOk_sqrtCfg B _ Pos.divHost Pos.hnU hf

end Silmaril.Wasm.SpecTec.Sim.Round5.Target
