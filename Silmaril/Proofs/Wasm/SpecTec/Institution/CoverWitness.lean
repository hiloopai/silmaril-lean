module

public import Silmaril.Wasm.SpecTec.Institution.Cover.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Cover
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInitLoops

/-!
# Choice cover on round 6's domain: a point of `Dom \ DomDet`

`nanCfg` is `f32.const nan; f64.promote_f32` on the empty store. It is valid, `BoundedSel`, and
every Core successor is `BoundedSel`, so it is in `Dom` (`dom_nanCfg`). Under the spec NaN
profile Core promotes the NaN to the canonical `f64` NaN of either sign (`step_nanCfg`), so it is
not in `DomDet` (`not_domDet_nanCfg`).

The successor clause of `Dom` is proved for the host-free semantics `Det.noHost`, through
Silmaril's decomposition `Step.head_inv`: every successor is the result of a scalar numeric
step at `cvtop`, a constant or `trap` (`head_convert`, `numericStep_result`). At `H := Empty`
the host-free semantics is finite and `HostOk`, so the witness meets every hypothesis of
`Nondet.Task.choiceCover` (`nonvacuous`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Cover

open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Wasm30
open Silmaril.Wasm.SpecTec.Institution.Nondet
open Silmaril.Wasm.SingleThreaded.Det (noHost)

variable {H : Type}

/-- Both canonical `f64` NaNs are allowed results of promoting the canonical `f32` NaN under a
spec NaN profile. -/
theorem promote_nan (P : Profile) (hP : P.nan = .spec) (neg : Bool) :
    convertP P .promote nanF32 (.ok (nanF64 neg)) := by
  simp only [convertP, hP]
  cases neg <;> simp only [convertRel, nanF32, nanF64, Bool.false_eq_true, ↓reduceIte] <;> decide

/-- **Core steps from the witness to both NaNs** under the spec NaN profile, at every host. -/
theorem step_nanCfg (nd : Bool) (r : RelaxedChoice) (host : HostSemantics H) (neg : Bool) :
    Step (Profile.spec nd r) host nanCfg (nanDone neg) :=
  .numeric (.convert (op := .promote) (promote_nan _ rfl neg))

/-- **The two successors differ.** -/
theorem nanDone_ne : (nanDone false : Config H) ≠ nanDone true := by
  intro h
  simp [nanDone, nanF64, Val.toAdmin] at h
  injection h with _ h₂
  exact absurd h₂ (by decide)

/-- **The witness is valid**: `⊢ nanCfg : f64`. -/
theorem configOk_nanCfg : ConfigOk (nanCfg (H := H)) [.num (.float .f64)] :=
  ⟨_, ⟨ConfigOk.coreStoreOk_empty, _, [], ConfigOk.moduleInstOk_empty _, .nil, rfl⟩,
    .cons (.plain (.numeric (.floatConst _ _))) (by simp)
      (.single (.plain (.numeric (.convert _))))⟩

/-- **The witness is bounded, export-free and free of `FloatMissel` code.** -/
theorem boundedSel_nanCfg : Round5.Target.BoundedSel (nanCfg (H := H)) :=
  ⟨⟨Round5.Target.bounded_empty
        (by simp [Round4.AdminsBnd, Round4.AdminBnd, Round4.instrBnd, Val.toAdmin]),
      Round5.Target.noExports_empty
        (by simp [Round5.Pos.AdminsNE, Round5.Pos.AdminNE, Val.toAdmin])⟩,
    ⟨by simp [nanCfg, Round5.Target.StoreSel], by
      simp [nanCfg, Round5.Target.AdminsSel, Round5.Target.AdminSel, Round5.Target.instrSel,
        Round5.SimdTy.FloatMissel, Val.toAdmin]⟩⟩

open Silmaril.Wasm.SingleThreaded.Det (FamShape) in
/-- A family left-hand side ending in `cvtop` is numeric. -/
theorem famShape_convert {k : Silmaril.Wasm.SingleThreaded.Det.Fam} {args : List Val}
    {op : ConvertOp} (h : FamShape k (vals args ++ [.plain (.convert op)])) : k = .numeric := by
  obtain ⟨a', e', he, -, hk⟩ := h
  obtain rfl := List.singleton_inj.1 (List.append_inj' he rfl).2
  exact hk.symm

open Silmaril.Wasm.SingleThreaded.Det in
/-- **A head step at `cvtop` is a numeric step.** -/
theorem head_convert {P : Profile} {s : Store H} {f : Frame} {args : List Val} {op : ConvertOp}
    {c₀ : Config H} (h : Head P s f args (.plain (.convert op)) c₀) :
    c₀.store = s ∧ c₀.frame = f ∧ NumericStep P (vals args ++ [.plain (.convert op)]) c₀.code := by
  cases h with
  | numeric h => exact ⟨rfl, rfl, h⟩
  | parametric h => exact absurd (famShape_convert (ParametricStep.shape h)) (by decide)
  | vector h => exact absurd (famShape_convert (VectorStep.shape h)) (by decide)
  | «variable» h => exact absurd (famShape_convert (VariableStep.shape h)) (by decide)
  | table h => exact absurd (famShape_convert (TableStep.shape h)) (by decide)
  | memory h => exact absurd (famShape_convert (MemoryStep.shape h)) (by decide)
  | reference h => exact absurd (famShape_convert (RefStep.shape h)) (by decide)
  | aggregate h => exact absurd (famShape_convert (AggregateStep.shape h)) (by decide)
  | callRefNull hc => exact hc.elim
  | callRefFunc _ hc => exact hc.elim

/-- `BoundedSel` on the empty store and frame, from the code alone. -/
theorem boundedSel_empty {code : List Admin} (h₁ : Round4.AdminsBnd code)
    (h₂ : Round5.Pos.AdminsNE code) (h₃ : Round5.Target.AdminsSel code) :
    Round5.Target.BoundedSel (⟨{}, ⟨[], {}⟩, code⟩ : Config H) :=
  ⟨⟨Round5.Target.bounded_empty h₁, Round5.Target.noExports_empty h₂⟩,
    ⟨by simp [Round5.Target.StoreSel], h₃⟩⟩

/-- A numeric constant is bounded, export-free and free of `FloatMissel` code. -/
theorem num_result (v : NumVal) :
    Round4.AdminsBnd [(Val.num v).toAdmin] ∧ Round5.Pos.AdminsNE [(Val.num v).toAdmin] ∧
      Round5.Target.AdminsSel [(Val.num v).toAdmin] := by
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩ <;>
    simp [Round4.AdminsBnd, Round4.AdminBnd, Round4.instrBnd, Round5.Pos.AdminsNE,
      Round5.Pos.AdminNE, Round5.Target.AdminsSel, Round5.Target.AdminSel,
      Round5.Target.instrSel, Round5.SimdTy.FloatMissel, Val.toAdmin]

/-- A scalar numeric left-hand side has an operand and an operator at least. -/
theorem numericStep_len {P : Profile} {l l' : List Admin} (h : NumericStep P l l') :
    2 ≤ l.length := by
  cases h <;> simp

set_option linter.unusedSimpArgs false in
/-- **The result of a scalar numeric step** is bounded, export-free and free of `FloatMissel`
code: one constant, or `trap`. -/
theorem numericStep_result {P : Profile} {l l' : List Admin} (h : NumericStep P l l') :
    Round4.AdminsBnd l' ∧ Round5.Pos.AdminsNE l' ∧ Round5.Target.AdminsSel l' := by
  cases h <;> first
    | exact num_result _
    | simp [Round4.AdminsBnd, Round4.AdminBnd, Round4.instrBnd, Round5.Pos.AdminsNE,
        Round5.Pos.AdminNE, Round5.Target.AdminsSel, Round5.Target.AdminSel,
        Round5.Target.instrSel, Round5.SimdTy.FloatMissel, constI32, Val.i32, Val.toAdmin]

/-- **Every successor of the witness is `BoundedSel`** (host-free: `Step.head_inv`). -/
theorem succ_boundedSel_nanCfg {P : Profile} {c₁ : Config H}
    (h : Step P noHost (nanCfg (H := H)) c₁) : Round5.Target.BoundedSel c₁ := by
  have h' : Step P noHost ⟨{}, ⟨[], {}⟩,
      vals [Val.num ⟨.float .f32, nanF32⟩] ++ Admin.plain (.convert .promote) :: []⟩ c₁ := h
  obtain ⟨pre, args, c₀, hw, hh, rfl⟩ := Step.head_inv h' rfl (by simp) (by simp)
  obtain ⟨hs, hf, hn⟩ := head_convert hh
  obtain ⟨h₁, h₂, h₃⟩ := numericStep_result hn
  rcases c₀ with ⟨s₀, f₀, code₀⟩
  simp only at hs hf h₁ h₂ h₃ hn ⊢
  subst hs hf
  rcases List.append_eq_singleton_iff.1 hw.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa using boundedSel_empty h₁ h₂ h₃
  · exact absurd (numericStep_len hn) (by simp)

/-! ## The witness is in `Dom \ DomDet` -/

/-- **The witness is 's domain**, host-free. -/
theorem dom_nanCfg (nd : Bool) (r : RelaxedChoice) :
    Dom (Profile.spec nd r) (noHost (H := H)) nanCfg :=
  ⟨⟨_, configOk_nanCfg⟩, boundedSel_nanCfg, fun _ h => succ_boundedSel_nanCfg h⟩

/-- **Core has two successors at the witness.** -/
theorem not_stepDet_nanCfg (nd : Bool) (r : RelaxedChoice) :
    ¬ StepDet (Profile.spec nd r) (noHost (H := H)) nanCfg := fun h =>
  nanDone_ne (h _ _ (step_nanCfg nd r _ false) (step_nanCfg nd r _ true))

/-- **The witness is not in `DomDet`.** -/
theorem not_domDet_nanCfg (nd : Bool) (r : RelaxedChoice) :
    ¬ DomDet (Profile.spec nd r) (noHost (H := H)) nanCfg := fun h =>
  not_stepDet_nanCfg nd r h.2

/-- The host-free semantics is finite. -/
theorem hostFinite_noHost : HostFinite (noHost : HostSemantics H) :=
  fun _ _ _ => ⟨[], fun _ => by simp⟩

/-- Over the empty host type the host-free semantics is `HostOk`. -/
theorem hostOk_noHost_empty : HostOk (noHost : HostSemantics Empty) :=
  fun _ _ h => h.elim

/-- **The off-`DomDet` statements are not vacuous**: at `H := Empty`, with the host-free
semantics (finite, `HostOk`, injective encoding), the witness is in `Dom \ DomDet`, its two
Core successors differ, and each is, up to `ConfigEq`, a step fact of `stepModel BI`
(`fwd_exact`). -/
theorem nonvacuous (nd : Bool) (r : RelaxedChoice) :
    Dom (Profile.spec nd r) (noHost (H := Empty)) nanCfg ∧
      ¬ DomDet (Profile.spec nd r) (noHost (H := Empty)) nanCfg ∧
      nanDone (H := Empty) false ≠ nanDone true ∧
      ∀ neg, Step (Profile.spec nd r) (noHost (H := Empty)) nanCfg (nanDone neg) ∧
        ∃ d', Bwd.ConfigEq (nanDone neg) d' ∧
          MStep (Round4Int.BI (Profile.spec nd r) Empty.elim noHost)
            (configV Empty.elim nanCfg) (configV Empty.elim d') :=
  ⟨dom_nanCfg nd r, not_domDet_nanCfg nd r, nanDone_ne, fun neg =>
    ⟨step_nanCfg nd r _ neg, fwd_exact (fun a => a.elim) hostFinite_noHost hostOk_noHost_empty
      (dom_nanCfg nd r) (step_nanCfg nd r _ neg)⟩⟩

end Silmaril.Wasm.SpecTec.Institution.Cover
