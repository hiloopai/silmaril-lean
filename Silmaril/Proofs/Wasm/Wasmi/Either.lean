module

public import Silmaril.Wasm.Atlas.Variant.Thms
public import Silmaril.Wasm.Wasmi.Defs

@[expose] public section

/-!
# `selectEither` selects either operand

With two values below the pattern `i32.const 0; local.get x; i32.ne; select t`, the loose
model reaches either value in three steps (`selectEither b`, `drop`, then `select-true` or
`select-false` on the constant). New proof.
-/

namespace Silmaril.Proofs.Wasm.Wasmi

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Wasmi Silmaril.Wasm.Atlas.Variant

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The constant selected by `selectEither b`. -/
theorem select_const (b : Bool) (v₁ v₂ : Val) (t : Option (List ValType)) (s : Store H)
    (f : Frame) :
    Execution.Core.Step P host
      ⟨s, f, [v₁.toAdmin, v₂.toAdmin, .plain (.intConst .i32 (if b then 1 else 0)),
        .plain (.select t)]⟩ ⟨s, f, [(if b then v₁ else v₂).toAdmin]⟩ := by
  cases b with
  | true => exact .parametric (ParametricStep.selectTrue (c := 1) (by decide))
  | false => exact .parametric (ParametricStep.selectFalse v₁ v₂ t)

/-- **Either operand**: from `v₁ v₂ (i32.const 0) (local.get x) i32.ne select`, the loose model
reaches `v₁` (`b = true`) and `v₂` (`b = false`). -/
theorem select_either (b : Bool) {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    {t : Option (List ValType)} (hv : f.local? x = some (some v)) (v₁ v₂ : Val) :
    Relation.ReflTransGen (Loose.Step P host)
      ⟨s, f, vals [v₁, v₂] ++ expression (zeroTestSel x t)⟩
      ⟨s, f, vals [if b then v₁ else v₂]⟩ := by
  have hq : Ctx Loose.Quirk ⟨s, f, vals [v₁, v₂] ++ expression (zeroTestSel x t) ++ []⟩
      ⟨s, f, vals [v₁, v₂] ++ [v.toAdmin, .plain .drop,
        .plain (.intConst .i32 (if b then 1 else 0)), .plain (.select t)] ++ []⟩ :=
    Ctx.instrs (Ctx.base (Loose.Quirk.selectEither b hv))
  have hd : Execution.Core.Step P host
      ⟨s, f, vals [v₁, v₂] ++ [v.toAdmin, .plain .drop] ++
        [.plain (.intConst .i32 (if b then 1 else 0)), .plain (.select t)]⟩
      ⟨s, f, vals [v₁, v₂] ++ [] ++
        [.plain (.intConst .i32 (if b then 1 else 0)), .plain (.select t)]⟩ :=
    .ctxtInstrs (.parametric (ParametricStep.drop v)) (Or.inl (by simp))
  have h₁ : Loose.Step P host ⟨s, f, vals [v₁, v₂] ++ expression (zeroTestSel x t)⟩
      ⟨s, f, vals [v₁, v₂] ++ [v.toAdmin, .plain .drop,
        .plain (.intConst .i32 (if b then 1 else 0)), .plain (.select t)]⟩ :=
    Or.inr (by simpa using hq)
  have h₂ : Loose.Step P host ⟨s, f, vals [v₁, v₂] ++ [v.toAdmin, .plain .drop,
        .plain (.intConst .i32 (if b then 1 else 0)), .plain (.select t)]⟩
      ⟨s, f, [v₁.toAdmin, v₂.toAdmin, .plain (.intConst .i32 (if b then 1 else 0)),
        .plain (.select t)]⟩ :=
    Or.inl (by simpa [vals] using hd)
  have h₃ : Loose.Step P host ⟨s, f, [v₁.toAdmin, v₂.toAdmin,
        .plain (.intConst .i32 (if b then 1 else 0)), .plain (.select t)]⟩
      ⟨s, f, vals [if b then v₁ else v₂]⟩ :=
    Or.inl (select_const b v₁ v₂ t s f)
  exact ((Relation.ReflTransGen.single h₁).tail h₂).tail h₃

end Silmaril.Proofs.Wasm.Wasmi
