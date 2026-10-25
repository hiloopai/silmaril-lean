module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Soundness.PureRedex

@[expose] public section

/-! # Soundness, numeric family

Preservation of `NumericStep` (a pure family: store and frame unchanged) and
progress for `NumericInstrOk`.

Statement change (progress): the constant instructions `CONST nt c` are typed by
`NumericInstrOk` but are values, not redexes, so they do not reduce. Progress
therefore assumes the instruction is not a value (`(Admin.plain i).val? = none`).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- Inversion to the family, the principal type split, and the reduct typing. -/
local macro "numeric_base" : tactic => `(tactic| (
  intro C A' tvs it xs₂ B hi hp hf D
  cases hi <;> rename_i hi <;> cases hi
  obtain ⟨e1, e2⟩ := params_split hp (by simp [← hf.length_eq])
  subst e1 e2
  first
    | exact AdminsOk.val_cons (.num _) D
    | exact AdminsOk.val_cons (w := .num ⟨.int _, _⟩) (.num _) D
    | exact AdminsOk.val_cons (w := .num ⟨.float _, _⟩) (.num _) D
    | exact AdminsOk.trap_cons (ResultOk.nil' _) (ResultOk.num1 _ _) D))

local macro "numeric_len" : tactic => `(tactic| (
  intro C it hi
  cases hi <;> rename_i hi <;> cases hi <;> simp))

/-- **Preservation (numeric).** A pure redex and its reduct have the same type. -/
theorem NumericStep.preservation {P : Profile} {s : Store H} {f : Frame} {C : Context}
    {is is' : List Admin} {it : InstrType} (_hst : StateOk s f C)
    (hty : AdminsOk s C is it) (h : NumericStep P is is') : AdminsOk s C is' it := by
  cases h with
  | @intUnOp t op x =>
    exact AdminsOk.pure_redex (vs := [.num ⟨.int t, x⟩]) (i := .intUnOp t op)
      (by numeric_len) (by numeric_base) hty
  | @floatUnOp t op x z _ =>
    exact AdminsOk.pure_redex (vs := [.num ⟨.float t, x⟩]) (i := .floatUnOp t op)
      (by numeric_len) (by numeric_base) hty
  | @intBinOp t op x y z _ =>
    exact AdminsOk.pure_redex (vs := [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩]) (i := .intBinOp t op)
      (by numeric_len) (by numeric_base) hty
  | @intBinOpTrap t op x y _ _ =>
    exact AdminsOk.pure_redex (vs := [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩]) (i := .intBinOp t op)
      (by numeric_len) (by numeric_base) hty
  | @floatBinOp t op x y z _ =>
    exact AdminsOk.pure_redex (vs := [.num ⟨.float t, x⟩, .num ⟨.float t, y⟩])
      (i := .floatBinOp t op) (by numeric_len) (by numeric_base) hty
  | @intTestOp t op x =>
    exact AdminsOk.pure_redex (vs := [.num ⟨.int t, x⟩]) (i := .intTestOp t op)
      (by numeric_len) (by numeric_base) hty
  | @intRelOp t op x y =>
    exact AdminsOk.pure_redex (vs := [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩]) (i := .intRelOp t op)
      (by numeric_len) (by numeric_base) hty
  | @floatRelOp t op x y =>
    exact AdminsOk.pure_redex (vs := [.num ⟨.float t, x⟩, .num ⟨.float t, y⟩])
      (i := .floatRelOp t op) (by numeric_len) (by numeric_base) hty
  | @convert op x z _ =>
    exact AdminsOk.pure_redex (vs := [.num ⟨op.source, x⟩]) (i := .convert op)
      (by numeric_len) (by numeric_base) hty
  | @convertTrap op x e _ =>
    exact AdminsOk.pure_redex (vs := [.num ⟨op.source, x⟩]) (i := .convert op)
      (by numeric_len) (by numeric_base) hty

/-- **Progress (numeric).** A well-typed instruction of this family, applied to
operands of its parameter types, reduces. The constants are values (see the
module doc for the added premise `hnv`). -/
theorem NumericInstrOk.progress {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {C : Context} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat} {vs : List Val}
    (_hst : StateOk s f C) (hi : NumericInstrOk C i ⟨t₁, xs, t₂⟩)
    (hvs : List.Forall₂ (ValOk s) vs t₁) (hnv : (Admin.plain i).val? = none) :
    ∃ c', Step P host ⟨s, f, vals vs ++ [.plain i]⟩ c' := by
  cases hi with
  | intConst => simp [Admin.val?] at hnv
  | floatConst => simp [Admin.val?] at hnv
  | intUnOp _ =>
    rcases hvs with _ | ⟨h1, _ | _⟩
    obtain ⟨x, rfl⟩ := ValOk.num_inv h1
    exact ⟨_, .numeric .intUnOp⟩
  | floatUnOp t op =>
    rcases hvs with _ | ⟨h1, _ | _⟩
    obtain ⟨x, rfl⟩ := ValOk.num_inv h1
    obtain ⟨z, hz⟩ := floatUnOpP_nonempty P t op x
    exact ⟨_, .numeric (.floatUnOp hz)⟩
  | intBinOp t op =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨x, rfl⟩ := ValOk.num_inv h1
    obtain ⟨y, rfl⟩ := ValOk.num_inv h2
    cases hr : intBinOp t op x y with
    | ok z => exact ⟨_, .numeric (.intBinOp hr)⟩
    | error e => exact ⟨_, .numeric (.intBinOpTrap hr)⟩
  | floatBinOp t op =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨x, rfl⟩ := ValOk.num_inv h1
    obtain ⟨y, rfl⟩ := ValOk.num_inv h2
    obtain ⟨z, hz⟩ := floatBinOpP_nonempty P t op x y
    exact ⟨_, .numeric (.floatBinOp hz)⟩
  | intTestOp t op =>
    rcases hvs with _ | ⟨h1, _ | _⟩
    obtain ⟨x, rfl⟩ := ValOk.num_inv h1
    exact ⟨_, .numeric .intTestOp⟩
  | intRelOp t op =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨x, rfl⟩ := ValOk.num_inv h1
    obtain ⟨y, rfl⟩ := ValOk.num_inv h2
    exact ⟨_, .numeric .intRelOp⟩
  | floatRelOp t op =>
    rcases hvs with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
    obtain ⟨x, rfl⟩ := ValOk.num_inv h1
    obtain ⟨y, rfl⟩ := ValOk.num_inv h2
    exact ⟨_, .numeric .floatRelOp⟩
  | convert op =>
    rcases hvs with _ | ⟨h1, _ | _⟩
    obtain ⟨x, rfl⟩ := ValOk.num_inv h1
    obtain ⟨r, hr⟩ := convertP_nonempty P op x
    cases r with
    | ok z => exact ⟨_, .numeric (.convert hr)⟩
    | error e => exact ⟨_, .numeric (.convertTrap hr)⟩

end Silmaril.Wasm.Execution.Core
