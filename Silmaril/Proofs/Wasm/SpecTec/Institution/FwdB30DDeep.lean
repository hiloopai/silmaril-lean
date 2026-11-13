module

public import Silmaril.Wasm.SpecTec.Institution.FwdB30D.Defs
public import Silmaril.Wasm.SpecTec.Institution.FwdB30S.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms

/-!
# `CfgRel` at a deeply rigid code is equality

`Bwd.AdminEq` relates two different instructions only at a `CALL_REF`, or at a label, handler
or frame whose bodies it relates. So an instruction with no `CALL_REF` at the top of itself or of
any label, handler or frame body it contains (`deepRigid`) is related only to itself. This
extends `FwdB30S.cfgRel_exact` from codes with no label, handler or frame at the top to codes
with any nesting of them.

* `adminEq_deep`, `codeEq_deep`: `AdminEq` and `CodeEq` from a deeply rigid code are equality.
* `cfgRel_exact_deep`: **`CfgRel` from the image of a configuration with deeply rigid code is
  equality.**
* `exact_of_cfgRel_deep`: existence up to `CfgRel` at a deeply rigid successor is existence at
  its image.
* `deepRigidL_append`, `deepRigidL_vals`, `deepRigidL_expression`, `deepRigidL_throwing`: the
  shapes of the successors.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30D

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim

variable {H : Type}

@[simp] theorem deepRigid_label (n : Nat) (cont : List Instr) (is : List Admin) :
    deepRigid (.label n cont is) = deepRigidL is := by
  simp only [deepRigid]

@[simp] theorem deepRigid_handler (n : Nat) (cs : List Catch) (is : List Admin) :
    deepRigid (.handler n cs is) = deepRigidL is := by
  simp only [deepRigid]

@[simp] theorem deepRigid_frame (n : Nat) (f : Frame) (is : List Admin) :
    deepRigid (.frame n f is) = deepRigidL is := by
  simp only [deepRigid]

@[simp] theorem deepRigidL_nil : deepRigidL [] = true := by
  simp only [deepRigidL]

@[simp] theorem deepRigidL_cons (a : Admin) (l : List Admin) :
    deepRigidL (a :: l) = (deepRigid a && deepRigidL l) := by
  simp only [deepRigidL]

/-- `deepRigidL` is `deepRigid` of every element. -/
theorem deepRigidL_eq_all : ∀ l : List Admin, deepRigidL l = l.all deepRigid
  | [] => by simp
  | a :: l => by simp [deepRigidL_eq_all l]

theorem deepRigidL_append (l m : List Admin) :
    deepRigidL (l ++ m) = (deepRigidL l && deepRigidL m) := by
  simp [deepRigidL_eq_all]

/-- A `CALL_REF` is not deeply rigid. -/
theorem not_deepRigid_callRef {a : Admin} (h : a.IsCallRef) : deepRigid a = false := by
  rcases Bwd.isCallRef_cases h with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> rfl

/-- The image of a `CALL_REF` is headed `CALL_REF`. -/
theorem callRef_img {a a₀ : Admin} (ha : a.IsCallRef) (he : adminToV a₀ = adminToV a) :
    a₀.IsCallRef := by
  rcases Bwd.isCallRef_cases ha with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · exact Typing.head_callRef (Typing.adminToV_case (op := "CALL_REF") he).symm
  · exact Typing.head_callRef (Typing.adminToV_case (op := "CALL_REF") he).symm

mutual
/-- **`AdminEq` from an instruction whose image is that of a deeply rigid one keeps the
image.** -/
theorem adminEq_img : ∀ {a b : Admin}, Bwd.AdminEq a b → ∀ {a₀ : Admin},
    adminToV a₀ = adminToV a → deepRigid a₀ = true → adminToV b = adminToV a
  | _, _, .refl _, _, _, _ => rfl
  | _, _, .call ha _, _, he, hr =>
    absurd hr (by rw [not_deepRigid_callRef (callRef_img ha he)]; decide)
  | _, _, .label hc, a₀, he, hr => by
    obtain ⟨n₀, c₀, b₀, rfl⟩ :=
      Typing.head_label (Typing.adminToV_case (op := "LABEL_%{%}%") he).symm
    simp only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq] at he
    simp only [adminToV, codeEq_img hc he.2.2.2.1 (by simpa using hr)]
  | _, _, .handler hc, a₀, he, hr => by
    obtain ⟨n₀, c₀, b₀, rfl⟩ :=
      Typing.head_handler (Typing.adminToV_case (op := "HANDLER_%{%}%") he).symm
    simp only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq] at he
    simp only [adminToV, codeEq_img hc he.2.2.2.1 (by simpa using hr)]
  | _, _, .frame hc, a₀, he, hr => by
    obtain ⟨n₀, c₀, b₀, rfl⟩ :=
      Typing.head_frame (Typing.adminToV_case (op := "FRAME_%{%}%") he).symm
    simp only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq] at he
    simp only [adminToV, codeEq_img hc he.2.2.2.1 (by simpa using hr)]

/-- **`CodeEq` from a code whose image is that of a deeply rigid code keeps the image.** -/
theorem codeEq_img : ∀ {l l' : List Admin}, Bwd.CodeEq l l' → ∀ {l₀ : List Admin},
    adminsToV l₀ = adminsToV l → deepRigidL l₀ = true → adminsToV l' = adminsToV l
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons hab hrest, l₀, he, hr => by
    cases l₀ with
    | nil => simp [adminsToV] at he
    | cons a₀ l₀ =>
      simp only [adminsToV, List.cons.injEq] at he ⊢
      simp only [deepRigidL_cons, Bool.and_eq_true] at hr
      exact ⟨adminEq_img hab he.1 hr.1, codeEq_img hrest he.2 hr.2⟩
end

/-- **`CfgRel` from the image of a configuration with deeply rigid code is equality.** -/
theorem cfgRel_exact_deep {hn : H → String} {c : Config H} {w : Value}
    (hrel : SpecTec.CfgRel hn (configV hn c) w) (hr : deepRigidL c.code = true) :
    w = configV hn c := by
  obtain ⟨c₁, d, ⟨hs, hf, hce⟩, h₁, rfl⟩ := hrel
  rw [Bwd.configV_eq, Bwd.configV_eq] at h₁
  obtain ⟨hz, hl⟩ := Bwd.cfgV_inj h₁
  have hd : adminsToV d.code = adminsToV c₁.code := codeEq_img hce hl hr
  rw [Bwd.configV_eq, Bwd.configV_eq, ← hs, ← hf, hd, ← hz, ← hl]

/-- **Existence up to `CfgRel` at a deeply rigid successor is existence at its image.** -/
theorem exact_of_cfgRel_deep {hn : H → String} {s : Store H} {f : Frame} {is' : List Admin}
    {Q : List Value → Prop}
    (h : ∃ js, Q js ∧ SpecTec.CfgRel hn (configV hn ⟨s, f, is'⟩) (cfgV (stateV hn s f) js))
    (hr : deepRigidL is' = true) : Q (adminsToV is') := by
  obtain ⟨js, hq, hrel⟩ := h
  have e := cfgRel_exact_deep hrel hr
  rw [Bwd.configV_eq] at e
  exact (Bwd.cfgV_inj e).2 ▸ hq

/-- **A fact up to `CfgRel` at a deeply rigid successor is at its image.** -/
theorem eq_of_cfgRel_deep {hn : H → String} {s : Store H} {f : Frame} {is' : List Admin}
    {js : List Value}
    (hrel : SpecTec.CfgRel hn (configV hn ⟨s, f, is'⟩) (cfgV (stateV hn s f) js))
    (hr : deepRigidL is' = true) : js = adminsToV is' := by
  have e := cfgRel_exact_deep hrel hr
  rw [Bwd.configV_eq] at e
  exact (Bwd.cfgV_inj e).2

/-! ## The shapes of the successors -/

/-- A value is deeply rigid. -/
theorem deepRigid_val (v : Val) : deepRigid v.toAdmin = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

theorem deepRigidL_vals (vs : List Val) : deepRigidL (vals vs) = true := by
  simp [deepRigidL_eq_all, vals, deepRigid_val]

/-- A block body is deeply rigid exactly when it has no `call_ref` at the top. -/
theorem deepRigidL_expression (body : List Instr) :
    deepRigidL (expression body) = callFree body := by
  simp [deepRigidL_eq_all, expression, callFree, List.all_map, Function.comp_def]

/-- `callFree` says that no instruction is a `call_ref`. -/
theorem callFree_iff (body : List Instr) : callFree body = true ↔ ∀ y, Instr.callRef y ∉ body := by
  simp only [callFree, List.all_eq_true]
  constructor
  · intro h y hy
    exact absurd (h _ hy) (by simp [deepRigid])
  · intro h i hi
    cases i <;> first | rfl | exact absurd hi (h _)

end Silmaril.Wasm.SpecTec.Institution.FwdB30D
