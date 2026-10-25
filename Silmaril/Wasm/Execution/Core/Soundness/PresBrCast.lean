module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Soundness.RedexTyping
public import Silmaril.Wasm.Execution.Core.Soundness.RefTyping
public import Silmaril.Wasm.Execution.Core.Soundness.StateFacts
public import Silmaril.Wasm.Validation.Subtyping.Properties

@[expose] public section

/-! # Preservation for the cast-branch rules of `Step`

`AdminsOk`-level replacement lemmas for `br_on_cast` / `br_on_cast_fail`
(`Step_read/br_on_cast-succeed|fail`, `Step_read/br_on_cast_fail-succeed|fail`).

The two rules that keep the operand at the type `diffrt rt₁ rt₂` need that the
null reference inhabits `closeRef rt₂` whenever it is nullable; this requires the
context's defined types to be valid in the empty context (`hT`), which follows
from `FrameOk` (`FrameOk.typesOkEmptyCast`).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

theorem Context.closeRef_eq_instRefCast {C : Context} {f : Frame} (ht : C.types = f.module.types)
    (rt : RefType) : C.closeRef rt = f.module.instRef rt := by
  simp [Context.closeRef, ModuleInst.instRef, ht]

theorem FrameOk.typesOkEmptyCast {s : Store H} {f : Frame} {C : Context} (hf : FrameOk s f C) :
    ∀ d ∈ C.types, TyOk {} d := by
  intro d hd
  obtain ⟨C₀, hm, -⟩ := hf.inv
  obtain ⟨-, hok, -⟩ := hm.inv
  rw [hf.types_eq] at hd
  exact hok d hd

/-- A closed reference type valid in `C` is valid in the empty context, when all of
`C`'s defined types are. -/
theorem closeRef_okEmptyCast {C : Context} (hT : ∀ d ∈ C.types, TyOk {} d) {rt : RefType}
    (h : TyOk C.toTypeCtx (C.closeRef rt)) : TyOk {} (C.closeRef rt) := by
  obtain ⟨n, hp⟩ := rt
  cases hp with
  | abstract a =>
    simp only [Context.closeRef, liftRef, liftHeap, Ty.substAll, Ty.subst]
    exact .ref (.abs a)
  | typeIdx x =>
    simp only [Context.closeRef, liftRef, liftHeap, liftTypeIdx, Ty.substAll, Ty.subst,
      Subst.all] at h ⊢
    cases hx : C.types[x.toNat]? with
    | none =>
      simp only [List.getElem?_map, hx, Option.map_none, Option.getD_none] at h ⊢
      cases h with
      | ref hh => cases hh with
        | use hu => cases hu with
          | idx hd =>
            have hd' : C.types[x.toNat]? = some _ := hd
            rw [hx] at hd'; cases hd'
    | some d =>
      simp only [List.getElem?_map, hx, Option.map_some, Option.getD_some]
      exact .ref (.use (.dt (hT d (List.mem_of_getElem? hx))))

/-- A reference not typed at a nullable valid cast target is not null. -/
theorem ne_null_of_not_refOkCast {s : Store H} {r : Ref} {h : CHeapType}
    (hok : TyOk {} (Ty.ref true h)) (hr : ¬ RefOk s r (.ref true h)) : r ≠ .null := by
  rintro rfl
  exact hr (.sub .null hok (.refNull .bot))

/-- The operand of a failed cast has the type `diffrt rt₁ rt₂`. -/
theorem refOk_diffrtCast {s : Store H} {Δ : TypeCtx} {r : Ref} {rt₀ r₁ r₂ : CRefType}
    (hb : RefBase s r rt₀) (hs : Sub Δ rt₀ r₁)
    (hnn : ∀ h₂, r₂ = .ref true h₂ → r ≠ .null) :
    ∃ rt', RefOk s r rt' ∧ Sub Δ rt' (Ty.diffrt r₁ r₂) := by
  cases r₂ with
  | ref n₂ h₂ =>
  cases n₂ with
  | false => exact ⟨rt₀, hb.refOk, by cases r₁; simpa [Ty.diffrt] using hs⟩
  | true =>
    have hn := hnn h₂ rfl
    cases rt₀ with
    | ref n₀ h₀ =>
    cases r₁ with
    | ref n₁ h₁ =>
    have := hb.nonnull hn; subst this
    exact ⟨_, hb.refOk, by simpa [Ty.diffrt] using .refNonNull (Sub.ref_inv hs).1⟩

/-- Generic inversion of a unary redex whose instruction takes `ts ++ [x]`. -/
theorem redex_inv_oneCast {s : Store H} {C : Context} {i : Instr} {v : Val} {it : InstrType}
    (hI : ∀ it', InstrOk C i it' → it'.inits = [] ∧ 1 ≤ it'.params.length)
    (h : AdminsOk s C (vals [v] ++ [.plain i]) it)
    (hne : i ≠ .throwRef := by intro h; cases h) :
    ∃ A b t₂ tv, InstrOk C i ⟨A ++ [b], [], t₂⟩ ∧ ValOk s v tv ∧ Sub C.toTypeCtx tv b ∧
      ∀ (s' : Store H) (out : List Admin), AdminsOk s' C out ⟨A, [], t₂⟩ →
        AdminsOk s' C out it := by
  have hI' : ∀ it', AdminOk s C (.plain i) it' →
      it'.inits = [] ∧ [v].length ≤ it'.params.length := by
    intro it' h'
    exact hI _ (h'.plain_inv_ne hne)
  obtain ⟨A, B, t₂, ts, hi, hvs, hB, hrep⟩ := redex_inv_gen hI' h
  have hi' : InstrOk C i ⟨A ++ B, [], t₂⟩ := hi.plain_inv_ne hne
  cases hvs with
  | cons hv hnil =>
    cases hnil
    cases hB with
    | cons hsb hnil2 =>
      cases hnil2
      exact ⟨A, _, t₂, _, hi', hv, hsb, hrep⟩

/-- Typing `[ref r, br l]` from a typing of `ref r` at the label's top type. -/
theorem ref_br_okCast {s : Store H} {C : Context} (hC : C.Wf) {r : Ref} {l : LabelIdx}
    {ts t₂ : List CValType} {rt : CRefType}
    (hl : C.labels[l.toNat]? = some (ts ++ [.refv rt]))
    (hr : AdminsOk s C [.ref r] ⟨[], [], [.refv rt]⟩) (hok₂ : ResultOk C.toTypeCtx t₂) :
    AdminsOk s C [.ref r, .plain (.br l)] ⟨ts, [], t₂⟩ := by
  have hL := hC.label hl
  have hts : ResultOk C.toTypeCtx ts := ResultOk.leftRT hL
  have h1 : AdminsOk s C [.ref r] ⟨ts, [], ts ++ [.refv rt]⟩ := by
    simpa using AdminsOk.frame (ts := ts) hr hts
  have h2 : AdminsOk s C [.plain (.br l)] ⟨ts ++ [.refv rt], [], t₂⟩ := by
    have := InstrOk.br (t₁ := []) (t₂ := t₂) hl ⟨by simp [ResultOk], hok₂, by simp⟩
    exact .single (.plain (by simpa using this))
  have := AdminsOk.seq h1 (by simp) (by simpa using h2)
  simpa using this

theorem brOnCast_hICast {C : Context} {l : LabelIdx} {rt₁ rt₂ : RefType} :
    ∀ it', InstrOk C (.brOnCast l rt₁ rt₂) it' → it'.inits = [] ∧ 1 ≤ it'.params.length := by
  intro it' h
  cases h with
  | _ => first
    | (rename_i h'; cases h')
    | simp

theorem brOnCastFail_hICast {C : Context} {l : LabelIdx} {rt₁ rt₂ : RefType} :
    ∀ it', InstrOk C (.brOnCastFail l rt₁ rt₂) it' → it'.inits = [] ∧ 1 ≤ it'.params.length := by
  intro it' h
  cases h with
  | _ => first
    | (rename_i h'; cases h')
    | simp

/-- Inversion of `br_on_cast` at a principal type. -/
theorem brOnCast_invCast {C : Context} {l : LabelIdx} {rt₁ rt₂ : RefType} {A : List CValType}
    {b : CValType} {t₂ : List CValType}
    (h : InstrOk C (.brOnCast l rt₁ rt₂) ⟨A ++ [b], [], t₂⟩) :
    ∃ rt, C.labels[l.toNat]? = some (A ++ [.refv rt]) ∧ TyOk C.toTypeCtx (C.closeRef rt₁) ∧
      TyOk C.toTypeCtx (C.closeRef rt₂) ∧ Sub C.toTypeCtx (C.closeRef rt₂) rt ∧
      b = .refv (C.closeRef rt₁) ∧
      t₂ = A ++ [.refv (Ty.diffrt (C.closeRef rt₁) (C.closeRef rt₂))] := by
  generalize hit : (⟨A ++ [b], [], t₂⟩ : InstrType) = it at h
  cases h with
  | brOnCast hl h₁ h₂ _ h₂l =>
    simp only [InstrType.plain, InstrType.mk.injEq] at hit
    obtain ⟨hp, -, rfl⟩ := hit
    obtain ⟨rfl, hb⟩ := List.append_inj' hp rfl
    cases hb
    exact ⟨_, hl, h₁, h₂, h₂l, rfl, rfl⟩
  | _ => rename_i h'; cases h'

/-- Inversion of `br_on_cast_fail` at a principal type. -/
theorem brOnCastFail_invCast {C : Context} {l : LabelIdx} {rt₁ rt₂ : RefType} {A : List CValType}
    {b : CValType} {t₂ : List CValType}
    (h : InstrOk C (.brOnCastFail l rt₁ rt₂) ⟨A ++ [b], [], t₂⟩) :
    ∃ rt, C.labels[l.toNat]? = some (A ++ [.refv rt]) ∧ TyOk C.toTypeCtx (C.closeRef rt₁) ∧
      TyOk C.toTypeCtx (C.closeRef rt₂) ∧
      Sub C.toTypeCtx (Ty.diffrt (C.closeRef rt₁) (C.closeRef rt₂)) rt ∧
      b = .refv (C.closeRef rt₁) ∧ t₂ = A ++ [.refv (C.closeRef rt₂)] := by
  generalize hit : (⟨A ++ [b], [], t₂⟩ : InstrType) = it at h
  cases h with
  | brOnCastFail hl h₁ h₂ _ hdl =>
    simp only [InstrType.plain, InstrType.mk.injEq] at hit
    obtain ⟨hp, -, rfl⟩ := hit
    obtain ⟨rfl, hb⟩ := List.append_inj' hp rfl
    cases hb
    exact ⟨_, hl, h₁, h₂, hdl, rfl, rfl⟩
  | _ => rename_i h'; cases h'

/-- `Step_read/br_on_cast-succeed`. -/
theorem Step.brOnCastSucceed_presCast {s : Store H} {C : Context} {f : Frame} {r : Ref}
    {l : LabelIdx} {rt₁ rt₂ : RefType} {it : InstrType}
    (h : AdminsOk s C [.ref r, .plain (.brOnCast l rt₁ rt₂)] it)
    (hr : RefOk s r (f.module.instRef rt₂)) (hC : C.Wf) (ht : C.types = f.module.types) :
    AdminsOk s C [.ref r, .plain (.br l)] it := by
  obtain ⟨A, b, t₂, tv, hi, -, -, hrep⟩ :=
    redex_inv_oneCast (v := .ref r) brOnCast_hICast h
  obtain ⟨rt, hl, h₁, h₂, h₂l, rfl, rfl⟩ := brOnCast_invCast hi
  rw [← Context.closeRef_eq_instRefCast ht] at hr
  have hL := hC.label hl
  have hrt : TyOk C.toTypeCtx rt := by
    have := ResultOk.rightRT hL; simp [ResultOk] at this; cases this with | ref h => exact .ref h
  apply hrep
  refine ref_br_okCast hC hl ?_ ?_
  · exact AdminsOk.val_sub (v := .ref r) (.ref hr) (.refv h₂l) (.refv hrt)
  · exact ResultOk.appendRT (ResultOk.leftRT hL) (ResultOk.single (.refv (TyOk.diffrt h₁)))

/-- `Step_read/br_on_cast-fail`. Needs `hT` (types valid in the empty context). -/
theorem Step.brOnCastFail_presCast {s : Store H} {C : Context} {f : Frame} {r : Ref}
    {l : LabelIdx} {rt₁ rt₂ : RefType} {it : InstrType}
    (h : AdminsOk s C [.ref r, .plain (.brOnCast l rt₁ rt₂)] it)
    (hr : ¬ RefOk s r (f.module.instRef rt₂)) (hC : C.Wf) (ht : C.types = f.module.types)
    (hT : ∀ d ∈ C.types, TyOk {} d) :
    AdminsOk s C [.ref r] it := by
  obtain ⟨A, b, t₂, tv, hi, hv, hsb, hrep⟩ :=
    redex_inv_oneCast (v := .ref r) brOnCast_hICast h
  obtain ⟨rt, hl, h₁, h₂, h₂l, rfl, rfl⟩ := brOnCast_invCast hi
  rw [← Context.closeRef_eq_instRefCast ht] at hr
  have hok₂ := closeRef_okEmptyCast hT h₂
  obtain ⟨r', rt₀, hr', hb, hs₀⟩ := ValOk.ref_invRT hv hsb
  cases hr'
  have hnn : ∀ h₂', C.closeRef rt₂ = .ref true h₂' → r ≠ .null := by
    intro h₂' he; rw [he] at hr hok₂; exact ne_null_of_not_refOkCast hok₂ hr
  obtain ⟨rt', hr'', hs'⟩ := refOk_diffrtCast hb hs₀ hnn
  have hL := hC.label hl
  apply hrep
  have := AdminsOk.frame (ts := A)
    (AdminsOk.val_sub (v := .ref r) (.ref hr'') (.refv hs') (.refv (TyOk.diffrt h₁)))
    (ResultOk.leftRT hL)
  simpa [Val.toAdmin] using this

/-- `Step_read/br_on_cast_fail-succeed`. -/
theorem Step.brOnCastFailSucceed_presCast {s : Store H} {C : Context} {f : Frame} {r : Ref}
    {l : LabelIdx} {rt₁ rt₂ : RefType} {it : InstrType}
    (h : AdminsOk s C [.ref r, .plain (.brOnCastFail l rt₁ rt₂)] it)
    (hr : RefOk s r (f.module.instRef rt₂)) (hC : C.Wf) (ht : C.types = f.module.types) :
    AdminsOk s C [.ref r] it := by
  obtain ⟨A, b, t₂, tv, hi, -, -, hrep⟩ :=
    redex_inv_oneCast (v := .ref r) brOnCastFail_hICast h
  obtain ⟨rt, hl, h₁, h₂, hdl, rfl, rfl⟩ := brOnCastFail_invCast hi
  rw [← Context.closeRef_eq_instRefCast ht] at hr
  have hL := hC.label hl
  apply hrep
  have := AdminsOk.frame (ts := A) (AdminsOk.val_single (C := C) (v := .ref r) (.ref hr))
    (ResultOk.leftRT hL)
  simpa [Val.toAdmin] using this

/-- `Step_read/br_on_cast_fail-fail`. Needs `hT` (types valid in the empty context). -/
theorem Step.brOnCastFailFail_presCast {s : Store H} {C : Context} {f : Frame} {r : Ref}
    {l : LabelIdx} {rt₁ rt₂ : RefType} {it : InstrType}
    (h : AdminsOk s C [.ref r, .plain (.brOnCastFail l rt₁ rt₂)] it)
    (hr : ¬ RefOk s r (f.module.instRef rt₂)) (hC : C.Wf) (ht : C.types = f.module.types)
    (hT : ∀ d ∈ C.types, TyOk {} d) :
    AdminsOk s C [.ref r, .plain (.br l)] it := by
  obtain ⟨A, b, t₂, tv, hi, hv, hsb, hrep⟩ :=
    redex_inv_oneCast (v := .ref r) brOnCastFail_hICast h
  obtain ⟨rt, hl, h₁, h₂, hdl, rfl, rfl⟩ := brOnCastFail_invCast hi
  rw [← Context.closeRef_eq_instRefCast ht] at hr
  have hok₂ := closeRef_okEmptyCast hT h₂
  obtain ⟨r', rt₀, hr', hb, hs₀⟩ := ValOk.ref_invRT hv hsb
  cases hr'
  have hnn : ∀ h₂', C.closeRef rt₂ = .ref true h₂' → r ≠ .null := by
    intro h₂' he; rw [he] at hr hok₂; exact ne_null_of_not_refOkCast hok₂ hr
  obtain ⟨rt', hr'', hs'⟩ := refOk_diffrtCast hb hs₀ hnn
  have hL := hC.label hl
  have hrt : TyOk C.toTypeCtx rt := by
    have := ResultOk.rightRT hL; simp [ResultOk] at this; cases this with | ref h => exact .ref h
  have hd : TyOk C.toTypeCtx (Ty.diffrt (C.closeRef rt₁) (C.closeRef rt₂)) := TyOk.diffrt h₁
  apply hrep
  refine ref_br_okCast hC hl ?_ ?_
  · exact AdminsOk.val_sub (v := .ref r) (.ref hr'')
      (.refv (Sub.trans_ref hd hs' hdl)) (.refv hrt)
  · exact ResultOk.appendRT (ResultOk.leftRT hL) (ResultOk.single (.refv h₂))

end Silmaril.Wasm.Execution.Core
