module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Soundness.StateFacts

@[expose] public section

/-! # Soundness, reference family

Preservation of `RefStep` (the frame is unchanged; the store is extended and
stays valid) and progress for `RefInstrOk` restricted to the instructions it reduces.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- **Preservation (reference).** -/
theorem RefStep.preservation {c c' : Config H} {C : Context} {it : InstrType}
    (hst : StateOk c.store c.frame C) (hty : AdminsOk c.store C c.code it)
    (h : RefStep c c') :
    c'.frame = c.frame ∧ StoreOk c'.store ∧ Extend c.store c'.store ∧
      AdminsOk c'.store C c'.code it := by
  obtain ⟨hs, hf⟩ := hst
  cases h with
  | @refNull s f ht =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := []) (i := .refNull ht) trivial
      (by intro it h; cases h; rfl) hty
    cases hi with
    | refNull hh =>
      exact hrep _ _ (AdminsOk.val_sub (v := .ref .null) (.ref .null) (.refv (.refNull .bot))
        (.refv (.ref hh)))
  | @refFunc s f x a ha =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := []) (i := .refFunc x) trivial
      (by intro it h; cases h; rfl) hty
    cases hi with
    | refFunc hd _ =>
      obtain ⟨a', ha', hx⟩ := hf.func hd
      rw [ha] at ha'
      cases ha'
      exact hrep _ _ (AdminsOk.val_single (v := .ref (.func a)) (.ref (hx.func_ref a _ rfl rfl)))
  | @refI31 s f i =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := [Val.i32 i]) (i := .refI31) trivial
      (by intro it h; cases h; rfl) hty
    cases hi
    exact hrep _ _ (AdminsOk.val_single (v := .ref (.i31 _)) (.ref (.i31 _)))
  | isNullTrue =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := [.ref .null]) (i := .refIsNull)
      trivial (by intro it h; cases h; rfl) hty
    cases hi
    exact hrep _ _ (AdminsOk.constI32 1)
  | @isNullFalse s f r _ =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := [.ref r]) (i := .refIsNull)
      trivial (by intro it h; cases h; rfl) hty
    cases hi
    exact hrep _ _ (AdminsOk.constI32 0)
  | asNonNullNull =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := [.ref .null]) (i := .refAsNonNull)
      trivial (by intro it h; cases h; rfl) hty
    cases hi with
    | refAsNonNull hh =>
      exact hrep _ _ (AdminsOk.trap_single (ResultOk.single (.refv (.ref hh))))
  | @asNonNullAddr s f r hr =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, hrep⟩ := redex_ref (vs := [.ref r]) (i := .refAsNonNull)
      trivial (by intro it h; cases h; rfl) hty
    cases hi with
    | refAsNonNull hh =>
      obtain ⟨t, hv, rfl⟩ : ∃ t, ValOk s (.ref r) t ∧ ts = [t] := by
        cases hvs with | cons hv hnil => cases hnil; exact ⟨_, hv, rfl⟩
      cases hsub with
      | cons hsub _ =>
        obtain ⟨r', rt₀, hr', hb, hs₀⟩ := ValOk.ref_invRT hv hsub
        cases hr'
        cases rt₀ with
        | ref n₀ h₀ =>
          have hn := hb.nonnull hr
          subst hn
          exact hrep _ _ (AdminsOk.val_sub (v := .ref r) (.ref hb.refOk)
            (.refv (.refNonNull (Sub.ref_inv hs₀).1)) (.refv (.ref hh)))
  | eqNull =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := [.ref .null, .ref .null])
      (i := .refEq) trivial (by intro it h; cases h; rfl) hty
    cases hi
    exact hrep _ _ (AdminsOk.constI32 1)
  | @eqTrue s f r _ =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := [.ref r, .ref r])
      (i := .refEq) trivial (by intro it h; cases h; rfl) hty
    cases hi
    exact hrep _ _ (AdminsOk.constI32 1)
  | @eqFalse s f r₁ r₂ _ =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := [.ref r₁, .ref r₂])
      (i := .refEq) trivial (by intro it h; cases h; rfl) hty
    cases hi
    exact hrep _ _ (AdminsOk.constI32 0)
  | @testTrue s f r rt _ =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := [.ref r]) (i := .refTest rt)
      trivial (by intro it h; cases h; rfl) hty
    cases hi
    exact hrep _ _ (AdminsOk.constI32 1)
  | @testFalse s f r rt _ =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := [.ref r]) (i := .refTest rt)
      trivial (by intro it h; cases h; rfl) hty
    cases hi
    exact hrep _ _ (AdminsOk.constI32 0)
  | @castSucceed s f r rt hr =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := [.ref r]) (i := .refCast rt)
      trivial (by intro it h; cases h; rfl) hty
    cases hi
    rw [← hf.closeRef] at hr
    exact hrep _ _ (AdminsOk.val_single (v := .ref r) (.ref hr))
  | @castFail s f r rt _ =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := [.ref r]) (i := .refCast rt)
      trivial (by intro it h; cases h; rfl) hty
    cases hi with
    | refCast hh _ _ =>
      exact hrep _ _ (AdminsOk.trap_single (ResultOk.single (.refv hh)))
  | @i31GetNull s f sx =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := [.ref .null]) (i := .i31Get sx)
      trivial (by intro it h; cases h; rfl) hty
    cases hi
    exact hrep _ _ (AdminsOk.trap_single (ResultOk.single (.num _)))
  | @i31GetNum s f sx i =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, -, -, hrep⟩ := redex_ref (vs := [.ref (.i31 i)]) (i := .i31Get sx)
      trivial (by intro it h; cases h; rfl) hty
    cases hi
    exact hrep _ _ (AdminsOk.constI32 _)
  | @externConvertNull s f =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, hrep⟩ := redex_ref (vs := [.ref .null])
      (i := .externConvertAny) trivial (by intro it h; cases h; rfl) hty
    cases hi with
    | externConvertAny n =>
      obtain ⟨t, hv, rfl⟩ : ∃ t, ValOk s (.ref .null) t ∧ ts = [t] := by
        cases hvs with | cons hv hnil => cases hnil; exact ⟨_, hv, rfl⟩
      cases hsub with
      | cons hsub _ =>
        obtain ⟨r', rt₀, hr', hb, hs₀⟩ := ValOk.ref_invRT hv hsub
        cases hr'
        cases hb
        have hn := (Sub.ref_inv hs₀).2 rfl
        subst hn
        exact hrep _ _ (AdminsOk.val_sub (v := .ref .null) (.ref .null) (.refv (.refNull .bot))
          (TyOk.refT_abs _ _))
  | @externConvertAddr s f r hr =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, hrep⟩ := redex_ref (vs := [.ref r])
      (i := .externConvertAny) trivial (by intro it h; cases h; rfl) hty
    cases hi with
    | externConvertAny n =>
      obtain ⟨t, hv, rfl⟩ : ∃ t, ValOk s (.ref r) t ∧ ts = [t] := by
        cases hvs with | cons hv hnil => cases hnil; exact ⟨_, hv, rfl⟩
      cases hsub with
      | cons hsub _ =>
        obtain ⟨r', rt₀, hr', hb, hs₀⟩ := ValOk.ref_invRT hv hsub
        cases hr'
        cases rt₀ with
        | ref n₀ h₀ =>
          have hany := RefBase.to_any ⟨hs, hf⟩ hb hr (Sub.ref_inv hs₀).1
          exact hrep _ _ (AdminsOk.val_sub (v := .ref (.extern r)) (.ref (.extern hany hr))
            (.refv (Sub.ref_false_le _ _)) (TyOk.refT_abs _ _))
  | @anyConvertNull s f =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, hrep⟩ := redex_ref (vs := [.ref .null])
      (i := .anyConvertExtern) trivial (by intro it h; cases h; rfl) hty
    cases hi with
    | anyConvertExtern n =>
      obtain ⟨t, hv, rfl⟩ : ∃ t, ValOk s (.ref .null) t ∧ ts = [t] := by
        cases hvs with | cons hv hnil => cases hnil; exact ⟨_, hv, rfl⟩
      cases hsub with
      | cons hsub _ =>
        obtain ⟨r', rt₀, hr', hb, hs₀⟩ := ValOk.ref_invRT hv hsub
        cases hr'
        cases hb
        have hn := (Sub.ref_inv hs₀).2 rfl
        subst hn
        exact hrep _ _ (AdminsOk.val_sub (v := .ref .null) (.ref .null) (.refv (.refNull .bot))
          (TyOk.refT_abs _ _))
  | @anyConvertAddr s f r =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    obtain ⟨t₁, t₂, ts, hi, hvs, hsub, hrep⟩ := redex_ref (vs := [.ref (.extern r)])
      (i := .anyConvertExtern) trivial (by intro it h; cases h; rfl) hty
    cases hi with
    | anyConvertExtern n =>
      obtain ⟨t, hv, rfl⟩ : ∃ t, ValOk s (.ref (.extern r)) t ∧ ts = [t] := by
        cases hvs with | cons hv hnil => cases hnil; exact ⟨_, hv, rfl⟩
      cases hsub with
      | cons hsub _ =>
        obtain ⟨r', rt₀, hr', hb, hs₀⟩ := ValOk.ref_invRT hv hsub
        cases hr'
        cases hb with
        | extern hany _ =>
          exact hrep _ _ (AdminsOk.val_sub (v := .ref r) (.ref hany)
            (.refv (Sub.ref_false_le _ _)) (TyOk.refT_abs _ _))

/-- **Progress (reference).** -/
theorem RefInstrOk.progress_ref {P : Profile} {host : HostSemantics H} {s : Store H}
    {f : Frame} {C : Context} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    {vs : List Val} (hst : StateOk s f C) (hi : RefInstrOk C i ⟨t₁, xs, t₂⟩) (hna : ¬ i.IsAggregate)
    (hvs : List.Forall₂ (ValOk s) vs t₁) :
    ∃ c', Step P host ⟨s, f, vals vs ++ [.plain i]⟩ c' := by
  cases hi with
  | refNull _ =>
    cases hvs
    exact ⟨_, .reference (.refNull _)⟩
  | refFunc hd _ =>
    cases hvs
    obtain ⟨a, ha, -⟩ := hst.2.func hd
    exact ⟨_, .reference (.refFunc ha)⟩
  | refI31 =>
    obtain ⟨v, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v Ty.i32 := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨rfl, hv⟩ := hv
    obtain ⟨b, rfl⟩ := ValOk.i32_invRT' hv
    exact ⟨_, .reference (.refI31 b)⟩
  | refIsNull _ =>
    obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v (Ty.refT true _) := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨r, rfl, -⟩ := ValOk.refv_inv hv
    by_cases hr : r = .null
    · subst hr; exact ⟨_, .reference .isNullTrue⟩
    · exact ⟨_, .reference (.isNullFalse hr)⟩
  | refAsNonNull _ =>
    obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v (Ty.refT true _) := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨r, rfl, -⟩ := ValOk.refv_inv hv
    by_cases hr : r = .null
    · subst hr; exact ⟨_, .reference .asNonNullNull⟩
    · exact ⟨_, .reference (.asNonNullAddr hr)⟩
  | refEq =>
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ : ∃ v₁ v₂, vs = [v₁, v₂] ∧
        ValOk s v₁ (Ty.refT true (.abs .eq)) ∧ ValOk s v₂ (Ty.refT true (.abs .eq)) := by
      cases hvs with
      | cons hv₁ h => cases h with | cons hv₂ hnil => cases hnil; exact ⟨_, _, rfl, hv₁, hv₂⟩
    obtain ⟨r₁, rfl, -⟩ := ValOk.refv_inv hv₁
    obtain ⟨r₂, rfl, -⟩ := ValOk.refv_inv hv₂
    by_cases he : r₁ = r₂
    · subst he
      by_cases hr : r₁ = .null
      · subst hr; exact ⟨_, .reference .eqNull⟩
      · exact ⟨_, .reference (.eqTrue hr)⟩
    · exact ⟨_, .reference (.eqFalse he)⟩
  | @refTest rt _ _ _ _ =>
    obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v (.refv _) := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨r, rfl, -⟩ := ValOk.refv_inv hv
    by_cases hr : RefOk s r (f.module.instRef rt)
    · exact ⟨_, .reference (.testTrue hr)⟩
    · exact ⟨_, .reference (.testFalse hr)⟩
  | @refCast rt _ _ _ _ =>
    obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v (.refv _) := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨r, rfl, -⟩ := ValOk.refv_inv hv
    by_cases hr : RefOk s r (f.module.instRef rt)
    · exact ⟨_, .reference (.castSucceed hr)⟩
    · exact ⟨_, .reference (.castFail hr)⟩
  | i31Get sx =>
    obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v (Ty.refT true (.abs .i31)) := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨r, rfl, hr⟩ := ValOk.refv_inv hv
    obtain ⟨rt₀, hb, hs₀⟩ := hr.principal_sub (Δ := {}) (Sub.refl {} (k := .ref) trivial _)
    cases rt₀ with
    | ref n₀ h₀ =>
      have hd := Sub.down_leaf (Sub.ref_inv hs₀).1 (.inl rfl)
      cases hb with
      | null => exact ⟨_, .reference (.i31GetNull sx)⟩
      | i31 b => exact ⟨_, .reference (.i31GetNum sx b)⟩
      | _ => simp [HeapDown, Ty.defHeap] at hd
  | externConvertAny n =>
    obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v (Ty.refT n (.abs .any)) := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨r, rfl, -⟩ := ValOk.refv_inv hv
    by_cases hr : r = .null
    · subst hr; exact ⟨_, .reference .externConvertNull⟩
    · exact ⟨_, .reference (.externConvertAddr hr)⟩
  | anyConvertExtern n =>
    obtain ⟨v, rfl, hv⟩ : ∃ v, vs = [v] ∧ ValOk s v (Ty.refT n (.abs .extern)) := by
      cases hvs with | cons hv hnil => cases hnil; exact ⟨_, rfl, hv⟩
    obtain ⟨r, rfl, hr⟩ := ValOk.refv_inv hv
    obtain ⟨rt₀, hb, hs₀⟩ := hr.principal_sub (Δ := {}) (Sub.refl {} (k := .ref) trivial _)
    cases rt₀ with
    | ref n₀ h₀ =>
      have hd := Sub.down_leaf (Sub.ref_inv hs₀).1 (.inr (.inr rfl))
      cases hb with
      | null => exact ⟨_, .reference .anyConvertNull⟩
      | extern _ _ => exact ⟨_, .reference (.anyConvertAddr _)⟩
      | _ => simp [HeapDown, Ty.defHeap] at hd
  | _ => exact absurd trivial hna

end Silmaril.Wasm.Execution.Core
