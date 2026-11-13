module

public import Silmaril.Wasm.Component.Reference.Validation.ValTypes.Defs
public import Silmaril.Wasm.Component.Reference.Validation.Context.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Predicates.Defs
public import Init.Data.String.Defs
public import Init.Data.Repr
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Validation.ValTypes`: laws of the component reference

Theorems of the component reference copy `Validation.ValTypes`, refined out of
`Silmaril.Raw.Wasm.Component.Validation.ValTypes`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types
variable {X : Type}

theorem resolveResource?_eq_ok {Γ : Ctx X} {r v : Nat} :
    resolveResource? Γ r = .ok v ↔ Γ.type? r = some (.resource v) := by
  simp only [resolveResource?, Ctx.typeSlotAt?, Ctx.listAt?, Ctx.type?]
  cases hs : Γ.types[r]? with
  | none => simp only [Option.map_none, reduceCtorEq]
  | some s =>
    simp only [Option.map_some, Option.some.injEq]
    cases hd : s.def_ <;> simp

theorem resolveFields?_eq_ok {Γ : Ctx X} {fs : List (String × Syntax.VT)}
    {ts : List (String × Types.ValType Nat)} :
    resolveFields? Γ fs = .ok ts ↔ ResolveFields Γ fs ts := by
  induction fs generalizing ts with
  | nil =>
    simp only [resolveFields?, Except.ok.injEq]
    constructor
    · rintro rfl; exact .nil
    · rintro ⟨⟩; rfl
  | cons f fs ih =>
    obtain ⟨n, v⟩ := f
    simp only [resolveFields?]
    constructor
    · intro h
      cases h1 : resolveVT? Γ v <;> cases h2 : resolveFields? Γ fs <;>
        simp only [h1, h2, reduceCtorEq, Except.ok.injEq] at h
      subst h
      exact .cons (resolveVT?_eq_ok.mp h1) (ih.mp h2)
    · rintro (_ | ⟨h1, h2⟩)
      rw [resolveVT?_eq_ok.mpr h1, ih.mpr h2]

theorem resolveList?_eq_ok {Γ : Ctx X} {vs : List Syntax.VT} {ts : List (Types.ValType Nat)} :
    resolveList? Γ vs = .ok ts ↔ ResolveList Γ vs ts := by
  induction vs generalizing ts with
  | nil =>
    simp only [resolveList?, Except.ok.injEq]
    constructor
    · rintro rfl; exact .nil
    · rintro ⟨⟩; rfl
  | cons v vs ih =>
    simp only [resolveList?]
    constructor
    · intro h
      cases h1 : resolveVT? Γ v <;> cases h2 : resolveList? Γ vs <;>
        simp only [h1, h2, reduceCtorEq, Except.ok.injEq] at h
      subst h
      exact .cons (resolveVT?_eq_ok.mp h1) (ih.mp h2)
    · rintro (_ | ⟨h1, h2⟩)
      rw [resolveVT?_eq_ok.mpr h1, ih.mpr h2]

theorem resolveCases?_eq_ok {Γ : Ctx X} {cs : List (String × Option Syntax.VT)}
    {ts : List (String × Option (Types.ValType Nat))} :
    resolveCases? Γ cs = .ok ts ↔ ResolveCases Γ cs ts := by
  induction cs generalizing ts with
  | nil =>
    simp only [resolveCases?, Except.ok.injEq]
    constructor
    · rintro rfl; exact .nil
    · rintro ⟨⟩; rfl
  | cons c cs ih =>
    obtain ⟨n, v⟩ := c
    simp only [resolveCases?]
    constructor
    · intro h
      cases h1 : resolveOpt? Γ v <;> cases h2 : resolveCases? Γ cs <;>
        simp only [h1, h2, reduceCtorEq, Except.ok.injEq] at h
      subst h
      exact .cons (resolveOpt?_eq_ok.mp h1) (ih.mp h2)
    · rintro (_ | ⟨h1, h2⟩)
      rw [resolveOpt?_eq_ok.mpr h1, ih.mpr h2]

end Silmaril.Wasm.Component.Validation

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types
variable {X : Type}

theorem resolveDef?_sound {Γ : Ctx X} {d : Syntax.DefValType} {t : Types.ValType Nat}
    (h : resolveDef? Γ d = .ok t) : ResolveDef Γ d t := by
  cases d with
  | prim p => cases h; exact .prim p
  | flags ls => cases h; exact .flags ls
  | enum ls => cases h; exact .enum ls
  | record fs =>
    obtain ⟨ts, h1, rfl⟩ : ∃ ts, resolveFields? Γ fs = .ok ts ∧ WIT.ValType.record ts = t :=
      by simp only [resolveDef?] at h; split at h <;> simp_all
    exact .record (resolveFields?_eq_ok.mp h1)
  | variant cs =>
    obtain ⟨ts, h1, rfl⟩ : ∃ ts, resolveCases? Γ cs = .ok ts ∧ WIT.ValType.variant ts = t :=
      by simp only [resolveDef?] at h; split at h <;> simp_all
    exact .variant (resolveCases?_eq_ok.mp h1)
  | list v =>
    obtain ⟨u, h1, rfl⟩ : ∃ u, resolveVT? Γ v = .ok u ∧ WIT.ValType.list u = t :=
      by simp only [resolveDef?] at h; split at h <;> simp_all
    exact .list (resolveVT?_eq_ok.mp h1)
  | fixedList v n =>
    obtain ⟨u, h1, rfl⟩ : ∃ u, resolveVT? Γ v = .ok u ∧ WIT.ValType.fixedList u n = t :=
      by simp only [resolveDef?] at h; split at h <;> simp_all
    exact .fixedList n (resolveVT?_eq_ok.mp h1)
  | tuple vs =>
    obtain ⟨ts, h1, rfl⟩ : ∃ ts, resolveList? Γ vs = .ok ts ∧ WIT.ValType.tuple ts = t :=
      by simp only [resolveDef?] at h; split at h <;> simp_all
    exact .tuple (resolveList?_eq_ok.mp h1)
  | option v =>
    obtain ⟨u, h1, rfl⟩ : ∃ u, resolveVT? Γ v = .ok u ∧ WIT.ValType.option u = t :=
      by simp only [resolveDef?] at h; split at h <;> simp_all
    exact .option (resolveVT?_eq_ok.mp h1)
  | result a b =>
    simp only [resolveDef?] at h; split at h <;> cases h
    next ha hb => exact .result (resolveOpt?_eq_ok.mp ha) (resolveOpt?_eq_ok.mp hb)
  | map k v =>
    simp only [resolveDef?] at h; split at h
    next hk hv =>
      split at h <;> cases h
      next hkey => exact .map (resolveVT?_eq_ok.mp hk) hkey (resolveVT?_eq_ok.mp hv)
    all_goals cases h
  | own r =>
    obtain ⟨u, h1, rfl⟩ : ∃ u, resolveResource? Γ r = .ok u ∧ WIT.ValType.own u = t :=
      by simp only [resolveDef?] at h; split at h <;> simp_all
    exact .own (resolveResource?_eq_ok.mp h1)
  | borrow r =>
    obtain ⟨u, h1, rfl⟩ : ∃ u, resolveResource? Γ r = .ok u ∧ WIT.ValType.borrow u = t :=
      by simp only [resolveDef?] at h; split at h <;> simp_all
    exact .borrow (resolveResource?_eq_ok.mp h1)
  | stream a =>
    obtain ⟨u, h1, rfl⟩ : ∃ u, resolveOpt? Γ a = .ok u ∧ WIT.ValType.stream u = t :=
      by simp only [resolveDef?] at h; split at h <;> simp_all
    exact .stream (resolveOpt?_eq_ok.mp h1)
  | future a =>
    obtain ⟨u, h1, rfl⟩ : ∃ u, resolveOpt? Γ a = .ok u ∧ WIT.ValType.future u = t :=
      by simp only [resolveDef?] at h; split at h <;> simp_all
    exact .future (resolveOpt?_eq_ok.mp h1)

theorem resolveDef?_complete {Γ : Ctx X} {d : Syntax.DefValType} {t : Types.ValType Nat}
    (h : ResolveDef Γ d t) : resolveDef? Γ d = .ok t := by
  cases h with
  | prim p => rfl
  | flags ls => rfl
  | enum ls => rfl
  | record h => simp only [resolveDef?, resolveFields?_eq_ok.mpr h]
  | variant h => simp only [resolveDef?, resolveCases?_eq_ok.mpr h]
  | list h => simp only [resolveDef?, resolveVT?_eq_ok.mpr h]
  | fixedList n h => simp only [resolveDef?, resolveVT?_eq_ok.mpr h]
  | tuple h => simp only [resolveDef?, resolveList?_eq_ok.mpr h]
  | option h => simp only [resolveDef?, resolveVT?_eq_ok.mpr h]
  | result ha hb => simp only [resolveDef?, resolveOpt?_eq_ok.mpr ha, resolveOpt?_eq_ok.mpr hb]
  | map hk hkey hv =>
    simp only [resolveDef?, resolveVT?_eq_ok.mpr hk, resolveVT?_eq_ok.mpr hv, hkey]
  | own h => simp only [resolveDef?, resolveResource?_eq_ok.mpr h]
  | borrow h => simp only [resolveDef?, resolveResource?_eq_ok.mpr h]
  | stream h => simp only [resolveDef?, resolveOpt?_eq_ok.mpr h]
  | future h => simp only [resolveDef?, resolveOpt?_eq_ok.mpr h]

theorem resolveDef?_eq_ok {Γ : Ctx X} {d : Syntax.DefValType} {t : Types.ValType Nat} :
    resolveDef? Γ d = .ok t ↔ ResolveDef Γ d t :=
  ⟨resolveDef?_sound, resolveDef?_complete⟩

theorem checkDefValType?_sound {feat : Features} {Γ : Ctx X} {d : Syntax.DefValType}
    {t : Types.ValType Nat} (h : checkDefValType? feat Γ d = .ok t) :
    ValidDefValType feat Γ d t := by
  unfold checkDefValType? at h
  split at h
  · cases h
  · next t' hr =>
    split at h
    · next hok => cases h; exact ⟨resolveDef?_eq_ok.mp hr, hok.1, hok.2⟩
    · cases h

theorem checkFuncType?_sound {feat : Features} {Γ : Ctx X} {ft : Syntax.FuncType}
    {t : Types.FuncType Nat} (h : checkFuncType? feat Γ ft = .ok t) :
    ValidFuncType feat Γ ft t := by
  unfold checkFuncType? at h
  split at h
  · next ps r h1 h2 =>
    dsimp only at h
    split at h
    · next hok =>
      cases h
      exact ⟨resolveFields?_eq_ok.mp h1, resolveOpt?_eq_ok.mp h2, rfl, hok⟩
    · cases h
  · cases h
  · cases h

end Silmaril.Wasm.Component.Validation
