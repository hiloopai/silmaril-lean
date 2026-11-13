module

public import Silmaril.Wasm.Component.Reference.Validation.CanonOpts.Defs
public import Silmaril.Wasm.Component.Reference.Validation.ValTypes.Defs
public import Silmaril.Wasm.Component.Engine.Interface
public import Init.Data.String.Defs
public import Init.Data.Repr
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms
public import Silmaril.Wasm.Component.Reference.Validation.ValTypes.Thms

/-!
# `Validation.CanonOpts`: laws of the component reference

Theorems of the component reference copy `Validation.CanonOpts`, refined out of
`Silmaril.Raw.Wasm.Component.Validation.CanonOpts`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types
variable {X : Type}

private theorem type?_of_typeSlotAt? {Γ : Ctx X} {t : Nat} {s : TypeSlot X}
    (h : Γ.typeSlotAt? t = .ok s) : Γ.type? t = some s.def_ := by
  have h' : Γ.types[t]? = some s := Ctx.listAt?_eq_ok.1 h
  simp [Ctx.type?, h']

theorem checkLift?_iff {feat : Features} {V : CoreView X} {Γ : Ctx X} {callee t : Nat}
    {opts : List Syntax.CanonOpt} {ft : Types.FuncType Nat} :
    checkLift? feat V Γ callee opts t = .ok ft ↔
      Γ.type? t = some (.func ft) ∧ LiftOk feat V Γ callee opts ft := by
  unfold checkLift?
  constructor
  · intro h
    split at h
    · cases h
    · rename_i s hs
      split at h
      · rename_i ft' hft
        split at h
        · cases h
          exact ⟨by rw [type?_of_typeSlotAt? hs, hft], by assumption⟩
        · cases h
      · cases h
  · rintro ⟨hty, hok⟩
    obtain ⟨s, hs, hdef⟩ : ∃ s, Γ.types[t]? = some s ∧ s.def_ = .func ft := by
      simpa [Ctx.type?] using hty
    rw [show Γ.typeSlotAt? t = .ok s from Ctx.listAt?_eq_ok.2 hs]
    simp only [hdef, hok, ↓reduceIte]

theorem checkLift?_sound {feat : Features} {V : CoreView X} {Γ : Ctx X} {callee t : Nat}
    {opts : List Syntax.CanonOpt} {ft : Types.FuncType Nat}
    (h : checkLift? feat V Γ callee opts t = .ok ft) :
    ValidCanon feat V Γ (.lift callee opts t) (.func ft) :=
  let ⟨hty, hok⟩ := checkLift?_iff.1 h
  .lift hty hok

theorem checkLower?_iff {feat : Features} {V : CoreView X} {Γ : Ctx X} {f : Nat}
    {opts : List Syntax.CanonOpt} {x : X} :
    checkLower? feat V Γ f opts = .ok x ↔
      ∃ ft, Γ.func? f = some ft ∧ LowerOk feat V Γ opts ft ∧
        x = V.ofFlat (CanonOpts.lowerCoreType V Γ opts ft) := by
  unfold checkLower?
  constructor
  · intro h
    split at h
    · cases h
    · rename_i ft hft
      split at h
      · cases h
        exact ⟨ft, Ctx.listAt?_eq_ok.1 hft, by assumption, rfl⟩
      · cases h
  · rintro ⟨ft, hf, hok, rfl⟩
    have : Γ.funcAt? f = .ok ft := Ctx.listAt?_eq_ok.2 hf
    rw [this]
    simp only [hok, ↓reduceIte]

theorem checkLower?_sound {feat : Features} {V : CoreView X} {Γ : Ctx X} {f : Nat}
    {opts : List Syntax.CanonOpt} {x : X} (h : checkLower? feat V Γ f opts = .ok x) :
    ValidCanon feat V Γ (.lower f opts) (.coreFunc x) := by
  obtain ⟨ft, hf, hok, rfl⟩ := checkLower?_iff.1 h
  exact .lower hf hok

theorem checkLiftLower?_sound {feat : Features} {V : CoreView X} {Γ : Ctx X}
    {c : Syntax.Canon} {e : CanonEntity X} (h : checkLiftLower? feat V Γ c = .ok e) :
    ValidCanon feat V Γ c e := by
  cases c with
  | lift callee opts t =>
    simp only [checkLiftLower?] at h
    cases hc : checkLift? feat V Γ callee opts t with
    | error _ => simp [hc, Except.map] at h
    | ok ft =>
      simp only [hc, Except.map, Except.ok.injEq] at h
      subst h
      exact checkLift?_sound hc
  | lower f opts =>
    simp only [checkLiftLower?] at h
    cases hc : checkLower? feat V Γ f opts with
    | error _ => simp [hc, Except.map] at h
    | ok x =>
      simp only [hc, Except.map, Except.ok.injEq] at h
      subst h
      exact checkLower?_sound hc
  | builtin _ => simp [checkLiftLower?] at h

end Silmaril.Wasm.Component.Validation
