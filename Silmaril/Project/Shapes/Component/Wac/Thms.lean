module

public import Silmaril.Project.Shapes.Component.Wac.Defs
public import Silmaril.Project.Formats.Wac.Thms
public import Silmaril.Wasm.Wac.Targets.Thms

/-!
# Standard problem shapes: WAC compositions (laws)

* `wacHasWorld_iff`, `wacHasIRWorld_iff`: the decision procedures (one kernel `Bool` per row).
* `fits_refl`, `fits_trans`: fitting is a preorder on worlds, so `WacHasWorld.self` (a
  profile component has its own surface world) and `WacHasWorld.trans` (a composition with
  world `W` has every world `W` fits: fewer imports needed, more exports offered).
* `WacHasWorld.of_check`: the verdict "no misfits" of `wasm-wac targets`
  (`Wac.Targets.check`) is a proof of `Fits` for the component the bytes parse to; with the
  profile, of `WacHasWorld`.
* `WacHasWorld.of_value`, `WacHasIRWorld.of_value`: rows on registered values, from the
  decision procedures.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Component

open Silmaril.Wasm Silmaril.Wasm.Wac.Targets
open Silmaril.Wasm.Component.Binary (Ast)
open Silmaril.Wasm.Wit.Project (WorldType IRWorld compWorld)

theorem wacHasWorld_iff (c : Ast) (W : WorldType) :
    wacHasWorld c W = true ↔ WacHasWorld c W := by
  simp only [wacHasWorld, Bool.and_eq_true, fits_iff, WacHasWorld, Wac.Profile]

theorem wacHasIRWorld_iff (c : Ast) (W : IRWorld) :
    wacHasIRWorld c W = true ↔ WacHasIRWorld c W := by
  simp only [wacHasIRWorld, Bool.and_eq_true, WacHasIRWorld, Wac.Profile]
  cases Wac.Lower.toCompCore c <;> simp

theorem fits_refl (w : WorldType) : Fits w w :=
  ⟨fun _ h => h, fun _ h _ => h⟩

theorem fits_trans {a b c : WorldType} (h₁ : Fits a b) (h₂ : Fits b c) : Fits a c :=
  ⟨fun i hi => h₂.1 i (h₁.1 i hi), fun e he ht => h₁.2 e (h₂.2 e he ht) ht⟩

/-- A profile component has its own surface world. -/
theorem WacHasWorld.self {c : Ast} (h : Wac.Profile c) : WacHasWorld c (surface c) :=
  ⟨h, fits_refl _⟩

/-- A composition with world `W` has every world that `W` fits. -/
theorem WacHasWorld.trans {c : Ast} {W W' : WorldType} (h : WacHasWorld c W) (hf : Fits W W') :
    WacHasWorld c W' :=
  ⟨h.1, fits_trans h.2 hf⟩

/-- **`wasm-wac targets` reports no misfits**: the bytes are a component, the WIT package has
the world `w`, and the component fits it. -/
theorem fits_of_check {comp wit : ByteArray} {n : Option String}
    (h : check comp wit n = .ok []) :
    ∃ c w, Component.Binary.parse comp = .ok c ∧ targetWorld wit n = .ok w ∧ Fits (surface c) w := by
  simp only [check, componentWorld, bind, Except.bind] at h
  cases hc : Component.Binary.parse comp with
  | error e => simp [hc] at h
  | ok c =>
    cases hw : targetWorld wit n with
    | error e => simp [hc, hw, pure, Except.pure] at h
    | ok w =>
      simp only [hc, hw, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨c, w, rfl, rfl, (misfits_nil_iff _ _).mp h⟩

/-- The `targets` verdict as the shape, for a component in the profile. -/
theorem WacHasWorld.of_check {comp wit : ByteArray} {n : Option String} {c : Ast} {w : WorldType}
    (h : check comp wit n = .ok []) (hc : Component.Binary.parse comp = .ok c)
    (hw : targetWorld wit n = .ok w) (hp : Wac.Profile c) : WacHasWorld c w := by
  obtain ⟨c', w', hc', hw', hf⟩ := fits_of_check h
  rw [hc] at hc'
  rw [hw] at hw'
  cases hc'
  cases hw'
  exact ⟨hp, hf⟩

/-- A row of `wac_has_world` on a registered value, from one kernel `Bool`. -/
theorem WacHasWorld.of_value {X : Value Ast} {W : WorldType}
    (h : (X.parse.any fun c => wacHasWorld c W) = true) : X.Satisfies fun c => WacHasWorld c W := by
  cases hx : X.parse with
  | none => rw [hx] at h; cases h
  | some c =>
    rw [hx] at h
    exact ⟨c, hx, (wacHasWorld_iff c W).mp h⟩

/-- A row of `wac_has_ir_world` on a registered value, from one kernel `Bool`. -/
theorem WacHasIRWorld.of_value {X : Value Ast} {W : IRWorld}
    (h : (X.parse.any fun c => wacHasIRWorld c W) = true) :
    X.Satisfies fun c => WacHasIRWorld c W := by
  cases hx : X.parse with
  | none => rw [hx] at h; cases h
  | some c =>
    rw [hx] at h
    exact ⟨c, hx, (wacHasIRWorld_iff c W).mp h⟩

/-- A refutation of `wac_has_world` on a registered value that parses. -/
theorem WacHasWorld.not_of_value {X : Value Ast} {W : WorldType}
    (h : (X.parse.any fun c => !wacHasWorld c W) = true) :
    ¬ X.Satisfies fun c => WacHasWorld c W := by
  rintro ⟨c, hx, hc⟩
  rw [hx] at h
  simp only [Option.any_some, Bool.not_eq_true'] at h
  rw [(wacHasWorld_iff c W).mpr hc] at h
  cases h

end Silmaril.Project.Shapes.Component

end

silmaril group silmaril.shapes.component.wac
  (title := "Standard problem shapes: WAC compositions")
  (children := [silmaril.shapes.component.wac_has_world, silmaril.shapes.component.wac_has_ir_world])

/-! Detached, as the other component shapes (`Silmaril.Project.Shapes.Component.Example.Thms`). -/
silmaril detached silmaril.shapes.component.wac (reason := "shape library")
silmaril detached silmaril.shapes.component.wac_has_world (reason := "shape library")
silmaril detached silmaril.shapes.component.wac_has_ir_world (reason := "shape library")
