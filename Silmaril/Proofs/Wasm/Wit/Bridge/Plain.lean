module

public import Silmaril.Wasm.Wit.Binary.Thms
public import Silmaril.Wasm.Component.Wat.Defs

/-!
# What the WIT decoder reads is in WAT normal form

The decoder of world and interface types (`Binary.compSteps`,
`Binary.instSteps`) accepts only declarations whose names are plain (no
attributes) and whose nested types are value, function or instance types, so
the WAT normal form is the identity on every list of declarations it reads
(`normComponentDecls_of_decWorld`). In particular the component type the encoder
writes for a world is in normal form, since it decodes (`decWorld_encodeWorld`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat
open Silmaril.Wasm.Wit.Binary

theorem instStep_norm {o : List Slot} {s s' : DSt} {d : InstanceDecl} (h : instStep o s d = .ok s') :
    normInstanceDecl d = d := by
  unfold instStep at h
  split at h <;> first | rfl | cases h

theorem instSteps_norm {o : List Slot} : ∀ {s s' : DSt} {ds : List InstanceDecl},
    instSteps o s ds = .ok s' → normInstanceDecls ds = ds
  | _, _, [], _ => rfl
  | s, s', d :: ds, h => by
    unfold instSteps at h
    cases h₁ : instStep o s d with
    | error e => rw [h₁] at h; cases h
    | ok s₁ =>
      rw [h₁] at h
      have hd : normInstanceDecl d = d := instStep_norm h₁
      have hds : normInstanceDecls ds = ds := instSteps_norm h
      simp only [normInstanceDecls, hd, hds]

theorem decInstance_norm {o : List Slot} {ds : List InstanceDecl} {b : Interface}
    (h : decInstance o ds = .ok b) : normInstanceDecls ds = ds := by
  unfold decInstance at h
  cases h₁ : instSteps o {} ds with
  | error e => rw [h₁] at h; cases h
  | ok s => exact instSteps_norm h₁

theorem compStep_norm {s s' : CSt} {d : ComponentDecl} (h : compStep s d = .ok s') :
    normComponentDecl d = d := by
  unfold compStep at h
  split at h
  · rename_i ds
    cases h₁ : decInstance s.slots ds with
    | error e => rw [h₁] at h; cases h
    | ok b =>
      have hn : normInstanceDecls ds = ds := decInstance_norm h₁
      simp only [normComponentDecl, normInstanceDecl, normDefType, hn]
  all_goals first | rfl | cases h

theorem compSteps_norm : ∀ {s s' : CSt} {ds : List ComponentDecl},
    compSteps s ds = .ok s' → normComponentDecls ds = ds
  | _, _, [], _ => rfl
  | s, s', d :: ds, h => by
    unfold compSteps at h
    cases h₁ : compStep s d with
    | error e => rw [h₁] at h; cases h
    | ok s₁ =>
      rw [h₁] at h
      have hd : normComponentDecl d = d := compStep_norm h₁
      have hds : normComponentDecls ds = ds := compSteps_norm h
      simp only [normComponentDecls, hd, hds]

/-- The declarations of a world type the decoder reads are in WAT normal form. -/
theorem normComponentDecls_of_decWorld {ds : List ComponentDecl} {w : World} (h : decWorld ds = .ok w) :
    normComponentDecls ds = ds := by
  unfold decWorld at h
  cases h₁ : compSteps {} ds with
  | error e => rw [h₁] at h; cases h
  | ok s => exact compSteps_norm h₁

end Silmaril.Wasm.Wit.Bridge
