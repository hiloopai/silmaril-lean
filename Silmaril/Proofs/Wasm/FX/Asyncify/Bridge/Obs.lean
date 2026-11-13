module

public import Silmaril.Wasm.FX.Asyncify.Bridge.Defs
public import Silmaril.Wasm.FX.Asyncify.Thms

/-!
# Behaviours across observation types

The tool's systems (`Tool.SRes`, behaviours `Tool.beh` in `Tool.Obs σ`) and the kernel's
observing machines (`FXAsync.Res` over `HOut V σ`) are compared as `FXAsync` machines over one
value type, `Tool.Obs σ`:

* `tool_beh_asRes`: `Tool.beh step x` is the image of `beh (asRes step) x` under `backObs`;
* `beh_mapObs`: `beh (mapObs g step) y` is the image of `beh step y` under `Obs.mapV g`;
* `beh_next_eq`: a deterministic step does not change the behaviours.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Bridge

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify
open Silmaril.Wasm.FX.Asyncify.Bridge

variable {σ X C O O' : Type}

/-! ## Tool systems as machines -/

/-- A tool step result as a machine result. -/
def liftR : Tool.SRes X σ → Res X (Tool.Obs σ)
  | .next y => .next y
  | .stop o => .stop (.done [.val o])

theorem asRes_eq (step : X → Tool.SRes X σ) (x : X) : asRes step x = liftR (step x) := by
  unfold asRes liftR
  cases step x <;> rfl

theorem runN_asRes (step : X → Tool.SRes X σ) :
    ∀ (n : Nat) (x : X), runN (asRes step) n x = liftR (Tool.runN step n x)
  | 0, _ => rfl
  | n + 1, x => by
    have e : asRes step x = liftR (step x) := asRes_eq step x
    cases hs : step x with
    | next y =>
      have h1 : runN (asRes step) (n + 1) x = runN (asRes step) n y := by
        simp only [runN, e, hs, liftR]
      have h2 : Tool.runN step (n + 1) x = Tool.runN step n y := by simp only [Tool.runN, hs]
      rw [h1, h2]
      exact runN_asRes step n y
    | stop o =>
      have h1 : runN (asRes step) (n + 1) x = .stop (.done [.val o]) := by
        simp only [runN, e, hs, liftR]
      have h2 : Tool.runN step (n + 1) x = .stop o := by simp only [Tool.runN, hs]
      rw [h1, h2]
      rfl

theorem liftR_next {r : Tool.SRes X σ} {y : X} (h : liftR r = .next y) : r = .next y := by
  cases r with
  | next y' => cases h; rfl
  | stop o => cases h

theorem liftR_stop {r : Tool.SRes X σ} {o : Outcome (Tool.Obs σ)} (h : liftR r = .stop o) :
    ∃ b, r = .stop b ∧ o = .done [.val b] := by
  cases r with
  | next y => cases h
  | stop b => cases h; exact ⟨b, rfl, rfl⟩

/-- **A tool system's behaviours are those of its machine**, read back by `backObs`. -/
theorem tool_beh_asRes (step : X → Tool.SRes X σ) (x : X) :
    Tool.beh step x = backObs '' beh (asRes step) x := by
  ext b
  constructor
  · rintro (⟨n, hn⟩ | ⟨rfl, hdiv⟩)
    · have h : runN (asRes step) n x = .stop (.done [.val b]) := by rw [runN_asRes, hn]; rfl
      exact ⟨.done [.val b], .inl ⟨n, _, h, rfl⟩, rfl⟩
    · have h : ∀ n, ∃ x', runN (asRes step) n x = .next x' := fun n => by
        obtain ⟨x', hx'⟩ := hdiv n
        exact ⟨x', by rw [runN_asRes, hx']; rfl⟩
      exact ⟨.diverges, .inr ⟨rfl, h⟩, rfl⟩
  · rintro ⟨b', (⟨n, o, hn, rfl⟩ | ⟨rfl, hdiv⟩), rfl⟩
    · have hl : liftR (Tool.runN step n x) = .stop o := by rw [← runN_asRes]; exact hn
      obtain ⟨c, hc, rfl⟩ := liftR_stop hl
      exact .inl ⟨n, hc⟩
    · have h : ∀ n, ∃ x', Tool.runN step n x = .next x' := fun n => by
        obtain ⟨x', hx'⟩ := hdiv n
        have hl : liftR (Tool.runN step n x) = .next x' := by rw [← runN_asRes]; exact hx'
        exact ⟨x', liftR_next hl⟩
      exact .inr ⟨rfl, h⟩

/-! ## Mapped observations -/

/-- The outcome of a mapped stop. -/
def mapOut (g : O → O') : Outcome O → Outcome O'
  | .done [.val h] => .done [.val (g h)]
  | _ => .trap

/-- A machine result with mapped observations. -/
def mapR (g : O → O') : Res C O → Res C O'
  | .next y => .next y
  | .stop o => .stop (mapOut g o)

theorem mapObs_eq (g : O → O') (step : C → Res C O) (y : C) :
    mapObs g step y = mapR g (step y) := by
  unfold mapObs mapR mapOut
  cases step y with
  | next => rfl
  | stop o =>
    cases o with
    | trap => rfl
    | done vs =>
      match vs with
      | [] => rfl
      | [.val _] => rfl
      | [.cont _] => rfl
      | a :: _ :: _ => cases a <;> rfl

theorem runN_mapObs (g : O → O') (step : C → Res C O) :
    ∀ (n : Nat) (y : C), runN (mapObs g step) n y = mapR g (runN step n y)
  | 0, _ => rfl
  | n + 1, y => by
    have e : mapObs g step y = mapR g (step y) := mapObs_eq g step y
    cases hs : step y with
    | next y' =>
      have h1 : runN (mapObs g step) (n + 1) y = runN (mapObs g step) n y' := by
        simp only [runN, e, hs, mapR]
      have h2 : runN step (n + 1) y = runN step n y' := by simp only [runN, hs]
      rw [h1, h2]
      exact runN_mapObs g step n y'
    | stop o =>
      have h1 : runN (mapObs g step) (n + 1) y = mapR g (.stop o) := by
        simp only [runN, e, hs, mapR]
      have h2 : runN step (n + 1) y = .stop o := by simp only [runN, hs]
      rw [h1, h2]

theorem mapR_stop (g : O → O') (o : Outcome O) : mapR g (.stop o : Res C O) = .stop (mapOut g o) :=
  rfl

theorem mapOut_toObs (g : O → O') (o : Outcome O) : (mapOut g o).toObs = Obs.mapV g o.toObs := by
  cases o with
  | trap => rfl
  | done vs =>
    match vs with
    | [] => rfl
    | [.val _] => rfl
    | [.cont _] => rfl
    | a :: _ :: _ => cases a <;> rfl

theorem mapR_next {g : O → O'} {r : Res C O} {y : C} (h : mapR g r = .next y) : r = .next y := by
  cases r with
  | next y' => cases h; rfl
  | stop o => cases h

theorem beh_mapObs_sub (g : O → O') (step : C → Res C O) (y : C) :
    beh (mapObs g step) y ⊆ Obs.mapV g '' beh step y := by
  rintro b (⟨n, o, hn, rfl⟩ | ⟨rfl, hdiv⟩)
  · have hm : mapR g (runN step n y) = .stop o := by rw [← runN_mapObs]; exact hn
    cases hr : runN step n y with
    | next y' => exact absurd (hr ▸ hm) (by simp only [mapR, reduceCtorEq, not_false_eq_true])
    | stop o₀ =>
      have ho : mapOut g o₀ = o := Res.stop.inj (hr ▸ hm)
      exact ⟨o₀.toObs, .inl ⟨n, o₀, hr, rfl⟩, by rw [← ho, mapOut_toObs]⟩
  · have h : ∀ n, ∃ y', runN step n y = .next y' := fun n => by
      obtain ⟨y', hy'⟩ := hdiv n
      have hm : mapR g (runN step n y) = .next y' := by rw [← runN_mapObs]; exact hy'
      exact ⟨y', mapR_next hm⟩
    exact ⟨.diverges, .inr ⟨rfl, h⟩, rfl⟩

theorem beh_mapObs_sup (g : O → O') (step : C → Res C O) (y : C) :
    Obs.mapV g '' beh step y ⊆ beh (mapObs g step) y := by
  rintro _ ⟨b', (⟨n, o, hn, rfl⟩ | ⟨rfl, hdiv⟩), rfl⟩
  · have h : runN (mapObs g step) n y = .stop (mapOut g o) := by
      rw [runN_mapObs, hn, mapR_stop]
    exact .inl ⟨n, _, h, (mapOut_toObs g o).symm⟩
  · have h : ∀ n, ∃ y', runN (mapObs g step) n y = .next y' := fun n => by
      obtain ⟨y', hy'⟩ := hdiv n
      exact ⟨y', by rw [runN_mapObs, hy']; rfl⟩
    exact .inr ⟨rfl, h⟩

/-- **The behaviours of a machine with mapped observations** are the mapped behaviours. -/
theorem beh_mapObs (g : O → O') (step : C → Res C O) (y : C) :
    beh (mapObs g step) y = Obs.mapV g '' beh step y :=
  Set.Subset.antisymm (beh_mapObs_sub g step y) (beh_mapObs_sup g step y)

/-! ## A deterministic step -/

/-- **A continuing step does not change the behaviours.** -/
theorem beh_next_eq {V : Type} {step : C → Res C V} {c c' : C} (h : step c = .next c') :
    beh step c = beh step c' := by
  have hs : ∀ n, runN step (n + 1) c = runN step n c' := fun n => by simp only [runN, h]
  ext b
  constructor
  · rintro (⟨n, o, hn, rfl⟩ | ⟨rfl, hdiv⟩)
    · cases n with
      | zero => cases hn
      | succ n => exact .inl ⟨n, o, (hs n).symm.trans hn, rfl⟩
    · exact .inr ⟨rfl, fun n => by rw [← hs n]; exact hdiv (n + 1)⟩
  · rintro (⟨n, o, hn, rfl⟩ | ⟨rfl, hdiv⟩)
    · exact .inl ⟨n + 1, o, (hs n).trans hn, rfl⟩
    · exact .inr ⟨rfl, fun n => by
        cases n with
        | zero => exact ⟨c, rfl⟩
        | succ n => rw [hs n]; exact hdiv n⟩

/-- `obsOut` is `backObs` after `Obs.mapV toolOut`. -/
theorem obsOut_eq (b : Obs (Host.HOut KV σ)) : obsOut b = backObs (Obs.mapV toolOut b) := by
  cases b with
  | trap => rfl
  | diverges => rfl
  | done vs =>
    match vs with
    | [] => rfl
    | [.val _] => rfl
    | [.cont _] => rfl
    | a :: _ :: _ => cases a <;> rfl

end Silmaril.Proofs.Wasm.FX.Asyncify.Bridge
