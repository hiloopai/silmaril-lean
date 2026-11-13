module

public import Silmaril.Proofs.Wasm.Models.FXSurplus.Typed
public import Silmaril.Wasm.Models.FXPresI.Thms

/-!
# Surplus operands add behaviours; `StepFX'` is neither deterministic nor type-preserving

* `beh_surplus`, `beh_tight`, `beh_arg`: `[1]`, `[1, 7]` and `[7, 1]` are `StepFX'` results of
  `surC`, at every profile, host and FX function table;
* `typed_not_one`: no `StepFXS` run of `surC` ends with one `i32` (by `FXPresI` preservation and
  `end_one_not_ok`), so `[1]` is not a typed behaviour (`not_behS_surplus`), while `[1, 7]` is
  (`behS_tight`);
* `not_subsingleton`: the `StepFX'` behaviours of `surC` are not a subsingleton;
* `not_presV`: preservation fails for `StepFX'` (`PresV surM` is false).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXSurplus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXSurplus Silmaril.Wasm.Models.FXResumeT
open Silmaril.Wasm.Models.FXPres Silmaril.Wasm.Models.FXPresI
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- A run ending with the values `vs` gives the behaviour `returns vs`. -/
theorem mem_of_run {K : List (Option ContFX)} {vs : List Val}
    (h : StepsFX' P host fx (surC H) (surEnd H K ((vals vs).map .core))) :
    .returns vs ∈ behavioursFX' P host fx (surC H) :=
  Or.inl ⟨_, .values vs, h, rfl, rfl⟩

/-- **`[1]` is a `StepFX'` result** (surplus payload). -/
theorem beh_surplus : .returns [Val.i32 1] ∈ behavioursFX' P host fx (surC H) :=
  mem_of_run run_surplus

/-- **`[1, 7]` is a `StepFX'` result** (tight payload). -/
theorem beh_tight : .returns [Val.i32 1, Val.i32 7] ∈ behavioursFX' P host fx (surC H) :=
  mem_of_run run_tight

/-- **`[7, 1]` is a `StepFX'` result** (tight payload, `resume` with an argument). -/
theorem beh_arg : .returns [Val.i32 7, Val.i32 1] ∈ behavioursFX' P host fx (surC H) :=
  mem_of_run run_arg

/-- **The `StepFX'` behaviours of `surC` are not a subsingleton.** -/
theorem not_subsingleton : ¬ (behavioursFX' P host fx (surC H)).Subsingleton := by
  intro h
  have := h (beh_surplus (P := P) (host := host) (fx := fx)) beh_tight
  simp at this

/-- **`[1, 7]` is a typed behaviour.** -/
theorem behS_tight : .returns [Val.i32 1, Val.i32 7] ∈ behavioursFXS P host fx (surC H) :=
  Or.inl ⟨_, .values [Val.i32 1, Val.i32 7], run_typed, rfl, rfl⟩

/-- **No typed run of `surC` ends with one `i32`.** -/
theorem typed_not_one {d : ConfigFX H} {n : BitVec 32} (h : StepsFXS P host fx (surC H) d) :
    d.code ≠ [c32 n] := by
  intro hd
  obtain ⟨Γ', -, -, hok⟩ := preservationI_steps h surC_ok
  have h₃ := hok.2.2
  rw [hd] at h₃
  exact tl_one_not h₃

/-- **`[1]` is not a typed behaviour**: the surplus payload adds it. -/
theorem not_behS_surplus : .returns [Val.i32 1] ∉ behavioursFXS P host fx (surC H) := by
  rintro (⟨d, r, hd, hc, hb⟩ | ⟨hb, -⟩)
  · cases r with
    | values vs =>
      simp only [Result.toBehaviour, Behaviour.returns.injEq] at hb
      subst hb
      exact typed_not_one (n := 1) hd hc
    | throw a => simp [Result.toBehaviour] at hb
    | trap => simp [Result.toBehaviour] at hb
  · simp at hb

/-- **Preservation fails for `StepFX'`**: along the surplus run, the typed `surC` reaches the
untyped `[1]`. -/
theorem not_presV : ¬ PresV surM P host fx := by
  intro hp
  have key : ∀ {c d : ConfigFX H}, StepsFX' P host fx c d →
      ∀ {Γ : List TypeIdx} {ts : List FTy}, ConfigOk (envP surM) Γ c ts →
        ∃ Γ', ConfigOk (envP surM) Γ' d ts := by
    intro c d h
    induction h with
    | refl => exact fun hc => ⟨_, hc⟩
    | tail _ hs ih =>
      intro Γ ts hc
      obtain ⟨Γ₁, h₁⟩ := ih hc
      exact hp _ _ _ _ hs h₁
  obtain ⟨Γ', hok⟩ := key run_surplus surC_ok
  exact end_one_not_ok hok

end Silmaril.Proofs.Wasm.Models.FXSurplus
