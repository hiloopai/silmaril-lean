module

public import Silmaril.Project.Shapes.WasmWastRef.Defs
public import Silmaril.Wasm.Execution.Core.Instantiation

/-!
# Proofs: WAST host references

* `valOk_of_argOkR`, `valOk_of_argsOkR`: an accepted argument is typed (`RefOk.extern` of
  `RefOk.host` for `(ref.extern n)`, with `Reftype_sub/null` for a nullable parameter);
* `invokeOk_of_invokeOkRB`: accepted arguments give the premise `InvokeOk` of `$invoke`;
* `matchAll_sound`: the decision `matchAll` is sound for `MatchAll`.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.Shapes.WasmWastRef

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Project.Shapes.WasmWastRef

theorem valOk_of_argOkR {s : Store Nat} {v : Val} {p : CValType} (h : argOkR v p = true) :
    ValOk s v p := by
  match v, p, h with
  | .num n, p, h =>
    simp only [argOkR, decide_eq_true_eq] at h
    subst h
    exact .num n
  | .ref (.extern (.host k)), .refv (.ref nul (.abs .extern)), _ =>
    have hx : RefOk s (.extern (.host k)) (.ref false (.abs .extern)) :=
      .extern (.host k) (by simp)
    cases nul with
    | false => exact .ref hx
    | true => exact .ref (.sub hx (.ref (.abs _)) (.refNull .heapRefl))

theorem valOk_of_argsOkR {s : Store Nat} :
    ∀ {vs : List Val} {ps : List CValType}, argsOkR vs ps = true → List.Forall₂ (ValOk s) vs ps
  | [], [], _ => .nil
  | v :: vs, p :: ps, h => by
    simp only [argsOkR, Bool.and_eq_true] at h
    exact .cons (valOk_of_argOkR h.1) (valOk_of_argsOkR h.2)
  | [], _ :: _, h => by simp [argsOkR] at h
  | _ :: _, [], h => by simp [argsOkR] at h

theorem invokeOk_of_invokeOkRB {s : Store Nat} {a : Nat} {args : List Val}
    (h : invokeOkRB s a args = true) : InvokeOk s a args := by
  unfold invokeOkRB at h
  split at h
  · rename_i fi hfi
    split at h
    · rename_i ps rs hft
      unfold DefType.funcType? at hft
      split at hft
      · rename_i P R hex
        simp only [Option.some.injEq, Prod.mk.injEq] at hft
        obtain ⟨rfl, rfl⟩ := hft
        exact ⟨fi, P, R, hfi, Expand.iff.mpr hex, valOk_of_argsOkR h⟩
      · cases hft
    · cases h
  · cases h

theorem matches_sound {p : Pat} {v : Val} (h : p.matches v = true) : p.Matches v := by
  cases p with
  | exact w => simpa [Pat.matches, Pat.Matches] using h
  | funcRef =>
    match v, h with
    | .ref (.func a), _ => exact ⟨a, rfl⟩

theorem matchAll_sound : ∀ {ps : List Pat} {vs : List Val}, matchAll ps vs = true → MatchAll ps vs
  | [], [], _ => .nil
  | p :: ps, v :: vs, h => by
    simp only [matchAll, Bool.and_eq_true] at h
    exact .cons (matches_sound h.1) (matchAll_sound h.2)
  | [], _ :: _, h => by simp [matchAll] at h
  | _ :: _, [], h => by simp [matchAll] at h

end Silmaril.Proofs.Project.Shapes.WasmWastRef

end
