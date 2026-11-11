module

public import Silmaril.Wasm.SSA.Bridge.Defs

/-! # Recognised functions have integer types -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Pipeline

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.SSA

theorem mapM_ofValType? : ∀ {ts : List ValType} {us : List IntType},
    ts.mapM ofValType? = some us → ts = us.map fun t => .num (.int t)
  | [], us, h => by simp at h; subst h; rfl
  | t :: ts, us, h => by
      rw [List.mapM_cons] at h
      cases ht : ofValType? t with
      | none => simp [ht] at h
      | some u =>
          cases hts : ts.mapM ofValType? with
          | none => simp [ht, hts] at h
          | some us' =>
              simp only [ht, hts, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq] at h
              subst h
              have : t = .num (.int u) := by
                cases t with
                | num n => cases n with
                  | int i => simp [ofValType?] at ht; subst ht; rfl
                  | float => simp [ofValType?] at ht
                | _ => simp [ofValType?] at ht
              simp [this, mapM_ofValType? hts]

theorem ofBFunc?_types {ft : FuncType} {bf : BFunc} {f : FragFunc} (h : ofBFunc? ft bf = some f) :
    ft.params = f.params.map (fun t => .num (.int t)) ∧ ft.results = resultTypes f.result := by
  obtain ⟨params, results⟩ := ft
  rcases results with _ | ⟨t, _ | ⟨t₂, rest⟩⟩
  · simp only [ofBFunc?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ps, hp, res, hr, ls, -, b, -, rfl⟩ := h
    subst hr
    exact ⟨mapM_ofValType? hp, rfl⟩
  · simp only [ofBFunc?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ps, hp, res, hr, ls, -, b, -, rfl⟩ := h
    cases ht : ofValType? t with
    | none => simp [ht] at hr
    | some u =>
        simp [ht] at hr; subst hr
        have := mapM_ofValType? (ts := [t]) (us := [u]) (by simp [ht])
        exact ⟨mapM_ofValType? hp, by simpa [resultTypes] using this⟩
  · simp [ofBFunc?] at h

end Silmaril.Proofs.Wasm.SSA.Pipeline
