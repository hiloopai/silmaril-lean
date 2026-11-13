module

public import Silmaril.Wasm.Validation.SubCheckR.Defs

/-!
# `Sub.checkR`: theorems

* `Sub.checkR_sound`: soundness, unconditionally.
* `TypeCtx.oracleOk_tyOk_check`: in a well-formed context whose `RECS` form a valid group,
  `TyOk.check` accepts every `_DEF` supertype of a `RECS` entry. This is new: the source states
  completeness under the oracle hypothesis `Δ.OracleOk (TyOk.check Δ)` and notes that
  `TyOk.check` was not proved complete. silmaril-lean now proves it complete
  (`TyOk.check_complete'`), which discharges the hypothesis.
* `Sub.checkR_complete`, `Sub.checkR_iff`: completeness and the decision property on valid
  types, under `Δ.Ok` and `Δ.RecsOk` only.

Ported from an earlier development `Silmaril/Wasm/Validation/Subtyping/CheckRecsTyOk.lean`.
The source's `Sub.checkR_complete_of_nil` is subsumed (`TypeCtx.recsOk_of_nil` gives `RecsOk`
when there are no `RECS`) and dropped.
-/

@[expose] public section

namespace Silmaril.Wasm.Validation

open Silmaril.Wasm.Validation

/-- **Soundness** of `Sub.checkR`. -/
theorem Sub.checkR_sound {Δ : TypeCtx} {k : TKind} {a b : Ty k}
    (h : Sub.checkR Δ a b = true) : Sub Δ a b :=
  Sub.checkRWith_sound (fun _ hd => TyOk.check_sound hd) h

/-- The declared supertypes of a valid `RECS` entry pass `TyOk.check`. -/
theorem TypeCtx.oracleOk_tyOk_check {Δ : TypeCtx} (hΔ : Δ.Ok) (hR : Δ.RecsOk) :
    Δ.OracleOk (fun d => TyOk.check Δ d) := by
  intro i st d hi hmem
  have hsub : SubOk2 Δ st i := hR i st hi
  cases hsub with
  | noSuper => exact absurd hmem List.not_mem_nil
  | @oneSuper _ _ u _ _ _ _ hu =>
    have hmem' : Ty.dt d ∈ [u] := hmem
    have hu_eq : Ty.dt d = u := List.mem_singleton.mp hmem'
    have hu' : TyOk Δ (Ty.dt d) := hu_eq ▸ hu
    cases hu' with
    | dt hd => exact TyOk.check_complete' hΔ hd

/-- **Completeness** of `Sub.checkR` on valid types, in a well-formed context whose `RECS` form
a valid group. -/
theorem Sub.checkR_complete {Δ : TypeCtx} (hΔ : Δ.Ok) (hR : Δ.RecsOk) {k : TKind}
    {a b : Ty k} (h : Sub Δ a b) (ha : TyOk Δ a) (hb : TyOk Δ b) : Sub.checkR Δ a b = true :=
  Sub.checkRWith_complete hΔ hR (TypeCtx.oracleOk_tyOk_check hΔ hR) h ha hb

/-- `Sub.checkR` decides subtyping between valid types under valid `RECS`. -/
theorem Sub.checkR_iff {Δ : TypeCtx} (hΔ : Δ.Ok) (hR : Δ.RecsOk) {k : TKind} {a b : Ty k}
    (ha : TyOk Δ a) (hb : TyOk Δ b) : Sub.checkR Δ a b = true ↔ Sub Δ a b :=
  ⟨Sub.checkR_sound, fun h => Sub.checkR_complete hΔ hR h ha hb⟩

end Silmaril.Wasm.Validation
