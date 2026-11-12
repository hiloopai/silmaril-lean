module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Decode

/-!
# Float track: what Core's conversions allow

`convertP P op x` is the profile's relation between an input and a result or trap. Every
conversion other than `promote`/`demote` is deterministic under every profile
(`convertP_iff_det`); `promote`/`demote` never trap (`convertP_error_resize`). From this, the
result lists `floatCall` returns satisfy `FloatAgree.cvtop`'s two conditions
(`agree_single`, `agree_opt`, `agree_list`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Floats

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics

variable {P : Profile}

/-- The conversions that do not change a float's width. -/
def Det (op : ConvertOp) : Prop := op ≠ .promote ∧ op ≠ .demote

/-- Core's own result is always allowed. -/
theorem convertP_self (P : Profile) (op : ConvertOp) (x : BitVec op.source.width) :
    convertP P op x (convert op x) := by
  unfold convertP
  cases P.nan
  · exact convertRel_self op x
  · rfl

/-- **The deterministic conversions** allow exactly Core's result. -/
theorem convertP_iff_det {op : ConvertOp} (hop : Det op) (x : BitVec op.source.width)
    (r : Except FloatTrap (BitVec op.target.width)) :
    convertP P op x r ↔ r = convert op x := by
  unfold convertP
  cases P.nan
  · cases op <;> first
      | exact absurd rfl hop.1
      | exact absurd rfl hop.2
      | (cases r <;> exact Iff.rfl)
  · exact Iff.rfl

/-- `promote`/`demote` never trap. -/
theorem convertP_error_resize {op : ConvertOp} (hop : op = .promote ∨ op = .demote)
    (x : BitVec op.source.width) (e : FloatTrap) : ¬ convertP P op x (.error e) := by
  unfold convertP
  rcases hop with rfl | rfl <;> cases P.nan <;> simp [convertRel, convert]

/-- The single result of a deterministic conversion that succeeds. -/
theorem agree_single {op : ConvertOp} (hop : Det op) {x : BitVec op.source.width}
    {w : BitVec op.target.width} (hw : convert op x = .ok w) :
    (∀ c, c ∈ [numV ⟨op.target, w⟩] ↔ ∃ z, convertP P op x (.ok z) ∧ c = numV ⟨op.target, z⟩) ∧
      ([numV ⟨op.target, w⟩] = [] ↔ ∃ e, convertP P op x (.error e)) := by
  refine ⟨fun c => ?_, ?_⟩
  · simp only [List.mem_singleton, convertP_iff_det hop, hw, Except.ok.injEq]
    exact ⟨fun h => ⟨w, rfl, h⟩, fun ⟨z, hz, h⟩ => hz ▸ h⟩
  · simp only [List.cons_ne_nil, false_iff, convertP_iff_det hop, hw]
    exact fun ⟨e, he⟩ => nomatch he

/-- `convRes` of a deterministic conversion is Core's result. -/
theorem convRes_det {op : ConvertOp} (hop : Det op) (x : BitVec op.source.width) :
    convRes P op x = match convert op x with | .ok z => some z | .error _ => none := by
  unfold convRes
  split
  · rename_i h
    have hs := Classical.choose_spec h
    rw [convertP_iff_det hop] at hs
    rw [← hs]
  · rename_i h
    cases hc : convert op x with
    | ok z => exact absurd ⟨z, (convertP_iff_det hop x _).2 hc.symm⟩ h
    | error e => rfl

/-- The option result of a deterministic conversion. -/
theorem agree_opt {op : ConvertOp} (hop : Det op) (x : BitVec op.source.width) :
    let L := ((convRes P op x).map fun z => numV ⟨op.target, z⟩).toList
    (∀ c, c ∈ L ↔ ∃ z, convertP P op x (.ok z) ∧ c = numV ⟨op.target, z⟩) ∧
      (L = [] ↔ ∃ e, convertP P op x (.error e)) := by
  intro L
  have hr : convRes P op x = match convert op x with | .ok z => some z | .error _ => none :=
    convRes_det hop x
  cases hc : convert op x with
  | ok w =>
      have hL : L = [numV ⟨op.target, w⟩] := by
        show ((convRes P op x).map _).toList = _
        rw [hr, hc]
        rfl
      rw [hL]
      exact agree_single hop hc
  | error e =>
      have hL : L = [] := by
        show ((convRes P op x).map _).toList = _
        rw [hr, hc]
        rfl
      have hno : ∀ z, ¬ convertP P op x (.ok z) := fun z hz =>
        nomatch ((convertP_iff_det hop x _).1 hz).trans hc
      rw [hL]
      exact ⟨fun c => ⟨fun h => (nomatch h), fun ⟨z, hz, _⟩ => absurd hz (hno z)⟩,
        ⟨fun _ => ⟨e, (convertP_iff_det hop x _).2 hc.symm⟩, fun _ => rfl⟩⟩

/-- The list result of `promote`/`demote`. -/
theorem agree_list {op : ConvertOp} (hop : op = .promote ∨ op = .demote)
    {x : BitVec op.source.width} {w : BitVec op.target.width} (hw : convert op x = .ok w) :
    let L := (bitsWhere op.target.width (fun z => convertP P op x (.ok z))).map
      fun z => numV ⟨op.target, z⟩
    (∀ c, c ∈ L ↔ ∃ z, convertP P op x (.ok z) ∧ c = numV ⟨op.target, z⟩) ∧
      (L = [] ↔ ∃ e, convertP P op x (.error e)) := by
  intro L
  refine ⟨fun c => mem_map_bitsWhere, ⟨fun hL => ?_, fun ⟨e, he⟩ => ?_⟩⟩
  · have hm : numV ⟨op.target, w⟩ ∈ L :=
      mem_map_bitsWhere.2 ⟨w, hw ▸ convertP_self P op x, rfl⟩
    rw [hL] at hm
    exact absurd hm List.not_mem_nil
  · exact absurd he (convertP_error_resize hop x e)

end Silmaril.Wasm.SpecTec.Sim.Floats
