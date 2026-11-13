module

public import Silmaril.Wasm.Component.Lime1Bridge.Thms
public import Silmaril.Wasm.Instantiation.Thms

/-!
# Allocation does not read element-segment types

`allocModule?` uses the type of an element segment only for the type of its element instance.
Element instances are dropped by `Lime1.Execution.ToCore.Store.erase`, so two modules that differ
only in their element types allocate stores that agree up to the element types:

* `ElemRetype S S'`: `S'` is `S` with other element types (same element references);
* `allocModule?_elems`: allocation of `{M with elems := es}` for `es` of the same length.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Inst

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- `S'` is `S` up to the types of its element instances. -/
def ElemRetype (S S' : Store H) : Prop :=
  S' = { S with elems := S'.elems } ∧ S'.elems.map (·.refs) = S.elems.map (·.refs)

theorem map_snd_zip_eq {α β γ : Type _} :
    ∀ {as : List α} {bs : List β} (l : List γ), as.length = bs.length →
      (as.zip l).map Prod.snd = (bs.zip l).map Prod.snd
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, [], _ => rfl
  | _ :: as, _ :: bs, c :: l, h => by
    simp only [List.zip_cons_cons, List.map_cons, map_snd_zip_eq (as := as) (bs := bs) l
      (by simpa using h)]

theorem allocModule?_elems {s : Store H} {M : Module} {es : List Elem}
    (hl : es.length = M.elems.length) {xas : List ExternAddr} {vG : List Val} {rT : List Ref}
    {rE : List (List Ref)} {S : Store H} {mi : ModuleInst}
    (h : allocModule? s M xas vG rT rE = some (S, mi)) :
    ∃ S', allocModule? s { M with elems := es } xas vG rT rE = some (S', mi) ∧ ElemRetype S S' := by
  unfold allocModule? at h ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Silmaril.Wasm.Lime1.Execution.allocMany_elem, Silmaril.Wasm.Lime1.Execution.allocMany_func,
    Prod.mk.injEq] at h ⊢
  obtain ⟨tt, htt, ft, hft, xi, hxi, rfl, rfl⟩ := h
  refine ⟨_, ⟨tt, htt, ft, hft, xi, ?_, rfl, ?_⟩, ?_⟩
  · exact hxi
  all_goals simp only [List.length_zip, List.length_map, hl]
  refine ⟨rfl, ?_⟩
  have hz : ∀ (ts us : List Validation.CRefType), ts.length = us.length →
      ((ts.zip rE).map fun p => (⟨p.1, p.2⟩ : ElemInst)).map (·.refs) =
        ((us.zip rE).map fun p => (⟨p.1, p.2⟩ : ElemInst)).map (·.refs) := fun ts us h => by
    simpa only [List.map_map, Function.comp_def] using map_snd_zip_eq rE h
  simp only [List.map_append]
  rw [hz _ _ (by simp only [List.length_map, hl] : (es.map _).length = (M.elems.map _).length)]

end Silmaril.Proofs.Wasm.Component.Lime1Inst
