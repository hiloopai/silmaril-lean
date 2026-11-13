module

public import Silmaril.Wasm.Unified.Versions.OwnV.Defs
public import Silmaril.Wasm.Unified.Versions.Own.Thms

/-!
# The own syntaxes are coherent (unrefined)

`cohL`, `coh10`, `coh20`: the translations of Lime1, 1.0 (through Lime1) and 2.0 into Core 3.0
translate the bodies of an instruction to the bodies of its image. `tr_map`, `eq_map_of_tr`:
translation by a total map; `tr_of_mapM`: translation by a partial one.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.Unified.Own

open Silmaril.Wasm Silmaril.Wasm.Unified.Versions.Own

/-- Translation by a total map. -/
theorem tr_map {L : Syn} {g : L.J → Instr} (hg : ∀ j, L.tr j = some (g j)) :
    (js : List L.J) → L.Tr js (js.map g)
  | [] => .nil
  | j :: js => .cons (hg j) (tr_map hg js)

/-- Translation by a total map is the map. -/
theorem eq_map_of_tr {L : Syn} {g : L.J → Instr} (hg : ∀ j, L.tr j = some (g j))
    {js : List L.J} {is : List Instr} (h : L.Tr js is) : is = js.map g :=
  Syn.tr_unique h (tr_map hg js)

/-- Translation by a partial map. -/
theorem tr_of_mapM {L : Syn} : {js : List L.J} → {is : List Instr} → js.mapM L.tr = some is →
    L.Tr js is
  | [], is, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact .nil
  | j :: js, is, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨i, hi, is', his, rfl⟩ := h
    exact .cons hi (tr_of_mapM his)

/-- **Lime1 is coherent.** -/
theorem cohL : synL.Coh := by
  intro j i h
  cases Option.some.inj h
  have hm := tr_map (L := synL) (g := Lime1.Instr.toCore) (fun _ => rfl)
  cases j <;> simp only [Lime1.Instr.toCore, Instr.bodies, Lime1.Expr.toCore_eq_map] <;>
    first
    | exact .nil
    | exact .cons (hm _) .nil
    | exact .cons (hm _) (.cons (hm _) .nil)

/-- **Wasm 1.0 (through Lime1) is coherent.** -/
theorem coh10 : syn10.Coh := by
  intro j i h
  cases Option.some.inj h
  have hm := tr_map (L := syn10) (g := fun j => j.toLime.toCore) (fun _ => rfl)
  cases j <;>
    simp only [V1.Instr.toLime, Lime1.Instr.toCore, Instr.bodies,
      V1.Expr.toLime_eq_map, Lime1.Expr.toCore_eq_map, List.map_map, Function.comp_def] <;>
    first
    | exact .nil
    | exact .cons (hm _) .nil
    | exact .cons (hm _) (.cons (hm _) .nil)

/-- **Wasm 2.0 is coherent.** -/
theorem coh20 : syn20.Coh := by
  intro j i h
  cases j <;> simp only [syn20, V2.Instr.toCore, V2.Instr.bodies, Option.map_eq_some_iff,
      Option.bind_eq_some_iff, Option.some.injEq] at h ⊢
  all_goals first
    | (subst h; exact .nil)
    | (obtain ⟨_, _, rfl⟩ := h; exact .nil)
    | (obtain ⟨cs, hcs, rfl⟩ := h
       exact .cons (tr_of_mapM (by rw [← V2.Expr.toCore_eq_mapM]; exact hcs)) .nil)
    | (obtain ⟨l, hl, r, hr, rfl⟩ := h
       exact .cons (tr_of_mapM (by rw [← V2.Expr.toCore_eq_mapM]; exact hl))
         (.cons (tr_of_mapM (by rw [← V2.Expr.toCore_eq_mapM]; exact hr)) .nil))

end Silmaril.Raw.Wasm.Unified.Own
