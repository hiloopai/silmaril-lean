module

public import Silmaril.Wasm.Component.BinaryP3.Project.Defs
public import Silmaril.Wasm.Component.BinaryP3.Thms

/-!
# Index scoping and WIT projection with async built-ins: conservativity

**PROVED**: on the embedding `Ast.ofV0` of the old syntax,

* `shadow_ofV0 : (Ast.ofV0 c).shadow = c`;
* `projectX3_ofV0 : projectX3 (Ast.ofV0 c) = projectX c`;
* `wellScopedC3_ofV0 : wellScopedC3 (Ast.ofV0 c) = wellScopedC c`;
* `topV0_ofV0 : topV0 (Ast.ofV0 c) = true`, and `not_parse_v0`: when the new parser reads
  `b` as a component `c` with `topV0 c = false`, the old parser does not read `b`.

So the lifted projection and check extend the old ones; they differ only on the
built-ins the old syntax lacks.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryP3

open Silmaril.Wasm.Wit.Project (CCount cStep cCheck splitSection projectX wellScopedC)

theorem toV0_ofV0 (x : Binary.Canon) : (Canon.ofV0 x).toV0? = some x := by
  cases x <;> rfl

theorem filterMap_toV0 : ∀ xs : List Binary.Canon,
    (xs.map Canon.ofV0).filterMap Canon.toV0? = xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.filterMap_cons, toV0_ofV0, filterMap_toV0 xs]

mutual
theorem section_shadow_ofV0 : ∀ s : Binary.Section, (Section.ofV0 s).shadow = s
  | .component c => by simp only [Section.ofV0, Section.shadow, ast_shadow_ofV0 c]
  | .canons xs => by simp only [Section.ofV0, Section.shadow, filterMap_toV0]
  | .custom .. | .coreModule _ | .coreInstances _ | .coreTypes _ | .instances _ | .aliases _
  | .types _ | .start _ | .imports _ | .exports _ | .values _ => rfl

theorem list_shadow_ofV0 : ∀ ss : List Binary.Section,
    Section.listShadow (Section.listOfV0 ss) = ss
  | [] => rfl
  | s :: ss => by
    simp only [Section.listOfV0, Section.listShadow, section_shadow_ofV0 s, list_shadow_ofV0 ss]

theorem ast_shadow_ofV0 : ∀ c : Binary.Ast, (Ast.ofV0 c).shadow = c
  | .mk ss => by simp only [Ast.ofV0, Ast.shadow, list_shadow_ofV0 ss]
end

/-- **The shadow of an embedded old component is that component.** -/
theorem shadow_ofV0 (c : Binary.Ast) : (Ast.ofV0 c).shadow = c := ast_shadow_ofV0 c

/-- **The lifted projection extends the old one.** -/
theorem projectX3_ofV0 (c : Binary.Ast) : projectX3 (Ast.ofV0 c) = projectX c := by
  simp only [projectX3, shadow_ofV0]

theorem listOfV0_map : ∀ ss : List Binary.Section, Section.listOfV0 ss = ss.map Section.ofV0
  | [] => rfl
  | s :: ss => by simp only [Section.listOfV0, List.map_cons, listOfV0_map ss]

theorem sections_ofV0 (c : Binary.Ast) : (Ast.ofV0 c).sections = c.sections.map Section.ofV0 := by
  cases c with
  | mk ss => simp only [Ast.ofV0, Ast.sections, Binary.Ast.sections, listOfV0_map]

theorem split_ofV0 (s : Binary.Section) :
    splitSection3 (Section.ofV0 s) = (splitSection s).map Section.ofV0 := by
  cases s <;>
    simp only [Section.ofV0, splitSection3, splitSection, List.map_map, Function.comp_def,
      List.map_cons, List.map_nil]

theorem step_ofV0 (k : CCount) (s : Binary.Section) : cStep3 k (Section.ofV0 s) = cStep k s := by
  cases s
  case canons xs =>
    match xs with
    | [] => rfl
    | [x] => cases x <;> rfl
    | x :: y :: ys =>
      show cStep k (Section.shadow (.canons ((x :: y :: ys).map Canon.ofV0))) = _
      simp only [Section.shadow, filterMap_toV0]
  all_goals rfl

theorem check_ofV0 : ∀ (k : CCount) (l : List Binary.Section),
    cCheck3 k (l.map Section.ofV0) = cCheck k l
  | _, [] => rfl
  | k, s :: l => by
    simp only [List.map_cons, cCheck3, cCheck, step_ofV0]
    cases cStep k s with
    | none => rfl
    | some k' => simp only [Option.bind_some, check_ofV0 k' l]

theorem flatMap_split_ofV0 : ∀ l : List Binary.Section,
    (l.map Section.ofV0).flatMap splitSection3 = (l.flatMap splitSection).map Section.ofV0
  | [] => rfl
  | s :: l => by
    simp only [List.map_cons, List.flatMap_cons, split_ofV0, List.map_append,
      flatMap_split_ofV0 l]

/-- **The lifted check extends the old one.** -/
theorem wellScopedC3_ofV0 (c : Binary.Ast) : wellScopedC3 (Ast.ofV0 c) = wellScopedC c := by
  simp only [wellScopedC3, wellScopedC, sections_ofV0, flatMap_split_ofV0, check_ofV0]

theorem all_toV0_map : ∀ xs : List Binary.Canon,
    (xs.map Canon.ofV0).all (fun x => x.toV0?.isSome) = true
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.all_cons, toV0_ofV0, Option.isSome_some, Bool.true_and,
      all_toV0_map xs]

theorem topV0_ofV0 (c : Binary.Ast) : topV0 (Ast.ofV0 c) = true := by
  rw [topV0, sections_ofV0, List.all_eq_true]
  intro s hs
  obtain ⟨s₀, -, rfl⟩ := List.mem_map.mp hs
  cases s₀
  case canons xs => exact all_toV0_map xs
  all_goals rfl

/-- **The old parser rejects a file with top-level async built-ins.** -/
theorem not_parse_v0 {b : ByteArray} {c : Ast} (h : parse b = .ok c) (hc : topV0 c = false) :
    ∀ c₀ : Binary.Ast, Binary.parse b ≠ .ok c₀ := by
  intro c₀ h₀
  have e := parse_ofV0 h₀
  rw [h] at e
  cases e
  rw [topV0_ofV0] at hc
  cases hc

end Silmaril.Wasm.Component.BinaryP3

end
