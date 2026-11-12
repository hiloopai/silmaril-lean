module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Script.Assemble
public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Thms

/-!
# Round 7: what the evaluator looks up from a reachable name

The closure facts of `Assemble.lean` are about the items of the script. The evaluator does not
see items: it looks definitions, relations and types up in an environment (`Env.findDef?`,
`findRel?`, `findTyp?`). This file connects the two, for `simEnv B` and `utf8Env B`:

* whatever `findDef?`, `findRel?` or `findTyp?` returns for `x` is the body of an item of the
  fixed script named `x` (`findDef?_simEnv_item`, `findRel?_simEnv_item`,
  `findTyp?_simEnv_item`), except `$utf8` in `utf8Env B`, which has no clauses
  (`findDef?_utf8Env_item`);
* so, for a reachable name, every event of the body is `evOk` and every reference is reachable
  (`findDef?_reach`, `findRel?_reach`, `findTyp?_reach`).

A later induction over the evaluator can thread the property "every event of this term is
`evOk` and its references are in `stepReach`" through `callDef`, `derives` and typing with these.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Script

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.IL hiding Id Prod

/-- The events of a definition's signature and clauses, as `defItems` records them. -/
def defDefEv (v : DefDef) : List Ev := evParams v.1 ++ evTyp v.2.1 ++ v.2.2.flatMap evClause

/-- The events of a relation's signature and rules. -/
def relDefEv (v : RelDef) : List Ev := evParams v.1 ++ evTyp v.2.2.1 ++ v.2.2.2.flatMap evRule

/-- The events of a type's parameters and instances. -/
def typDefEv (v : TypDef) : List Ev := evParams v.1 ++ v.2.flatMap evInst

theorem mem_of_find? {α : Type} : ∀ {m : Map α} {x : IL.Id} {v : α}, m.find? x = some v → (x, v) ∈ m
  | [], _, _, h => by simp at h
  | (y, w) :: m, x, v, h => by
    rw [Map.find?_cons] at h
    split at h
    · cases h; rename_i hy; subst hy; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_find? h)

theorem mem_bind_empty {α : Type} {x y : IL.Id} {v w : α} (h : (x, v) ∈ (Map.empty : Map α).bind y w) :
    x = y ∧ v = w := by
  unfold Map.bind at h
  split at h
  · simp [Map.empty] at h
  · simpa [Map.empty] using h

mutual
theorem mem_defsOfDef : ∀ (d : Def) {x : IL.Id} {v : DefDef}, (x, v) ∈ defsOfDef d →
    (1, x, defDefEv v) ∈ defItems d
  | .typD .., _, _, h => by simp [defsOfDef, Map.empty] at h
  | .relD .., _, _, h => by simp [defsOfDef, Map.empty] at h
  | .gramD .., _, _, h => by simp [defsOfDef, Map.empty] at h
  | .decD y ps t cls, _, _, h => by
    obtain ⟨rfl, rfl⟩ := mem_bind_empty h
    simp [defItems, defDefEv]
  | .recD ds, _, _, h => mem_defsOfDefs ds h

theorem mem_defsOfDefs : ∀ (ds : List Def) {x : IL.Id} {v : DefDef}, (x, v) ∈ defsOfDefs ds →
    (1, x, defDefEv v) ∈ defsItems ds
  | [], _, _, h => by simp [defsOfDefs, Map.empty] at h
  | d :: ds, _, _, h => by
    simp only [defsOfDefs, List.mem_append] at h
    simp only [defsItems, List.mem_append]
    rcases h with h | h
    · exact Or.inr (mem_defsOfDefs ds h)
    · exact Or.inl (mem_defsOfDef d h)
end

mutual
theorem mem_relsOfDef : ∀ (d : Def) {x : IL.Id} {v : RelDef}, (x, v) ∈ relsOfDef d →
    (0, x, relDefEv v) ∈ defItems d
  | .typD .., _, _, h => by simp [relsOfDef, Map.empty] at h
  | .decD .., _, _, h => by simp [relsOfDef, Map.empty] at h
  | .gramD .., _, _, h => by simp [relsOfDef, Map.empty] at h
  | .relD y ps op t rules, _, _, h => by
    obtain ⟨rfl, rfl⟩ := mem_bind_empty h
    simp [defItems, relDefEv]
  | .recD ds, _, _, h => mem_relsOfDefs ds h

theorem mem_relsOfDefs : ∀ (ds : List Def) {x : IL.Id} {v : RelDef}, (x, v) ∈ relsOfDefs ds →
    (0, x, relDefEv v) ∈ defsItems ds
  | [], _, _, h => by simp [relsOfDefs, Map.empty] at h
  | d :: ds, _, _, h => by
    simp only [relsOfDefs, List.mem_append] at h
    simp only [defsItems, List.mem_append]
    rcases h with h | h
    · exact Or.inr (mem_relsOfDefs ds h)
    · exact Or.inl (mem_relsOfDef d h)
end

mutual
theorem mem_typsOfDef : ∀ (d : Def) {x : IL.Id} {v : TypDef}, (x, v) ∈ typsOfDef d →
    (2, x, typDefEv v) ∈ defItems d
  | .relD .., _, _, h => by simp [typsOfDef, Map.empty] at h
  | .decD .., _, _, h => by simp [typsOfDef, Map.empty] at h
  | .gramD .., _, _, h => by simp [typsOfDef, Map.empty] at h
  | .typD y ps insts, _, _, h => by
    obtain ⟨rfl, rfl⟩ := mem_bind_empty h
    simp [defItems, typDefEv]
  | .recD ds, _, _, h => mem_typsOfDefs ds h

theorem mem_typsOfDefs : ∀ (ds : List Def) {x : IL.Id} {v : TypDef}, (x, v) ∈ typsOfDefs ds →
    (2, x, typDefEv v) ∈ defsItems ds
  | [], _, _, h => by simp [typsOfDefs, Map.empty] at h
  | d :: ds, _, _, h => by
    simp only [typsOfDefs, List.mem_append] at h
    simp only [defsItems, List.mem_append]
    rcases h with h | h
    · exact Or.inr (mem_typsOfDefs ds h)
    · exact Or.inl (mem_typsOfDef d h)
end

/-! ## Lookups in `simEnv B` and `utf8Env B` -/

theorem findDef?_envOfScript_item {s : Script} {x : IL.Id} {v : DefDef}
    (h : (envOfScript s).findDef? x = some v) : (1, x, defDefEv v) ∈ items s := by
  rw [envOfScript, envOfDefs_eq] at h
  have hm := mem_of_find? h
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact mem_defsOfDefs s hm
  · simp [Env.empty, Map.empty] at hm

theorem findRel?_envOfScript_item {s : Script} {x : IL.Id} {v : RelDef}
    (h : (envOfScript s).findRel? x = some v) : (0, x, relDefEv v) ∈ items s := by
  rw [envOfScript, envOfDefs_eq] at h
  have hm := mem_of_find? h
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact mem_relsOfDefs s hm
  · simp [Env.empty, Map.empty] at hm

theorem findTyp?_envOfScript_item {s : Script} {x : IL.Id} {v : TypDef}
    (h : (envOfScript s).findTyp? x = some v) : (2, x, typDefEv v) ∈ items s := by
  rw [envOfScript, envOfDefs_eq] at h
  have hm := mem_of_find? h
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact mem_typsOfDefs s hm
  · simp [Env.empty, Map.empty] at hm

theorem findDef?_simEnv_item {B : Builtins} {x : IL.Id} {v : DefDef}
    (h : (simEnv B).findDef? x = some v) : (1, x, defDefEv v) ∈ items Scripts.Wasm30.fixed :=
  by
    unfold simEnv baseEnv at h
    rw [Env.findDef?_withBuiltins] at h
    exact findDef?_envOfScript_item h

theorem findRel?_simEnv_item {B : Builtins} {x : IL.Id} {v : RelDef}
    (h : (simEnv B).findRel? x = some v) : (0, x, relDefEv v) ∈ items Scripts.Wasm30.fixed :=
  by
    unfold simEnv baseEnv at h
    rw [Env.findRel?_withBuiltins] at h
    exact findRel?_envOfScript_item h

theorem findTyp?_simEnv_item {B : Builtins} {x : IL.Id} {v : TypDef}
    (h : (simEnv B).findTyp? x = some v) : (2, x, typDefEv v) ∈ items Scripts.Wasm30.fixed :=
  by
    unfold simEnv baseEnv at h
    rw [show ∀ (e : Env), (e.withBuiltins B).findTyp? x = e.findTyp? x from fun _ => rfl] at h
    exact findTyp?_envOfScript_item h

/-- In `utf8Env B`, a definition is `$utf8` without clauses, or the body of an item. -/
theorem findDef?_utf8Env_item {B : Builtins} {x : IL.Id} {v : DefDef}
    (h : (utf8Env B).findDef? x = some v) :
    (x = "utf8" ∧ v = (utf8Params, utf8Res, [])) ∨ (1, x, defDefEv v) ∈ items Scripts.Wasm30.fixed := by
  by_cases hx : x = "utf8"
  · subst hx
    rw [findDef?_utf8Env] at h
    exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  · rw [findDef?_utf8Env_of_ne B hx] at h
    exact Or.inr (findDef?_simEnv_item h)

/-! ## Reachable lookups are harmless -/

/-- **A reachable definition's body is closed and harmless.** -/
theorem findDef?_reach {B : Builtins} {x : IL.Id} {v : DefDef} (hR : (1, x) ∈ stepReach)
    (h : (simEnv B).findDef? x = some v) :
    (∀ r ∈ evRefs (defDefEv v), r ∈ stepReach) ∧ ∀ e ∈ defDefEv v, evOk (1, x) e = true :=
  ⟨stepReach_closed (findDef?_simEnv_item h) hR, evOk_of_mem (findDef?_simEnv_item h) hR⟩

/-- **A reachable relation's rules are closed and harmless.** -/
theorem findRel?_reach {B : Builtins} {x : IL.Id} {v : RelDef} (hR : (0, x) ∈ stepReach)
    (h : (simEnv B).findRel? x = some v) :
    (∀ r ∈ evRefs (relDefEv v), r ∈ stepReach) ∧ ∀ e ∈ relDefEv v, evOk (0, x) e = true :=
  ⟨stepReach_closed (findRel?_simEnv_item h) hR, evOk_of_mem (findRel?_simEnv_item h) hR⟩

/-- **A reachable type's instances are closed and harmless.** -/
theorem findTyp?_reach {B : Builtins} {x : IL.Id} {v : TypDef} (hR : (2, x) ∈ stepReach)
    (h : (simEnv B).findTyp? x = some v) :
    (∀ r ∈ evRefs (typDefEv v), r ∈ stepReach) ∧ ∀ e ∈ typDefEv v, evOk (2, x) e = true :=
  ⟨stepReach_closed (findTyp?_simEnv_item h) hR, evOk_of_mem (findTyp?_simEnv_item h) hR⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.Script
