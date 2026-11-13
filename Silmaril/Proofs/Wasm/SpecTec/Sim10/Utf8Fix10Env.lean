module

public import Silmaril.Wasm.SpecTec.Sim10.Utf8Fix.Defs

/-!
# The 1.0 `$utf8` erratum: the tables of `utf8Env10T B`

`fixedU10` replaces one definition declaration of `StoreFix.fixedT10`, so:

* `typsOfDefs_replaceDec`, `defsOfDefs_replaceDec`, `relsOfDefs_replaceDec`,
  `gramsOfDefs_replaceDec` (structural): replacing a definition declaration rewrites the
  definition table entry by entry and leaves the type, relation and grammar tables alone;
* **`findDef?_utf8Env10T`**: `utf8Env10T B` finds `$utf8` with no clauses;
* `findDef?_utf8Env10T_of_ne`, `findTyp?_utf8Env10T`, `findRel?_utf8Env10T`,
  `findGram?_utf8Env10T`: elsewhere it finds what `simEnv10T B` finds;
* `call_utf8Env10T_of_ne`, `call_utf8Env10T_utf8`: its primitives are `B` off `$utf8`, and
  `Round6.MemSimd.utf8Call` at `$utf8`.

So the fixed script has the same lookups as the environment-level form of the erratum used for
2.0 and 3.0 (`bindDef "utf8"` with no clauses).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Fix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7 (utf8Params utf8Res)
open Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd (withUtf8 utf8Call)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T fixedT10)

set_option maxRecDepth 100000

/-! ## Replacing a definition declaration -/

/-- Rewrite the entry of `x` in a table. -/
def replE {α : Type} (x : IL.Id) (v : α) (p : IL.Id × α) : IL.Id × α :=
  if p.1 = x then (x, v) else p

mutual
theorem defsOfDef_replaceDec (x ps t cs) (hx : x ≠ "_") : ∀ d : Def,
    defsOfDef (replaceDef (.decD x ps t cs) d) = (defsOfDef d).map (replE x (ps, t, cs))
  | .recD ds => by
    simp only [replaceDef, defsOfDef]; exact defsOfDefs_replaceDec x ps t cs hx ds
  | .decD y ps' t' cs' => by
    by_cases hy : x = y
    · subst hy
      simp [replaceDef, matchesDecl, declKind?, defsOfDef, Map.bind, Map.empty, hx, replE]
    · have hy' : ¬ y = x := fun h => hy h.symm
      by_cases h_ : y = "_"
      · subst h_
        simp [replaceDef, matchesDecl, declKind?, defsOfDef, Map.bind, Map.empty, hy]
      · simp [replaceDef, matchesDecl, declKind?, defsOfDef, Map.bind, Map.empty, hy, h_, replE,
          hy']
  | .typD _ _ _ => by simp [replaceDef, matchesDecl, declKind?, defsOfDef, Map.empty]
  | .gramD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?, defsOfDef, Map.empty]
  | .relD _ _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?, defsOfDef, Map.empty]
theorem defsOfDefs_replaceDec (x ps t cs) (hx : x ≠ "_") : ∀ ds : List Def,
    defsOfDefs (replaceDefs (.decD x ps t cs) ds) = (defsOfDefs ds).map (replE x (ps, t, cs))
  | [] => rfl
  | d :: ds => by
    simp only [replaceDefs, defsOfDefs, List.map_append]
    rw [defsOfDef_replaceDec x ps t cs hx d, defsOfDefs_replaceDec x ps t cs hx ds]
end

mutual
theorem typsOfDef_replaceDec (x ps t cs) : ∀ d : Def,
    typsOfDef (replaceDef (.decD x ps t cs) d) = typsOfDef d
  | .recD ds => by simp only [replaceDef, typsOfDef]; exact typsOfDefs_replaceDec x ps t cs ds
  | .decD _ _ _ _ => by simp only [replaceDef]; split <;> rfl
  | .typD _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .gramD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .relD _ _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
theorem typsOfDefs_replaceDec (x ps t cs) : ∀ ds : List Def,
    typsOfDefs (replaceDefs (.decD x ps t cs) ds) = typsOfDefs ds
  | [] => rfl
  | d :: ds => by
    simp only [replaceDefs, typsOfDefs]
    rw [typsOfDef_replaceDec x ps t cs d, typsOfDefs_replaceDec x ps t cs ds]
end

mutual
theorem relsOfDef_replaceDec (x ps t cs) : ∀ d : Def,
    relsOfDef (replaceDef (.decD x ps t cs) d) = relsOfDef d
  | .recD ds => by simp only [replaceDef, relsOfDef]; exact relsOfDefs_replaceDec x ps t cs ds
  | .decD _ _ _ _ => by simp only [replaceDef]; split <;> rfl
  | .typD _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .gramD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .relD _ _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
theorem relsOfDefs_replaceDec (x ps t cs) : ∀ ds : List Def,
    relsOfDefs (replaceDefs (.decD x ps t cs) ds) = relsOfDefs ds
  | [] => rfl
  | d :: ds => by
    simp only [replaceDefs, relsOfDefs]
    rw [relsOfDef_replaceDec x ps t cs d, relsOfDefs_replaceDec x ps t cs ds]
end

mutual
theorem gramsOfDef_replaceDec (x ps t cs) : ∀ d : Def,
    gramsOfDef (replaceDef (.decD x ps t cs) d) = gramsOfDef d
  | .recD ds => by simp only [replaceDef, gramsOfDef]; exact gramsOfDefs_replaceDec x ps t cs ds
  | .decD _ _ _ _ => by simp only [replaceDef]; split <;> rfl
  | .typD _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .gramD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .relD _ _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
theorem gramsOfDefs_replaceDec (x ps t cs) : ∀ ds : List Def,
    gramsOfDefs (replaceDefs (.decD x ps t cs) ds) = gramsOfDefs ds
  | [] => rfl
  | d :: ds => by
    simp only [replaceDefs, gramsOfDefs]
    rw [gramsOfDef_replaceDec x ps t cs d, gramsOfDefs_replaceDec x ps t cs ds]
end

/-- Looking up a rewritten table. -/
theorem find?_map_replE {α : Type} (x : IL.Id) (v : α) (y : IL.Id) :
    ∀ m : Map α, Map.find? (m.map (replE x v)) y =
      if y = x then (Map.find? m y).map (fun _ => v) else Map.find? m y
  | [] => by simp [Map.find?]
  | (z, w) :: m => by
    have ih := find?_map_replE x v y m
    by_cases hz : z = x
    · subst hz
      by_cases hy : y = z
      · subst hy; simp [Map.find?, replE]
      · simp [Map.find?, replE, hy, Ne.symm hy, ih]
    · by_cases hy : y = x
      · subst hy
        simp [Map.find?, replE, hz, ih]
      · simp [Map.find?, replE, hz, hy, ih]

/-! ## The tables of `utf8Env10T B` -/

variable (B : Builtins)

theorem utf8Env10T_tables :
    (utf8Env10T B).typs = (simEnv10T B).typs ∧
      (utf8Env10T B).defs = (simEnv10T B).defs.map (replE "utf8" (utf8Params, utf8Res, [])) ∧
      (utf8Env10T B).rels = (simEnv10T B).rels ∧ (utf8Env10T B).grams = (simEnv10T B).grams ∧
      (utf8Env10T B).builtins = withUtf8 B := by
  simp only [utf8Env10T, simEnv10T, fixedU10, utf8Decl10, Env.withBuiltins, envOfScript,
    envOfDefs_eq]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · rw [typsOfDefs_replaceDec]
  · rw [defsOfDefs_replaceDec _ _ _ _ (by decide)]
    simp [Env.empty, Map.empty]
  · rw [relsOfDefs_replaceDec]
  · rw [gramsOfDefs_replaceDec]

set_option maxRecDepth 8000000 in
theorem findDef_utf8_simEnv10T : ∃ cs,
    (simEnv10T B).findDef? "utf8" = some (utf8Params, utf8Res, cs) := ⟨_, rfl⟩

/-- **The fixed script declares `$utf8` with no clauses.** -/
@[simp] theorem findDef?_utf8Env10T :
    (utf8Env10T B).findDef? "utf8" = some (utf8Params, utf8Res, []) := by
  obtain ⟨cs, hcs⟩ := findDef_utf8_simEnv10T B
  simp only [Env.findDef?] at hcs ⊢
  rw [(utf8Env10T_tables B).2.1, find?_map_replE, hcs]
  simp

theorem findDef?_utf8Env10T_of_ne {x : IL.Id} (hx : x ≠ "utf8") :
    (utf8Env10T B).findDef? x = (simEnv10T B).findDef? x := by
  simp only [Env.findDef?]
  rw [(utf8Env10T_tables B).2.1, find?_map_replE]
  simp [hx]

theorem findTyp?_utf8Env10T (x : IL.Id) : (utf8Env10T B).findTyp? x = (simEnv10T B).findTyp? x := by
  simp only [Env.findTyp?, (utf8Env10T_tables B).1]

theorem findRel?_utf8Env10T (x : IL.Id) : (utf8Env10T B).findRel? x = (simEnv10T B).findRel? x := by
  simp only [Env.findRel?, (utf8Env10T_tables B).2.2.1]

theorem findGram?_utf8Env10T (x : IL.Id) :
    (utf8Env10T B).findGram? x = (simEnv10T B).findGram? x := by
  simp only [Env.findGram?, (utf8Env10T_tables B).2.2.2.1]

theorem call_utf8Env10T_of_ne {x : IL.Id} (hx : x ≠ "utf8") (ws : List ArgV) :
    (utf8Env10T B).builtins.call x ws = B.call x ws := by
  simp [(utf8Env10T_tables B).2.2.2.2, withUtf8, hx]

theorem call_utf8Env10T_utf8 (ws : List ArgV) :
    (utf8Env10T B).builtins.call "utf8" ws = utf8Call ws := by
  simp [(utf8Env10T_tables B).2.2.2.2, withUtf8]

end Silmaril.Wasm.SpecTec.Sim10.Utf8Fix
