module

public import Silmaril.Wasm.SpecTec.Institution.Versions.Defs
public import Silmaril.Wasm.SpecTec.Scripts.Thms
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata

/-!
# Counting the rules two scripts share, in Lean

`spectec-gen theory-diff` (`tools/spectec-gen/src/theory.rs`, unverified) reports, for two
scripts, how many rules of the first the second keeps verbatim. This module computes the same
count inside Lean and connects it to the institution's `theoryOf`:

* `ruleList env` lists the rules of an environment's relation table, keeping, as `findRel?`
  does, only the first binding of each relation name; `theoryOf_eq_ruleList` says that
  `theoryOf env` is exactly the set of its elements.
* `inTheoryB env φ` decides `φ ∈ theoryOf env` by comparing printed definitions (`IL.defEq`,
  injective by `IL.defEq_iff`); `inTheoryB_iff` is the soundness and completeness of that test.
* So `(ruleList env₁).countP (inTheoryB env₂)` is the number of rules of `env₁` (with
  multiplicity, as the tool counts) that lie in `retained env₁ env₂`
  (`countP_eq_retained`), and the kernel evaluates it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- The rule sentence of `r` in the relation `x` declared with `(ps, op, t)`. -/
def ruleSen (x : IL.Id) (ps : List Param) (op : MixopS) (t : Typ) (r : Rule) : SSen :=
  .rule (x, ps, op, t) r

/-- The relation name of a rule sentence. -/
def SSen.relName : SSen → Option IL.Id
  | .rule d _ => some d.1
  | .fact .. => none

/-- The rules of a relation table, keeping only the first binding of each name, which is the
one `Map.find?` (hence `Env.findRel?`) returns. -/
def tableRules : Map RelDef → List SSen
  | [] => []
  | (x, (ps, op, t, rules)) :: m =>
      rules.map (ruleSen x ps op t) ++ (tableRules m).filter (fun φ => φ.relName != some x)

/-- The rules of an environment. -/
def ruleList (env : Env) : List SSen := tableRules env.rels

/-- Membership in `tableRules`, read off the table. -/
theorem mem_tableRules {φ : SSen} :
    ∀ {m : Map RelDef}, φ ∈ tableRules m ↔ ∃ (d : RelDecl) (rules : List Rule) (r : Rule),
      m.find? d.1 = some (d.2.1, d.2.2.1, d.2.2.2, rules) ∧ r ∈ rules ∧ φ = .rule d r
  | [] => by simp [tableRules, Map.find?]
  | (x, (ps, op, t, rules)) :: m => by
      simp only [tableRules, List.mem_append, List.mem_map, List.mem_filter, mem_tableRules,
        Map.find?]
      constructor
      · rintro (⟨r, hr, rfl⟩ | ⟨⟨d, rs, r, hd, hr, rfl⟩, hn⟩)
        · exact ⟨(x, ps, op, t), rules, r, by simp, hr, rfl⟩
        · have hx : x ≠ d.1 := fun h => by simp [SSen.relName, h] at hn
          exact ⟨d, rs, r, by simp [hx, hd], hr, rfl⟩
      · rintro ⟨d, rs, r, hd, hr, rfl⟩
        by_cases hx : x = d.1
        · simp only [hx, ite_true, Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hd
          exact .inl ⟨r, hr, by simp [ruleSen, hx]⟩
        · simp only [hx, ite_false] at hd
          exact .inr ⟨⟨d, rs, r, hd, hr, rfl⟩, by simp [SSen.relName, Ne.symm hx]⟩

/-- **`theoryOf` is the set of `ruleList`'s elements.** -/
theorem theoryOf_eq_ruleList (env : Env) : theoryOf env = {φ | φ ∈ ruleList env} := by
  ext φ
  simp only [theoryOf, Set.mem_ofPred_eq, ruleList, mem_tableRules, Env.findRel?]

/-- The name of a rule. -/
def ruleName : Rule → IL.Id
  | .ruleD x .. => x

/-- Decide whether a rule sentence is in the theory of `env`: the relation of its name is
declared the same way and has a rule printed the same way. Rule names are compared first, so
that only same-named rules are printed. -/
def inTheoryB (env : Env) : SSen → Bool
  | .rule (x, ps, op, t) r =>
      match env.findRel? x with
      | some (ps', op', t', rules) => rules.any fun r' =>
          ruleName r' == ruleName r && defEq (.relD x ps' op' t' [r']) (.relD x ps op t [r])
      | none => false
  | .fact .. => false

/-- **`inTheoryB` decides membership in the theory.** -/
theorem inTheoryB_iff (env : Env) (φ : SSen) : inTheoryB env φ = true ↔ φ ∈ theoryOf env := by
  match φ with
  | .fact .. => simp [inTheoryB, theoryOf]
  | .rule (x, ps, op, t) r =>
      simp only [inTheoryB, theoryOf, Set.mem_ofPred_eq, SSen.rule.injEq]
      constructor
      · intro h
        split at h
        · rename_i ps' op' t' rules hf
          obtain ⟨r', hr', hn⟩ := List.any_eq_true.mp h
          have he := (Bool.and_eq_true _ _ ▸ hn).2
          simp only [defEq_iff, Def.relD.injEq, List.cons.injEq, and_true, true_and] at he
          obtain ⟨rfl, rfl, rfl, rfl⟩ := he
          exact ⟨(x, ps', op', t'), rules, r', hf, hr', rfl, rfl⟩
        · simp at h
      · rintro ⟨d, rules, r', hf, hr', hd, rfl⟩
        subst hd
        rw [show env.findRel? x = some (ps, op, t, rules) from hf]
        exact List.any_eq_true.mpr ⟨r, hr', by simp⟩

/-- The number of rules of `env₁` that `env₂` keeps, counted as `theory-diff` counts them. -/
def retainedCount (env₁ env₂ : Env) : Nat := (ruleList env₁).countP (inTheoryB env₂)

/-- **`retainedCount` counts `retained`**: on the entries of `ruleList env₁` (whose elements are
`theoryOf env₁`), `inTheoryB env₂` holds exactly of the members of `retained env₁ env₂`. -/
theorem inTheoryB_iff_retained {env₁ env₂ : Env} {φ : SSen} (hφ : φ ∈ ruleList env₁) :
    inTheoryB env₂ φ = true ↔ φ ∈ retained env₁ env₂ := by
  have h₁ : φ ∈ theoryOf env₁ := by rw [theoryOf_eq_ruleList]; exact hφ
  rw [inTheoryB_iff, retained, Set.mem_inter_iff]
  exact ⟨fun h => ⟨h₁, h⟩, fun h => h.2⟩

end Silmaril.Wasm.SpecTec.Institution
