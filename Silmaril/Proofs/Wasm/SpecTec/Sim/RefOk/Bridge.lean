module

public import Silmaril.Wasm.SpecTec.Sim.Integrate.Thms

/-!
# What `RefsGC.RefOkBridge` commits to about the store

`RefOkBridge env` states `DDerives env O "Ref_ok" … (storeV hn s, ref, rt) ↔ RefOk s r rt` for
**every** Core store `s`. Every rule of SpecTec's `Ref_ok` quantifies `s : store`, so under the
declarative reading (`DDerives` checks every quantifier against its declared type, `QuantsOk`)
its left-hand side forces `storeV hn s` to be a typed `store`. Core's `RefOk s .null
(.ref true .bot)` holds of every store, so `RefOkBridge` implies that the image of every Core
store is a typed `store` (`storeTyped_of_refOkBridge`). That fails (argued, not formally refuted:
a formal refutation needs a definite `hasTyp … = .ok false` on a concrete store, a heavy
evaluation) for stores holding a type with an index `≥ 2 ^ 32` (`_IDX x` is a `typeidx`, a
`u32`), which Core's `Ty` permits. So `RefOkBridge` as stated is (argued) unsatisfiable, and has
to be restated under a store-typing hypothesis before it can be proved; see
`docs/projects/spectec/README.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- Every rule of `Ref_ok` concludes `(s, …)` and quantifies `s : store`. -/
def RefOkRulesStore (env : Env) : Prop :=
  ∃ t rules, env.findRel? "Ref_ok" = some ([], "%|-%:%", t, rules) ∧
    ∀ R ∈ rules, ∃ nm qs e₂ prems, R = .ruleD nm qs "%|-%:%" (.tupE (.varE "s" :: e₂)) prems ∧
      Param.expP "s" storeT ∈ qs

set_option maxRecDepth 100000 in
/-- The script's `Ref_ok` has that shape. -/
theorem refOkRulesStore_simEnv (B : Builtins) : RefOkRulesStore (simEnv B) := by
  refine ⟨_, _, rfl, ?_⟩
  intro R hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, _, _, rfl, by simp⟩

/-- A `Ref_ok` derivation at the image of `s` types the image of `s`, in the rule's scope. -/
theorem storeTyped_of_dderives {env : Env} (hR : RefOkRulesStore env) {O : ElseI}
    {hn : H → String} {s : Store H} {a b : Value}
    (h : DDerives env O "Ref_ok" "%|-%:%" [] (.tuple [storeV hn s, a, b])) :
    ∃ ρ, HasTyp env ρ storeT (storeV hn s) := by
  obtain ⟨t, rules, hrel, hrs⟩ := hR
  cases h with
  | rule hrel' hrule _ hq he _ =>
    rw [hrel] at hrel'
    cases hrel'
    obtain ⟨nm, qs, e₂, prems, hReq, hmem⟩ := hrs _ (List.mem_of_getElem? hrule)
    cases hReq
    obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 he
    cases hv
    obtain ⟨w, ws, hw, hs, -⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
    cases hw
    obtain ⟨u, hu, ht⟩ := hq _ _ hmem
    rw [evalExp_varE_iff.1 hs] at hu
    cases hu
    exact ⟨_, ht⟩

/-- **`RefOkBridge` forces every store image to be a typed `store`** (in some scope). -/
theorem storeTyped_of_refOkBridge (B : Builtins) (K : RefsGC.RefOkBridge (simEnv B))
    (hn : H → String) (s : Store H) :
    ∃ ρ, HasTyp (simEnv B) ρ storeT (storeV hn s) :=
  storeTyped_of_dderives (refOkRulesStore_simEnv B)
    ((K.refOk hn noElse s .null (.ref true .bot)).2 RefOk.null)

end Silmaril.Wasm.SpecTec.Sim.RefOk
