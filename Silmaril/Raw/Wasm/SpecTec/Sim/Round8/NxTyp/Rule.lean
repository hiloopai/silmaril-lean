module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.NxTyp.Fwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.NxTyp.Assemble
public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Script.Thms

/-!
# Round 8, typing across erasure without a swap set: at rule instances (unrefined)

* `envN_utf8Env`: every type of `tyB` in the round-7 environment is checked (`nTypMap_fixed`).
* `agr_inst`: a rule instance's scope and its erasure agree on the quantifiers of export-free type,
  because their values are export-free (`NxSites.nxB_of_quantsOk`).
* `typFwdN_utf8Env`: `TypFwdN` in the round-7 environment, for every choice of primitives.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV nxB)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites (sigFixed)

variable {B : Builtins}

/-- **Every type of `tyB` in the round-7 environment is checked.** -/
theorem envN_utf8Env : EnvN TypAgree.tyB (utf8Env B) := by
  intro x td h hS
  rw [findTyp?_utf8Env] at h
  have hm := TypAgree.mem_typs_of_findTyp h
  have := List.all_eq_true.1 nTypMap_fixed _ hm
  simp only [hS, Bool.not_true, Bool.false_or] at this
  exact this

theorem typsTP_inst (σ : List (IL.Id × Value)) :
    TypsTP TypAgree.tyB (VarEnv.empty.bindVals σ) := fun _ hp => by
  simp [VarEnv.bindVals, VarEnv.empty, Map.empty] at hp

theorem mem_nxNames {qs : List Param} {x : IL.Id} (h : x ∈ nxNames qs) :
    ∃ t, Param.expP x t ∈ qs ∧ nxT t = true := by
  simp only [nxNames, List.mem_filterMap] at h
  obtain ⟨q, hq, hx⟩ := h
  cases q with
  | expP y t =>
    by_cases ht : nxT t = true
    · simp only [ht, ↓reduceIte, Option.some.injEq] at hx
      subst hx
      exact ⟨t, hq, ht⟩
    · simp [ht] at hx
  | _ => simp at hx

/-- **A rule instance and its erasure agree on the quantifiers of export-free type.** -/
theorem agr_inst {qs : List Param} {σ : List (IL.Id × Value)}
    (hq : QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs) :
    Agr (nxNames qs) (VarEnv.empty.bindVals σ) (eraseScope (VarEnv.empty.bindVals σ)) := by
  refine ⟨fun x hx => ?_, rfl, rfl, rfl⟩
  obtain ⟨t, ht, hnx⟩ := mem_nxNames hx
  obtain ⟨w, hw, hn⟩ := NxSites.nxB_of_quantsOk
    (NxSites.typsNx_bindVals (NxSites.typsNx_empty _) σ) hq ht hnx
  rw [Erase.find?_eraseScope, hw]
  simp [Swap.eraseV_of_nxB _ hn]

/-- The kernel check `nRelQuants_fixed`, read at a quantifier of a rule of a reachable relation. -/
theorem nTy_quant {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem}
    (hx : Script.stepReach.contains (0, x) = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op' e prems)) {y : IL.Id} {ty : Typ}
    (hy : Param.expP y ty ∈ qs) : nTy TypAgree.tyB (nxNames qs) ty = true := by
  rw [findRel?_utf8Env] at hrel
  have hm := EraseAll.mem_rels_of_findRel' hrel
  have h := List.all_eq_true.1 nRelQuants_fixed _ hm
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  have h' := h _ (List.mem_of_getElem? hrule)
  simp only [List.all_eq_true] at h'
  simpa using h' _ hy

/-- **`TypFwdN` holds in the round-7 environment**, for every choice of primitives. -/
theorem typFwdN_utf8Env : TypFwdN (utf8Env B) := by
  intro x ps op t rules i nm qs op' e prems σ hx hrel hrule hq y ty hy
  obtain ⟨w, hw, hty⟩ := hq y ty hy
  refine ⟨eraseV w, by rw [Erase.find?_eraseScope, hw]; rfl, ?_⟩
  exact hasTyp_fwd envN_utf8Env (NxSites.envNx_utf8Env B) (agr_inst hq) (typsTP_inst σ)
    (nTy_quant hx hrel hrule hy) hty

end Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp
