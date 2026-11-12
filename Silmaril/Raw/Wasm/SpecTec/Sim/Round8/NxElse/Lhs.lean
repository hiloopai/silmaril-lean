module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.NxElse.Fire
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.NxElse.Check

/-!
# Round 8, `otherwise` across erasure: the left-hand side of a fired `otherwise` rule (unrefined)

* `elseLhs_at`: the kernel check `elseLhs_fixed`, read at a rule.
* `evalExp_pair`: a pair expression evaluates componentwise.
* `fired_lhs`: when a rule of a `grE` relation with an `otherwise` premise fires on `v`, its
  arguments are `[]` and `v = (a, b)` with `a` export-free (`eraseV a = a`). The erased instance
  evaluates the conclusion to `eraseV v` (`NxErase.erase_alt`); its left-hand side reads only
  quantifiers of export-free type, so it evaluates alike in the instance and its erasure
  (`NxTyp.agr_inst`), and the two values of the left-hand side are equal.
* `otherwiseB_erase`: SpecTec's `otherwise` reads `v` only through its left-hand side.
* `hO_else`: the `hO` of `NxDer.derFwdN`, for `elseF` of SpecTec's `otherwise` on the original
  side and SpecTec's `otherwise` on the erased side.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxElse

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (grE gdE BIErase)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVs eraseA)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Round6.Reading (conclAlts otherwiseB otherwiseAtB)

variable {B : Builtins}

/-- The kernel check `elseLhs_fixed`, read at a rule. -/
theorem elseLhs_at {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem}
    (hx : grE x = true) (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op' e prems)) (hel : prems.any elseIn = true)
    {e' : Exp} (he' : e' ∈ conclAlts e) : lhsNx qs e' = true := by
  rw [findRel?_utf8Env] at hrel
  have h := List.all_eq_true.1 elseLhs_fixed _ (EraseAll.mem_rels_of_findRel' hrel)
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h
  have h' := h _ (List.mem_of_getElem? hrule)
  simp only [hel, Bool.not_true, Bool.false_or, List.all_eq_true] at h'
  exact h' e' he'

theorem lhsNx_eq {qs : List Param} {e : Exp} (h : lhsNx qs e = true) :
    ∃ l r, e = .tupE [l, r] ∧ EraseDer.varsIn (NxTyp.nxNames qs) (freeExp l) = true := by
  unfold lhsNx at h
  split at h
  · exact ⟨_, _, rfl, h⟩
  · exact absurd h Bool.false_ne_true

/-- A pair expression evaluates componentwise. -/
theorem evalExp_pair {n : Nat} {env : Env} {ρ : VarEnv} {l r : Exp} {w : Value}
    (h : evalExp n env ρ (.tupE [l, r]) = .ok w) :
    ∃ k a b, n = k + 2 ∧ evalExp k env ρ l = .ok a ∧ evalExp k env ρ r = .ok b ∧
      w = .tuple [a, b] := by
  rcases n with _ | _ | k
  · simp [evalExp] at h
  · simp [evalExp, evalExps] at h
  · simp only [evalExp, evalExps, List.mapM_cons, List.mapM_nil] at h
    cases ha : evalExp k env ρ l with
    | error s => simp [ha] at h
    | ok a =>
      cases hb : evalExp k env ρ r with
      | error s => simp [ha, hb] at h
      | ok b =>
        simp [ha, hb] at h
        exact ⟨k, a, b, rfl, ha, hb, by subst h; rfl⟩

/-- Agreement on the quantifiers of export-free type gives agreement on an expression reading
only them. -/
theorem agreeOn_of_agr {qs : List Param} {ρ ρ' : VarEnv} (h : NxTyp.Agr (NxTyp.nxNames qs) ρ ρ')
    {l : Exp} (hl : EraseDer.varsIn (NxTyp.nxNames qs) (freeExp l) = true) :
    VarEnv.AgreeOn (freeExp l) ρ ρ' :=
  ⟨fun x hx => (h.vals x (EraseDer.varsIn_mem hl x hx)).symm,
    fun x _ => by simp only [VarEnv.findTyp?, h.typs],
    fun x _ => by simp only [VarEnv.findDef?, h.defs],
    fun x _ => by simp only [VarEnv.findGram?, h.grams]⟩

section Fired

variable (hB : NxSound.BuiltinsVT NxTyped.sigX NxTyped.tsigFixed (utf8Env B))
  (H : BIErase NxErase.QT gdE (utf8Env B))
include hB H

/-- **A fired `otherwise` rule of a `grE` relation has no arguments and an export-free left-hand
side.** -/
theorem fired_lhs {x : IL.Id} {args : List ArgV} {i : Nat} {v : Value} (hx : grE x = true)
    (hF : Fired (utf8Env B) x args i v) :
    args = [] ∧ ∃ a b, v = .tuple [a, b] ∧ eraseV a = a := by
  obtain ⟨ps, op, t, rules, nm, qs, e, prems, e', ρ₀, σ, hrel, hrule, hel, halt, hps, hq,
    ⟨n, hn⟩⟩ := hF
  have hr : NxSites.reach 0 x = true := List.contains_iff_mem.2 (EraseAll.reach_of_grE hx)
  have hRF := NxRule.rFacts hr hrel hrule
  obtain ⟨hargs, hρ⟩ := EraseDer.bindParams_nil_args (hRF.params ▸ hps)
  subst hargs hρ
  refine ⟨rfl, ?_⟩
  obtain ⟨l, r, rfl, hl⟩ := lhsNx_eq (elseLhs_at hx hrel hrule hel halt)
  obtain ⟨k, a, b, rfl, ha, hb, rfl⟩ := evalExp_pair hn
  refine ⟨a, b, rfl, ?_⟩
  have hCE : ∀ k, NxErase.CallE gdE NxTyped.sigX NxTyped.tsigFixed NxRule.ctx0 (utf8Env B)
      (NxRule.qScope qs (VarEnv.empty.bindVals σ)) k :=
    fun k => NxClause.clauseErase B hB H _ k rfl rfl
  have hE := NxErase.erase_alt (NxFlow.flowSound B hB) H hr hrel hrule hq hCE halt
    ((EraseAll.xFacts hx hrel hrule).alts _ halt) (k + 2)
  rw [hn] at hE
  obtain ⟨k', a', b', hk, ha', _, hw⟩ := evalExp_pair hE
  have hk' : k' = k := by omega
  subst hk'
  rw [← evalExp_agreeOn (agreeOn_of_agr (NxTyp.agr_inst hq) hl), ha] at ha'
  cases ha'
  simp only [eraseV, eraseVs, Value.tuple.injEq, List.cons.injEq] at hw
  exact hw.1

end Fired

/-- **SpecTec's `otherwise` reads a value only through its left-hand side**, so it reads a pair
with an export-free left-hand side and its erasure alike. -/
theorem otherwiseB_erase {env : Env} {x : IL.Id} {i : Nat} {a b : Value} (ha : eraseV a = a)
    (h : otherwiseB env x [] i (.tuple [a, b])) :
    otherwiseB env x [] i (eraseV (.tuple [a, b])) := by
  unfold otherwiseB at h ⊢
  rw [otherwiseAtB] at h ⊢
  intro j hj ps op t rules r hrel hr w hw
  refine h j hj ps op t rules r hrel hr w ?_
  obtain ⟨a', b', c, hv, rfl⟩ := hw
  simp only [eraseV, eraseVs, Value.tuple.injEq, List.cons.injEq] at hv
  exact ⟨a, b, c, rfl, by rw [← hv.1, ha]⟩

/-- **The `hO` of `NxDer.derFwdN` holds** for `elseF` of SpecTec's `otherwise` on the original
side and SpecTec's `otherwise` on the erased side. -/
theorem hO_else (hB : NxSound.BuiltinsVT NxTyped.sigX NxTyped.tsigFixed (utf8Env B))
    (H : BIErase NxErase.QT gdE (utf8Env B)) :
    ∀ x args i v, elseF (utf8Env B) (otherwiseB (utf8Env B)) x args i v →
      otherwiseB (utf8Env B) x (args.map eraseA) i (eraseV v) := by
  intro x args i v ⟨hO, hx, hF⟩
  obtain ⟨rfl, a, b, rfl, ha⟩ := fired_lhs hB H hx hF
  exact otherwiseB_erase ha hO

end Silmaril.Wasm.SpecTec.Sim.Round8.NxElse
