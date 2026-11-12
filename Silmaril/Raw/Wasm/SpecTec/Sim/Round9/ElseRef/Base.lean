module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.ElseRef.Check

/-!
# Round 9, RE: `Ref_ok` backward across erasure of the store (unrefined)

* `closedX_erase`, `closedNx_self`, `closedX_true`: the checks `closedX`, `closedNx` read in a
  rule instance: round 7's erasure equation, an export-free value equal on both sides, and a
  condition `true` on the erased side `true` on the original one.
* `evalExp_triple'`, `evalExp_triple_mk`: triples evaluate componentwise.
* `refBwd`: a derivation of `Ref_ok` at `(eraseV sv, r, t)` gives one at `(sv, r, t)`, for a
  store `sv`. At every rule the store quantifier is rebound to `sv`; the other quantifiers keep
  their (export-free) values, so the erased new instance agrees with the old one; the conclusion
  and the `Ref_ok` premises are triples `(s, e₂, e₃)` read componentwise; the other premises go
  back by `closedX_true` and `closedNx_self`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound (DefsVT)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxRule (qScope ctx0)
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVs nxB)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (BIErase grE gdE xExp eraseP)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames)
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
open Round6.Reading (DDerivesB DPremB RuleBodyB conclAlts otherwiseAtB)

variable {B : Builtins}

/-! ## The checks, read -/

theorem closedX_parts {qs : List Param} {e : Exp} (h : closedX qs e = true) :
    EraseDer.varsIn (quantNames qs) (freeExp e) = true ∧
      tyOk sigX tsigFixed (quantsΓ qs) e = true ∧ NxFlow.auxE ctx0 e = true ∧
      NxErase.auxX ctx0 e = true ∧ badE sigX (quantsΓ qs) e = 0 ∧ xExp grE gdE e = true ∧
      "_" ∉ quantNames qs := by
  simp only [closedX, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun hm => by rw [List.contains_iff_mem.2 hm] at h7; cases h7⟩

section Closed

variable (hD : ∀ m, DefsVT sigX tsigFixed (utf8Env B) m) (H : BIErase QT gdE (utf8Env B))
  {qs : List Param} {σ : List (IL.Id × Value)}
  (hq : Sim.QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs)
  (hCE : ∀ k, NxErase.CallE gdE sigX tsigFixed ctx0 (utf8Env B)
    (qScope qs (VarEnv.empty.bindVals σ)) k)
include hD H hq hCE

theorem closedX_erase {e : Exp} (hc : closedX qs e = true) (n : Nat) :
    evalExp n (utf8Env B) (eraseScope (VarEnv.empty.bindVals σ)) e =
      eraseV <$> evalExp n (utf8Env B) (VarEnv.empty.bindVals σ) e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := closedX_parts hc
  exact NxErase.erase_closed hD H hq h7 hCE h1 h2 h3 h4 h5 h6 n

theorem closedX_true {e : Exp} (hc : closedX qs e = true) {n : Nat}
    (h : evalExp n (utf8Env B) (eraseScope (VarEnv.empty.bindVals σ)) e = .ok (.bool true)) :
    evalExp n (utf8Env B) (VarEnv.empty.bindVals σ) e = .ok (.bool true) := by
  rw [closedX_erase hD H hq hCE hc n] at h
  obtain ⟨u, hu, hue⟩ := map_eq_ok h
  rw [hu, eraseV_eq_bool hue]

theorem closedNx_self {e : Exp} (hc : closedNx qs e = true) {n : Nat} {w : Value}
    (h : evalExp n (utf8Env B) (eraseScope (VarEnv.empty.bindVals σ)) e = .ok w) :
    evalExp n (utf8Env B) (VarEnv.empty.bindVals σ) e = .ok w := by
  simp only [closedNx, Bool.and_eq_true] at hc
  obtain ⟨hc, hnx⟩ := hc
  rw [closedX_erase hD H hq hCE hc n] at h
  obtain ⟨u, hu, rfl⟩ := map_eq_ok h
  obtain ⟨h1, h2, h3, -, -, -, h7⟩ := closedX_parts hc
  have hok := NxRule.eOk_of_closed hD hq h7 h1 h2 h3 ⟨n, hu⟩
  rw [hu, Swap.eraseV_of_nxB _ (NxRule.nxB_of_eOk hok hnx)]

end Closed

/-! ## Triples and variables -/

theorem evalExp_triple' {n : Nat} {env : Env} {ρ : VarEnv} {a b c : Exp} {w : Value}
    (h : evalExp n env ρ (.tupE [a, b, c]) = .ok w) :
    ∃ k va vb vc, n = k + 2 ∧ evalExp k env ρ a = .ok va ∧ evalExp k env ρ b = .ok vb ∧
      evalExp k env ρ c = .ok vc ∧ w = .tuple [va, vb, vc] := by
  rcases n with _ | _ | k
  · simp [evalExp] at h
  · simp [evalExp, evalExps] at h
  · simp only [evalExp, evalExps, List.mapM_cons, List.mapM_nil] at h
    cases ha : evalExp k env ρ a with
    | error s => simp [ha] at h
    | ok va =>
      cases hb : evalExp k env ρ b with
      | error s => simp [ha, hb] at h
      | ok vb =>
        cases hc : evalExp k env ρ c with
        | error s => simp [ha, hb, hc] at h
        | ok vc =>
          simp [ha, hb, hc] at h
          exact ⟨k, va, vb, vc, rfl, ha, hb, hc, by subst h; rfl⟩

theorem evalExp_triple_mk {k : Nat} {env : Env} {ρ : VarEnv} {a b c : Exp} {va vb vc : Value}
    (ha : evalExp k env ρ a = .ok va) (hb : evalExp k env ρ b = .ok vb)
    (hc : evalExp k env ρ c = .ok vc) :
    evalExp (k + 2) env ρ (.tupE [a, b, c]) = .ok (.tuple [va, vb, vc]) := by
  simp [evalExp, evalExps, ha, hb, hc]

theorem evalExp_varE_swap {k : Nat} {env : Env} {ρ ρ' : VarEnv} {z : IL.Id} {w u : Value}
    (h : evalExp k env ρ (.varE z) = .ok w) (h' : ρ'.findVal? z = some u) :
    evalExp k env ρ' (.varE z) = .ok u := by
  rcases k with _ | k
  · simp [evalExp] at h
  · simp [evalExp, h']

/-! ## Quantifiers -/

theorem typQ_type {qs : List Param} {z : IL.Id} {n : String} (h : typQ qs z n = true) {t : Typ}
    (ht : Param.expP z t ∈ qs) : t = .varT n [] := by
  simp only [typQ, Bool.and_eq_true, List.all_eq_true] at h
  have h' := h.2 _ ht
  simp only [bne_self_eq_false, Bool.false_or] at h'
  unfold isVarT at h'
  split at h'
  · rename_i x; simp only [beq_iff_eq] at h'; rw [h']
  · cases h'

theorem typQ_mem {qs : List Param} {z : IL.Id} {n : String} (h : typQ qs z n = true) :
    z ∈ quantNames qs := by
  simp only [typQ, Bool.and_eq_true, List.contains_iff_mem] at h
  exact h.1

theorem quantsVar_mem {qs : List Param} (h : quantsVar qs = true) {y : IL.Id} {t : Typ}
    (hy : Param.expP y t ∈ qs) : ∃ n, t = .varT n [] := by
  simp only [quantsVar, List.all_eq_true] at h
  have h' := h _ hy
  split at h'
  · rename_i n heq; cases heq; exact ⟨n, rfl⟩
  · cases h'

theorem quantsNxL_mem {qs : List Param} {zs : List IL.Id} (h : quantsNxL qs zs = true)
    {y : IL.Id} {t : Typ} (hy : Param.expP y t ∈ qs) (hz : y ∉ zs) : Round8.NxTyp.nxT t = true := by
  simp only [quantsNxL, List.all_eq_true] at h
  have h' := h _ hy
  simp only [Bool.or_eq_true, List.contains_iff_mem] at h'
  exact h'.resolve_left hz

/-- Rebinding a quantifier of a named type keeps it typed. -/
theorem hasTyp_var_inst {σ σ' : List (IL.Id × Value)} {n : String} {v : Value}
    (h : HasTyp (utf8Env B) (VarEnv.empty.bindVals σ) (.varT n []) v) :
    HasTyp (utf8Env B) (VarEnv.empty.bindVals σ') (.varT n []) v :=
  hasTyp_varT_scope rfl rfl h

/-- The kernel check `refRel_fixed`, read at the relation. -/
theorem refRel_at {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    (hrel : (utf8Env B).findRel? "Ref_ok" = some (ps, op, t, rules)) :
    ps = [] ∧ ∀ r ∈ rules, refRule r = true := by
  rw [findRel?_utf8Env] at hrel
  have h := List.all_eq_true.1 refRel_fixed _ (EraseAll.mem_rels_of_findRel' hrel)
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff,
    List.all_eq_true] at h
  exact h

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef
