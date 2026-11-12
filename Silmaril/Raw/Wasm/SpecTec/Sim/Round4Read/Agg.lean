module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4Read.Common
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Aggregates.Eval

/-!
# Track r4-read: `Step_read/array.len-array` (81), backward, under the store bounds

SpecTec's result is `CONST I32 (% |$arrayinst(z)[a].FIELDS|)`, the exact length; Core's is
`BitVec.ofNat 32` of it. Round 3 found the rule false without a bound: an array
of `2 ^ 32` or more fields steps in SpecTec to the image of no Core configuration. The store
bounds (`ReadValid.store`, `Aggregates.Bounded.arrays`) exclude it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4Read

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV aconstV)
open BwdRead (cfg_inv)

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- **A `REF.ARRAY_ADDR` image, decoded.** -/
theorem decode_refArray {a : Admin} {A : Value} (h : adminToV a = .case "REF.ARRAY_ADDR" A) :
    ∃ k, a = .ref (.array k) ∧ A = .num (.natN k) := by
  obtain ⟨k, rfl⟩ := BwdPureStep.head_refArray (Typing.adminToV_case h).symm
  refine ⟨k, rfl, ?_⟩
  injection h with _ h₂
  exact h₂.symm

variable (B : Builtins)

/-- **`Step_read` 81 (`array.len-array`), backward, under the store bounds.** -/
theorem bwdV_arrayLenArray : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 81 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hv _ hf
  obtain ⟨σ, hq, he, -⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).arrayLenArray hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A, fa, -⟩ := hq "a" (.varT "addr" []) (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "REF.ARRAY_ADDR" A,
      .case "ARRAY.LEN" (.tuple [])]]) ∧ ∃ L, EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
        (.lenE (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")) L ∧
        w = .list [.case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [L])])] := by
    concl_inv he
  obtain ⟨⟨hZ, hcode⟩, L, hL, hw⟩ := hc.imp_left cfg_inv
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_pair hcode
  obtain ⟨k, rfl, rfl⟩ := decode_refArray h₁
  obtain rfl := BwdRead.aggDecode.arrayLen a₂ _ h₂
  subst hZ
  obtain ⟨fs, hfs, rfl⟩ := evalExp_lenE_iff.1 hL
  obtain ⟨R, hR, hRF⟩ := evalExp_dotE_iff.1 hfs
  obtain ⟨Ls, j, hLs, hj, hidx⟩ := evalExp_idxE_iff.1 hR
  have eLs : Ls = .list (s.arrays.map arrayInstV) :=
    EvalExp.unique hLs (Aggregates.evalExp_arrayinst (Aggregates.aggDefs_simEnv B) rfl
      (evalExp_var fz))
  have ej : j = k := by
    have := EvalExp.unique hj (evalExp_var fa)
    simpa using this
  subst eLs ej
  have hmap : (s.arrays[j]?).map arrayInstV = some R := by simpa [Value.idx?] using hidx
  obtain ⟨ai, ha, rfl⟩ := Option.map_eq_some_iff.1 hmap
  have efs : fs = ai.fields.map fieldValV := by simpa [arrayInstV] using hRF.symm
  subst efs
  have hlt : ai.fields.length < 2 ^ 32 := hv.store.aggs.arrays ai (List.mem_of_getElem? ha)
  refine ⟨[constI32 (BitVec.ofNat 32 ai.fields.length)], ?_, .aggregate (.arrayLenArray ha)⟩
  rw [hw]
  simp only [adminsToV, Memory.adminToV_constI32, Memory.toNat_ofNat_of_lt hlt,
    List.length_map]

/-- **`|$arrayinst(z)[a].FIELDS|` on an encoded state, read back**: the array exists. -/
theorem arrayLen_inv {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {k : Nat} {v : Value}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fa : (VarEnv.empty.bindVals σ).findVal? "a" = some (.num (.natN k)))
    (h : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.lenE (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")) v) :
    ∃ ai, s.arrays[k]? = some ai ∧ v = .num (.natN ai.fields.length) := by
  obtain ⟨fs, hfs, rfl⟩ := evalExp_lenE_iff.1 h
  obtain ⟨R, hR, hRF⟩ := evalExp_dotE_iff.1 hfs
  obtain ⟨Ls, j, hLs, hj, hidx⟩ := evalExp_idxE_iff.1 hR
  have eLs : Ls = .list (s.arrays.map arrayInstV) :=
    EvalExp.unique hLs (Aggregates.evalExp_arrayinst (Aggregates.aggDefs_simEnv B) rfl
      (evalExp_var fz))
  have ej : j = k := by
    have := EvalExp.unique hj (evalExp_var fa)
    simpa using this
  subst eLs ej
  have hmap : (s.arrays[j]?).map arrayInstV = some R := by simpa [Value.idx?] using hidx
  obtain ⟨ai, ha, rfl⟩ := Option.map_eq_some_iff.1 hmap
  have efs : fs = ai.fields.map fieldValV := by simpa [arrayInstV] using hRF.symm
  subst efs
  exact ⟨ai, ha, by simp⟩

/-- **`Step_read` 83 (`array.fill-oob`), backward.** The premise evaluates
`$arrayinst(z)[a]`, so the array exists; no validity is needed. -/
theorem bwdV_arrayFillOob : ∀ (c : Config H) (w : Value), ReadValid c →
    Typed (simEnv B) hn c → Fires (simEnv B) "Step_read" 83 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w _ _ hf
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (State.hasReadRules_simEnv B).arrayFillOob hf)
  obtain ⟨Z, fz, -⟩ := hq "z" stateT (by simp)
  obtain ⟨A, fa, -⟩ := hq "a" (.varT "addr" []) (by simp)
  obtain ⟨I, fi, -⟩ := hq "i" State.num32T (by simp)
  obtain ⟨V, fv, hV⟩ := hq "val" State.valT (by simp)
  obtain ⟨N, fn, -⟩ := hq "n" (.varT "n" []) (by simp)
  obtain ⟨X, fx, -⟩ := hq "x" State.idxT (by simp)
  have hc : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [Z, .list [.case "REF.ARRAY_ADDR" A,
      .case "CONST" (.tuple [.case "I32" (.tuple []), I]), V,
      .case "CONST" (.tuple [.case "I32" (.tuple []), .case "%" (.tuple [N])]),
      .case "ARRAY.FILL" X]]) ∧ w = .list [.case "TRAP" (.tuple [])] := by
    concl_inv he
  obtain ⟨hZ, hcode⟩ := cfg_inv hc.1
  obtain ⟨a₁, a₂, a₃, a₄, a₅, rfl, h₁, h₂, h₃, h₄, h₅⟩ := BwdRead.adminsToV_eq_quint hcode
  obtain ⟨k, rfl, rfl⟩ := decode_refArray h₁
  obtain ⟨i, rfl, rfl⟩ := decode_aconst_at (t := .i32) h₂
  obtain ⟨v, rfl⟩ := (Typing.stateDecode_simEnv B).val a₃ _ (valsOnly_bindVals σ) (h₃ ▸ hV)
  obtain ⟨n, rfl, hN⟩ := decode_aconst_at (t := .i32) h₄
  have eN : N = .num (.natN n.toNat) := by simpa using hN
  subst eN
  obtain ⟨x, rfl⟩ := BwdRead.head_arrayFill (Typing.adminToV_case h₅).symm
  subst hZ
  obtain ⟨v₁, v₂, e₁, e₂, hcmp⟩ := evalExp_cmpE_iff.1 (ifPrem (hp _ List.mem_cons_self))
  obtain ⟨ai, ha, rfl⟩ := arrayLen_inv B fz fa e₂
  have ev₁ : v₁ = .num (.natN (i.toNat + n.toNat)) :=
    EvalExp.unique e₁ (RefsGC.evalExp_addNat (RefsGC.evalExp_unpct (evalExp_var fi))
      (evalExp_var fn))
  subst ev₁
  refine ⟨[.trap], BwdRead.trap_out hc.2, ?_⟩
  exact .aggregate (.arrayFillOob ha (BwdRead.gt_nat_inv hcmp))

end Silmaril.Wasm.SpecTec.Sim.Round4Read
