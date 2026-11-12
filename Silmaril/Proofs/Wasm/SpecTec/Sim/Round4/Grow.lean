module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round4.Valid

/-!
# Round 4: `table.grow-fail` and `memory.grow-fail` backward, over valid configurations

`Step/table.grow-fail` (16) and `Step/memory.grow-fail` (27) have no premise, so SpecTec fires
them at every index; round 3 refuted the backward conjunct of the earlier targets with
`memory.grow 0` and no memory (`Round3.not_wholeStepBounded`). From a **valid** source
(`ConfigOk c ts`) the index names a table or memory of the store (`table?_of_configOk`,
`mem?_of_configOk`), and Core's `growFail` fires whenever the profile lets growth fail, which
`Profile.spec nd r` always does. So both rules are backward-simulated by Core's step, for every
`B`, exactly (no `ConfigEq` needed).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics
open BwdPureStep (fires_step codes_two codes_three payload_of_caseE head_of_caseE ref_of_var
  aconst_of_image head_of_typed_addrtype)

variable {H : Type} {B : Builtins}

theorem head_memoryGrow {a : Admin} (h : Typing.adminHead a = "MEMORY.GROW") :
    ∃ x, a = .plain (.memoryGrow x) := by
  revert h
  admin_head_inv

theorem head_tableGrow {a : Admin} (h : Typing.adminHead a = "TABLE.GROW") :
    ∃ x, a = .plain (.tableGrow x) := by
  revert h
  admin_head_inv

/-- **A `CONST at (% n)` element of a left-hand side, `at` a typed `addrtype`**, is an
address-typed constant, and `at` is bound to its address type. -/
theorem aconstN_of_lhs {σ : List (IL.Id × Value)} {qs : List Param} {a : Admin}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) qs)
    (hm : Param.expP "at" (.varT "addrtype" []) ∈ qs)
    (h : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.varE "n"])])) (adminToV a)) :
    ∃ (at_ : AddrType) (b : BitVec at_.intType.width), a = aconst at_ b ∧
      (VarEnv.empty.bindVals σ).findVal? "at" = some (Encode.toValue at_) := by
  obtain ⟨u, hu, he⟩ := payload_of_caseE h
  obtain ⟨u₁, u₂, hu₁, -, rfl⟩ := State.evalExp_tup2_inv hu
  obtain ⟨AT, fAT, tAT⟩ := hq "at" _ hm
  have e₁ : u₁ = AT := EvalExp.unique (evalExp_subE_iff.1 hu₁) (evalExp_var fAT)
  obtain ⟨op, w, hw, hop⟩ := head_of_typed_addrtype (valsOnly_bindVals σ) tAT
  have he' : adminToV a = .case "CONST" (.tuple [.case op w, u₂]) := by rw [he, e₁, hw]
  obtain ⟨at_, b, rfl, -⟩ := aconst_of_image he' hop
  have hE : (Encode.toValue at_ : Value) = AT := by
    rw [State.adminToV_aconst] at he
    simp only [State.aconstV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and]
      at he
    exact he.1.trans e₁
  exact ⟨at_, b, rfl, hE ▸ fAT⟩

/-- The right-hand side `z; CONST at (% $inv_signed_($size(at), -1))` of both grow-fail rules,
evaluated: Core's `-1` at the address type. -/
theorem growFail_rhs {σ : List (IL.Id × Value)} {Z : Value} {at_ : AddrType} {w : Value}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some Z)
    (fa : (VarEnv.empty.bindVals σ).findVal? "at" = some (Encode.toValue at_))
    (h : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.caseE "%;%" (.tupE [.varE "z",
      .listE [.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.callE "inv_signed_" [.expA (.callE "size"
          [.expA (.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []))]),
        .expA (.unE .minusOp (.numT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))]])])]])) w) :
    w = cfgV Z [adminToV (aconst at_ (BitVec.allOnes _))] := by
  refine EvalExp.unique h ?_
  rw [State.adminToV_aconst]
  exact evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case (evalExp_tup2
    (evalExp_subE_iff.2 (evalExp_var fa)) (evalExp_case (evalExp_tupE_iff.2 ⟨_,
      evalExps_cons (State.evalExp_growFailResult (State.growDefs_simEnv B) at_ rfl rfl fa)
        evalExps_nil, rfl⟩))))))

variable {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **`Step/memory.grow-fail` (27) backward, from a valid source**: Core's `growFail`, in every
profile in which growth may fail. -/
theorem bwd_memoryGrowFail (hP : ∀ k a n d, P.growMayFail k a n d) {c : Config H}
    {ts : List CValType} (hc : ConfigOk c ts) {w : Value}
    (hf : Fires (simEnv B) "Step" 27 (.tuple [configV hn c, w])) : BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, -⟩ := fires_step (hasStepRules_simEnv B).memoryGrowFail hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes_two hes
  obtain ⟨at_, b, rfl, fa⟩ := aconstN_of_lhs hq (.tail _ (.head _)) h₁
  obtain ⟨x, rfl⟩ := head_memoryGrow (head_of_caseE h₂)
  obtain ⟨ma, mi, hm⟩ := mem?_of_configOk (x := x) hc (by simp)
  refine ⟨⟨s, f, [aconst at_ (BitVec.allOnes _)]⟩, growFail_rhs fz fa hr, ?_⟩
  exact .memory (.growFail hm (.inl (hP _ _ _ _)))

/-- **`Step/table.grow-fail` (16) backward, from a valid source**: Core's `growFail`, in every
profile in which growth may fail. -/
theorem bwd_tableGrowFail (hP : ∀ k a n d, P.growMayFail k a n d) {c : Config H}
    {ts : List CValType} (hc : ConfigOk c ts) {w : Value}
    (hf : Fires (simEnv B) "Step" 16 (.tuple [configV hn c, w])) : BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, -⟩ := fires_step (hasStepRules_simEnv B).tableGrowFail hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes_three hes
  obtain ⟨r, rfl, -⟩ := ref_of_var hq (.tail _ (.head _)) h₁
  obtain ⟨at_, b, rfl, fa⟩ := aconstN_of_lhs hq (.tail _ (.tail _ (.head _))) h₂
  obtain ⟨x, rfl⟩ := head_tableGrow (head_of_caseE h₃)
  obtain ⟨ta, ti, ht⟩ := table?_of_configOk (x := x) hc (by simp)
  refine ⟨⟨s, f, [aconst at_ (BitVec.allOnes _)]⟩, growFail_rhs fz fa hr, ?_⟩
  exact .table (.growFail ht (.inl (hP _ _ _ _)))

/-- Growth may always fail under `Profile.spec`. -/
theorem growMayFail_spec (nd : Bool) (r : RelaxedChoice) :
    ∀ k a n d, (Profile.spec nd r).growMayFail k a n d := fun _ _ _ _ => trivial

end Silmaril.Wasm.SpecTec.Sim.Round4
