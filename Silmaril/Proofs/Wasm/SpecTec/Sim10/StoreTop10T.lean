module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreAgree10Fwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.MemTrap
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdMem
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreFix10Fire

/-!
# The 1.0 store trap rules in `simEnv10T`, in both directions

`Step` 7 (`store-num-trap`) and 9 (`store-pack-trap`) of the wasm-1.0 script quantify the state
and the parts of the instruction (`z`, `i`, `t` or `Inn`, `c`, `n`, `ao`), not the code. So they
fire in `simEnv10T` as soon as the state is typed there, whatever the rest of the code is:

* `fires10T_storeNumTrap`, `fires10T_storePackTrap` (**forward**): at the image of V1's
  `intStoreTrap`/`floatStoreTrap`, from a state typed in `simEnv10T`, at every builtins. The
  evaluations are done in `simEnv10` and moved (`Sim20.StoreAgree.evalExp_of`); the numeric
  quantifiers are typed in `simEnv10` and moved (`hasTyp_repair`); the state is typed in
  `simEnv10T` directly, so a store whose functions contain stores is allowed.
* `bwd10T_storeNumTrap`, `bwd10T_storePackTrap` (**backward**): a firing of rule 7 or 9 in
  `simEnv10T` from the image of a `GoodV1` configuration is the image of a V1 step. The proof is
  round 3's (`Whole.bwd10_storeNumTrap`), with each evaluation moved back to `simEnv10`
  (`evalExp_back`), which needs no typing.
* `sstepB10T_of_fires`: a firing of a `Step` rule in `simEnv10T` is an `SStepB` step there.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value frameMemory
  effectiveAddress)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk TypedV ValsOnly stateT evalExp_tup2 evalExp_case
  dderives_iff_fires)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T sstepB10T_iff)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (EnvSame evalExp_of)
open Silmaril.Wasm.SpecTec.Sim20.Whole (div8E addrE memLenE constIE evalExp_div8 evalExp_addNat20
  evalExp_iPay width_cases)
open Silmaril.Wasm.SpecTec.Sim10.Whole (storeNumTrapRule10 storePackTrapRule10 innE10 valI32T'
  sizeTE evalExp_memLen10 evalExp_off10 evalExp_size10 packWidth10_cases evalExp_zTrap10
  adminToV_value adminsToV_map10)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Moving rules and evaluations -/

/-- A rule of `simEnv10 B` is a rule of `simEnv10T B`, at the same index. -/
theorem hasRuleAtT {x : IL.Id} {op : MixopS} {k : Nat} {r : Rule}
    (h : HasRuleAt (simEnv10 B) x op k r) : HasRuleAt (simEnv10T B) x op k r :=
  let ⟨ps, t, rules, hrel, hps, hk⟩ := h
  ⟨ps, t, rules, (findRel?_simEnv10T B x).trans hrel, hps, hk⟩

theorem evalExps_back {e₁ e₂ : Env} (hS : EnvSame e₁ e₂) {ρ : VarEnv} :
    ∀ {es : List Exp} {vs : List Value}, EvalExps e₂ ρ es vs → EvalExps e₁ ρ es vs
  | [], _, h => by rw [evalExps_nil_iff.1 h]; exact evalExps_nil
  | _ :: _, _, h => by
    obtain ⟨v, vs, h₁, h₂, rfl⟩ := evalExps_cons_iff.1 h
    exact evalExps_cons (evalExp_back hS h₁) (evalExps_back hS h₂)

/-- A typing in `simEnv10` is one in `simEnv10T`. -/
theorem hasTypT {ρ : VarEnv} {t : Typ} {v : Value} (h : HasTyp (simEnv10 B) ρ t v) :
    HasTyp (simEnv10T B) ρ t v :=
  Sim20.StoreAgree.hasTyp_repair (envSame10T B) (typRepair10T B) h

/-- **A firing of a `Step` rule in `simEnv10T` is a step there.** -/
theorem sstepB10T_of_fires {k : Nat} {v v' : Value} (h : Fires (simEnv10T B) "Step" k (.tuple [v, v'])) :
    SStepB (simEnv10T B) v v' := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAtT (B := B) (Whole.hasRuleAt_pure10 B)
  exact (sstepB10T_iff B).2 ((dderives_iff_fires hrel).2 ⟨k, h⟩)

/-! ## Left-hand sides -/

/-- The image of `CONST I32 i; v; st`. -/
theorem adminsToV_store3 (i : BitVec 32) (v : Execution.Runtime.Value) (st : V1.Instr) :
    adminsToV [value ⟨.int .i32, i⟩, value v, .source st] =
      [.case "CONST" (.tuple [caseNilV "I32", pctV i.toNat]), valV v, instrToV st] := by
  rw [adminsToV_map10]
  simp only [List.map_cons, List.map_nil, adminToV_value]
  rfl

/-- The scalar `STORE` without a pack size, as V1 encodes it. -/
def StoreNumV10 (v : Execution.Runtime.Value) (ao : V1.MemArg) (st : V1.Instr) : Prop :=
  instrToV st = .case "STORE" (.tuple [valTypeV v.type, .opt none, memargV ao])

/-- The left-hand side `z; CONST I32 i; CONST t c; STORE t ε ao`, evaluated. -/
theorem evalExp_storeNumLhs10 {ρ : VarEnv} {s : Store H} {f : Frame} {i : BitVec 32}
    {v : Execution.Runtime.Value} {ao : V1.MemArg} {st : V1.Instr} (hS : StoreNumV10 v ao st)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV i.toNat))
    (ft : ρ.findVal? "t" = some (valTypeV v.type)) (fc : ρ.findVal? "c" = some (numV v))
    (fa : ρ.findVal? "ao" = some (memargV ao)) :
    EvalExp (simEnv10 B) ρ (.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "CONST" (.tupE [.varE "t", .varE "c"]),
      .caseE "STORE" (.tupE [.varE "t", .optE none, .varE "ao"])]]))
      (configV hn ⟨s, f, [value ⟨.int .i32, i⟩, value v, .source st]⟩) := by
  rw [Whole.configV_eq_cfgV10, adminsToV_store3, hS]
  exact evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_case (evalExp_tup2 Sim20.Pure.evalExp_caseNil (Sim.evalExp_var fi)))
    (evalExps_cons (evalExp_case (evalExp_tup2 (Sim.evalExp_var ft) (Sim.evalExp_var fc)))
      (evalExps_cons (evalExp_case (Sim.evalExp_tup3 (Sim.evalExp_var ft)
        (evalExp_optE_none_iff.2 rfl) (Sim.evalExp_var fa))) evalExps_nil)), rfl⟩))

/-- The left-hand side `z; CONST I32 i; CONST Inn c; STORE Inn (% n) ao`, evaluated. -/
theorem evalExp_storePackLhs10 {ρ : VarEnv} {s : Store H} {f : Frame} {i : BitVec 32}
    {t : IntType} {x : BitVec t.width} {sz : V1.PackSize} {ao : V1.MemArg}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV i.toNat))
    (fInn : ρ.findVal? "Inn" = some (valTypeV (.int t))) (fc : ρ.findVal? "c" = some (pctV x.toNat))
    (fn : ρ.findVal? "n" = some (.num (.natN sz.width))) (fa : ρ.findVal? "ao" = some (memargV ao)) :
    EvalExp (simEnv10 B) ρ (.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "CONST" (.tupE [innE10, .varE "c"]),
      .caseE "STORE" (.tupE [innE10, .optE (some (.caseE "%" (.tupE [.varE "n"]))), .varE "ao"])]]))
      (configV hn ⟨s, f, [value ⟨.int .i32, i⟩, value ⟨.int t, x⟩,
        .source (.intStore t (some sz) ao)]⟩) := by
  rw [Whole.configV_eq_cfgV10, adminsToV_store3]
  have hInn : EvalExp (simEnv10 B) ρ innE10 (valTypeV (.int t)) :=
    evalExp_subE_iff.2 (Sim.evalExp_var fInn)
  have hsz : EvalExp (simEnv10 B) ρ (.optE (some (.caseE "%" (.tupE [.varE "n"]))))
      (.opt (some (szV sz))) :=
    evalExp_optE_some_iff.2 ⟨_, evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons
      (Sim.evalExp_var fn) evalExps_nil, rfl⟩), rfl⟩
  exact evalExp_case (evalExp_tup2 (Sim.evalExp_var fz) (evalExp_listE_iff.2 ⟨_, evalExps_cons
    (evalExp_case (evalExp_tup2 Sim20.Pure.evalExp_caseNil (Sim.evalExp_var fi)))
    (evalExps_cons (evalExp_case (evalExp_tup2 hInn (Sim.evalExp_var fc)))
      (evalExps_cons (evalExp_case (Sim.evalExp_tup3 hInn hsz (Sim.evalExp_var fa)))
        evalExps_nil)), rfl⟩))

/-- The trap premise, at a V1 access out of bounds. -/
theorem prem10_of_trap {ρ : VarEnv} {e : Exp} {s : Store H} {f : Frame} {i : BitVec 32}
    {ao : V1.MemArg} {w : Nat} {a : Execution.Runtime.MemAddr} {m : MemInst}
    (hρ : ρ.findDef? "mem" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fi : ρ.findVal? "i" = some (pctV i.toNat)) (fa : ρ.findVal? "ao" = some (memargV ao))
    (he : EvalExp (simEnv10 B) ρ e (.num (.natN w)))
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128) (hm : frameMemory s f = some (a, m))
    (hlt : m.data.size < effectiveAddress i ao + w / 8) :
    EvalExp (simEnv10 B) ρ (.cmpE .gtOp (.numT .natT) (addrE (div8E e)) memLenE) (.bool true) := by
  refine evalExp_cmpNum (evalExp_addNat20 (evalExp_addNat20 (evalExp_iPay fi) (evalExp_off10 fa))
    (evalExp_div8 he hw)) (evalExp_memLen10 hρ fz hm) ?_
  simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]
  simpa [effectiveAddress] using hlt

/-! ## Rule 7, forward -/

/-- **`Step/store-num-trap` fires in `simEnv10T`** at the image of V1's `intStoreTrap` and
`floatStoreTrap` without a pack size, from a state typed in `simEnv10T`, at every builtins. -/
theorem fires10T_storeNumTrap {s : Store H} {f : Frame} {i : BitVec 32}
    {v : Execution.Runtime.Value} {ao : V1.MemArg} {st : V1.Instr} (hS : StoreNumV10 v ao st)
    {a : Execution.Runtime.MemAddr} {m : MemInst}
    (hz : TypedV (simEnv10T B) stateT (stateV hn s f)) (hm : frameMemory s f = some (a, m))
    (hlt : m.data.size < effectiveAddress i ao + v.type.width / 8) :
    Fires (simEnv10T B) "Step" 7 (.tuple [
      configV hn ⟨s, f, [value ⟨.int .i32, i⟩, value v, .source st]⟩,
      configV hn ⟨s, f, [.trap]⟩]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("t", valTypeV v.type), ("c", numV v), ("ao", memargV ao)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Sim20.Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) := rfl
  have ft : (VarEnv.empty.bindVals σ).findVal? "t" = some (valTypeV v.type) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (numV v) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have hS' := envSame10T B
  have hq : QuantsOk (simEnv10T B) (VarEnv.empty.bindVals σ)
      (match storeNumTrapRule10 with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fz (hz _ hρ)
      (QuantsOk.cons fi (hasTypT (Whole.hasTyp_valNum10 ⟨.int .i32, i⟩
        Sim20.Pure.evalExp_caseNil))
      (QuantsOk.cons ft (hasTypT (Whole.typedV_valtype10 v.type _ hρ))
      (QuantsOk.cons fc (hasTypT (Whole.hasTyp_valNum10 v (Sim.evalExp_var ft)))
      (QuantsOk.cons fa (hasTypT (Whole.typedV_memarg10 ao _ hρ)) QuantsOk.nil))))
  refine Sim20.Pure.fires_of_ruleAt (hasRuleAtT (Whole.hasRuleAt10_storeNumTrap B)) σ hq
    (evalExp_of hS' (evalExp_tup2 (evalExp_storeNumLhs10 hS fz fi ft fc fa) (evalExp_zTrap10 fz)))
    ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_of hS' (prem10_of_trap rfl fz fi fa
    (evalExp_size10 v.type rfl (Sim.evalExp_var ft)) (width_cases v.type) hm hlt))

/-! ## Rule 9, forward -/

/-- **`Step/store-pack-trap` fires in `simEnv10T`** at the image of V1's packed `intStoreTrap`,
from a state typed in `simEnv10T`, at every builtins. -/
theorem fires10T_storePackTrap {s : Store H} {f : Frame} {i : BitVec 32} {t : IntType}
    {x : BitVec t.width} {sz : V1.PackSize} {ao : V1.MemArg} {a : Execution.Runtime.MemAddr}
    {m : MemInst} (hz : TypedV (simEnv10T B) stateT (stateV hn s f))
    (hm : frameMemory s f = some (a, m)) (hlt : m.data.size < effectiveAddress i ao + sz.width / 8) :
    Fires (simEnv10T B) "Step" 9 (.tuple [
      configV hn ⟨s, f, [value ⟨.int .i32, i⟩, value ⟨.int t, x⟩,
        .source (.intStore t (some sz) ao)]⟩,
      configV hn ⟨s, f, [.trap]⟩]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("Inn", valTypeV (.int t)), ("c", pctV x.toNat), ("n", .num (.natN sz.width)),
    ("ao", memargV ao)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Sim20.Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) := rfl
  have fInn : (VarEnv.empty.bindVals σ).findVal? "Inn" = some (valTypeV (.int t)) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV x.toNat) := rfl
  have fn : (VarEnv.empty.bindVals σ).findVal? "n" = some (.num (.natN sz.width)) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have hS' := envSame10T B
  have hq : QuantsOk (simEnv10T B) (VarEnv.empty.bindVals σ)
      (match storePackTrapRule10 with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fz (hz _ hρ)
      (QuantsOk.cons fi (hasTypT (Whole.hasTyp_valNum10 ⟨.int .i32, i⟩
        Sim20.Pure.evalExp_caseNil))
      (QuantsOk.cons fInn (hasTypT (Whole.typedV_inn10 t _ hρ))
      (QuantsOk.cons fc (hasTypT (Whole.hasTyp_valNum10 ⟨.int t, x⟩
        (evalExp_subE_iff.2 (Sim.evalExp_var fInn))))
      (QuantsOk.cons fn (hasTypT (Whole.typedV_n10 _ _ hρ))
      (QuantsOk.cons fa (hasTypT (Whole.typedV_memarg10 ao _ hρ)) QuantsOk.nil)))))
  refine Sim20.Pure.fires_of_ruleAt (hasRuleAtT (Whole.hasRuleAt10_storePackTrap B)) σ hq
    (evalExp_of hS' (evalExp_tup2 (evalExp_storePackLhs10 fz fi fInn fc fn fa)
      (evalExp_zTrap10 fz))) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_of hS' (prem10_of_trap rfl fz fi fa (Sim.evalExp_var fn)
    (packWidth10_cases sz) hm hlt))

/-! ## Rules 7 and 9, backward -/

/-- **`Step/store-num-trap` backwards in `simEnv10T`**, at a `GoodV1` configuration. -/
theorem bwd10T_storeNumTrap {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodV1 c) (hf : Fires (simEnv10T B) "Step" 7 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨s, f, code⟩ := c
  have hS := envSame10T B
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ :=
    Whole.firesCfg10_inv (hasRuleAtT (Whole.hasRuleAt10_storeNumTrap B)) hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := Whole.codes10_three (evalExps_back hS hes)
  obtain ⟨i, rfl, fi⟩ := Whole.constI32_of_lhs10 h₁
  obtain ⟨⟨ty, x⟩, rfl, hty⟩ := Whole.const_tc10 h₂
  obtain ⟨ao, fa, hd⟩ := Whole.storeNum_decode (evalExp_varE_iff.1 hty) h₃
  have ew : w = configV hn ⟨s, f, [.trap]⟩ :=
    EvalExp.unique (evalExp_back hS hrh) (evalExp_zTrap10 fz)
  have hlt : ∀ a m, frameMemory s f = some (a, m) →
      m.data.size < effectiveAddress i ao + ty.width / 8 := fun a m hm =>
    Whole.trap_of_prem10 fz (evalExp_varE_iff.1 fi) fa (evalExp_size10 ty rfl hty)
      (width_cases ty) hm (evalExp_back hS (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _))))
  rcases hd with ⟨t', rfl, rfl⟩ | ⟨t', rfl, rfl⟩
  · obtain ⟨a, m, hm⟩ := Whole.mem_of_good3 hg (fun h => h)
    exact ⟨_, ew, Whole.step_intStoreTrap hm (hlt a m hm)⟩
  · obtain ⟨a, m, hm⟩ := Whole.mem_of_good3 hg (fun h => h)
    exact ⟨_, ew, Whole.step_floatStoreTrap hm (hlt a m hm)⟩

/-- **`Step/store-pack-trap` backwards in `simEnv10T`**, at a `GoodV1` configuration. -/
theorem bwd10T_storePackTrap {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodV1 c) (hf : Fires (simEnv10T B) "Step" 9 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨s, f, code⟩ := c
  have hS := envSame10T B
  obtain ⟨σ, -, fz, hes, hrh, hp⟩ :=
    Whole.firesCfg10_inv (hasRuleAtT (Whole.hasRuleAt10_storePackTrap B)) hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := Whole.codes10_three (evalExps_back hS hes)
  obtain ⟨i, rfl, fi⟩ := Whole.constI32_of_lhs10 h₁
  obtain ⟨⟨ty, x⟩, rfl, hty⟩ := Whole.const_tc10 h₂
  obtain ⟨t, sz, ao, rfl, rfl, fa, fn⟩ := Whole.storePack_decode (Whole.inn_of_eval10 hty) h₃
  have ew : w = configV hn ⟨s, f, [.trap]⟩ :=
    EvalExp.unique (evalExp_back hS hrh) (evalExp_zTrap10 fz)
  obtain ⟨a, m, hm⟩ := Whole.mem_of_good3 hg (fun h => h)
  have hlt : m.data.size < effectiveAddress i ao + sz.width / 8 :=
    Whole.trap_of_prem10 fz (evalExp_varE_iff.1 fi) fa (Sim.evalExp_var fn) (packWidth10_cases sz)
      hm (evalExp_back hS (Sim20.Pure.ifPrem (hp _ (List.mem_singleton_self _))))
  exact ⟨_, ew, Whole.step_intStoreTrap hm hlt⟩

end Silmaril.Wasm.SpecTec.Sim10.StoreAgree
