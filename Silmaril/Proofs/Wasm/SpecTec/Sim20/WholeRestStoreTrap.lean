module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestCopyGt

/-!
# The store and vector-store trap rules backwards

`Step` 11 (`store-num-trap`), 13 (`store-pack-trap`), 15 (`vstore-oob`) and 17 (`vstore_lane-oob`)
of the wasm-2.0 script rewrite `z; CONST I32 i; c; STORE … ao` to `z; TRAP` under
`i + ao.OFFSET + w/8 > |$mem(z, 0).BYTES|`, where `w` is `$size(nt)`, the pack width `n`,
`$size(V128)` or the lane width `N`, and `w/8` is computed in `rat` and converted back (`evalExp_div8`).
At V2's `storeIntTrap`, `storeFloatTrap`, `storePackTrap`, `vecStoreOob` and `vecStoreLaneOob`
the premise is `|mi.bytes| < effAddr i ao + w/8`; the memory exists by `ResOkL`.

This discharges `Step` 11, 13, 15, 17 (`bwdStep_storeNumTrap`, `bwdStep_storePackTrap`,
`bwdStep_vstoreOob`, `bwdStep_vstoreLaneOob`), leaving the two `grow-succeed` rules (`BwdRestW10`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (natV evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm (PackSize NumType IntType FloatType)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (relRules)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## The bound `i + ao.OFFSET + w/8` -/

/-- `w/8`, in `rat` and back. -/
abbrev div8E (e : Exp) : Exp :=
  .cvtE (.binE .divOp (.numT .ratT) (.cvtE e .natT .ratT) (.cvtE (.numE (.natN 8)) .natT .ratT))
    .ratT .natT

/-- `ao.OFFSET.%.0`. -/
abbrev offE : Exp := .projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0

/-- `i.%.0 + ao.OFFSET.%.0 + e`. -/
abbrev addrE (e : Exp) : Exp :=
  .binE .addOp (.numT .natT) (.binE .addOp (.numT .natT) iPay offE) e

/-- The trap premise `i + ao.OFFSET + w/8 > |$mem(z, 0).BYTES|`. -/
abbrev storeTrapPrem (e : Exp) : Prem := .ifPr (.cmpE .gtOp (.numT .natT) (addrE (div8E e)) memLenE)

/-- A natural, converted from `rat`. -/
theorem cvt_ratNat (k : Nat) : Num.cvt .natT (.ratN (k : Rat)) = some (.natN k) := by
  simp [Num.cvt]

/-- **`w/8` at the widths of Wasm.** -/
theorem evalExp_div8 {env : Env} {ρ : VarEnv} {e : Exp} {w : Nat}
    (he : EvalExp env ρ e (.num (.natN w)))
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128) :
    EvalExp env ρ (div8E e) (.num (.natN (w / 8))) := by
  have h₈ : EvalExp env ρ (.cvtE (.numE (.natN 8)) .natT .ratT) (.num (.ratN 8)) :=
    evalExp_cvtNum (evalExp_numE_iff.2 rfl) rfl
  have hd : EvalExp env ρ (.binE .divOp (.numT .ratT) (.cvtE e .natT .ratT)
      (.cvtE (.numE (.natN 8)) .natT .ratT)) (.num (.ratN ((w : Rat) / 8))) :=
    evalExp_binNum (evalExp_cvtNum he rfl) h₈ (by simp [Num.bin])
  have h8 : (w : Rat) / 8 = ((w / 8 : Nat) : Rat) := by
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> norm_num
  rw [h8] at hd
  exact evalExp_cvtNum hd (cvt_ratNat _)

/-- `ao.OFFSET.%.0` at a memarg. -/
theorem evalExp_off {env : Env} {ρ : VarEnv} {a : V2.MemArg}
    (h : ρ.findVal? "ao" = some (memargV a)) : EvalExp env ρ offE (.num (.natN a.offset.val)) :=
  evalExp_projE_iff.2 ⟨[.num (.natN a.offset.val)], evalExp_uncaseE_iff.2
    (evalExp_dotE_iff.2 ⟨_, evalExp_var h, rfl⟩), Int.le_refl 0, rfl⟩

/-- **The trap premise, read back.** -/
theorem trap_of_prem {σ : List (IL.Id × Value)} {e : Exp} {s : Store H} {f : Frame} {i : BitVec 32}
    {a : V2.MemArg} {w ad : Nat} {mi : MemInst}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat))
    (fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV a))
    (he : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) e (.num (.natN w)))
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128)
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hp : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.cmpE .gtOp (.numT .natT) (addrE (div8E e)) memLenE) (.bool true)) :
    mi.bytes.size < effAddr i.toNat a + w / 8 := by
  have h := cmp_of_prem hp (evalExp_addNat20 (evalExp_addNat20 (evalExp_iPay fi) (evalExp_off fa))
    (evalExp_div8 he hw)) (evalExp_memLen20 rfl fz ha hm)
  have h' : mi.bytes.size < i.toNat + a.offset.val + w / 8 := by
    simpa [cmpValues, Num.cmp, Res.ofOption] using h
  exact h'

/-- `z; TRAP`. -/
abbrev zTrapRhs : Exp := .caseE "%;%" (.tupE [.varE "z", trapRhs])

/-- `z; TRAP`, evaluated. -/
theorem evalExp_zTrap {ρ : VarEnv} {s : Store H} {f : Frame}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) :
    EvalExp (simEnv20 B) ρ zTrapRhs (configV hn ⟨s, f, [.trap]⟩) :=
  evalExp_case (evalExp_tup2 (evalExp_var fz) evalExp_trapRhs)

/-! ## The rules, verbatim -/

/-- `Step/vstore-oob`, rule 15 (verbatim). -/
def vstoreOobRule : Rule :=
  .ruleD "vstore-oob" [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA
    (.caseE "I32" (.tupE []))]), .expP "c" (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]),
    .expP "ao" (.varT "memarg" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c"]),
      .caseE "VSTORE" (.tupE [.caseE "V128" (.tupE []), .varE "ao"])]]), zTrapRhs])
    [storeTrapPrem (.callE "size" [.expA (.caseE "V128" (.tupE []))])]

/-- `Step/vstore_lane-oob`, rule 17 (verbatim). -/
def vstoreLaneOobRule : Rule :=
  .ruleD "vstore_lane-oob" [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA
    (.caseE "I32" (.tupE []))]), .expP "c" (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]),
    .expP "N" (.varT "N" []), .expP "ao" (.varT "memarg" []), .expP "j" (.varT "laneidx" [])]
    "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c"]),
      .caseE "VSTORE_LANE" (.tupE [.caseE "V128" (.tupE []), .caseE "%" (.tupE [.varE "N"]),
        .varE "ao", .varE "j"])]]), zTrapRhs])
    [storeTrapPrem (.varE "N")]

/-- `Step/store-num-trap`, rule 11 (verbatim). -/
def storeNumTrapRule : Rule :=
  .ruleD "store-num-trap" [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA
    (.caseE "I32" (.tupE []))]), .expP "nt" (.varT "numtype" []),
    .expP "c" (.varT "num_" [.expA (.varE "nt")]), .expP "ao" (.varT "memarg" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "CONST" (.tupE [.varE "nt", .varE "c"]),
      .caseE "STORE" (.tupE [.varE "nt", .optE none, .varE "ao"])]]), zTrapRhs])
    [storeTrapPrem (.callE "size" [.expA (.subE (.varE "nt") (.varT "numtype" [])
      (.varT "valtype" []))])]

/-- `Inn <: numtype`. -/
abbrev innE : Exp := .subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])

/-- `Step/store-pack-trap`, rule 13 (verbatim). -/
def storePackTrapRule : Rule :=
  .ruleD "store-pack-trap" [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA
    (.caseE "I32" (.tupE []))]), .expP "Inn" (.varT "Inn" []),
    .expP "c" (.varT "num_" [.expA innE]), .expP "n" (.varT "n" []),
    .expP "ao" (.varT "memarg" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE, .caseE "CONST" (.tupE [innE, .varE "c"]),
      .caseE "STORE" (.tupE [innE, .optE (some (.caseE "%" (.tupE [.varE "n"]))), .varE "ao"])]]),
      zTrapRhs])
    [storeTrapPrem (.varE "n")]

theorem hasRuleAt_vstoreOob : HasRuleAt (simEnv20 B) "Step" "%~>%" 15 vstoreOobRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_vstoreLaneOob : HasRuleAt (simEnv20 B) "Step" "%~>%" 17 vstoreLaneOobRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_storeNumTrap : HasRuleAt (simEnv20 B) "Step" "%~>%" 11 storeNumTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_storePackTrap : HasRuleAt (simEnv20 B) "Step" "%~>%" 13 storePackTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Heads, operands, `$size(V128)` -/

theorem head20_vconst {a : Admin} (h : adminHead20 a = "VCONST") : ∃ c, a = .plain (.vecConst c) := by
  revert h; admin_head_inv20

theorem head20_vstore {a : Admin} (h : adminHead20 a = "VSTORE") : ∃ ao, a = .plain (.vecStore ao) := by
  revert h; admin_head_inv20

theorem head20_vstoreLane {a : Admin} (h : adminHead20 a = "VSTORE_LANE") :
    ∃ sz ao j, a = .plain (.vecStoreLane sz ao j) := by
  revert h; admin_head_inv20

theorem head20_store {a : Admin} (h : adminHead20 a = "STORE") :
    (∃ t p ao, a = .plain (.intStore t p ao)) ∨ (∃ t ao, a = .plain (.floatStore t ao)) := by
  revert h
  cases a with
  | plain i =>
    cases i <;> simp [adminHead20, instrHead20]
  | _ => simp [adminHead20]

set_option maxRecDepth 100000 in
/-- `$size(V128) = 128`. -/
theorem evalExp_sizeV128 {ρ : VarEnv} (hρ : ρ.findDef? "size" = none) :
    EvalExp (simEnv20 B) ρ (.callE "size" [.expA (.caseE "V128" (.tupE []))]) (.num (.natN 128)) := by
  refine evalExp_callE_iff.2 (callDef_of_tryClauses hρ (Pure.findDef_size20 B)
    (evalArgs_cons (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)) evalArgs_nil) ?_)
  repeat (refine tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
    (matchExp_caseE_undef (by decide)))) ?_)
  exact tryClauses_hit (ρ₀ := VarEnv.empty)
    (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil)
    premsHold_nil (evalExp_numE_iff.2 rfl)

/-- The memory, from `GoodW` at a store instruction (third of three). -/
theorem mem_of_goodW3 {s : Store H} {f : Frame} {a₁ a₂ : Admin} {i : V2.Instr}
    (hg : GoodW ⟨s, f, [a₁, a₂, .plain i]⟩)
    (hi : InstrResOk (⟨s, f⟩ : State H) i → ((⟨s, f⟩ : State H).mem? memIdx0).isSome) :
    ∃ ad mi, f.module.memAddr? memIdx0 = some ad ∧ s.memInst? ad = some mi := by
  have hres : InstrResOk (⟨s, f⟩ : State H) i := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.1
  exact mem_of_isSome (hi hres)

/-! ## The rules backwards -/

/-- **`Step/vstore-oob` backwards**, at a `GoodW` configuration. -/
theorem bwdStep_vstoreOob {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodW c) (hf : Fires (simEnv20 B) "Step" 15 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hr, hp⟩ := firesCfg_full20 hasRuleAt_vstoreOob hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes20_three hes
  obtain ⟨i, rfl, fi⟩ := constI_of_lhs h₁
  obtain ⟨v, rfl⟩ := head20_vconst (head20_of_caseE h₂)
  obtain ⟨ao, rfl⟩ := head20_vstore (head20_of_caseE h₃)
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) :=
    var_snd (tup_of_caseE h₃ (us := [caseNilV "V128", memargV ao]) rfl)
  obtain ⟨ad, mi, ha, hm⟩ := mem_of_goodW3 hg (fun h => h)
  have hlt := trap_of_prem fz fi fa (evalExp_sizeV128 rfl) (by decide) ha hm
    (Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨_, EvalExp.unique hr (evalExp_zTrap fz), .vecStoreOob ha hm hlt⟩

/-- The pattern `% N`, read back at a pack width. -/
theorem width_of_pct {ρ : VarEnv} {sz : PackSize}
    (h : EvalExp (simEnv20 B) ρ (.caseE "%" (.tupE [.varE "N"])) (szV sz)) :
    ρ.findVal? "N" = some (.num (.natN sz.width)) := by
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 h
  have eu : u = .tuple [.num (.natN sz.width)] := by
    simp only [szV, pctV, Value.case.injEq] at hcu
    exact hcu.2.symm
  exact var_fst (Sim.RefsGC.elems_of_tup (eu ▸ hu))

/-- The operands of `VSTORE_LANE V128 (% N) ao j`, read back. -/
theorem vstoreLane_scope {ρ : VarEnv} {sz : PackSize} {ao : V2.MemArg} {j : LaneIdx}
    (h : EvalExp (simEnv20 B) ρ (.caseE "VSTORE_LANE" (.tupE [.caseE "V128" (.tupE []),
      .caseE "%" (.tupE [.varE "N"]), .varE "ao", .varE "j"]))
      (adminToV (.plain (.vecStoreLane sz ao j)))) :
    ρ.findVal? "ao" = some (memargV ao) ∧ ρ.findVal? "N" = some (.num (.natN sz.width)) := by
  have hs := tup_of_caseE h (us := [caseNilV "V128", szV sz, memargV ao, pctV j.val]) rfl
  obtain ⟨u₁, ws, -, hws, he₁⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hs
  have e₁ : ws = [szV sz, memargV ao, pctV j.val] := (List.cons.inj he₁).2.symm
  subst e₁
  obtain ⟨u₂, ws', hu₂, -, he₂⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hws
  have e₂ : u₂ = szV sz := (List.cons.inj he₂).1.symm
  exact ⟨var_snd hws, width_of_pct (e₂ ▸ hu₂)⟩

theorem packWidth_cases (sz : PackSize) :
    sz.width = 8 ∨ sz.width = 16 ∨ sz.width = 32 ∨ sz.width = 64 ∨ sz.width = 128 := by
  cases sz <;> simp [PackSize.width]

/-- **`Step/vstore_lane-oob` backwards**, at a `GoodW` configuration. -/
theorem bwdStep_vstoreLaneOob {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodW c) (hf : Fires (simEnv20 B) "Step" 17 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hr, hp⟩ := firesCfg_full20 hasRuleAt_vstoreLaneOob hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes20_three hes
  obtain ⟨i, rfl, fi⟩ := constI_of_lhs h₁
  obtain ⟨v, rfl⟩ := head20_vconst (head20_of_caseE h₂)
  obtain ⟨sz, ao, j, rfl⟩ := head20_vstoreLane (head20_of_caseE h₃)
  obtain ⟨fa, fN⟩ := vstoreLane_scope h₃
  obtain ⟨ad, mi, ha, hm⟩ := mem_of_goodW3 hg (fun h => h)
  have hlt := trap_of_prem fz fi fa (evalExp_var fN) (packWidth_cases sz) ha hm
    (Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨_, EvalExp.unique hr (evalExp_zTrap fz), .vecStoreLaneOob ha hm hlt⟩

/-- The second component of a three-element payload. -/
theorem snd_of3 {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v₁ v₂ v₃ : Value}
    (h : EvalExps env ρ [e₁, e₂, e₃] [v₁, v₂, v₃]) : EvalExp env ρ e₂ v₂ := by
  obtain ⟨w₁, ws, -, hws, he₁⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 h
  have e₁ : ws = [v₂, v₃] := (List.cons.inj he₁).2.symm
  subst e₁
  obtain ⟨u₂, ws', hu₂, -, he₂⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hws
  have e₂ : u₂ = v₂ := (List.cons.inj he₂).1.symm
  exact e₂ ▸ hu₂

/-- The third component of a three-element payload, a variable. -/
theorem thd_of3 {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {x : IL.Id} {v₁ v₂ v₃ : Value}
    (h : EvalExps env ρ [e₁, e₂, .varE x] [v₁, v₂, v₃]) : ρ.findVal? x = some v₃ := by
  obtain ⟨w₁, ws, -, hws, he₁⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 h
  have e₁ : ws = [v₂, v₃] := (List.cons.inj he₁).2.symm
  subst e₁
  exact var_snd hws

/-- `$size(nt <: valtype)` at a number type. -/
theorem evalExp_sizeNt {ρ : VarEnv} {t : NumType} (hρ : ρ.findDef? "size" = none)
    (fnt : ρ.findVal? "nt" = some (numTypeV t)) :
    EvalExp (simEnv20 B) ρ (.callE "size" [.expA (.subE (.varE "nt") (.varT "numtype" [])
      (.varT "valtype" []))]) (.num (.natN t.width)) :=
  evalExp_callE_iff.2 (Pure.callDef_size20 t hρ
    (evalArgs_cons (evalExp_subE_iff.2 (evalExp_var fnt)) evalArgs_nil))

theorem width_cases (t : NumType) :
    t.width = 8 ∨ t.width = 16 ∨ t.width = 32 ∨ t.width = 64 ∨ t.width = 128 := by
  rcases t with (_ | _) | (_ | _) <;> simp [NumType.width, IntType.width, FloatType.width]

/-- The operands of `CONST nt c; STORE nt ε ao`, read back. -/
theorem storeNum_decode {ρ : VarEnv} {t : NumType} {x : BitVec t.width} {a₃ : Admin}
    (h₂ : EvalExp (simEnv20 B) ρ (.caseE "CONST" (.tupE [.varE "nt", .varE "c"]))
      (adminToV (Val.num ⟨t, x⟩).toAdmin))
    (h₃ : EvalExp (simEnv20 B) ρ (.caseE "STORE" (.tupE [.varE "nt", .optE none, .varE "ao"]))
      (adminToV a₃)) :
    ρ.findVal? "nt" = some (numTypeV t) ∧
      ((∃ t' ao, t = .int t' ∧ a₃ = .plain (.intStore t' none ao) ∧
          ρ.findVal? "ao" = some (memargV ao)) ∨
        (∃ t' ao, t = .float t' ∧ a₃ = .plain (.floatStore t' ao) ∧
          ρ.findVal? "ao" = some (memargV ao))) := by
  have fnt := var_fst (tup_of_caseE h₂ (adminToV_numAdmin t x))
  refine ⟨fnt, ?_⟩
  rcases head20_store (head20_of_caseE h₃) with ⟨t', p, ao, rfl⟩ | ⟨t', ao, rfl⟩
  · have hs := tup_of_caseE h₃ (us := [numTypeV (.int t'), .opt (p.map szV), memargV ao]) rfl
    have et : t = .int t' := numTypeV_inj (Option.some.inj (fnt.symm.trans (var_fst hs)))
    have hp0 : p = none := by
      have h := evalExp_optE_none_iff.1 (snd_of3 hs)
      cases p <;> simp_all
    exact .inl ⟨t', ao, et, by rw [hp0], thd_of3 hs⟩
  · have hs := tup_of_caseE h₃ (us := [numTypeV (.float t'), .opt none, memargV ao]) rfl
    have et : t = .float t' := numTypeV_inj (Option.some.inj (fnt.symm.trans (var_fst hs)))
    exact .inr ⟨t', ao, et, rfl, thd_of3 hs⟩

/-- **`Step/store-num-trap` backwards**, at a `GoodW` configuration. -/
theorem bwdStep_storeNumTrap {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodW c) (hf : Fires (simEnv20 B) "Step" 11 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hr, hp⟩ := firesCfg_full20 hasRuleAt_storeNumTrap hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes20_three hes
  obtain ⟨i, rfl, fi⟩ := constI_of_lhs h₁
  obtain ⟨t, x, rfl⟩ := num_of_const (head20_of_caseE h₂)
  obtain ⟨fnt, ⟨t', ao, rfl, rfl, fa⟩ | ⟨t', ao, rfl, rfl, fa⟩⟩ := storeNum_decode h₂ h₃
  · obtain ⟨ad, mi, ha, hm⟩ := mem_of_goodW3 hg (fun h => h)
    exact ⟨_, EvalExp.unique hr (evalExp_zTrap fz), .storeIntTrap ha hm (trap_of_prem fz fi fa
      (evalExp_sizeNt rfl fnt) (width_cases (.int t')) ha hm
      (Pure.ifPrem (hp _ (List.mem_singleton_self _))))⟩
  · obtain ⟨ad, mi, ha, hm⟩ := mem_of_goodW3 hg (fun h => h)
    exact ⟨_, EvalExp.unique hr (evalExp_zTrap fz), .storeFloatTrap ha hm (trap_of_prem fz fi fa
      (evalExp_sizeNt rfl fnt) (width_cases (.float t')) ha hm
      (Pure.ifPrem (hp _ (List.mem_singleton_self _))))⟩

/-- The first component of a payload `(Inn <: numtype, …)`, read back. -/
theorem inn_of_fst {ρ : VarEnv} {es : List Exp} {u : Value} {us : List Value}
    (h : EvalExps (simEnv20 B) ρ (innE :: es) (u :: us)) : ρ.findVal? "Inn" = some u := by
  obtain ⟨u', us', hu, -, he⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 h
  have e : u' = u := (List.cons.inj he).1.symm
  exact e ▸ evalExp_varE_iff.1 (evalExp_subE_iff.1 hu)

/-- The operands of `CONST Inn c; STORE Inn (% n) ao`, read back. -/
theorem storePack_decode {ρ : VarEnv} {t : NumType} {x : BitVec t.width} {a₃ : Admin}
    (h₂ : EvalExp (simEnv20 B) ρ (.caseE "CONST" (.tupE [innE, .varE "c"]))
      (adminToV (Val.num ⟨t, x⟩).toAdmin))
    (h₃ : EvalExp (simEnv20 B) ρ (.caseE "STORE" (.tupE [innE,
      .optE (some (.caseE "%" (.tupE [.varE "n"]))), .varE "ao"])) (adminToV a₃)) :
    ∃ t' sz ao, t = .int t' ∧ a₃ = .plain (.intStore t' (some sz) ao) ∧
      ρ.findVal? "ao" = some (memargV ao) ∧ ρ.findVal? "n" = some (.num (.natN sz.width)) := by
  have fInn := inn_of_fst (tup_of_caseE h₂ (adminToV_numAdmin t x))
  rcases head20_store (head20_of_caseE h₃) with ⟨t', p, ao, rfl⟩ | ⟨t', ao, rfl⟩
  · have hs := tup_of_caseE h₃ (us := [numTypeV (.int t'), .opt (p.map szV), memargV ao]) rfl
    have et : t = .int t' := numTypeV_inj (Option.some.inj (fInn.symm.trans (inn_of_fst hs)))
    obtain ⟨u, hu, hpu⟩ := evalExp_optE_some_iff.1 (snd_of3 hs)
    obtain ⟨sz, rfl, rfl⟩ : ∃ sz, p = some sz ∧ u = szV sz := by
      cases p with
      | none => simp at hpu
      | some sz => exact ⟨sz, rfl, by simpa using hpu.symm⟩
    obtain ⟨u', hu', hcu⟩ := evalExp_caseE_iff.1 hu
    have eu : u' = .tuple [.num (.natN sz.width)] := by
      simp only [szV, pctV, Value.case.injEq] at hcu
      exact hcu.2.symm
    exact ⟨t', sz, ao, et, rfl, thd_of3 hs, var_fst (Sim.RefsGC.elems_of_tup (eu ▸ hu'))⟩
  · have hs := tup_of_caseE h₃ (us := [numTypeV (.float t'), .opt none, memargV ao]) rfl
    obtain ⟨u, -, hpu⟩ := evalExp_optE_some_iff.1 (snd_of3 hs)
    simp at hpu

/-- **`Step/store-pack-trap` backwards**, at a `GoodW` configuration. -/
theorem bwdStep_storePackTrap {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodW c) (hf : Fires (simEnv20 B) "Step" 13 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hr, hp⟩ := firesCfg_full20 hasRuleAt_storePackTrap hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes20_three hes
  obtain ⟨i, rfl, fi⟩ := constI_of_lhs h₁
  obtain ⟨t, x, rfl⟩ := num_of_const (head20_of_caseE h₂)
  obtain ⟨t', sz, ao, rfl, rfl, fa, fN⟩ := storePack_decode h₂ h₃
  obtain ⟨ad, mi, ha, hm⟩ := mem_of_goodW3 hg (fun h => h)
  exact ⟨_, EvalExp.unique hr (evalExp_zTrap fz), .storePackTrap ha hm (trap_of_prem fz fi fa
    (evalExp_var fN) (packWidth_cases sz) ha hm (Pure.ifPrem (hp _ (List.mem_singleton_self _))))⟩

/-! ## What is left -/

/-- The `Step` rules discharged here. -/
def doneStep10 : List Nat := [11, 13, 15, 17]

/-- **What is left of `BwdRestW9`**: the two `grow-succeed` rules, `Step` 8 and 19. -/
structure BwdRestW10 (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) :
    Prop where
  step : ∀ (i : Nat), i ∈ [8, 19] → ∀ (c : Config H) (w : Value), GoodW c →
    Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-- A `Step` rule beyond the 22 does not fire. -/
theorem not_firesStep_ge {i : Nat} (hi : 22 ≤ i) {v : Value} :
    ¬ Fires (simEnv20 B) "Step" i v := by
  rintro ⟨t, rules, r, hrel, hr, -⟩
  have hl : rules.length = 22 := by
    have h : relRules (simEnv20 B) "Step" = rules := by simp [relRules, hrel]
    rw [← h, relRules_simEnv20]
    have h22 : stepTags20.length = 22 := rfl
    have := congrArg List.length stepTags20_eq
    rw [List.length_map, h22] at this
    exact this
  have : rules[i]? = none := List.getElem?_eq_none (by omega)
  rw [this] at hr
  cases hr

/-- `BwdRestW9` from what is left. -/
theorem bwdRestW9_of_rest10 {P : Profile} {host : HostSemantics H} (R : BwdRestW10 B hn P host) :
    BwdRestW9 B hn P host where
  step i h6 hin hdn c w hg hf := by
    by_cases hi : i < 22
    · have hm := step9_left hi h6 hin hdn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
      · exact R.step 8 (by simp) c w hg hf
      · exact bwdStep_storeNumTrap hg hf
      · exact bwdStep_storePackTrap hg hf
      · exact bwdStep_vstoreOob hg hf
      · exact bwdStep_vstoreLaneOob hg hf
      · exact R.step 19 (by simp) c w hg hf
    · exact absurd hf (not_firesStep_ge (by omega))

/-- **`Task.wholeStepBwdW` from the two `grow-succeed` rules** (`BwdRestW10`). -/
theorem wholeStepBwdW_of_rest10
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
        BwdRestW10 (Sim.Floats.floatIntB (Profile.spec nd r)) hn (Profile.spec nd r) host) :
    Task.wholeStepBwdW :=
  wholeStepBwdW_of_rest9 fun H hn hinj host nd r => bwdRestW9_of_rest10 (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim20.Whole
