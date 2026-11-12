module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdPureStep.Drop

/-!
# Track bwd-pure-step: `table.set`, backward (`Step` 13, 14)

The premise reads `$table(z, x).REFS`, which evaluates only when the module lists `x` and the
store holds the address (`table_inv`); this is Core's `s.table? f x`. The address-typed
operand `CONST at i` is decoded by `aconst_of_lhs` (`at` is a typed `addrtype`). For
`table.set-val`, the forward evaluation of `$with_table` (`State.evalExp_withTable`) names the
successor. Needs `B` not to interpret `$table` (true of `Prims.builtins`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdPureStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge (moduleInstToValue)

theorem head_tableSet {a : Admin} (h : Typing.adminHead a = "TABLE.SET") :
    ∃ x, a = .plain (.tableSet x) := by
  revert h
  admin_head_inv

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem addrtypeCases_heads :
    (IntNumeric.instCases Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d88 0).map
      (fun c : TypCase => match c with | .mk o _ _ _ => o) = ["I32", "I64"] := rfl

/-- A typed `addrtype` is `I32` or `I64`. -/
theorem head_of_typed_addrtype {ρ : VarEnv} (hρ : ValsOnly ρ) {v : Value}
    (h : HasTyp (simEnv B) ρ (.varT "addrtype" []) v) :
    ∃ op w, v = .case op w ∧ op ∈ ["I32", "I64"] := by
  have hl : localTyp? ρ "addrtype" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [Typing.findTyp_addrtype] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hrest
  · obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
    obtain ⟨t, qs, prems, hm, -⟩ := hasTypCase_mem hc
    have hmem := List.mem_map_of_mem (f := fun c : TypCase => match c with | .mk o _ _ _ => o) hm
    rw [addrtypeCases_heads] at hmem
    exact ⟨op, w, rfl, hmem⟩
  · exact absurd hrest not_hasTypInsts_nil

/-- An image `CONST (op w) u` with `op` an address type's tag is an address-typed constant. -/
theorem aconst_of_image {a : Admin} {op : MixopS} {w u : Value}
    (he : adminToV a = .case "CONST" (.tuple [.case op w, u])) (hop : op ∈ ["I32", "I64"]) :
    ∃ (at_ : AddrType) (b : BitVec at_.intType.width), a = aconst at_ b ∧ u = pctV b.toNat := by
  rcases Typing.head_const (Typing.adminToV_case he).symm with ⟨t, b, rfl⟩ | ⟨t, b, rfl⟩
  · cases t with
    | i32 =>
        have he' : Value.case "CONST" (.tuple [caseNilV "I32", pctV b.toNat]) =
            .case "CONST" (.tuple [.case op w, u]) := he
        simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at he'
        exact ⟨.i32, b, rfl, he'.2.symm⟩
    | i64 =>
        have he' : Value.case "CONST" (.tuple [caseNilV "I64", pctV b.toNat]) =
            .case "CONST" (.tuple [.case op w, u]) := he
        simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at he'
        exact ⟨.i64, b, rfl, he'.2.symm⟩
  · exfalso
    have hf : Value.case "CONST" (.tuple [Vec.numTypeV (.float t), Sim.floatV t b]) =
        .case "CONST" (.tuple [.case op w, u]) := (Typing.toValue_numType (.float t)) ▸ he
    cases t <;> simp [Vec.numTypeV, caseNilV] at hf <;> simp [← hf.1] at hop

/-- **A `CONST at i` element of a left-hand side, `at` a typed `addrtype`**, is an
address-typed constant. -/
theorem aconst_of_lhs {σ : List (IL.Id × Value)} {qs : List Param} {a : Admin}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) qs)
    (hm : Param.expP "at" (.varT "addrtype" []) ∈ qs)
    (h : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i"])) (adminToV a)) :
    ∃ (at_ : AddrType) (b : BitVec at_.intType.width), a = aconst at_ b ∧
      (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV b.toNat) := by
  obtain ⟨u, hu, he⟩ := payload_of_caseE h
  obtain ⟨u₁, u₂, hu₁, hu₂, rfl⟩ := State.evalExp_tup2_inv hu
  obtain ⟨AT, fAT, tAT⟩ := hq "at" _ hm
  have e₁ : u₁ = AT := EvalExp.unique (evalExp_subE_iff.1 hu₁) (evalExp_var fAT)
  obtain ⟨op, w, hw, hop⟩ := head_of_typed_addrtype (valsOnly_bindVals σ) tAT
  have he' : adminToV a = .case "CONST" (.tuple [.case op w, u₂]) := by rw [he, e₁, hw]
  obtain ⟨at_, b, rfl, hb⟩ := aconst_of_image he' hop
  exact ⟨at_, b, rfl, hb ▸ evalExp_varE_iff.1 hu₂⟩

variable (B)
variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-- **`$table(z, x)`, inverted**: the module lists `x` and the store holds the table. -/
theorem table_inv (hb : ∀ Z X : Value, B.call "table" [.val Z, .val X] = none) {ρ : VarEnv}
    (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {k : Nat} {T : Value}
    (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])))
    (h : EvalExp (simEnv B) ρ (.callE "table" [.expA (.varE "z"), .expA (.varE "x")]) T) :
    ∃ ta ti, f.module.tables[k]? = some ta ∧ s.tables[ta]? = some ti ∧
      T = tableInstToValue CT ti := by
  have D := State.stateDefs_simEnv B
  have hbody := evalExp_call1_inv D.table (Prims.findDef_none_of_valsOnly hρ _) (hb _ _)
    (evalArgs_cons (evalExp_var fz) (evalArgs_cons (evalExp_var fx) evalArgs_nil))
    State.matchArgs_zxPat h
  obtain ⟨L, j, hL, hj, hLj⟩ := evalExp_idxE_iff.1 hbody
  have eL : L = .list (s.tables.map (tableInstToValue CT)) :=
    EvalExp.unique hL (evalExp_dotE_iff.2 ⟨_, State.evalExp_sof D rfl (evalExp_var rfl),
      State.storeV_TABLES hn s⟩)
  obtain ⟨ta, hta, hj'⟩ := moduleIdx_inv D rfl rfl rfl (State.moduleV_TABLES _) hj
  have hj'' : j = ta := by simpa using hj'
  have hLt : (s.tables.map (tableInstToValue CT))[ta]? = some T := by
    rw [eL, hj''] at hLj
    exact hLj
  rw [List.getElem?_map] at hLt
  obtain ⟨ti, hti, he⟩ := Option.map_eq_some_iff.1 hLt
  exact ⟨ta, ti, hta, hti, he.symm⟩

/-- The premise `i!%.0 ⋈ |$table(z, x).REFS|`, read back. -/
theorem tablePrem_inv (hb : ∀ Z X : Value, B.call "table" [.val Z, .val X] = none)
    {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {k n : Nat} {op : CmpOp}
    (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])))
    (fi : ρ.findVal? "i" = some (pctV n))
    (h : EvalExp (simEnv B) ρ (.cmpE op (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
      (.lenE (.dotE (.callE "table" [.expA (.varE "z"), .expA (.varE "x")]) "REFS")))
      (.bool true)) :
    ∃ ta ti, f.module.tables[k]? = some ta ∧ s.tables[ta]? = some ti ∧
      cmpValues op (.num (.natN n)) (.num (.natN ti.refs.length)) = .ok (.bool true) := by
  obtain ⟨v₁, v₂, e₁, e₂, hc⟩ := evalExp_cmpE_iff.1 h
  have ev₁ : v₁ = .num (.natN n) := EvalExp.unique e₁ (RefsGC.evalExp_unpct (evalExp_var fi))
  subst ev₁
  obtain ⟨vs, hvs, rfl⟩ := evalExp_lenE_iff.1 e₂
  obtain ⟨T, hT, hTf⟩ := evalExp_dotE_iff.1 hvs
  obtain ⟨ta, ti, hta, hti, rfl⟩ := table_inv B hb hρ fz fx hT
  rw [State.tableInstV_REFS, Option.some.injEq, Value.list.injEq] at hTf
  subst hTf
  rw [List.length_map] at hc
  exact ⟨ta, ti, hta, hti, hc⟩

variable {w : Value}

/-- `Backward.step 13` (`table.set-oob`). -/
theorem bwd_tableSetOob (hb : ∀ Z X : Value, B.call "table" [.val Z, .val X] = none)
    {c : Config H} (hf : Fires (simEnv B) "Step" 13 (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, hp⟩ := fires_step (hasStepRules_simEnv B).tableSetOob hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes_three hes
  obtain ⟨at_, i, rfl, fi⟩ := aconst_of_lhs hq (.tail _ (.head _)) h₁
  obtain ⟨r, rfl, -⟩ := ref_of_var hq (.tail _ (.tail _ (.tail _ (.head _)))) h₂
  obtain ⟨x, rfl⟩ := head_tableSet (head_of_caseE h₃)
  obtain ⟨ta, ti, hta, hti, hc⟩ := tablePrem_inv B hb (valsOnly_bindVals σ) fz
    (idx_of_var h₃ rfl) fi (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
  have hge : ti.refs.length ≤ i.toNat := by simpa [cmpValues, Num.cmp, Res.ofOption] using hc
  have ht : s.table? f x = some (ta, ti) := by simp [Store.table?, hta, hti]
  exact ⟨⟨s, f, [.trap]⟩, EvalExp.unique hr (by beval), .table (.setOob ht hge)⟩

/-- `$with_table(z, x, i!%.0, ref)` at a table in range, evaluated forward. -/
theorem withTable_eval {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} {f : Frame}
    {x : TableIdx} {n ta : Nat} {ti : TableInst} {r : Ref}
    (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (.case "%" (.tuple [.num (.natN x.toNat)])))
    (fi : ρ.findVal? "i" = some (pctV n)) (fr : ρ.findVal? "ref" = some (refToValue r))
    (hta : f.module.tables[x.toNat]? = some ta) (hti : s.tables[ta]? = some ti)
    (hlt : n < ti.refs.length) :
    EvalExp (simEnv B) ρ (.callE "with_table" [.expA (.varE "z"), .expA (.varE "x"),
      .expA (.projE (.uncaseE (.varE "i") "%") 0), .expA (.varE "ref")])
      (stateV hn (s.setTable ta { ti with refs := ti.refs.set n r }) f) :=
  State.evalExp_withTable (State.stateDefs_simEnv B)
    (Prims.findDef_none_of_valsOnly hρ _) (evalExp_var fz) (evalExp_var fx)
    (RefsGC.evalExp_unpct (evalExp_var fi)) (evalExp_var fr) (State.storeV_TABLES hn s)
    (State.frameV_MODULE f) (State.moduleV_TABLES _) (State.getElem?_map_natN hta)
    (by simp [hti]) (State.tableInstV_REFS ti) (by simpa using hlt)
    (State.tableInstV_setRef ti n r) (State.storeV_setTable hn s ta _)

/-- `Backward.step 14` (`table.set-val`). -/
theorem bwd_tableSetVal (hb : ∀ Z X : Value, B.call "table" [.val Z, .val X] = none)
    {c : Config H} (hf : Fires (simEnv B) "Step" 14 (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, hp⟩ := fires_step (hasStepRules_simEnv B).tableSetVal hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes_three hes
  obtain ⟨at_, i, rfl, fi⟩ := aconst_of_lhs hq (.tail _ (.head _)) h₁
  obtain ⟨r, rfl, fr⟩ := ref_of_var hq (.tail _ (.tail _ (.tail _ (.head _)))) h₂
  obtain ⟨x, rfl⟩ := head_tableSet (head_of_caseE h₃)
  have fx := idx_of_var h₃ rfl
  have hρ := valsOnly_bindVals σ
  obtain ⟨ta, ti, hta, hti, hc⟩ := tablePrem_inv B hb hρ fz fx fi
    (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
  have hlt : i.toNat < ti.refs.length := by simpa [cmpValues, Num.cmp, Res.ofOption] using hc
  have ht : s.table? f x = some (ta, ti) := by simp [Store.table?, hta, hti]
  obtain ⟨W₁, hW₁, rfl⟩ := rhs_nil hr
  have e₁ := EvalExp.unique hW₁ (withTable_eval B hρ fz fx fi fr hta hti hlt)
  exact ⟨_, by rw [e₁]; rfl, .table (.setVal ht hlt)⟩

end Silmaril.Wasm.SpecTec.Sim.BwdPureStep
