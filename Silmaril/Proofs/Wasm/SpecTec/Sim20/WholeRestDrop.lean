module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestInert

/-!
# `elem.drop` and `data.drop` backwards, at any `GoodW` configuration

Rules 10 (`elem.drop`) and 21 (`data.drop`) of the wasm-2.0 `Step` have no premise. They write
through `$with_elem(z, x, ε)` and `$with_data(z, x, ε)` (`Original.d326`, `d327`), which update
`s.ELEMS[f.MODULE.ELEMS[x]].REFS` and `s.DATAS[f.MODULE.DATAS[x]].BYTES`.

* The segment exists because `GoodW` includes `ResOkL` (`elem_of_res`, `data_of_res`); no
  inversion of the updaters is needed.
* The updaters are evaluated forward at the 2.0 state encoding (`evalExp_withElem20`,
  `evalExp_withData20`), and the right-hand side of the firing is then unique.

This discharges `Step` 10 and 21 of `BwdRestW3` (`bwdStep_elemDrop`, `bwdStep_dataDrop`).
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
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk PremW DDerives otherwise stateT evalExp_tup2 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1 pathGet_root pathGet_dot pathGet_idx pathSet_idx
  pathSet_dot pathSet_root evalExp_idxPayload HasClause1 idxPayload iterVar matchExp_iterVar)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Heads -/

theorem head20_elemDrop {a : Admin} (h : adminHead20 a = "ELEM.DROP") :
    ∃ x, a = .plain (.elemDrop x) := by
  revert h; admin_head_inv20

theorem head20_dataDrop {a : Admin} (h : adminHead20 a = "DATA.DROP") :
    ∃ x, a = .plain (.dataDrop x) := by
  revert h; admin_head_inv20

/-! ## The rules, verbatim -/

/-- `Step/elem.drop`, rule 10 of `Step` (verbatim). -/
def elemDropRule : Rule :=
  (Rule.ruleD "elem.drop" [(Param.expP "z" (Typ.varT "state" [])), (Param.expP "x" (Typ.varT "idx" []))]
  "%~>%" (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z"), (Exp.listE [(Exp.caseE "ELEM.DROP"
  (Exp.varE "x"))])])), (Exp.caseE "%;%" (Exp.tupE [(Exp.callE "with_elem" [(Arg.expA (Exp.varE "z")),
  (Arg.expA (Exp.varE "x")), (Arg.expA (Exp.listE []))]), (Exp.listE [])]))]) [])

/-- `Step/data.drop`, rule 21 of `Step` (verbatim). -/
def dataDropRule : Rule :=
  (Rule.ruleD "data.drop" [(Param.expP "z" (Typ.varT "state" [])), (Param.expP "x" (Typ.varT "idx" []))]
  "%~>%" (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z"), (Exp.listE [(Exp.caseE "DATA.DROP"
  (Exp.varE "x"))])])), (Exp.caseE "%;%" (Exp.tupE [(Exp.callE "with_data" [(Arg.expA (Exp.varE "z")),
  (Arg.expA (Exp.varE "x")), (Arg.expA (Exp.listE []))]), (Exp.listE [])]))]) [])

theorem hasRuleAt_elemDrop : HasRuleAt (simEnv20 B) "Step" "%~>%" 10 elemDropRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_dataDrop : HasRuleAt (simEnv20 B) "Step" "%~>%" 21 dataDropRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## The updaters -/

/-- `(s; f), x, y*`, the argument pattern of `$with_elem` and `$with_data`. -/
abbrev sfxIterPat (y ys : IL.Id) : List Arg :=
  [.expA (.caseE "%;%" (.tupE [.varE "s", .varE "f"])), .expA (.varE "x"), .expA (iterVar y ys)]

/-- The body of a segment updater `s[.F[f.MODULE.F[x]].G = y*]; f`. -/
abbrev segUpdBody (F G : AtomS) (y ys : IL.Id) : Exp :=
  .caseE "%;%" (.tupE [.updE (.varE "s") (.dotP (.idxP (.dotP .rootP F)
    (.idxE (.dotE (.dotE (.varE "f") "MODULE") F) idxPayload)) G) (iterVar y ys), .varE "f"])

theorem hasClause_withElem20 : HasClause1 (simEnv20 B) "with_elem" (sfxIterPat "r" "r*")
    (segUpdBody "ELEMS" "REFS" "r" "r*") := ⟨_, _, _, rfl⟩

theorem hasClause_withData20 : HasClause1 (simEnv20 B) "with_data" (sfxIterPat "b" "b*")
    (segUpdBody "DATAS" "BYTES" "b" "b*") := ⟨_, _, _, rfl⟩

/-- `(s; f), x, y*` matches a state, an index and a list. -/
theorem matchArgs_sfxIter {env : Env} {S F X : Value} {l : List Value} {y ys : IL.Id}
    (hy : y ≠ "_") (hy' : y ≠ "s" ∧ y ≠ "f" ∧ y ≠ "x") (hys : ys ≠ "s" ∧ ys ≠ "f" ∧ ys ≠ "x") :
    MatchArgs env VarEnv.empty (sfxIterPat y ys) [.val (.case "%;%" (.tuple [S, F])), .val X,
      .val (.list l)]
      ((((VarEnv.empty.bindVal "s" S).bindVal "f" F).bindVal "x" X).bindVal ys (.list l)) :=
  matchArgs_cons (matchArg_expA State.matchExp_state)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_iterVar (by
        simp [VarEnv.findVal?, VarEnv.bindVal, VarEnv.empty, hy'.1.symm, hy'.2.1.symm,
          hy'.2.2.symm]) hy (by
        simp [VarEnv.findVal?, VarEnv.bindVal, VarEnv.empty, hys.1.symm,
          hys.2.1.symm, hys.2.2.symm]))) matchArgs_nil))

/-- The store with one element segment emptied. -/
theorem storeV_dropElem (s : Store H) (a : Nat) (ei : ElemInst) :
    (storeV hn s).setField "ELEMS"
        (.list ((s.elems.map elemInstV).set a (elemInstV { ei with refs := [] }))) =
      some (storeV hn (s.setElemInst a { ei with refs := [] })) := by
  simp [storeV, Value.setField, Store.setElemInst, List.map_set]

/-- The store with one data segment emptied. -/
theorem storeV_dropData (s : Store H) (a : Nat) :
    (storeV hn s).setField "DATAS"
        (.list ((s.datas.map dataInstV).set a (dataInstV ⟨ByteArray.empty⟩))) =
      some (storeV hn (s.setDataInst a ⟨ByteArray.empty⟩)) := by
  simp [storeV, Value.setField, Store.setDataInst, List.map_set]

/-- **`$with_elem(z, x, ε)`**, at a module listing element address `a` at `x` and a store holding
a segment there. -/
theorem evalExp_withElem20 {ρ : VarEnv} {ez ex : Exp} {s : Store H} {f : Frame} {x : ElemIdx}
    {a : Nat} {ei : ElemInst} (hρ : ρ.findDef? "with_elem" = none)
    (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv20 B) ρ ex (idxV x))
    (ha : f.module.elems[x.toNat]? = some a) (he : s.elems[a]? = some ei) :
    EvalExp (simEnv20 B) ρ (.callE "with_elem" [.expA ez, .expA ex, .expA (.listE [])])
      (stateV hn (s.setElemInst a { ei with refs := [] }) f) := by
  refine evalExp_call1 hasClause_withElem20 hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons Pure.evalExp_list0 evalArgs_nil)))
    (matchArgs_sfxIter (by decide) (by decide) (by decide)) ?_
  refine evalExp_case (evalExp_tup2 ?_ (evalExp_var rfl))
  refine evalExp_updE_iff.2 ⟨storeV hn s, .list [], evalExp_var rfl,
    Equiv.Execution.evalExp_iterPat (by decide) rfl, ?_⟩
  let σ : VarEnv := (((VarEnv.empty.bindVal "s" (storeV hn s)).bindVal "f" (frameV f)).bindVal "x"
    (idxV x)).bindVal "r*" (.list [])
  have hai : EvalExp (simEnv20 B) σ (.idxE (.dotE (.dotE (.varE "f") "MODULE") "ELEMS")
      idxPayload) (.num (.natN a)) :=
    evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
      evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl, State.frameV_module f⟩, rfl⟩,
      evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩
  have hel : PathGet (simEnv20 B) σ (storeV hn s) (.dotP .rootP "ELEMS")
      (.list (s.elems.map elemInstV)) := pathGet_dot pathGet_root rfl
  have hset : (elemInstV ei).setField "REFS" (.list []) =
      some (elemInstV { ei with refs := [] }) := by
    simp [elemInstV, Value.setField]
  have hlt : a < s.elems.length := (List.getElem?_eq_some_iff.1 he).1
  exact pathSet_dot (pathGet_idx hel hai (by simp [Value.idx?, List.getElem?_map, he])) hset
    (pathSet_idx hel hai (by simp [Value.setIdx, hlt])
      (pathSet_dot pathGet_root (storeV_dropElem s a ei) pathSet_root))

/-- **`$with_data(z, x, ε)`**, at a module listing data address `a` at `x` and a store holding a
segment there. -/
theorem evalExp_withData20 {ρ : VarEnv} {ez ex : Exp} {s : Store H} {f : Frame} {x : DataIdx}
    {a : Nat} {di : DataInst} (hρ : ρ.findDef? "with_data" = none)
    (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv20 B) ρ ex (idxV x))
    (ha : f.module.datas[x.toNat]? = some a) (hd : s.datas[a]? = some di) :
    EvalExp (simEnv20 B) ρ (.callE "with_data" [.expA ez, .expA ex, .expA (.listE [])])
      (stateV hn (s.setDataInst a ⟨ByteArray.empty⟩) f) := by
  refine evalExp_call1 hasClause_withData20 hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons Pure.evalExp_list0 evalArgs_nil)))
    (matchArgs_sfxIter (by decide) (by decide) (by decide)) ?_
  refine evalExp_case (evalExp_tup2 ?_ (evalExp_var rfl))
  refine evalExp_updE_iff.2 ⟨storeV hn s, .list [], evalExp_var rfl,
    Equiv.Execution.evalExp_iterPat (by decide) rfl, ?_⟩
  let σ : VarEnv := (((VarEnv.empty.bindVal "s" (storeV hn s)).bindVal "f" (frameV f)).bindVal "x"
    (idxV x)).bindVal "b*" (.list [])
  have hai : EvalExp (simEnv20 B) σ (.idxE (.dotE (.dotE (.varE "f") "MODULE") "DATAS")
      idxPayload) (.num (.natN a)) :=
    evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
      evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl, State.frameV_module f⟩, rfl⟩,
      evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩
  have hdl : PathGet (simEnv20 B) σ (storeV hn s) (.dotP .rootP "DATAS")
      (.list (s.datas.map dataInstV)) := pathGet_dot pathGet_root rfl
  have hset : (dataInstV di).setField "BYTES" (.list []) = some (dataInstV ⟨ByteArray.empty⟩) := by
    simp [dataInstV, Value.setField, bytesV]
  have hlt : a < s.datas.length := (List.getElem?_eq_some_iff.1 hd).1
  exact pathSet_dot (pathGet_idx hdl hai (by simp [Value.idx?, List.getElem?_map, hd])) hset
    (pathSet_idx hdl hai (by simp [Value.setIdx, hlt])
      (pathSet_dot pathGet_root (storeV_dropData s a) pathSet_root))

/-! ## The lookups, from `ResOkL` -/

/-- A defined element segment, from `GoodW` at `elem.drop x`. -/
theorem elem_of_res {s : Store H} {f : Frame} {x : ElemIdx}
    (h : InstrResOk (⟨s, f⟩ : State H) (.elemDrop x)) :
    ∃ a ei, f.module.elems[x.toNat]? = some a ∧ s.elems[a]? = some ei := by
  obtain ⟨ei, hei⟩ := Option.isSome_iff_exists.1 (show ((⟨s, f⟩ : State H).elem? x).isSome from h)
  simp only [State.elem?, ModuleInst.elemAddr?, Store.elemInst?, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at hei
  obtain ⟨a, ha, he⟩ := hei
  exact ⟨a, ei, ha, he⟩

/-- A defined data segment, from `GoodW` at `data.drop x`. -/
theorem data_of_res {s : Store H} {f : Frame} {x : DataIdx}
    (h : InstrResOk (⟨s, f⟩ : State H) (.dataDrop x)) :
    ∃ a di, f.module.datas[x.toNat]? = some a ∧ s.datas[a]? = some di := by
  obtain ⟨di, hdi⟩ := Option.isSome_iff_exists.1 (show ((⟨s, f⟩ : State H).data? x).isSome from h)
  simp only [State.data?, ModuleInst.dataAddr?, Store.dataInst?, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at hdi
  obtain ⟨a, ha, hd⟩ := hdi
  exact ⟨a, di, ha, hd⟩

/-! ## The two rules backwards -/

/-- **A firing configuration rule `z; es ~> rh`, inverted, with its right-hand side and
premises**: the code evaluates element by element, the state variable is bound to the image of
the state, and `rh` evaluates to the successor. -/
theorem firesCfg_full20 {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param} {es : List Exp}
    {rh : Exp} {prems : List Prem} {c : Config H} {w : Value}
    (h : HasRuleAt (simEnv20 B) x "%~>%" k
      (.ruleD nm qs "%~>%" (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE es]), rh]) prems))
    (hf : Fires (simEnv20 B) x k (.tuple [configV hn c, w])) :
    ∃ σ, QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) qs ∧
      (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn c.store c.frame) ∧
      EvalExps (simEnv20 B) (VarEnv.empty.bindVals σ) es (adminsToV c.code) ∧
      EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) rh w ∧
      ∀ pr ∈ prems, PremW (simEnv20 B) (DDerives (simEnv20 B) (otherwise (simEnv20 B)))
        (otherwise (simEnv20 B) x [] k (.tuple [configV hn c, w])) (VarEnv.empty.bindVals σ) pr := by
  obtain ⟨σ, hq, he, hp⟩ := Sim.State.Fires.rule_eq h hf
  have hl := Sim.RefsGC.lhs_of_concl he
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 hl
  have hu' : u = .tuple [stateV hn c.store c.frame, .list (adminsToV c.code)] :=
    (Value.case.inj hcu.symm).2
  obtain ⟨hZ, hL⟩ := Pure.evalExp_tup2_inv (hu' ▸ hu)
  exact ⟨σ, hq, evalExp_varE_iff.1 hZ, Sim.RefsGC.elems_of_list hL, Sim.RefsGC.rhs_of_concl he, hp⟩

/-- **`Step/elem.drop` backwards**, at a `GoodW` configuration. -/
theorem bwdStep_elemDrop {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodW c) (hf : Fires (simEnv20 B) "Step" 10 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hr, -⟩ := firesCfg_full20 hasRuleAt_elemDrop hf
  obtain ⟨a₁, rfl, h₁⟩ := codes20_one hes
  obtain ⟨x, rfl⟩ := head20_elemDrop (head20_of_caseE h₁)
  have hres : InstrResOk (⟨s, f⟩ : State H) (.elemDrop x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2
  obtain ⟨a, ei, ha, he⟩ := elem_of_res hres
  have fx := idx_of_caseE (X := idxV x) h₁ rfl
  have hw : w = configV hn ⟨s.setElemInst a { ei with refs := [] }, f, []⟩ :=
    EvalExp.unique hr (evalExp_case (evalExp_tup2
      (evalExp_withElem20 rfl (evalExp_var fz) (evalExp_var fx) ha he) Pure.evalExp_list0))
  exact ⟨_, hw, .elemDrop ha he⟩

/-- **`Step/data.drop` backwards**, at a `GoodW` configuration. -/
theorem bwdStep_dataDrop {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodW c) (hf : Fires (simEnv20 B) "Step" 21 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hr, -⟩ := firesCfg_full20 hasRuleAt_dataDrop hf
  obtain ⟨a₁, rfl, h₁⟩ := codes20_one hes
  obtain ⟨x, rfl⟩ := head20_dataDrop (head20_of_caseE h₁)
  have hres : InstrResOk (⟨s, f⟩ : State H) (.dataDrop x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2
  obtain ⟨a, di, ha, hd⟩ := data_of_res hres
  have fx := idx_of_caseE (X := idxV x) h₁ rfl
  have hw : w = configV hn ⟨s.setDataInst a ⟨ByteArray.empty⟩, f, []⟩ :=
    EvalExp.unique hr (evalExp_case (evalExp_tup2
      (evalExp_withData20 rfl (evalExp_var fz) (evalExp_var fx) ha hd) Pure.evalExp_list0))
  exact ⟨_, hw, .dataDrop ha hd⟩

end Silmaril.Wasm.SpecTec.Sim20.Whole
