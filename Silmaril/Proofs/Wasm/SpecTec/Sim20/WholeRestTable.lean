module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestDrop
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeResEdge

/-!
# `table.get`, `table.set` and the two `grow-fail` rules backwards, at any `GoodW` configuration

* `Step_read` 10 (`table.get-val`): `z; CONST I32 i; TABLE.GET x ~> $table(z, x).REFS[i]` under
  `i < |$table(z, x).REFS|` (`bwdRead_tableGetVal`).
* `Step` 6 (`table.set-trap`) and 7 (`table.set-val`): `z; CONST I32 i; ref; TABLE.SET x` to
  `z; TRAP` under `i ≥ |…|`, and to `$with_table(z, x, i, ref); ε` under `i < |…|`
  (`bwdStep_tableSetTrap`, `bwdStep_tableSetVal`).
* `Step` 9 (`table.grow-fail`) and 20 (`memory.grow-fail`): no premise; the result is
  `CONST I32 $inv_signed_(32, -1)`, V2's `i32.const -1`. V2's `tableGrowFail`/`memoryGrowFail`
  ask the profile to allow the failure, so these two take `∀ …, P.growMayFail …`, true of every
  `Profile.spec nd r` (`bwdStep_tableGrowFail`, `bwdStep_memGrowFail`).

The table, and for `memory.grow` the memory, exist because `GoodW` includes `ResOkL`
(`table_of_res`, `mem_of_res`). `$table` and `$with_table` are evaluated forward at the 2.0 state
encoding (`evalExp_table20`, `evalExp_withTable20`), so the premises read back as V2's bounds and
the right-hand sides are unique.
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
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk stateT evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1 pathGet_root pathGet_dot pathGet_idx pathSet_idx
  pathSet_dot pathSet_root evalExp_idxPayload HasClause1 idxPayload)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Heads and operands -/

theorem head20_tableGet {a : Admin} (h : adminHead20 a = "TABLE.GET") :
    ∃ x, a = .plain (.tableGet x) := by
  revert h; admin_head_inv20

theorem head20_tableSet {a : Admin} (h : adminHead20 a = "TABLE.SET") :
    ∃ x, a = .plain (.tableSet x) := by
  revert h; admin_head_inv20

theorem head20_tableGrow {a : Admin} (h : adminHead20 a = "TABLE.GROW") :
    ∃ x, a = .plain (.tableGrow x) := by
  revert h; admin_head_inv20

theorem head20_memoryGrow {a : Admin} (h : adminHead20 a = "MEMORY.GROW") :
    a = .plain .memoryGrow := by
  revert h; admin_head_inv20

/-- `i.%.0`, the payload of a `num_(I32)` variable `i`. -/
abbrev iPay : Exp := .projE (.uncaseE (.varE "i") "%") 0

/-- `CONST I32 i`, the left-hand side element. -/
abbrev constIE : Exp := .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i"])

/-- `CONST I32 (% n)`, the left-hand side element with a natural `n`. -/
abbrev constNE : Exp := .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [.varE "n"])])

/-- `$table(z, x)`. -/
abbrev tableE : Exp := .callE "table" [.expA (.varE "z"), .expA (.varE "x")]

/-- `|$table(z, x).REFS|`. -/
abbrev tableLenE : Exp := .lenE (.dotE tableE "REFS")

/-- The image of an `i32` constant. -/
theorem adminToV_constI32 (c : BitVec 32) :
    adminToV (constI32 c) = .case "CONST" (.tuple [caseNilV "I32", pctV c.toNat]) := rfl

/-- A `CONST I32 i` element of a left-hand side binds `i` to the constant's payload. -/
theorem constI_of_lhs {env : Env} {ρ : VarEnv} {a : Admin}
    (h : EvalExp env ρ constIE (adminToV a)) :
    ∃ c : BitVec 32, a = constI32 c ∧ ρ.findVal? "i" = some (pctV c.toNat) := by
  obtain ⟨c, rfl⟩ := constI32_of_lhs h
  exact ⟨c, rfl, var_snd (tup_of_caseE h (adminToV_constI32 c))⟩

/-- A `CONST I32 (% n)` element of a left-hand side binds `n` to the constant's value. -/
theorem constN_of_lhs {env : Env} {ρ : VarEnv} {a : Admin}
    (h : EvalExp env ρ constNE (adminToV a)) :
    ∃ c : BitVec 32, a = constI32 c ∧ ρ.findVal? "n" = some (.num (.natN c.toNat)) := by
  obtain ⟨c, rfl⟩ := constI32_of_lhs h
  refine ⟨c, rfl, ?_⟩
  have hs := tup_of_caseE h (adminToV_constI32 c)
  obtain ⟨w, ws, -, hws, he⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hs
  obtain ⟨-, rfl⟩ := List.cons.inj he
  obtain ⟨u, us, hu, -, he'⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hws
  obtain ⟨rfl, -⟩ := List.cons.inj he'
  obtain ⟨u', hu', hc⟩ := evalExp_caseE_iff.1 hu
  have e : u' = .tuple [.num (.natN c.toNat)] := by
    simp only [pctV, Value.case.injEq] at hc
    exact hc.2.symm
  subst e
  exact var_fst (Sim.RefsGC.elems_of_tup hu')

/-- `i.%.0` at `i = %(k)`. -/
theorem evalExp_iPay {env : Env} {ρ : VarEnv} {k : Nat} (h : ρ.findVal? "i" = some (pctV k)) :
    EvalExp env ρ iPay (.num (.natN k)) :=
  evalExp_projE_iff.2 ⟨[.num (.natN k)], evalExp_uncaseE_iff.2 (evalExp_var h), Int.le_refl 0, rfl⟩

/-! ## Comparisons on naturals, read back -/

theorem lt_of_cmp {p q : Nat}
    (h : cmpValues .ltOp (.num (.natN p)) (.num (.natN q)) = .ok (.bool true)) : p < q := by
  simpa [cmpValues, Num.cmp, Res.ofOption] using h

theorem le_of_cmpGe {p q : Nat}
    (h : cmpValues .geOp (.num (.natN p)) (.num (.natN q)) = .ok (.bool true)) : q ≤ p := by
  simpa [cmpValues, Num.cmp, Res.ofOption] using h

/-- An `if` premise comparing two naturals, read back. -/
theorem cmp_of_prem {env : Env} {ρ : VarEnv} {op : CmpOp} {e₁ e₂ : Exp} {p q : Nat}
    (h : EvalExp env ρ (.cmpE op (.numT .natT) e₁ e₂) (.bool true))
    (h₁ : EvalExp env ρ e₁ (.num (.natN p))) (h₂ : EvalExp env ρ e₂ (.num (.natN q))) :
    cmpValues op (.num (.natN p)) (.num (.natN q)) = .ok (.bool true) := by
  obtain ⟨v₁, v₂, e₁', e₂', hc⟩ := evalExp_cmpE_iff.1 h
  rw [EvalExp.unique e₁' h₁, EvalExp.unique e₂' h₂] at hc
  exact hc

/-! ## `$table`, `$with_table` -/

theorem hasClause_table20 : HasClause1 (simEnv20 B) "table" State.sfxPat
    (.idxE (.dotE (.varE "s") "TABLES") (.idxE (.dotE (.dotE (.varE "f") "MODULE") "TABLES")
      idxPayload)) := ⟨_, _, _, rfl⟩

/-- `(s; f), x, i, r`, the argument pattern of `$with_table`. -/
abbrev sfxirPat : List Arg :=
  [.expA (.caseE "%;%" (.tupE [.varE "s", .varE "f"])), .expA (.varE "x"), .expA (.varE "i"),
    .expA (.varE "r")]

theorem hasClause_withTable20 : HasClause1 (simEnv20 B) "with_table" sfxirPat
    (.caseE "%;%" (.tupE [.updE (.varE "s") (.idxP (.dotP (.idxP (.dotP .rootP "TABLES")
      (.idxE (.dotE (.dotE (.varE "f") "MODULE") "TABLES") idxPayload)) "REFS") (.varE "i"))
      (.varE "r"), .varE "f"])) := ⟨_, _, _, rfl⟩

/-- **`$table(z, x)`**, at a module listing table address `a` at `x` and a store holding a table
there. -/
theorem evalExp_table20 {ρ : VarEnv} {ez ex : Exp} {s : Store H} {f : Frame} {x : TableIdx}
    {a : Nat} {ti : TableInst} (hρ : ρ.findDef? "table" = none)
    (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv20 B) ρ ex (idxV x))
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti) :
    EvalExp (simEnv20 B) ρ (.callE "table" [.expA ez, .expA ex]) (tableInstV ti) :=
  evalExp_call1 hasClause_table20 hρ (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil))
    State.matchArgs_sfx (evalExp_idxE_iff.2 ⟨_, a, evalExp_dotE_iff.2 ⟨storeV hn s,
      evalExp_var rfl, rfl⟩, evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2
        ⟨moduleInstV f.module, evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl,
          State.frameV_module f⟩, rfl⟩, evalExp_idxPayload rfl,
        by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩,
      by simp [Value.idx?, List.getElem?_map, ht]⟩)

/-- `|$table(z, x).REFS|`. -/
theorem evalExp_tableLen20 {ρ : VarEnv} {s : Store H} {f : Frame} {x : TableIdx} {a : Nat}
    {ti : TableInst} (hρ : ρ.findDef? "table" = none)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fx : ρ.findVal? "x" = some (idxV x))
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti) :
    EvalExp (simEnv20 B) ρ tableLenE (.num (.natN ti.refs.length)) := by
  refine evalExp_lenE_iff.2 ⟨ti.refs.map refV, evalExp_dotE_iff.2 ⟨tableInstV ti,
    evalExp_table20 hρ (evalExp_var fz) (evalExp_var fx) ha ht, rfl⟩, ?_⟩
  simp

/-- The store with one table entry replaced. -/
theorem storeV_setTable20 (s : Store H) (a : Nat) (ti : TableInst) :
    (storeV hn s).setField "TABLES" (.list ((s.tables.map tableInstV).set a (tableInstV ti))) =
      some (storeV hn (s.setTableInst a ti)) := by
  simp [storeV, Value.setField, Store.setTableInst, List.map_set]

/-- **`$with_table(z, x, i, r)`**, at a table in range. -/
theorem evalExp_withTable20 {ρ : VarEnv} {ez ex ei er : Exp} {s : Store H} {f : Frame}
    {x : TableIdx} {a i : Nat} {ti : TableInst} {r : Ref} (hρ : ρ.findDef? "with_table" = none)
    (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv20 B) ρ ex (idxV x))
    (hi : EvalExp (simEnv20 B) ρ ei (.num (.natN i))) (hr : EvalExp (simEnv20 B) ρ er (refV r))
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti)
    (hlt : i < ti.refs.length) :
    EvalExp (simEnv20 B) ρ (.callE "with_table" [.expA ez, .expA ex, .expA ei, .expA er])
      (stateV hn (s.setTableInst a (ti.setRef i r)) f) := by
  refine evalExp_call1 hasClause_withTable20 hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hi (evalArgs_cons hr evalArgs_nil))))
    (matchArgs_cons (matchArg_expA State.matchExp_state) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))) ?_
  refine evalExp_case (evalExp_tup2 ?_ (evalExp_var rfl))
  let σ : VarEnv := ((((VarEnv.empty.bindVal "s" (storeV hn s)).bindVal "f" (frameV f)).bindVal
    "x" (idxV x)).bindVal "i" (.num (.natN i))).bindVal "r" (refV r)
  have hai : EvalExp (simEnv20 B) σ (.idxE (.dotE (.dotE (.varE "f") "MODULE") "TABLES")
      idxPayload) (.num (.natN a)) :=
    evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
      evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl, State.frameV_module f⟩, rfl⟩,
      evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩
  have hts : PathGet (simEnv20 B) σ (storeV hn s) (.dotP .rootP "TABLES")
      (.list (s.tables.map tableInstV)) := pathGet_dot pathGet_root rfl
  have hg : PathGet (simEnv20 B) σ (storeV hn s) (.idxP (.dotP .rootP "TABLES")
      (.idxE (.dotE (.dotE (.varE "f") "MODULE") "TABLES") idxPayload)) (tableInstV ti) :=
    pathGet_idx hts hai (by simp [Value.idx?, List.getElem?_map, ht])
  have hR : (tableInstV ti).field? "REFS" = some (.list (ti.refs.map refV)) := rfl
  have hset : (tableInstV ti).setField "REFS" (.list ((ti.refs.map refV).set i (refV r))) =
      some (tableInstV (ti.setRef i r)) := by
    simp [tableInstV, Value.setField, TableInst.setRef, List.map_set]
  have ha' : a < s.tables.length := (List.getElem?_eq_some_iff.1 ht).1
  refine evalExp_updE_iff.2 ⟨storeV hn s, refV r, evalExp_var rfl, evalExp_var rfl, ?_⟩
  exact pathSet_idx (pathGet_dot hg hR) (evalExp_var rfl) (by simp [Value.setIdx, hlt])
    (pathSet_dot hg hset (pathSet_idx hts hai (by simp [Value.setIdx, ha'])
      (pathSet_dot pathGet_root (storeV_setTable20 s a _) pathSet_root)))

/-! ## The lookups, from `ResOkL` -/

/-- A defined table, from `InstrResOk` at an instruction naming table `x`. -/
theorem table_of_isSome {s : Store H} {f : Frame} {x : TableIdx}
    (h : ((⟨s, f⟩ : State H).table? x).isSome) :
    ∃ a ti, f.module.tables[x.toNat]? = some a ∧ s.tables[a]? = some ti := by
  obtain ⟨ti, hti⟩ := Option.isSome_iff_exists.1 h
  simp only [State.table?, ModuleInst.tableAddr?, Store.tableInst?, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at hti
  obtain ⟨a, ha, ht⟩ := hti
  exact ⟨a, ti, ha, ht⟩

/-- A defined memory, from `InstrResOk` at an instruction naming the memory. -/
theorem mem_of_isSome {s : Store H} {f : Frame}
    (h : ((⟨s, f⟩ : State H).mem? memIdx0).isSome) :
    ∃ a mi, f.module.memAddr? memIdx0 = some a ∧ s.memInst? a = some mi := by
  obtain ⟨mi, hmi⟩ := Option.isSome_iff_exists.1 h
  simp only [State.mem?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hmi
  obtain ⟨a, ha, hm⟩ := hmi
  exact ⟨a, mi, ha, hm⟩

/-! ## The rules, verbatim -/

/-- `Step_read/table.get-val`, rule 10 of `Step_read` (verbatim). -/
def tableGetValRule : Rule :=
  .ruleD "table.get-val" [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA
    (.caseE "I32" (.tupE []))]), .expP "x" (.varT "idx" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE, .caseE "TABLE.GET" (.varE "x")]]),
      .listE [.subE (.idxE (.dotE tableE "REFS") iPay) (.varT "ref" []) (.varT "admininstr" [])]])
    [.ifPr (.cmpE .ltOp (.numT .natT) iPay tableLenE)]

/-- `Step/table.set-trap`, rule 6 of `Step` (verbatim). -/
def tableSetTrapRule : Rule :=
  .ruleD "table.set-trap" [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA
    (.caseE "I32" (.tupE []))]), .expP "ref" (.varT "ref" []), .expP "x" (.varT "idx" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .subE (.varE "ref") (.varT "ref" []) (.varT "admininstr" []), .caseE "TABLE.SET" (.varE "x")]]),
      .caseE "%;%" (.tupE [.varE "z", .listE [.caseE "TRAP" (.tupE [])]])])
    [.ifPr (.cmpE .geOp (.numT .natT) iPay tableLenE)]

/-- `Step/table.set-val`, rule 7 of `Step` (verbatim). -/
def tableSetValRule : Rule :=
  .ruleD "table.set-val" [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA
    (.caseE "I32" (.tupE []))]), .expP "ref" (.varT "ref" []), .expP "x" (.varT "idx" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .subE (.varE "ref") (.varT "ref" []) (.varT "admininstr" []), .caseE "TABLE.SET" (.varE "x")]]),
      .caseE "%;%" (.tupE [.callE "with_table" [.expA (.varE "z"), .expA (.varE "x"), .expA iPay,
        .expA (.varE "ref")], .listE []])])
    [.ifPr (.cmpE .ltOp (.numT .natT) iPay tableLenE)]

/-- `$inv_signed_(32, -1)`. -/
abbrev minusOneE : Exp :=
  .callE "inv_signed_" [.expA (.numE (.natN 32)),
    .expA (.unE .minusOp (.numT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))]

/-- `z; CONST I32 (% $inv_signed_(32, -1))`, the right-hand side of the `grow-fail` rules. -/
abbrev growFailRhs : Exp :=
  .caseE "%;%" (.tupE [.varE "z", .listE [.caseE "CONST" (.tupE [.caseE "I32" (.tupE []),
    .caseE "%" (.tupE [minusOneE])])]])

/-- `Step/table.grow-fail`, rule 9 of `Step` (verbatim). -/
def tableGrowFailRule : Rule :=
  .ruleD "table.grow-fail" [.expP "z" (.varT "state" []), .expP "ref" (.varT "ref" []),
    .expP "n" (.varT "n" []), .expP "x" (.varT "idx" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [
      .subE (.varE "ref") (.varT "ref" []) (.varT "admininstr" []), constNE,
      .caseE "TABLE.GROW" (.varE "x")]]), growFailRhs]) []

theorem hasRuleAt_tableGetVal : HasRuleAt (simEnv20 B) "Step_read" "%~>%" 10 tableGetValRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_tableSetTrap : HasRuleAt (simEnv20 B) "Step" "%~>%" 6 tableSetTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_tableSetVal : HasRuleAt (simEnv20 B) "Step" "%~>%" 7 tableSetValRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_tableGrowFail : HasRuleAt (simEnv20 B) "Step" "%~>%" 9 tableGrowFailRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## `$inv_signed_(32, -1)` -/

/-- `$inv_signed_(32, -1)` is `2^32 - 1`, the payload of V2's `i32.const -1`. -/
theorem evalExp_minusOne {ρ : VarEnv} (hρ : ρ.findDef? "inv_signed_" = none) :
    EvalExp (simEnv20 B) ρ minusOneE (.num (.natN (BitVec.allOnes 32).toNat)) := by
  have hm : EvalExp (simEnv20 B) ρ (.unE .minusOp (.numT .intT) (.cvtE (.numE (.natN 1)) .natT
      .intT)) (.num (.intN (-1))) :=
    evalExp_unE_iff.2 ⟨.num (.intN 1), evalExp_cvtNum evalExp_num rfl, by simp [unValue, Num.un]⟩
  have e : Silmaril.Wasm.Numerics.invSigned_ 32 (-1) = (BitVec.allOnes 32).toNat := by decide
  rw [← e]
  exact evalExp_callE_iff.2 ((Pure.numEnvCore_simEnv20 B).callDef_invSigned hρ
    (evalArgs_cons evalExp_num (evalArgs_cons hm evalArgs_nil)) (by decide) (by decide)
    (by decide))

/-- The image of V2's `i32.const -1` configuration. -/
theorem growFail_rhs {ρ : VarEnv} {s : Store H} {f : Frame} (hρ : ρ.findDef? "inv_signed_" = none)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) :
    EvalExp (simEnv20 B) ρ growFailRhs (configV hn ⟨s, f, [constI32 (BitVec.allOnes 32)]⟩) :=
  evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1 (evalExp_case (evalExp_tup2
    (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
    (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_minusOne hρ) evalExps_nil,
      rfl⟩))))))

/-! ## The rules backwards -/

/-- **`Step_read/table.get-val` backwards**, at a `GoodW` configuration. -/
theorem bwdRead_tableGetVal {c : Config H} {w : List Value} (hg : GoodW c)
    (hf : Fires (simEnv20 B) "Step_read" 10 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hr, hp⟩ := firesCfg_full20 hasRuleAt_tableGetVal hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes20_two hes
  obtain ⟨c, rfl, fi⟩ := constI_of_lhs h₁
  obtain ⟨x, rfl⟩ := head20_tableGet (head20_of_caseE h₂)
  have hres : InstrResOk (⟨s, f⟩ : State H) (.tableGet x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.1
  obtain ⟨a, ti, ha, ht⟩ := table_of_isSome hres
  have fx := idx_of_caseE (X := idxV x) h₂ rfl
  have hlt : c.toNat < ti.refs.length := lt_of_cmp (cmp_of_prem (Pure.ifPrem (hp _ (by simp)))
    (evalExp_iPay fi) (evalExp_tableLen20 rfl fz fx ha ht))
  have hr' : ti.refs[c.toNat]? = some ti.refs[c.toNat] := List.getElem?_eq_getElem hlt
  have hw : Value.list w = .list [refV ti.refs[c.toNat]] :=
    EvalExp.unique hr (evalExp_list1 (evalExp_subE_iff.2 (evalExp_idxE_iff.2 ⟨_, c.toNat,
      evalExp_dotE_iff.2 ⟨tableInstV ti, evalExp_table20 rfl (evalExp_var fz) (evalExp_var fx) ha ht,
        rfl⟩, evalExp_iPay fi, by simp [Value.idx?, List.getElem?_map, hr']⟩)))
  refine ⟨[aref ti.refs[c.toNat]], ?_, .tableGetVal (by
    simp [State.table?, ModuleInst.tableAddr?, Store.tableInst?, ha, ht]) hr'⟩
  rw [Value.list.inj hw]
  exact (congrArg (fun v => [v]) (Pure.adminToV_toAdmin (.ref _))).symm

/-- **`Step/table.set-trap` backwards**, at a `GoodW` configuration. -/
theorem bwdStep_tableSetTrap {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodW c) (hf : Fires (simEnv20 B) "Step" 6 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, hp⟩ := firesCfg_full20 hasRuleAt_tableSetTrap hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes20_three hes
  obtain ⟨c, rfl, fi⟩ := constI_of_lhs h₁
  obtain ⟨r, rfl⟩ := ref20_of_var hq (by simp) h₂
  obtain ⟨x, rfl⟩ := head20_tableSet (head20_of_caseE h₃)
  have hres : InstrResOk (⟨s, f⟩ : State H) (.tableSet x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.1
  obtain ⟨a, ti, ha, ht⟩ := table_of_isSome hres
  have fx := idx_of_caseE (X := idxV x) h₃ rfl
  have hge : ti.refs.length ≤ c.toNat := le_of_cmpGe (cmp_of_prem (Pure.ifPrem (hp _ (by simp)))
    (evalExp_iPay fi) (evalExp_tableLen20 rfl fz fx ha ht))
  have hw : w = configV hn ⟨s, f, [.trap]⟩ :=
    EvalExp.unique hr (evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_list1
      (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)))))
  exact ⟨_, hw, .tableSetTrap ha ht hge⟩

/-- **`Step/table.set-val` backwards**, at a `GoodW` configuration. -/
theorem bwdStep_tableSetVal {P : Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (hg : GoodW c) (hf : Fires (simEnv20 B) "Step" 7 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, hp⟩ := firesCfg_full20 hasRuleAt_tableSetVal hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes20_three hes
  obtain ⟨c, rfl, fi⟩ := constI_of_lhs h₁
  obtain ⟨r, rfl⟩ := ref20_of_var hq (by simp) h₂
  obtain ⟨x, rfl⟩ := head20_tableSet (head20_of_caseE h₃)
  have hres : InstrResOk (⟨s, f⟩ : State H) (.tableSet x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.1
  obtain ⟨a, ti, ha, ht⟩ := table_of_isSome hres
  have fx := idx_of_caseE (X := idxV x) h₃ rfl
  have fr : (VarEnv.empty.bindVals σ).findVal? "ref" = some (refV r) := by
    have h := evalExp_varE_iff.1 (evalExp_subE_iff.1 h₂)
    rwa [show adminToV (aref r) = refV r from Pure.adminToV_toAdmin (.ref r)] at h
  have hlt : c.toNat < ti.refs.length := lt_of_cmp (cmp_of_prem (Pure.ifPrem (hp _ (by simp)))
    (evalExp_iPay fi) (evalExp_tableLen20 rfl fz fx ha ht))
  have hw : w = configV hn ⟨s.setTableInst a (ti.setRef c.toNat r), f, []⟩ :=
    EvalExp.unique hr (evalExp_case (evalExp_tup2 (evalExp_withTable20 rfl (evalExp_var fz)
      (evalExp_var fx) (evalExp_iPay fi) (evalExp_var fr) ha ht hlt) Pure.evalExp_list0))
  exact ⟨_, hw, .tableSetVal ha ht hlt⟩

/-- **`Step/table.grow-fail` backwards**, at a `GoodW` configuration, where the profile allows
growth to fail. -/
theorem bwdStep_tableGrowFail {P : Profile} {host : HostSemantics H}
    (hP : ∀ k a n d, P.growMayFail k a n d) {c : Config H} {w : Value}
    (hg : GoodW c) (hf : Fires (simEnv20 B) "Step" 9 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, -⟩ := firesCfg_full20 hasRuleAt_tableGrowFail hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes20_three hes
  obtain ⟨r, rfl⟩ := ref20_of_var hq (by simp) h₁
  obtain ⟨n, rfl, -⟩ := constN_of_lhs h₂
  obtain ⟨x, rfl⟩ := head20_tableGrow (head20_of_caseE h₃)
  have hres : InstrResOk (⟨s, f⟩ : State H) (.tableGrow x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.1
  obtain ⟨a, ti, ha, ht⟩ := table_of_isSome hres
  exact ⟨_, EvalExp.unique hr (growFail_rhs rfl fz), .tableGrowFail ha ht (.inl (hP _ _ _ _))⟩

/-- **`Step/memory.grow-fail` backwards**, at a `GoodW` configuration, where the profile allows
growth to fail. -/
theorem bwdStep_memGrowFail {P : Profile} {host : HostSemantics H}
    (hP : ∀ k a n d, P.growMayFail k a n d) {c : Config H} {w : Value}
    (hg : GoodW c) (hf : Fires (simEnv20 B) "Step" 20 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hr, -⟩ := firesCfg_full20 (hasRuleAt_memGrowFail B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes20_two hes
  obtain ⟨n, rfl, -⟩ := constN_of_lhs h₁
  obtain rfl := head20_memoryGrow (head20_of_caseE h₂)
  have hres : InstrResOk (⟨s, f⟩ : State H) .memoryGrow := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.1
  obtain ⟨a, mi, ha, hm⟩ := mem_of_isSome hres
  exact ⟨_, EvalExp.unique hr (growFail_rhs rfl fz), .memoryGrowFail ha hm (.inl (hP _ _ _ _))⟩

/-! ## What is left -/

/-- The `Step_read` rules discharged here. -/
def doneRead4 : List Nat := [10]

/-- The `Step` rules discharged here and in `WholeRestDrop`. -/
def doneStep4 : List Nat := [6, 7, 9, 10, 20, 21]

/-- **What is left of `BwdRestW3`** after this pass. -/
structure BwdRestW4 (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) :
    Prop where
  read : ∀ (i : Nat), i ∉ deadRead20 → i ∉ [7, 8] → i ∉ inertRead20 → i ∉ doneRead4 →
    ∀ (c : Config H) (w : List Value), GoodW c →
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code'
  step : ∀ (i : Nat), 6 ≤ i → i ∉ inertStep20 → i ∉ doneStep4 → ∀ (c : Config H) (w : Value),
    GoodW c → Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-- `BwdRestW3` from what is left, at a profile that allows growth to fail. -/
theorem bwdRestW3_of_rest4 {P : Profile} {host : HostSemantics H}
    (hP : ∀ k a n d, P.growMayFail k a n d) (R : BwdRestW4 B hn P host) :
    BwdRestW3 B hn P host where
  read i hd h78 hin c w hg hc hw hf := by
    by_cases h10 : i = 10
    · subst h10; exact bwdRead_tableGetVal hg hf
    · exact R.read i hd h78 hin (by simp [doneRead4, h10]) c w hg hc hw hf
  step i h6 hin c w hg hf := by
    by_cases e6 : i = 6
    · subst e6; exact bwdStep_tableSetTrap hg hf
    by_cases e7 : i = 7
    · subst e7; exact bwdStep_tableSetVal hg hf
    by_cases e9 : i = 9
    · subst e9; exact bwdStep_tableGrowFail hP hg hf
    by_cases e10 : i = 10
    · subst e10; exact bwdStep_elemDrop hg hf
    by_cases e20 : i = 20
    · subst e20; exact bwdStep_memGrowFail hP hg hf
    by_cases e21 : i = 21
    · subst e21; exact bwdStep_dataDrop hg hf
    exact R.step i h6 hin (by simp [doneStep4, e6, e7, e9, e10, e20, e21]) c w hg hf

/-- The spec profiles allow every growth to fail. -/
theorem growMayFail_spec (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice) :
    ∀ k a n d, (Profile.spec nd r).growMayFail k a n d := fun _ _ _ _ => trivial

/-- **`Task.wholeStepBwdW` from what is left after this pass** (`BwdRestW4`). -/
theorem wholeStepBwdW_of_rest4
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
        BwdRestW4 (Sim.Floats.floatIntB (Profile.spec nd r)) hn (Profile.spec nd r) host) :
    Task.wholeStepBwdW :=
  wholeStepBwdW_of_rest3 fun H hn hinj host nd r =>
    bwdRestW3_of_rest4 (growMayFail_spec nd r) (h H hn hinj host nd r)

end Silmaril.Wasm.SpecTec.Sim20.Whole
