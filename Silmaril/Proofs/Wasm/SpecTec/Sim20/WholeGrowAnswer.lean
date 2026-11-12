module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestGrow

/-!
# The two `grow-succeed` rules backwards, at builtins that answer growth

`WholeRestGrow` shows that `$growtable(ti, n, r)` and `$growmemory(mi, n)` are whatever the
builtins `B` answer. At `floatIntB` they answer nothing, so `Step` 8 and 19 never fire. Here `B`
may answer, as long as every answer it gives at the image of a V2 instance is the image of V2's
successful growth (`GrowAnswers20`). Then the two rules are V2's `tableGrowSucceed` and
`memoryGrowSucceed` backwards, at every `GoodW` configuration, in every profile that lets growth
succeed (`bwdStep_tableGrowSucceed`, `bwdStep_memGrowSucceed`, `bwdRestW10_of_answers`).

The bounds V2's result needs come from the growth itself, not from typing:
* `table.grow` returns `CONST I32 (% |refs|)`, and V2 returns `i32.const (ofNat |refs|)`. The two
  agree because `TableInst.grow?` succeeding means `|refs| + n < 2 ^ 32` (`refs_lt_of_grow`).
* `memory.grow` returns `CONST I32 (% (|bytes| / (64 · $Ki)))`, computed in `rat` and converted to
  `nat`. The conversion succeeds only when the quotient is whole, and then it is `mi.pages`
  (`pages_of_cvt`). `MemInst.grow?` succeeding means `mi.pages + n ≤ 2 ^ 16`
  (`pages_lt_of_grow`).

`floatIntB` satisfies `GrowAnswers20` vacuously (`growAnswers20_floatIntB`).
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
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)
open Silmaril.Wasm.SpecTec.Sim (Fires evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (relRules)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1 pathGet_root pathGet_dot pathGet_idx pathSet_idx
  pathSet_dot pathSet_root evalExp_idxPayload HasClause1 idxPayload)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Builtins whose growth is V2's -/

/-- **`B`'s growth answers are V2's**: wherever `B` answers `$growtable` or `$growmemory` at the
image of a V2 instance, the answer is the image of V2's successful growth. -/
structure GrowAnswers20 (B : Builtins) : Prop where
  table : ∀ (ti : TableInst) (n : Nat) (r : Ref) (v : Value),
    B.call "growtable" [.val (tableInstV ti), .val (.num (.natN n)), .val (refV r)] = some v →
    ∃ ti', ti.grow? n r = some ti' ∧ v = tableInstV ti'
  mem : ∀ (mi : MemInst) (n : Nat) (v : Value),
    B.call "growmemory" [.val (memInstV mi), .val (.num (.natN n))] = some v →
    ∃ mi', mi.grow? n = some mi' ∧ v = memInstV mi'

/-- `floatIntB` answers no growth, so it satisfies `GrowAnswers20` vacuously. -/
theorem growAnswers20_floatIntB (P : Profile) : GrowAnswers20 (Sim.Floats.floatIntB P) where
  table _ _ _ _ h := by rw [floatIntB_growtable] at h; cases h
  mem _ _ _ h := by rw [floatIntB_growmemory] at h; cases h

/-! ## Bounds from a successful growth -/

theorem refs_lt_of_grow {ti ti' : TableInst} {n : Nat} {r : Ref} (h : ti.grow? n r = some ti') :
    ti.refs.length < 2 ^ 32 := by
  unfold TableInst.grow? at h
  split at h
  · rename_i hc
    omega
  · cases h

theorem pages_lt_of_grow {mi mi' : MemInst} {n : Nat} (h : mi.grow? n = some mi') :
    mi.pages < 2 ^ 32 := by
  unfold MemInst.grow? at h
  split at h
  · rename_i hc
    simp only [MemInst.pages]
    omega
  · cases h

/-- A whole quotient by `65536`, converted from `rat`, is the natural quotient. -/
theorem pages_of_cvt {k : Nat} {m : Num}
    (h : Num.cvt .natT (.ratN ((k : Rat) / 65536)) = some m) : m = .natN (k / 65536) := by
  simp only [Num.cvt] at h
  split at h
  · rename_i hc
    obtain ⟨hd, hn⟩ := hc
    cases h
    have hq : (((k : Rat) / 65536).num : Rat) = (k : Rat) / 65536 :=
      Rat.intCast_num_of_den_eq_one hd
    have hk : ((k : Rat) / 65536).num * 65536 = (k : Int) := by
      have h' : (((k : Rat) / 65536).num : Rat) * 65536 = (k : Rat) := by
        rw [hq]
        field_simp
      exact_mod_cast h'
    congr 1
    omega
  · cases h

/-! ## `$with_tableinst`, `$with_meminst` -/

/-- `(s; f), x, y`, the argument pattern of `$with_tableinst` and `$with_meminst`. -/
abbrev sfxyPat (y : IL.Id) : List Arg :=
  [.expA (.caseE "%;%" (.tupE [.varE "s", .varE "f"])), .expA (.varE "x"), .expA (.varE y)]

/-- The body of `$with_tableinst`/`$with_meminst`: `s[.F[f.MODULE.F[x]] = y]; f`. -/
abbrev withInstBody20 (F : AtomS) (y : IL.Id) : Exp :=
  .caseE "%;%" (.tupE [.updE (.varE "s") (.idxP (.dotP .rootP F)
    (.idxE (.dotE (.dotE (.varE "f") "MODULE") F) idxPayload)) (.varE y), .varE "f"])

theorem hasClause_withTableinst20 :
    HasClause1 (simEnv20 B) "with_tableinst" (sfxyPat "ti") (withInstBody20 "TABLES" "ti") :=
  ⟨_, _, _, rfl⟩

theorem hasClause_withMeminst20 :
    HasClause1 (simEnv20 B) "with_meminst" (sfxyPat "mi") (withInstBody20 "MEMS" "mi") :=
  ⟨_, _, _, rfl⟩

/-- The store with one memory replaced. -/
theorem storeV_setMem20 (s : Store H) (a : Nat) (mi : MemInst) :
    (storeV hn s).setField "MEMS" (.list ((s.mems.map memInstV).set a (memInstV mi))) =
      some (storeV hn (s.setMemInst a mi)) := by
  simp [storeV, Value.setField, Store.setMemInst, List.map_set]

/-- **`$with_tableinst(z, x, ti')`**, at a table in range. -/
theorem evalExp_withTableinst20 {ρ : VarEnv} {ez ex ey : Exp} {s : Store H} {f : Frame}
    {x : TableIdx} {a : Nat} {ti ti' : TableInst} (hρ : ρ.findDef? "with_tableinst" = none)
    (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv20 B) ρ ex (idxV x))
    (hy : EvalExp (simEnv20 B) ρ ey (tableInstV ti'))
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti) :
    EvalExp (simEnv20 B) ρ (.callE "with_tableinst" [.expA ez, .expA ex, .expA ey])
      (stateV hn (s.setTableInst a ti') f) := by
  refine evalExp_call1 hasClause_withTableinst20 hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hy evalArgs_nil)))
    (matchArgs_cons (matchArg_expA State.matchExp_state) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        matchArgs_nil))) ?_
  refine evalExp_case (evalExp_tup2 ?_ (evalExp_var rfl))
  have ha' : a < s.tables.length := (List.getElem?_eq_some_iff.1 ht).1
  refine evalExp_updE_iff.2 ⟨storeV hn s, tableInstV ti', evalExp_var rfl, evalExp_var rfl, ?_⟩
  exact pathSet_idx (i := a) (pathGet_dot pathGet_root rfl)
    (evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
      evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl, State.frameV_module f⟩, rfl⟩,
      evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩)
    (by simp [Value.setIdx, ha'])
    (pathSet_dot pathGet_root (storeV_setTable20 s a _) pathSet_root)

/-- **`$with_meminst(z, 0, mi')`**, at a memory in range. -/
theorem evalExp_withMeminst20 {ρ : VarEnv} {ez ex ey : Exp} {s : Store H} {f : Frame}
    {x : MemIdx} {a : Nat} {mi mi' : MemInst} (hρ : ρ.findDef? "with_meminst" = none)
    (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv20 B) ρ ex (idxV x))
    (hy : EvalExp (simEnv20 B) ρ ey (memInstV mi'))
    (ha : f.module.mems[x.toNat]? = some a) (hm : s.mems[a]? = some mi) :
    EvalExp (simEnv20 B) ρ (.callE "with_meminst" [.expA ez, .expA ex, .expA ey])
      (stateV hn (s.setMemInst a mi') f) := by
  refine evalExp_call1 hasClause_withMeminst20 hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hy evalArgs_nil)))
    (matchArgs_cons (matchArg_expA State.matchExp_state) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        matchArgs_nil))) ?_
  refine evalExp_case (evalExp_tup2 ?_ (evalExp_var rfl))
  have ha' : a < s.mems.length := (List.getElem?_eq_some_iff.1 hm).1
  refine evalExp_updE_iff.2 ⟨storeV hn s, memInstV mi', evalExp_var rfl, evalExp_var rfl, ?_⟩
  exact pathSet_idx (i := a) (pathGet_dot pathGet_root rfl)
    (evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
      evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl, State.frameV_module f⟩, rfl⟩,
      evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩)
    (by simp [Value.setIdx, ha'])
    (pathSet_dot pathGet_root (storeV_setMem20 s a _) pathSet_root)

/-! ## The rules, verbatim -/

/-- `CONST I32 (% e)`. -/
abbrev constI32E (e : Exp) : Exp :=
  .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .caseE "%" (.tupE [e])])

/-- `Step/table.grow-succeed`, rule 8 of `Step` (verbatim). -/
def tableGrowSucceedRule : Rule :=
  .ruleD "table.grow-succeed" [.expP "z" (.varT "state" []), .expP "ref" (.varT "ref" []),
    .expP "n" (.varT "n" []), .expP "x" (.varT "idx" []), .expP "ti" (.varT "tableinst" [])]
    "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [
      .subE (.varE "ref") (.varT "ref" []) (.varT "admininstr" []), constNE,
      .caseE "TABLE.GROW" (.varE "x")]]),
      .caseE "%;%" (.tupE [.callE "with_tableinst" [.expA (.varE "z"), .expA (.varE "x"),
        .expA (.varE "ti")], .listE [constI32E tableLenE]])])
    [.ifPr (.cmpE .eqOp .boolT growTableCallE (.varE "ti"))]

/-- `|$mem(z, 0).BYTES| / (64 · $Ki)`, in `rat` and back. -/
abbrev pagesE : Exp :=
  .cvtE (.binE .divOp (.numT .ratT) (.cvtE (.lenE (.dotE mem0E "BYTES")) .natT .ratT)
    (.cvtE (.binE .mulOp (.numT .natT) (.numE (.natN 64)) (.callE "Ki" [])) .natT .ratT))
    .ratT .natT

/-- `Step/memory.grow-succeed`, rule 19 of `Step` (verbatim). -/
def memGrowSucceedRule : Rule :=
  .ruleD "memory.grow-succeed" [.expP "z" (.varT "state" []), .expP "n" (.varT "n" []),
    .expP "mi" (.varT "meminst" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constNE, .caseE "MEMORY.GROW" (.tupE [])]]),
      .caseE "%;%" (.tupE [.callE "with_meminst" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.varE "mi")],
        .listE [constI32E pagesE]])])
    [.ifPr (.cmpE .eqOp .boolT growMemCallE (.varE "mi"))]

theorem hasRuleAt_tableGrowSucceedV :
    HasRuleAt (simEnv20 B) "Step" "%~>%" 8 tableGrowSucceedRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasRuleAt_memGrowSucceedV :
    HasRuleAt (simEnv20 B) "Step" "%~>%" 19 memGrowSucceedRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Reading a right-hand side `z'; CONST I32 (% e)` back -/

theorem tup1_inv' {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : EvalExp env ρ (.tupE [e]) v) : ∃ u, v = .tuple [u] ∧ EvalExp env ρ e u := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 h
  obtain ⟨u, us, rfl, hu, hus⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hus
  exact ⟨u, rfl, hu⟩

theorem list1_inv' {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : EvalExp env ρ (.listE [e]) v) : ∃ u, v = .list [u] ∧ EvalExp env ρ e u := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 h
  obtain ⟨u, us, rfl, hu, hus⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hus
  exact ⟨u, rfl, hu⟩

theorem tup2_inv' {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) v) :
    ∃ u₁ u₂, v = .tuple [u₁, u₂] ∧ EvalExp env ρ e₁ u₁ ∧ EvalExp env ρ e₂ u₂ := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 h
  obtain ⟨u₁, us, rfl, hu₁, hus⟩ := Equiv.Validation.evalExps_cons_iff.1 hvs
  obtain ⟨u₂, us', rfl, hu₂, hus'⟩ := Equiv.Validation.evalExps_cons_iff.1 hus
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hus'
  exact ⟨u₁, u₂, rfl, hu₁, hu₂⟩

/-- **`W; CONST I32 (% e)`, read back**: the value of each hole. -/
theorem rhsConst_inv {env : Env} {ρ : VarEnv} {W D : Exp} {w : Value}
    (h : EvalExp env ρ (.caseE "%;%" (.tupE [W, .listE [constI32E D]])) w) :
    ∃ vW vD, EvalExp env ρ W vW ∧ EvalExp env ρ D vD ∧
      w = .case "%;%" (.tuple [vW, .list [.case "CONST" (.tuple [caseNilV "I32",
        .case "%" (.tuple [vD])])]]) := by
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vW, vL, rfl, hW, hL⟩ := tup2_inv' hu
  obtain ⟨vC, rfl, hC⟩ := list1_inv' hL
  obtain ⟨uC, hC', rfl⟩ := evalExp_caseE_iff.1 hC
  obtain ⟨vI, vP, rfl, hI, hP⟩ := tup2_inv' hC'
  obtain ⟨uI, hI', rfl⟩ := evalExp_caseE_iff.1 hI
  obtain ⟨uP, hP', rfl⟩ := evalExp_caseE_iff.1 hP
  obtain ⟨vD, rfl, hD⟩ := tup1_inv' hP'
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hI'
  obtain rfl := Equiv.Validation.evalExps_nil_iff.1 hvs
  exact ⟨vW, vD, hW, hD, rfl⟩

/-! ## The premises, read back -/

/-- **The premise of `table.grow-succeed`, read back**: `ti` is V2's grown table. -/
theorem growTablePrem_inv {ρ : VarEnv} (hG : GrowAnswers20 B)
    (hd : ρ.findDef? "growtable" = none) {ti : TableInst} {n : Nat} {r : Ref}
    (et : EvalExp (simEnv20 B) ρ tableE (tableInstV ti))
    (fn : ρ.findVal? "n" = some (.num (.natN n))) (fr : ρ.findVal? "ref" = some (refV r))
    (h : EvalExp (simEnv20 B) ρ (.cmpE .eqOp .boolT growTableCallE (.varE "ti")) (.bool true)) :
    ∃ ti', ti.grow? n r = some ti' ∧ ρ.findVal? "ti" = some (tableInstV ti') := by
  obtain ⟨u₁, u₂, e₁, e₂, hc⟩ := evalExp_cmpE_iff.1 h
  have hu : u₁ = u₂ := cmpValues_eq_true_iff.1 hc
  obtain ⟨T, N, R, eT, eN, eR, hA⟩ := applies_of_call3 hd e₁
  have hT : T = tableInstV ti := EvalExp.unique eT et
  have hN : N = .num (.natN n) := EvalExp.unique eN (evalExp_var fn)
  have hR : R = refV r := EvalExp.unique eR (evalExp_var fr)
  have hB : B.call "growtable" [.val (tableInstV ti), .val (.num (.natN n)), .val (refV r)] =
      some u₁ := hT ▸ hN ▸ hR ▸ growtable20_builtin hA
  obtain ⟨ti', hgr, hv⟩ := hG.table ti n r u₁ hB
  exact ⟨ti', hgr, by rw [evalExp_varE_iff.1 e₂, ← hu, hv]⟩

/-- **The premise of `memory.grow-succeed`, read back**: `mi` is V2's grown memory. -/
theorem growMemPrem_inv {ρ : VarEnv} (hG : GrowAnswers20 B)
    (hd : ρ.findDef? "growmemory" = none) {mi : MemInst} {n : Nat}
    (em : EvalExp (simEnv20 B) ρ mem0E (memInstV mi))
    (fn : ρ.findVal? "n" = some (.num (.natN n)))
    (h : EvalExp (simEnv20 B) ρ (.cmpE .eqOp .boolT growMemCallE (.varE "mi")) (.bool true)) :
    ∃ mi', mi.grow? n = some mi' ∧ ρ.findVal? "mi" = some (memInstV mi') := by
  obtain ⟨u₁, u₂, e₁, e₂, hc⟩ := evalExp_cmpE_iff.1 h
  have hu : u₁ = u₂ := cmpValues_eq_true_iff.1 hc
  obtain ⟨M, N, eM, eN, hA⟩ := applies_of_call2' hd e₁
  have hM : M = memInstV mi := EvalExp.unique eM em
  have hN : N = .num (.natN n) := EvalExp.unique eN (evalExp_var fn)
  have hB : B.call "growmemory" [.val (memInstV mi), .val (.num (.natN n))] = some u₁ :=
    hM ▸ hN ▸ growmemory20_builtin hA
  obtain ⟨mi', hgr, hv⟩ := hG.mem mi n u₁ hB
  exact ⟨mi', hgr, by rw [evalExp_varE_iff.1 e₂, ← hu, hv]⟩

/-! ## The right-hand sides -/

/-- `$with_tableinst(z, x, ti)`. -/
abbrev withTableinstE : Exp :=
  .callE "with_tableinst" [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE "ti")]

/-- `$with_meminst(z, 0, mi)`. -/
abbrev withMeminstE : Exp :=
  .callE "with_meminst" [.expA (.varE "z"), .expA (.caseE "%" (.tupE [.numE (.natN 0)])),
    .expA (.varE "mi")]

/-- **The right-hand side of `table.grow-succeed`** is V2's: the grown table and the old size. -/
theorem tableGrowRhs_eval {ρ : VarEnv} {s : Store H} {f : Frame} {x : TableIdx} {a : Nat}
    {ti ti' : TableInst} (hw : ρ.findDef? "with_tableinst" = none)
    (htb : ρ.findDef? "table" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (idxV x)) (fti : ρ.findVal? "ti" = some (tableInstV ti'))
    (ha : f.module.tables[x.toNat]? = some a) (ht : s.tables[a]? = some ti)
    (hlt : ti.refs.length < 4294967296) :
    EvalExp (simEnv20 B) ρ (.caseE "%;%" (.tupE [withTableinstE, .listE [constI32E tableLenE]]))
      (configV hn ⟨s.setTableInst a ti', f, [constI32 (BitVec.ofNat 32 ti.refs.length)]⟩) := by
  have hv : configV hn ⟨s.setTableInst a ti', f, [constI32 (BitVec.ofNat 32 ti.refs.length)]⟩ =
      .case "%;%" (.tuple [stateV hn (s.setTableInst a ti') f,
        .list [.case "CONST" (.tuple [caseNilV "I32", pctV ti.refs.length])]]) := by
    simp [configV, adminsToV, adminToV_constI32, Nat.mod_eq_of_lt hlt]
  rw [hv]
  exact evalExp_case (evalExp_tup2 (evalExp_withTableinst20 hw (evalExp_var fz) (evalExp_var fx)
    (evalExp_var fti) ha ht) (evalExp_list1 (evalExp_case (evalExp_tup2
      (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_tableLen20 htb fz fx ha ht)
        evalExps_nil, rfl⟩))))))

/-- `|bytes| / (64 · $Ki)` in `rat`. -/
theorem evalExp_pagesQ {ρ : VarEnv} {s : Store H} {f : Frame} {a : Nat} {mi : MemInst}
    (hρ : ρ.findDef? "mem" = none) (hk : ρ.findDef? "Ki" = none)
    (fz : ρ.findVal? "z" = some (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi) :
    EvalExp (simEnv20 B) ρ (.binE .divOp (.numT .ratT)
      (.cvtE (.lenE (.dotE mem0E "BYTES")) .natT .ratT)
      (.cvtE (.binE .mulOp (.numT .natT) (.numE (.natN 64)) (.callE "Ki" [])) .natT .ratT))
      (.num (.ratN ((mi.bytes.size : Rat) / 65536))) := by
  have h64 : EvalExp (simEnv20 B) ρ (.binE .mulOp (.numT .natT) (.numE (.natN 64))
      (.callE "Ki" [])) (.num (.natN 65536)) :=
    evalExp_binNum (evalExp_numE_iff.2 rfl) (evalExp_ki20 hk) (by simp [Num.bin])
  refine evalExp_binNum (evalExp_cvtNum (evalExp_memLen20 hρ fz ha hm) rfl)
    (evalExp_cvtNum h64 rfl) ?_
  simp [Num.bin]

/-- **The page count of the old memory, read back**: when the conversion succeeds it is
`mi.pages`. -/
theorem pagesE_inv {ρ : VarEnv} {s : Store H} {f : Frame} {a : Nat} {mi : MemInst} {v : Value}
    (hρ : ρ.findDef? "mem" = none) (hk : ρ.findDef? "Ki" = none)
    (fz : ρ.findVal? "z" = some (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (h : EvalExp (simEnv20 B) ρ pagesE v) : v = .num (.natN mi.pages) := by
  obtain ⟨q, m, eq, hcvt, rfl⟩ := evalExp_cvtE_iff.1 h
  have hq : Value.num q = .num (.ratN ((mi.bytes.size : Rat) / 65536)) :=
    EvalExp.unique eq (evalExp_pagesQ hρ hk fz ha hm)
  have hc : Num.cvt .natT (.ratN ((mi.bytes.size : Rat) / 65536)) = some m :=
    Value.num.inj hq ▸ hcvt
  rw [pages_of_cvt hc]
  rfl

/-- `0`, as the memory index `%(0)`. -/
theorem evalExp_idx0 {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.caseE "%" (.tupE [.numE (.natN 0)])) (idxV memIdx0) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil, rfl⟩)

/-- **The right-hand side of `memory.grow-succeed`, read back**: the grown memory and the old
page count. -/
theorem memGrowRhs_inv {ρ : VarEnv} {s : Store H} {f : Frame} {a : Nat} {mi mi' : MemInst}
    {w : Value} (hw : ρ.findDef? "with_meminst" = none) (hρ : ρ.findDef? "mem" = none)
    (hk : ρ.findDef? "Ki" = none) (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fmi : ρ.findVal? "mi" = some (memInstV mi'))
    (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
    (hlt : mi.pages < 4294967296)
    (hr : EvalExp (simEnv20 B) ρ (.caseE "%;%" (.tupE [withMeminstE, .listE [constI32E pagesE]])) w) :
    w = configV hn ⟨s.setMemInst a mi', f, [constI32 (BitVec.ofNat 32 mi.pages)]⟩ := by
  obtain ⟨vW, vD, eW, eD, rfl⟩ := rhsConst_inv hr
  have hW : vW = stateV hn (s.setMemInst a mi') f :=
    EvalExp.unique eW (evalExp_withMeminst20 hw (evalExp_var fz) evalExp_idx0 (evalExp_var fmi)
      ha hm)
  have hD : vD = .num (.natN mi.pages) := pagesE_inv hρ hk fz ha hm eD
  rw [hW, hD]
  simp [configV, adminsToV, adminToV_constI32, Nat.mod_eq_of_lt hlt, pctV]

/-! ## The rules backwards -/

/-- **`Step/table.grow-succeed` backwards**, at a `GoodW` configuration, at builtins whose growth
answers are V2's, in a profile that lets growth succeed. -/
theorem bwdStep_tableGrowSucceed {P : Profile} {host : HostSemantics H} (hG : GrowAnswers20 B)
    (hP : ∀ k a n d, P.growMaySucceed k a n d) {c : Config H} {w : Value}
    (hg : GoodW c) (hf : Fires (simEnv20 B) "Step" 8 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, hp⟩ := firesCfg_full20 hasRuleAt_tableGrowSucceedV hf
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := codes20_three hes
  obtain ⟨r, rfl⟩ := ref20_of_var hq (by simp) h₁
  obtain ⟨n, rfl, fn⟩ := constN_of_lhs h₂
  obtain ⟨x, rfl⟩ := head20_tableGrow (head20_of_caseE h₃)
  have hres : InstrResOk (⟨s, f⟩ : State H) (.tableGrow x) := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.2.1
  obtain ⟨a, ti, ha, ht⟩ := table_of_isSome hres
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) := idx_of_caseE h₃ rfl
  have fr : (VarEnv.empty.bindVals σ).findVal? "ref" = some (refV r) := by
    rw [← show adminToV (aref r) = refV r from Pure.adminToV_toAdmin (.ref r)]
    exact evalExp_varE_iff.1 (evalExp_subE_iff.1 h₁)
  have et : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) tableE (tableInstV ti) :=
    evalExp_table20 rfl (evalExp_var fz) (evalExp_var fx) ha ht
  obtain ⟨ti', hgr, fti⟩ :=
    growTablePrem_inv hG rfl et fn fr (Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  exact ⟨_, EvalExp.unique hr (tableGrowRhs_eval rfl rfl fz fx fti ha ht (refs_lt_of_grow hgr)),
    .tableGrowSucceed ha ht hgr (hP _ _ _ _)⟩

/-- **`Step/memory.grow-succeed` backwards**, at a `GoodW` configuration, at builtins whose growth
answers are V2's, in a profile that lets growth succeed. -/
theorem bwdStep_memGrowSucceed {P : Profile} {host : HostSemantics H} (hG : GrowAnswers20 B)
    (hP : ∀ k a n d, P.growMaySucceed k a n d) {c : Config H} {w : Value}
    (hg : GoodW c) (hf : Fires (simEnv20 B) "Step" 19 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hr, hp⟩ := firesCfg_full20 hasRuleAt_memGrowSucceedV hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes20_two hes
  obtain ⟨n, rfl, fn⟩ := constN_of_lhs h₁
  obtain rfl := head20_memoryGrow (head20_of_caseE h₂)
  have hres : InstrResOk (⟨s, f⟩ : State H) .memoryGrow := by
    simpa [GoodW, ResOkL, ResOkA] using hg.2.2.2.1
  obtain ⟨a, mi, ha, hm⟩ := mem_of_isSome hres
  have em : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) mem0E (memInstV mi) :=
    evalExp_mem20 rfl (evalExp_var fz) evalExp_idx0 ha hm
  obtain ⟨mi', hgr, fmi⟩ :=
    growMemPrem_inv hG rfl em fn (Pure.ifPrem (hp _ (List.mem_singleton_self _)))
  have hw : w = configV hn ⟨s.setMemInst a mi', f, [constI32 (BitVec.ofNat 32 mi.pages)]⟩ :=
    memGrowRhs_inv rfl rfl rfl fz fmi ha hm (pages_lt_of_grow hgr) hr
  exact ⟨_, hw, .memoryGrowSucceed ha hm hgr (hP _ _ _ _)⟩

/-! ## `BwdRestW10` at answering builtins -/

/-- **`BwdRestW10` at builtins whose growth answers are V2's**, in a profile that lets growth
succeed. -/
theorem bwdRestW10_of_answers {P : Profile} {host : HostSemantics H} (hG : GrowAnswers20 B)
    (hP : ∀ k a n d, P.growMaySucceed k a n d) : BwdRestW10 B hn P host where
  step i hi c w hg hf := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact bwdStep_tableGrowSucceed hG hP hg hf
    · exact bwdStep_memGrowSucceed hG hP hg hf

/-! ## The backward half at any builtins with these properties -/

/-- A listed inert rule does not fire, at any builtins answering no inert primitive. -/
theorem not_fires_inertG (E : InertEnv (simEnv20 B)) {x : IL.Id} {l : List Nat}
    (hok : inertOk x l = true) {i : Nat} (hi : i ∈ l) {v : Value} :
    ¬ Fires (simEnv20 B) x i v := by
  rintro ⟨t, rules, r, hrel, hr, hb⟩
  have hrules : relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed) x = rules := by
    rw [← relRules_simEnv20 B]
    simp [relRules, hrel]
  have h₁ := List.all_eq_true.1 hok i hi
  rw [hrules, hr] at h₁
  exact not_body_inert E h₁ hb

/-- `BwdRestW2` from `BwdRestW3`, at any builtins answering no inert primitive. -/
theorem bwdRestW2_of_rest3G {P : Profile} {host : HostSemantics H}
    (E : InertEnv (simEnv20 B)) (R : BwdRestW3 B hn P host) : BwdRestW2 B hn P host where
  read i hd h78 c w hg hc hw hf := by
    by_cases hi : i ∈ inertRead20
    · exact absurd hf (not_fires_inertG E inertRead20_ok hi)
    · exact R.read i hd h78 hi c w hg hc hw hf
  step i h6 c w hg hf := by
    by_cases hi : i ∈ inertStep20
    · exact absurd hf (not_fires_inertG E inertStep20_ok hi)
    · exact R.step i h6 hi c w hg hf

/-- **The backward half at any builtins that extend the spec's numerics, answer no inert
primitive, and answer growth as V2 does**, in a profile that lets growth both fail and succeed:
every step of the wasm-2.0 script from the image of a `GoodW` configuration is the image of a V2
step. At `floatIntB` this is `wholeStepBwdW`. With builtins that do answer `$growtable` and
`$growmemory`, `Step` 8 and 19 fire and are matched by V2's `grow-succeed` steps. -/
theorem wholeStepBwdW_at {P : Profile} {host : HostSemantics H}
    (hI : Sim.IntNumeric.IntB B) (hF : Sim.Floats.FloatB P B) (E : InertEnv (simEnv20 B))
    (hG : GrowAnswers20 B) (hPf : ∀ k a n d, P.growMayFail k a n d)
    (hPs : ∀ k a n d, P.growMaySucceed k a n d) (c : Config H) (w : Value) (hg : GoodW c)
    (hs : Sim.Round6.Reading.SStepB (simEnv20 B) (configV hn c) w) :
    ∃ c', w = configV hn c' ∧ Step P host c c' := by
  have R10 : BwdRestW10 B hn P host := bwdRestW10_of_answers hG hPs
  have R3 : BwdRestW3 B hn P host :=
    bwdRestW3_of_rest4 hPf (bwdRestW4_of_rest5 (bwdRestW5_of_rest6 (bwdRestW6_of_rest7
      (bwdRestW7_of_rest8 (bwdRestW8_of_rest9 (bwdRestW9_of_rest10 R10))))))
  exact backward20G_of_parts (bwdPartsG_of_restW hI hF
    (bwdRestW_of_rest2 (bwdRestW2_of_rest3G E R3))) cfgInv_goodW c w hg hs

end Silmaril.Wasm.SpecTec.Sim20.Whole
