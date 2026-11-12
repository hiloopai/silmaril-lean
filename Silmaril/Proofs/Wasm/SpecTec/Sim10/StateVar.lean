module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Assemble
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StateVar

/-!
# Variables and `call` in 1.0, backwards, transferred from 2.0

The census finds 1.0's `Step_read/call` (2), `local.get` (6), `global.get` (7) and `Step/local.set`
(5) byte-identical to 2.0's, and 1.0's state accessors `$local`, `$global`, `$funcaddr` and
`$with_local` have 2.0's clauses (`hasClause_local10`, …, kernel `rfl` against the 2.0 clause
terms of `Sim20.State`). What differs is the encoding the clauses read: 1.0's store has four
fields and its values are V1 values (`Sim10.frameV`, `Sim10.storeV`). So the 2.0 rule constants
(`Sim20.State.localGetRule`, …) are the 1.0 rules, and the evaluations are redone at the 1.0
encoding with the generic call and path lemmas of `Sim.State.Eval`.

Backwards, at a configuration whose named resources exist (`ResOkL10`, part of `GoodV1`), each is
V1's `Step.localGet`, `globalGet`, `call` and `localSet`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values)
open Silmaril.Wasm.Execution.Runtime (Frame GlobalInst)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk evalExp_tup2 evalExp_list1 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.State (HasClause1 idxPayload evalExp_call1 pathGet_root pathGet_dot
  pathSet_idx pathSet_dot pathSet_root evalExp_idxPayload)
open Silmaril.Wasm.SpecTec.Sim20.State (sfxPat sfxvPat sfPat matchArgs_sfx matchArgs_sfxv
  matchArgs_sf localGetRule globalGetRule callRule localSetRule)
open Silmaril.Wasm.SpecTec.Sim20.Pure (evalExp_list0)

set_option maxRecDepth 100000

variable (B : Builtins)

/-! ## Provenance and clauses -/

theorem hasRuleAt10_call : HasRuleAt (simEnv10 B) "Step_read" "%~>%" 2 callRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_localGet : HasRuleAt (simEnv10 B) "Step_read" "%~>%" 6 localGetRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_globalGet : HasRuleAt (simEnv10 B) "Step_read" "%~>%" 7 globalGetRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩
theorem hasRuleAt10_localSet : HasRuleAt (simEnv10 B) "Step" "%~>%" 5 localSetRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasClause_local10 : HasClause1 (simEnv10 B) "local" sfxPat
    (.idxE (.dotE (.varE "f") "LOCALS") idxPayload) := ⟨_, _, _, rfl⟩

theorem hasClause_global10 : HasClause1 (simEnv10 B) "global" sfxPat
    (.idxE (.dotE (.varE "s") "GLOBALS") (.idxE (.dotE (.dotE (.varE "f") "MODULE") "GLOBALS")
      idxPayload)) := ⟨_, _, _, rfl⟩

theorem hasClause_funcaddr10 : HasClause1 (simEnv10 B) "funcaddr" sfPat
    (.dotE (.dotE (.varE "f") "MODULE") "FUNCS") := ⟨_, _, _, rfl⟩

theorem hasClause_withLocal10 : HasClause1 (simEnv10 B) "with_local" sfxvPat
    (.caseE "%;%" (.tupE [.varE "s", .updE (.varE "f") (.idxP (.dotP .rootP "LOCALS") idxPayload)
      (.varE "v")])) := ⟨_, _, _, rfl⟩

/-! ## The accessors at the 1.0 encoding -/

variable {B} {H : Type} {hn : H → String}

/-- **`$local(z, x)`**, at a 1.0 state and a local index in range. -/
theorem evalExp_local10 {ρ : VarEnv} {ez ex : Exp} {s : Store H} {f : Frame} {x : LocalIdx}
    {v : Execution.Runtime.Value} (hρ : ρ.findDef? "local" = none)
    (hz : EvalExp (simEnv10 B) ρ ez (stateV hn s f))
    (hx : EvalExp (simEnv10 B) ρ ex (idxV x)) (hv : f.locals[x.toNat]? = some v) :
    EvalExp (simEnv10 B) ρ (.callE "local" [.expA ez, .expA ex]) (valV v) :=
  evalExp_call1 (hasClause_local10 B) hρ (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil))
    matchArgs_sfx (evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨frameV f,
      evalExp_var rfl, rfl⟩, evalExp_idxPayload rfl,
      by simp [Value.idx?, List.getElem?_map, hv]⟩)

/-- **`$global(z, x)`**, at a 1.0 state whose module lists global address `a` at `x`. -/
theorem evalExp_global10 {ρ : VarEnv} {ez ex : Exp} {s : Store H} {f : Frame} {x : GlobalIdx}
    {a : Execution.Runtime.GlobalAddr} {g : GlobalInst} (hρ : ρ.findDef? "global" = none)
    (hz : EvalExp (simEnv10 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv10 B) ρ ex (idxV x))
    (ha : f.module.globals[x.toNat]? = some a) (hg : s.globals[a.value]? = some g) :
    EvalExp (simEnv10 B) ρ (.callE "global" [.expA ez, .expA ex]) (globalInstV g) :=
  evalExp_call1 (hasClause_global10 B) hρ (evalArgs_cons hz (evalArgs_cons hx evalArgs_nil))
    matchArgs_sfx (evalExp_idxE_iff.2 ⟨_, a.value, evalExp_dotE_iff.2 ⟨storeV hn s,
      evalExp_var rfl, rfl⟩,
      evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
        evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl, rfl⟩, rfl⟩,
        evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩,
      by simp [Value.idx?, List.getElem?_map, hg]⟩)

/-- **`$funcaddr(z)`**, the frame's function addresses. -/
theorem evalExp_funcaddr10 {ρ : VarEnv} {ez : Exp} {s : Store H} {f : Frame}
    (hρ : ρ.findDef? "funcaddr" = none) (hz : EvalExp (simEnv10 B) ρ ez (stateV hn s f)) :
    EvalExp (simEnv10 B) ρ (.callE "funcaddr" [.expA ez]) (addrsV f.module.funcs) :=
  evalExp_call1 (hasClause_funcaddr10 B) hρ (evalArgs_cons hz evalArgs_nil) matchArgs_sf
    (evalExp_dotE_iff.2 ⟨moduleInstV f.module, evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl,
      rfl⟩, rfl⟩)

/-- **`$with_local(z, x, v)`**, at a local index in range. -/
theorem evalExp_withLocal10 {ρ : VarEnv} {ez ex ev : Exp} {s : Store H} {f : Frame}
    {x : LocalIdx} {v : Execution.Runtime.Value} (hρ : ρ.findDef? "with_local" = none)
    (hz : EvalExp (simEnv10 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv10 B) ρ ex (idxV x))
    (hv : EvalExp (simEnv10 B) ρ ev (valV v)) (hlt : x.toNat < f.locals.length) :
    EvalExp (simEnv10 B) ρ (.callE "with_local" [.expA ez, .expA ex, .expA ev])
      (stateV hn s { f with locals := f.locals.set x.toNat v }) := by
  refine evalExp_call1 (hasClause_withLocal10 B) hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hv evalArgs_nil))) matchArgs_sfxv ?_
  refine evalExp_case (evalExp_tup2 (evalExp_var rfl) ?_)
  refine evalExp_updE_iff.2 ⟨frameV f, valV v, evalExp_var rfl, evalExp_var rfl, ?_⟩
  have hs : Value.setIdx (.list (f.locals.map valV)) x.toNat (valV v) =
      some (.list ((f.locals.map valV).set x.toNat (valV v))) := by
    simp [Value.setIdx, hlt]
  have hf : (frameV f).setField "LOCALS" (.list ((f.locals.map valV).set x.toNat (valV v))) =
      some (frameV { f with locals := f.locals.set x.toNat v }) := by
    simp [frameV, Value.setField, List.map_set]
  exact pathSet_idx (pathGet_dot pathGet_root rfl) (evalExp_idxPayload rfl) hs
    (pathSet_dot pathGet_root hf pathSet_root)

/-! ## Backwards -/

/-- The resources named by a one-instruction `GoodV1` configuration exist. -/
theorem instrResOk_of_good {s : Store H} {f : Frame} {i : V1.Instr}
    (hg : GoodV1 (⟨s, f, [.source i]⟩ : Config H)) : InstrResOk10 s f i := by
  simpa [GoodV1, ResOkL10, ResOkA10] using hg.1

/-- The index operand `OP x` of a one-instruction left-hand side, read back. -/
theorem idx_of_caseE10 {ρ : VarEnv} {op : MixopS} {a : Admin} {X : Value}
    (ha : EvalExp (simEnv10 B) ρ (.caseE op (.varE "x")) (adminToV a))
    (hX : adminToV a = .case op X) : EvalExp (simEnv10 B) ρ (.varE "x") X := by
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 ha
  obtain rfl : u = X := (Value.case.inj (hcu.symm.trans hX)).2
  exact hu

/-- **`Step_read/local.get` backwards**, at a `GoodV1` configuration. -/
theorem bwd10_localGet {host : HostSemantics H} {c : Config H} {w : List Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10 B) "Step_read" 6 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, -⟩ := firesCfg10_inv (hasRuleAt10_localGet B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain ⟨x, rfl⟩ := head10_localGet (head10_of_caseE ha)
  have hr : x.toNat < f.locals.length := instrResOk_of_good hg
  obtain ⟨v, hv⟩ : ∃ v, f.locals[x.toNat]? = some v := ⟨_, List.getElem?_eq_getElem hr⟩
  have hx := idx_of_caseE10 ha rfl
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.listE [.subE (.callE "local" [.expA (.varE "z"),
      .expA (.varE "x")]) (.varT "val" []) (.varT "admininstr" [])]) (.list (adminsToV [value v])) := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
    exact evalExp_list1 (evalExp_subE_iff.2 (evalExp_local10 rfl (evalExp_var fz) hx hv))
  exact ⟨[value v], Value.list.inj (EvalExp.unique hrh he), .localGet s f x v hv⟩

/-- **`Step_read/global.get` backwards**, at a `GoodV1` configuration. -/
theorem bwd10_globalGet {host : HostSemantics H} {c : Config H} {w : List Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10 B) "Step_read" 7 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, -⟩ := firesCfg10_inv (hasRuleAt10_globalGet B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain ⟨x, rfl⟩ := head10_globalGet (head10_of_caseE ha)
  obtain ⟨ad, g, had, hgl⟩ : ∃ ad g, f.module.globals[x.toNat]? = some ad ∧
      s.globals[ad.value]? = some g := instrResOk_of_good hg
  have hx := idx_of_caseE10 ha rfl
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ) (.listE [.subE (.dotE (.callE "global" [.expA (.varE "z"),
      .expA (.varE "x")]) "VALUE") (.varT "val" []) (.varT "admininstr" [])])
      (.list (adminsToV [value g.value])) := by
    rw [adminsToV_map10, List.map_singleton, adminToV_value]
    exact evalExp_list1 (evalExp_subE_iff.2 (evalExp_dotE_iff.2
      ⟨_, evalExp_global10 rfl (evalExp_var fz) hx had hgl, rfl⟩))
  exact ⟨[value g.value], Value.list.inj (EvalExp.unique hrh he),
    .globalGet s f x ad g had hgl⟩

/-- **`Step_read/call` backwards**, at a `GoodV1` configuration. -/
theorem bwd10_call {host : HostSemantics H} {c : Config H} {w : List Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10 B) "Step_read" 2 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, -, fz, hes, hrh, -⟩ := firesCfg10_inv (hasRuleAt10_call B) hf
  obtain ⟨a, rfl, ha⟩ := codes10_one hes
  obtain ⟨x, rfl⟩ := head10_call (head10_of_caseE ha)
  have hr : (f.module.funcs[x.toNat]?).isSome := instrResOk_of_good hg
  obtain ⟨fa, hfa⟩ := Option.isSome_iff_exists.1 hr
  have hx := idx_of_caseE10 ha rfl
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.listE [.caseE "CALL_ADDR" (.idxE (.callE "funcaddr" [.expA (.varE "z")]) idxPayload)])
      (.list (adminsToV [.invoke fa])) :=
    evalExp_list1 (evalExp_case (evalExp_idxE_iff.2 ⟨_, x.toNat,
      evalExp_funcaddr10 rfl (evalExp_var fz), evalExp_idxPayload (evalExp_varE_iff.1 hx),
      by simp [Value.idx?, addrsV, List.getElem?_map, hfa]⟩))
  exact ⟨[.invoke fa], Value.list.inj (EvalExp.unique hrh he), .call s f x fa hfa⟩

/-- **`Step/local.set` backwards**, at a `GoodV1` configuration. -/
theorem bwd10_localSet {host : HostSemantics H} {c : Config H} {w : Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10 B) "Step" 5 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes, hrh, -⟩ := firesCfg10_inv (hasRuleAt10_localSet B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨v, rfl, fv⟩ := val10_of_var hq (by simp) h₁
  obtain ⟨x, rfl⟩ := head10_localSet (head10_of_caseE h₂)
  have hr : x.toNat < f.locals.length := by
    have h := hg.1
    simp only [ResOkL10] at h
    exact h.2.1
  have hx := idx_of_caseE10 h₂ rfl
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.callE "with_local" [.expA (.varE "z"), .expA (.varE "x"),
        .expA (.varE "val")], .listE []]))
      (configV hn ⟨s, { f with locals := f.locals.set x.toNat v }, []⟩) :=
    evalExp_case (evalExp_tup2 (evalExp_withLocal10 rfl (evalExp_var fz) hx (evalExp_var fv) hr)
      evalExp_list0)
  obtain ⟨old, hold⟩ : ∃ old, f.locals[x.toNat]? = some old := ⟨_, List.getElem?_eq_getElem hr⟩
  exact ⟨_, EvalExp.unique hrh he, .localSet s f x v old hold⟩

end Silmaril.Wasm.SpecTec.Sim10.Whole
