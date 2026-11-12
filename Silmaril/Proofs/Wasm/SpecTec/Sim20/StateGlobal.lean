module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StateVar

/-!
# `Step/global.set` of the wasm-2.0 script against V2's `Step.globalSet`

Rule 5 of `Step` (`globalSetRule`, verbatim from `Scripts.Wasm20.Original`, provenance
`hasRuleAt_globalSet` by kernel `rfl`) writes through `$with_global(z, x, val)`
(`Original.d321`), `s[.GLOBALS[f.MODULE.GLOBALS[x]].VALUE = v]`. At a V2 configuration whose
module lists global address `a` at `x` and whose store holds a global instance there, it fires
with exactly the image of `Step.globalSet`'s right-hand side (`globalSet_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.State

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk TypedV evalExp_tup2 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (FiresB ruleConcl)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1 pathGet_root pathGet_dot pathGet_idx pathSet_idx
  pathSet_dot pathSet_root evalExp_idxPayload HasClause1 idxPayload)
open Silmaril.Wasm.SpecTec.Sim20.Pure (quant_val evalExp_list2 evalExp_tup2_inv adminToV_toAdmin)

variable (B : Builtins)

set_option maxRecDepth 100000

/-- `Step/global.set`, rule 5 of `Step` (verbatim). -/
def globalSetRule : Rule :=
  (Rule.ruleD "global.set"
  [(Param.expP "z" (Typ.varT "state" [])), (Param.expP "val" (Typ.varT "val" [])), (Param.expP "x"
  (Typ.varT "idx" []))] "%~>%" (Exp.tupE [(Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z"), (Exp.listE
  [(Exp.subE (Exp.varE "val") (Typ.varT "val" []) (Typ.varT "admininstr" [])), (Exp.caseE "GLOBAL.SET"
  (Exp.varE "x"))])])), (Exp.caseE "%;%" (Exp.tupE [(Exp.callE "with_global" [(Arg.expA (Exp.varE "z")),
  (Arg.expA (Exp.varE "x")), (Arg.expA (Exp.varE "val"))]), (Exp.listE [])]))]) [])

theorem hasRuleAt_globalSet : HasRuleAt (simEnv20 B) "Step" "%~>%" 5 globalSetRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `$with_global`'s one clause. -/
theorem hasClause_withGlobal20 : HasClause1 (simEnv20 B) "with_global" sfxvPat
    (.caseE "%;%" (.tupE [.updE (.varE "s") (.dotP (.idxP (.dotP .rootP "GLOBALS")
      (.idxE (.dotE (.dotE (.varE "f") "MODULE") "GLOBALS") idxPayload)) "VALUE") (.varE "v"),
      .varE "f"])) := ⟨_, _, _, rfl⟩

variable {H : Type} (hn : H → String)

/-- The store with one global's value replaced. -/
theorem storeV_setGlobal (s : Store H) {a : Nat} (g : GlobalInst)
    (v : Val) :
    (storeV hn s).setField "GLOBALS"
        (.list ((s.globals.map globalInstV).set a (globalInstV { g with value := v }))) =
      some (storeV hn (s.setGlobalInst a { g with value := v })) := by
  simp [storeV, Value.setField, Store.setGlobalInst, List.map_set]

/-- **`$with_global(z, x, v)`**, at a module listing global address `a` at `x` and a store
holding a global instance at `a`. -/
theorem evalExp_withGlobal20 {ρ : VarEnv} {ez ex ev : Exp} {s : Store H} {f : Frame}
    {x : GlobalIdx} {v : Val} {a : Nat} {g : GlobalInst} (hρ : ρ.findDef? "with_global" = none)
    (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv20 B) ρ ex (idxV x))
    (hv : EvalExp (simEnv20 B) ρ ev (valV v)) (ha : f.module.globals[x.toNat]? = some a)
    (hg : s.globals[a]? = some g) :
    EvalExp (simEnv20 B) ρ (.callE "with_global" [.expA ez, .expA ex, .expA ev])
      (stateV hn (s.setGlobalInst a { g with value := v }) f) := by
  refine evalExp_call1 (hasClause_withGlobal20 B) hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hv evalArgs_nil))) matchArgs_sfxv ?_
  refine evalExp_case (evalExp_tup2 ?_ (evalExp_var rfl))
  refine evalExp_updE_iff.2 ⟨storeV hn s, valV v, evalExp_var rfl, evalExp_var rfl, ?_⟩
  let σ : VarEnv := (((VarEnv.empty.bindVal "s" (storeV hn s)).bindVal "f" (frameV f)).bindVal "x"
    (idxV x)).bindVal "v" (valV v)
  have hai : EvalExp (simEnv20 B) σ (.idxE (.dotE (.dotE (.varE "f") "MODULE") "GLOBALS")
      idxPayload) (.num (.natN a)) :=
    evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
      evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl, frameV_module f⟩, rfl⟩,
      evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩
  have hgl : PathGet (simEnv20 B) σ (storeV hn s) (.dotP .rootP "GLOBALS")
      (.list (s.globals.map globalInstV)) := pathGet_dot pathGet_root rfl
  have hel : PathGet (simEnv20 B) σ (storeV hn s)
      (.idxP (.dotP .rootP "GLOBALS") (.idxE (.dotE (.dotE (.varE "f") "MODULE") "GLOBALS")
        idxPayload)) (globalInstV g) :=
    pathGet_idx hgl hai (by simp [Value.idx?, List.getElem?_map, hg])
  have hset : (globalInstV g).setField "VALUE" (valV v) =
      some (globalInstV { g with value := v }) := by
    simp [globalInstV, Value.setField]
  have hlt : a < s.globals.length := (List.getElem?_eq_some_iff.1 hg).1
  exact pathSet_dot hel hset (pathSet_idx hgl hai (by simp [Value.setIdx, hlt])
    (pathSet_dot pathGet_root (storeV_setGlobal hn s g v) pathSet_root))

/-- The conclusion of `global.set`, evaluated. -/
theorem eval_globalSet {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {x : GlobalIdx}
    {v : Val} {a : Nat} {g : GlobalInst}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f))
    (fv : (VarEnv.empty.bindVals σ).findVal? "val" = some (valV v))
    (fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x))
    (ha : f.module.globals[x.toNat]? = some a) (hg : s.globals[a]? = some g) :
    EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (ruleConcl globalSetRule)
      (.tuple [.case "%;%" (.tuple [stateV hn s f, .list [valV v, .case "GLOBAL.SET" (idxV x)]]),
        configV hn ⟨s.setGlobalInst a { g with value := v }, f, []⟩]) :=
  evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list2 (evalExp_subE_iff.2 (evalExp_var fv)) (evalExp_case (evalExp_var fx)))))
    (evalExp_case (evalExp_tup2 (evalExp_withGlobal20 B hn rfl (evalExp_var fz) (evalExp_var fx)
      (evalExp_var fv) ha hg) Silmaril.Wasm.SpecTec.Sim20.Pure.evalExp_list0))

/-- The image of `global.set`'s configuration. -/
theorem configV_globalSet (s : Store H) (f : Frame) (x : GlobalIdx) (v : Val) :
    configV hn ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩ =
      .case "%;%" (.tuple [stateV hn s f, .list [valV v, .case "GLOBAL.SET" (idxV x)]]) := by
  show Value.case "%;%" (.tuple [stateV hn s f, .list [adminToV v.toAdmin,
    instrToV (.globalSet x)]]) = _
  rw [adminToV_toAdmin]
  rfl

/-- `global.set`, read back. -/
theorem globalSet_inv {s : Store H} {f : Frame} {x : GlobalIdx} {v : Val} {a : Nat}
    {g : GlobalInst} (ha : f.module.globals[x.toNat]? = some a) (hg : s.globals[a]? = some g)
    {w : Value}
    (hf : FiresB (simEnv20 B) "Step" 5 (.tuple [.case "%;%" (.tuple [stateV hn s f,
      .list [valV v, .case "GLOBAL.SET" (idxV x)]]), w])) :
    w = configV hn ⟨s.setGlobalInst a { g with value := v }, f, []⟩ := by
  obtain ⟨σ, hq, he⟩ := (firesB_noPrems_iff (hasRuleAt_globalSet B) rfl).1 hf
  obtain ⟨Z, fz⟩ := quant_val (x := "z") (t := stateT) hq (by simp)
  obtain ⟨U, fu⟩ := quant_val (x := "val") (t := .varT "val" []) hq (by simp)
  obtain ⟨X, fx⟩ := quant_val (x := "x") (t := idxT) hq (by simp)
  obtain ⟨hl, hr⟩ := evalExp_tup2_inv he
  have hu : Value.case "%;%" (.tuple [Z, .list [U, .case "GLOBAL.SET" X]]) =
      .case "%;%" (.tuple [stateV hn s f, .list [valV v, .case "GLOBAL.SET" (idxV x)]]) :=
    EvalExp.unique (evalExp_case (evalExp_tup2 (evalExp_var fz)
      (evalExp_list2 (evalExp_subE_iff.2 (evalExp_var fu)) (evalExp_case (evalExp_var fx))))) hl
  have hu' : Z = stateV hn s f ∧ U = valV v ∧ X = idxV x := by
    simpa only [Value.case.injEq, Value.tuple.injEq, Value.list.injEq, List.cons.injEq, true_and,
      and_true] using hu
  have hev := eval_globalSet B hn (hu'.1 ▸ fz) (hu'.2.1 ▸ fu) (hu'.2.2 ▸ fx) ha hg
  exact EvalExp.unique hr (evalExp_tup2_inv hev).2

/-- **`Step/global.set` is `Step.globalSet`**, where V2's lookups are defined. -/
theorem globalSet_iff {s : Store H} {f : Frame} {x : GlobalIdx} {v : Val} {a : Nat}
    {g : GlobalInst} (ha : f.module.globals[x.toNat]? = some a) (hg : s.globals[a]? = some g)
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (hv : TypedV (simEnv20 B) (.varT "val" []) (valV v)) (hx : TypedV (simEnv20 B) idxT (idxV x))
    {w : Value} :
    FiresB (simEnv20 B) "Step" 5
        (.tuple [configV hn ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩, w]) ↔
      w = configV hn ⟨s.setGlobalInst a { g with value := v }, f, []⟩ := by
  rw [configV_globalSet]
  refine ⟨globalSet_inv B hn ha hg, ?_⟩
  rintro rfl
  exact (firesB_noPrems_iff (hasRuleAt_globalSet B) rfl).2
    ⟨[("z", stateV hn s f), ("val", valV v), ("x", idxV x)],
      QuantsOk.cons rfl (hz _ ⟨rfl, rfl, rfl⟩) (QuantsOk.cons rfl (hv _ ⟨rfl, rfl, rfl⟩)
        (QuantsOk.cons rfl (hx _ ⟨rfl, rfl, rfl⟩) QuantsOk.nil)),
      eval_globalSet B hn rfl rfl rfl ha hg⟩

/-- `Step.globalSet` at the same configuration. -/
theorem globalSet_step (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    {s : Store H} {f : Frame} {x : GlobalIdx} {v : Val} {a : Nat} {g : GlobalInst}
    (ha : f.module.globals[x.toNat]? = some a) (hg : s.globals[a]? = some g) :
    Step P host ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩
      ⟨s.setGlobalInst a { g with value := v }, f, []⟩ :=
  .globalSet ha hg

end Silmaril.Wasm.SpecTec.Sim20.State
