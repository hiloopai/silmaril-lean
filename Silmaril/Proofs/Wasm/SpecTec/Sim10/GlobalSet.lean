module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StateVar
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StateGlobal

/-!
# `Step/global.set` of 1.0, backwards

1.0's `Step/global.set` (rule 6) is 2.0's rule 5 verbatim (`Sim20.State.globalSetRule`, kernel
`rfl` at the 1.0 index), and 1.0's `$with_global` has 2.0's one clause
(`hasClause_withGlobal10`, kernel `rfl`). The clause writes `VALUE` and keeps `TYPE`.

At the 1.0 encoding a V1 `GlobalInst` has no type of its own: `globalInstV g` derives `TYPE` from
`g.value.type`. So the script's update `globalInstV g [.VALUE = v]` is the image of V1's
`{g with value := v}` exactly when `v.type = g.value.type` (`setField_globalInstV`). That is the
`GSetOk` conjunct of `GoodV1`, which validation guarantees. Backwards, at a `GoodV1`
configuration, the rule is V1's `Step.globalSet` (the target exists and is mutable by `ResOkL10`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value setGlobal)
open Silmaril.Wasm.Execution.Runtime (Frame GlobalInst)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires evalExp_tup2 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.State (HasClause1 idxPayload evalExp_call1 pathGet_root pathGet_dot
  pathGet_idx pathSet_idx pathSet_dot pathSet_root evalExp_idxPayload)
open Silmaril.Wasm.SpecTec.Sim20.State (sfxvPat matchArgs_sfxv globalSetRule)
open Silmaril.Wasm.SpecTec.Sim20.Pure (evalExp_list0)

set_option maxRecDepth 100000

variable (B : Builtins)

/-! ## Provenance -/

theorem hasRuleAt10_globalSet : HasRuleAt (simEnv10 B) "Step" "%~>%" 6 globalSetRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem hasClause_withGlobal10 : HasClause1 (simEnv10 B) "with_global" sfxvPat
    (.caseE "%;%" (.tupE [.updE (.varE "s") (.dotP (.idxP (.dotP .rootP "GLOBALS")
      (.idxE (.dotE (.dotE (.varE "f") "MODULE") "GLOBALS") idxPayload)) "VALUE") (.varE "v"),
      .varE "f"])) := ⟨_, _, _, rfl⟩

/-! ## `$with_global` at the 1.0 encoding -/

variable {B} {H : Type} {hn : H → String}

/-- **The script's write of `VALUE` is V1's write of the value**, when the type is kept. -/
theorem setField_globalInstV {g : GlobalInst} {v : Execution.Runtime.Value}
    (ht : v.type = g.value.type) :
    (globalInstV g).setField "VALUE" (valV v) = some (globalInstV { g with value := v }) := by
  simp [globalInstV, Value.setField, ht]

/-- The 1.0 store with one global replaced. -/
theorem storeV_setGlobal10 (s : Store H) (a : Execution.Runtime.GlobalAddr) (g : GlobalInst) :
    (storeV hn s).setField "GLOBALS" (.list ((s.globals.map globalInstV).set a.value
        (globalInstV g))) = some (storeV hn (setGlobal s a g)) := by
  simp [storeV, Value.setField, setGlobal, List.map_set]

/-- **`$with_global(z, x, v)`** at the 1.0 encoding, for a value of the global's type. -/
theorem evalExp_withGlobal10 {ρ : VarEnv} {ez ex ev : Exp} {s : Store H} {f : Frame}
    {x : GlobalIdx} {v : Execution.Runtime.Value} {a : Execution.Runtime.GlobalAddr}
    {g : GlobalInst} (hρ : ρ.findDef? "with_global" = none)
    (hz : EvalExp (simEnv10 B) ρ ez (stateV hn s f)) (hx : EvalExp (simEnv10 B) ρ ex (idxV x))
    (hv : EvalExp (simEnv10 B) ρ ev (valV v)) (ha : f.module.globals[x.toNat]? = some a)
    (hg : s.globals[a.value]? = some g) (ht : v.type = g.value.type) :
    EvalExp (simEnv10 B) ρ (.callE "with_global" [.expA ez, .expA ex, .expA ev])
      (stateV hn (setGlobal s a { g with value := v }) f) := by
  refine evalExp_call1 (hasClause_withGlobal10 B) hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hv evalArgs_nil))) matchArgs_sfxv ?_
  refine evalExp_case (evalExp_tup2 ?_ (evalExp_var rfl))
  refine evalExp_updE_iff.2 ⟨storeV hn s, valV v, evalExp_var rfl, evalExp_var rfl, ?_⟩
  let σ : VarEnv := (((VarEnv.empty.bindVal "s" (storeV hn s)).bindVal "f" (frameV f)).bindVal "x"
    (idxV x)).bindVal "v" (valV v)
  have hai : EvalExp (simEnv10 B) σ (.idxE (.dotE (.dotE (.varE "f") "MODULE") "GLOBALS")
      idxPayload) (.num (.natN a.value)) :=
    evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
      evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl, rfl⟩, rfl⟩,
      evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩
  have hgl : PathGet (simEnv10 B) σ (storeV hn s) (.dotP .rootP "GLOBALS")
      (.list (s.globals.map globalInstV)) := pathGet_dot pathGet_root rfl
  have hel : PathGet (simEnv10 B) σ (storeV hn s)
      (.idxP (.dotP .rootP "GLOBALS") (.idxE (.dotE (.dotE (.varE "f") "MODULE") "GLOBALS")
        idxPayload)) (globalInstV g) :=
    pathGet_idx hgl hai (by simp [Value.idx?, List.getElem?_map, hg])
  have hlt : a.value < s.globals.length := (List.getElem?_eq_some_iff.1 hg).1
  exact pathSet_dot hel (setField_globalInstV ht) (pathSet_idx hgl hai
    (by simp [Value.setIdx, hlt]) (pathSet_dot pathGet_root (storeV_setGlobal10 s a _)
      pathSet_root))

/-! ## Backwards -/

/-- An exact `global.set` redex is active in itself, in its own frame. -/
theorem activeF_self (f : Frame) (l : List Admin) : ActiveF f l f l := by
  have h : ActiveF f ([] ++ l ++ []) f l := .piece
  simpa using h

/-- **`Step/global.set` backwards**, at a `GoodV1` configuration. -/
theorem bwd10_globalSet {host : HostSemantics H} {c : Config H} {w : Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10 B) "Step" 6 (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, fz, hes, hrh, -⟩ := firesCfg10_inv (hasRuleAt10_globalSet B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes10_two hes
  obtain ⟨v, rfl, fv⟩ := val10_of_var hq (by simp) h₁
  obtain ⟨x, rfl⟩ := head10_globalSet (head10_of_caseE h₂)
  obtain ⟨ad, g, had, hgl, hmut⟩ : ∃ ad g, f.module.globals[x.toNat]? = some ad ∧
      s.globals[ad.value]? = some g ∧ g.mutability = .var := by
    have h := hg.1
    simp only [ResOkL10, ResOkA10, InstrResOk10] at h
    exact h.2.1
  have ht : v.type = g.value.type := hg.2.2.2 f v x ad g (activeF_self _ _) had hgl
  have hx := idx_of_caseE10 h₂ rfl
  have he : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.callE "with_global" [.expA (.varE "z"), .expA (.varE "x"),
        .expA (.varE "val")], .listE []]))
      (configV hn ⟨setGlobal s ad { g with value := v }, f, []⟩) :=
    evalExp_case (evalExp_tup2 (evalExp_withGlobal10 rfl (evalExp_var fz) hx (evalExp_var fv)
      had hgl ht) evalExp_list0)
  exact ⟨_, EvalExp.unique hrh he, .globalSet s f x ad g v had hgl hmut⟩

end Silmaril.Wasm.SpecTec.Sim10.Whole
