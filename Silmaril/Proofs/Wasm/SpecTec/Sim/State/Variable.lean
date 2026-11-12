module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.State.Common

/-!
# Family M: `local.*` and `global.*`, Core → SpecTec

The five rules of `VariableStep`: `Step_pure/local.tee` (30), `Step_read/local.get` (23),
`Step_read/global.get` (24), `Step/local.set` (11) and `Step/global.set` (12), each constructed
under the declarative reading for arbitrary state values (`spure_localTee`, `sread_localGet`, …),
and assembled into the `Forward.variable_` obligation at `simEnv B` (`fwd_variable_`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.State

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecNumeric (cmpValues_eq_true_iff)

/-! ## The rules, for arbitrary values -/

section Rules

variable {env : Env}

/-- `Step_pure/local.tee`: `val (LOCAL.TEE x) ~> val val (LOCAL.SET x)`. -/
theorem spure_localTee (h : HasRuleAt env "Step_pure" "%~>%" 30 Equiv.Execution.localTeeRule)
    {V X : Value} (hv : TypedV env valT V) (hx : TypedV env idxT X) :
    SPure env [V, .case "LOCAL.TEE" X] [V, V, .case "LOCAL.SET" X] := by
  let ρ := VarEnv.empty.bindVals [("val", V), ("x", X)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fv : ρ.findVal? "val" = some V := rfl
  have fx : ρ.findVal? "x" = some X := rfl
  have ev : EvalExp env ρ (.subE (.varE "val") (.varT "val" []) (.varT "instr" [])) V :=
    evalExp_subE_iff.2 (evalExp_var fv)
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fv (hv ρ hρ) (QuantsOk.cons fx (hx ρ hρ) QuantsOk.nil))
    (evalExp_tup2
      (evalExp_listE_iff.2 ⟨_, evalExps_cons ev (evalExps_cons (evalExp_case (evalExp_var fx))
        evalExps_nil), rfl⟩)
      (evalExp_listE_iff.2 ⟨_, evalExps_cons ev (evalExps_cons ev
        (evalExps_cons (evalExp_case (evalExp_var fx)) evalExps_nil)), rfl⟩))
    (fun _ h => by cases h)

/-- `Step_read/local.get`: `z; (LOCAL.GET x) ~> val` when `$local(z, x) = ?(val)`. -/
theorem sread_localGet (h : HasRuleAt env "Step_read" "%~>%" 23 Equiv.ExecRead.localGetRule)
    (D : StateDefs env) {S F V L : Value} {n : Nat} (hz : TypedV env stateT (stV S F))
    (hx : TypedV env idxT (idxV n)) (hv : TypedV env valT V)
    (hL : F.field? "LOCALS" = some L) (hr : L.idx? n = some (.opt (some V))) :
    SRead env (cfgV (stV S F) [.case "LOCAL.GET" (idxV n)]) [V] := by
  let ρ := VarEnv.empty.bindVals [("z", stV S F), ("x", idxV n), ("val", V)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stV S F) := rfl
  have fx : ρ.findVal? "x" = some (idxV n) := rfl
  have fv : ρ.findVal? "val" = some V := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fx (hx ρ hρ)
      (QuantsOk.cons fv (hv ρ hρ) QuantsOk.nil)))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_var fx)))))
      (evalExp_list1 (evalExp_subE_iff.2 (evalExp_var fv))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _,
      evalExp_local D rfl (evalExp_var fz) (evalExp_var fx) hL hr,
      evalExp_optE_some_iff.2 ⟨V, evalExp_var fv, rfl⟩, cmpValues_eq_true_iff.2 rfl⟩)))

/-- `Step_read/global.get`: `z; (GLOBAL.GET x) ~> val` when `$global(z, x).VALUE = val`. -/
theorem sread_globalGet (h : HasRuleAt env "Step_read" "%~>%" 24 Equiv.ExecRead.globalGetRule)
    (D : StateDefs env) {S F M g V : Value} {Ls As : List Value} {n a : Nat}
    (hz : TypedV env stateT (stV S F)) (hx : TypedV env idxT (idxV n)) (hv : TypedV env valT V)
    (hS : S.field? "GLOBALS" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "GLOBALS" = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (hg : Ls[a]? = some g) (hV : g.field? "VALUE" = some V) :
    SRead env (cfgV (stV S F) [.case "GLOBAL.GET" (idxV n)]) [V] := by
  let ρ := VarEnv.empty.bindVals [("z", stV S F), ("x", idxV n), ("val", V)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stV S F) := rfl
  have fx : ρ.findVal? "x" = some (idxV n) := rfl
  have fv : ρ.findVal? "val" = some V := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fx (hx ρ hρ)
      (QuantsOk.cons fv (hv ρ hρ) QuantsOk.nil)))
    (evalExp_tup2 (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_list1 (evalExp_case (evalExp_var fx)))))
      (evalExp_list1 (evalExp_subE_iff.2 (evalExp_var fv))))
    (prems_one (.ifPr (evalExp_cmpE_iff.2 ⟨_, _,
      evalExp_dotE_iff.2 ⟨g, evalExp_global D rfl (evalExp_var fz) (evalExp_var fx) hS hM hA ha hg,
        hV⟩,
      evalExp_var fv, cmpValues_eq_true_iff.2 rfl⟩)))

/-- `Step/local.set`: `z; val (LOCAL.SET x) ~> $with_local(z, x, val); ε`. -/
theorem sstep_localSet (h : HasRuleAt env "Step" "%~>%" 11 Equiv.ExecStepRules.localSetRule)
    (D : StateDefs env) {S F F' V : Value} {L : List Value} {n : Nat}
    (hz : TypedV env stateT (stV S F)) (hx : TypedV env idxT (idxV n)) (hv : TypedV env valT V)
    (hL : F.field? "LOCALS" = some (.list L)) (hn : n < L.length)
    (hF : F.setField "LOCALS" (.list (L.set n (.opt (some V)))) = some F') :
    SStep env (cfgV (stV S F) [V, .case "LOCAL.SET" (idxV n)]) (cfgV (stV S F') []) := by
  let ρ := VarEnv.empty.bindVals [("z", stV S F), ("val", V), ("x", idxV n)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stV S F) := rfl
  have fx : ρ.findVal? "x" = some (idxV n) := rfl
  have fv : ρ.findVal? "val" = some V := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fv (hv ρ hρ)
      (QuantsOk.cons fx (hx ρ hρ) QuantsOk.nil)))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_subE_iff.2 (evalExp_var fv))
          (evalExps_cons (evalExp_case (evalExp_var fx)) evalExps_nil), rfl⟩)))
      (evalExp_case (evalExp_tup2
        (evalExp_withLocal D rfl (evalExp_var fz) (evalExp_var fx) (evalExp_var fv) hL hn hF)
        (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩))))
    (fun _ h => by cases h)

/-- `Step/global.set`: `z; val (GLOBAL.SET x) ~> $with_global(z, x, val); ε`. -/
theorem sstep_globalSet (h : HasRuleAt env "Step" "%~>%" 12 Equiv.ExecStepRules.globalSetRule)
    (D : StateDefs env) {S S' F M g g' V : Value} {Ls As : List Value} {n a : Nat}
    (hz : TypedV env stateT (stV S F)) (hx : TypedV env idxT (idxV n)) (hv : TypedV env valT V)
    (hS : S.field? "GLOBALS" = some (.list Ls)) (hM : F.field? "MODULE" = some M)
    (hA : M.field? "GLOBALS" = some (.list As)) (ha : As[n]? = some (.num (.natN a)))
    (hg : Ls[a]? = some g) (hg' : g.setField "VALUE" V = some g')
    (hS' : S.setField "GLOBALS" (.list (Ls.set a g')) = some S') :
    SStep env (cfgV (stV S F) [V, .case "GLOBAL.SET" (idxV n)]) (cfgV (stV S' F) []) := by
  let ρ := VarEnv.empty.bindVals [("z", stV S F), ("val", V), ("x", idxV n)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some (stV S F) := rfl
  have fx : ρ.findVal? "x" = some (idxV n) := rfl
  have fv : ρ.findVal? "val" = some V := rfl
  exact dderives_of_ruleAt h _
    (QuantsOk.cons fz (hz ρ hρ) (QuantsOk.cons fv (hv ρ hρ)
      (QuantsOk.cons fx (hx ρ hρ) QuantsOk.nil)))
    (evalExp_tup2
      (evalExp_case (evalExp_tup2 (evalExp_var fz)
        (evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_subE_iff.2 (evalExp_var fv))
          (evalExps_cons (evalExp_case (evalExp_var fx)) evalExps_nil), rfl⟩)))
      (evalExp_case (evalExp_tup2
        (evalExp_withGlobal D rfl (evalExp_var fz) (evalExp_var fx) (evalExp_var fv) hS hM hA ha
          hg hg' hS')
        (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩))))
    (fun _ h => by cases h)

end Rules

/-! ## The `Forward.variable_` obligation -/

section Forward

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- `Store.global?` unfolded. -/
theorem Store.global?_eq_some {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat}
    {g : GlobalInst} (h : s.global? f x = some (a, g)) :
    f.module.globals[x.toNat]? = some a ∧ s.globals[a]? = some g := by
  simp only [Store.global?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨a', ha, g', hg, rfl, rfl⟩ := h
  exact ⟨ha, hg⟩

/-- The image of an index. -/
theorem toValue_idx {k : IndexKind} (x : Idx k) : Encode.toValue x = idxV x.toNat := rfl

variable (B : Builtins) {hn : H → String} (T : TypingFacts (simEnv B) hn)
  (St : StateTyping (simEnv B))
include T St

/-- `VariableStep.localGet`, forward. -/
theorem fwd_localGet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (h : f.local? x = some (some v)) :
    FwdP (simEnv B) hn ⟨s, f, [.plain (.localGet x)]⟩ ⟨s, f, [v.toAdmin]⟩ := by
  intro hc hc'
  have hv : TypedV (simEnv B) valT (valV v) := typedV_val_of_mem T hc' (by simp)
  have hcode' : TypedV (simEnv B) instrsT (.list [valV v]) := by
    simpa only [adminsToV_cons, adminsToV_nil, adminToV_toAdmin] using typedV_code T hc'
  have hr : (Value.list (f.locals.map fun o => .opt (o.map valV))).idx? x.toNat =
      some (.opt (some (valV v))) := by
    simp only [Frame.local?] at h
    simp [Value.idx?, h]
  show SStep _ (cfgV _ [_]) (cfgV _ [adminToV v.toAdmin])
  rw [adminToV_toAdmin]
  exact sstep_read (hasStepRules_simEnv B).read (typedV_state T hc) (typedV_code T hc) hcode'
    (sread_localGet (hasReadRules_simEnv B).localGet (stateDefs_simEnv B) (typedV_state T hc)
      (St.idx _ x.value.isLt) hv (frameV_LOCALS f) hr)

/-- `VariableStep.localSet`, forward. -/
theorem fwd_localSet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hx : x.toNat < f.locals.length) :
    FwdP (simEnv B) hn ⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩ ⟨s, f.setLocal x v, []⟩ := by
  intro hc _
  have hv : TypedV (simEnv B) valT (valV v) := typedV_val_of_mem T hc (by simp)
  show SStep _ (cfgV _ [adminToV v.toAdmin, _]) (cfgV _ [])
  rw [adminToV_toAdmin]
  exact sstep_localSet (hasStepRules_simEnv B).localSet (stateDefs_simEnv B) (typedV_state T hc)
    (St.idx _ x.value.isLt) hv (frameV_LOCALS f) (by simpa using hx) (frameV_setLocal f x v)

/-- `VariableStep.localTee`, forward. -/
theorem fwd_localTee {s : Store H} {f : Frame} {x : LocalIdx} {v : Val} :
    FwdP (simEnv B) hn ⟨s, f, [v.toAdmin, .plain (.localTee x)]⟩
      ⟨s, f, [v.toAdmin, v.toAdmin, .plain (.localSet x)]⟩ := by
  intro hc hc'
  have hv : TypedV (simEnv B) valT (valV v) := typedV_val_of_mem T hc (by simp)
  have hcode : TypedV (simEnv B) instrsT (.list [valV v, adminToV (.plain (.localTee x))]) := by
    simpa only [adminsToV_cons, adminsToV_nil, adminToV_toAdmin] using typedV_code T hc
  have hcode' : TypedV (simEnv B) instrsT
      (.list [valV v, valV v, adminToV (.plain (.localSet x))]) := by
    simpa only [adminsToV_cons, adminsToV_nil, adminToV_toAdmin] using typedV_code T hc'
  show SStep _ (cfgV _ [adminToV v.toAdmin, _]) (cfgV _ [adminToV v.toAdmin, adminToV v.toAdmin, _])
  rw [adminToV_toAdmin]
  exact sstep_pure (hasStepRules_simEnv B).pure (typedV_state T hc) hcode hcode'
    (spure_localTee (hasPureRules_simEnv B).localTee hv (St.idx _ x.value.isLt))

/-- `VariableStep.globalGet`, forward. -/
theorem fwd_globalGet {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (h : s.global? f x = some (a, g)) :
    FwdP (simEnv B) hn ⟨s, f, [.plain (.globalGet x)]⟩ ⟨s, f, [g.value.toAdmin]⟩ := by
  intro hc hc'
  obtain ⟨ha, hg⟩ := Store.global?_eq_some h
  have hv : TypedV (simEnv B) valT (valV g.value) := typedV_val_of_mem T hc' (by simp)
  have hcode' : TypedV (simEnv B) instrsT (.list [valV g.value]) := by
    simpa only [adminsToV_cons, adminsToV_nil, adminToV_toAdmin] using typedV_code T hc'
  show SStep _ (cfgV _ [_]) (cfgV _ [adminToV g.value.toAdmin])
  rw [adminToV_toAdmin]
  exact sstep_read (hasStepRules_simEnv B).read (typedV_state T hc) (typedV_code T hc) hcode'
    (sread_globalGet (hasReadRules_simEnv B).globalGet (stateDefs_simEnv B) (typedV_state T hc)
      (St.idx _ x.value.isLt) hv (storeV_GLOBALS hn s) (frameV_MODULE f) (moduleV_GLOBALS _)
      (getElem?_map_natN ha) (by simp [hg]) (globalInstV_VALUE g))

/-- `VariableStep.globalSet`, forward. -/
theorem fwd_globalSet {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    {v : Val} (h : s.global? f x = some (a, g)) :
    FwdP (simEnv B) hn ⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩ ⟨s.setGlobal a v, f, []⟩ := by
  intro hc _
  obtain ⟨ha, hg⟩ := Store.global?_eq_some h
  have hv : TypedV (simEnv B) valT (valV v) := typedV_val_of_mem T hc (by simp)
  show SStep _ (cfgV _ [adminToV v.toAdmin, _]) (cfgV _ [])
  rw [adminToV_toAdmin]
  exact sstep_globalSet (hasStepRules_simEnv B).globalSet (stateDefs_simEnv B) (typedV_state T hc)
    (St.idx _ x.value.isLt) hv (storeV_GLOBALS hn s) (frameV_MODULE f) (moduleV_GLOBALS _)
    (getElem?_map_natN ha) (by simp [hg]) (globalInstV_setValue g v) (storeV_setGlobal hn s hg v)

/-- **`Forward.variable_` at `simEnv B`.** Every `local.get`, `local.set`, `local.tee`,
`global.get` and `global.set` step of Core between typed configurations is a SpecTec step. -/
theorem fwd_variable_ : ∀ {c c' : Config H} (_ : VariableStep c c'), FwdP (simEnv B) hn c c'
  | _, _, .localGet h => fwd_localGet B T St h
  | _, _, .localSet hx => fwd_localSet B T St hx
  | _, _, .localTee => fwd_localTee B T St
  | _, _, .globalGet h => fwd_globalGet B T St h
  | _, _, .globalSet h => fwd_globalSet B T St h

end Forward

end Silmaril.Wasm.SpecTec.Sim.State
