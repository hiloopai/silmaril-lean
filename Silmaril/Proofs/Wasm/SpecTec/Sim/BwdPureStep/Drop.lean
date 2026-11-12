module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdPureStep.Variable

/-!
# Track bwd-pure-step: `elem.drop` and `data.drop`, backward (`Step` 17, 28)

`$with_elem(z, x, ε)` and `$with_data(z, x, ε)` update the segment the module lists at `x`,
through `$fof(z).MODULE.F[x!%.0]`, which fails unless the module lists `x` and the store holds
the address (`modAddr_inv`). The forward evaluations (`State.evalExp_withElem`,
`State.evalExp_withData`) then name the successor. Needs `B` not to interpret `$with_elem`,
`$with_data` (true of `Prims.builtins`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdPureStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

theorem head_elemDrop {a : Admin} (h : Typing.adminHead a = "ELEM.DROP") :
    ∃ x, a = .plain (.elemDrop x) := by
  revert h
  admin_head_inv

theorem head_dataDrop {a : Admin} (h : Typing.adminHead a = "DATA.DROP") :
    ∃ x, a = .plain (.dataDrop x) := by
  revert h
  admin_head_inv

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
variable (B : Builtins)

/-- **An updater `$sof(z)[.F[$fof(z).MODULE.F[x!%.0]].G = r*]; $fof(z)`, read back**: the
module lists `x` and the store holds the address. -/
theorem segUpd_addr {ρ₀ : VarEnv} {F G : AtomS} {er : Exp} {s : Store H} {f : Frame} {k : Nat}
    {As : List Nat} {Ls : List Value} {W : Value}
    (fz : ρ₀.findVal? "z" = some (stateV hn s f))
    (fx : ρ₀.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])))
    (hd : ρ₀.findDef? "fof" = none) (hd' : ρ₀.findDef? "sof" = none)
    (hM : (moduleInstToValue CT f.module).field? F = some (.list (As.map fun a => .num (.natN a))))
    (hS : (storeV hn s).field? F = some (.list Ls))
    (h : EvalExp (simEnv B) ρ₀ (.caseE "%;%" (.tupE [.updE (.callE "sof" [.expA (.varE "z")])
      (.dotP (.idxP (.dotP .rootP F) (State.modAddr F)) G) er,
      .callE "fof" [.expA (.varE "z")]])) W) :
    ∃ a e, As[k]? = some a ∧ Ls[a]? = some e := by
  have D := State.stateDefs_simEnv B
  obtain ⟨W₁, W₂, h₁, -, -⟩ := body_pair h
  obtain ⟨S₀, O, hS₀, -, hps⟩ := evalExp_updE_iff.1 h₁
  have eS : S₀ = storeV hn s := EvalExp.unique hS₀ (State.evalExp_sof D hd' (evalExp_var fz))
  obtain ⟨E, -, hG, -, -⟩ := pathSet_dot_inv (eS ▸ hps)
  obtain ⟨iv, i, hiv, hi, hLa⟩ := storeIdx_inv hS hG
  obtain ⟨a, ha, rfl⟩ := moduleIdx_inv D fz fx hd hM hiv
  have hia : i = a := by simpa [Value.asNat?] using hi.symm
  exact ⟨a, E, ha, hia ▸ hLa⟩

/-- The arguments of `$with_elem(z, x, ε)`/`$with_data(z, x, ε)`, matched. -/
theorem matchArgs_zxNil {env : Env} {Z X : Value} {y ys : IL.Id} (hy : y ≠ "_")
    (hy' : ((VarEnv.empty.bindVal "z" Z).bindVal "x" X).findVal? y = none)
    (hys : ((VarEnv.empty.bindVal "z" Z).bindVal "x" X).findVal? ys = none) :
    MatchArgs env VarEnv.empty [.expA (.varE "z"), .expA (.varE "x"), .expA (State.iterVar y ys)]
      [.val Z, .val X, .val (.list [])]
      (((VarEnv.empty.bindVal "z" Z).bindVal "x" X).bindVal ys (.list [])) :=
  matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
    (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA
      (State.matchExp_iterVar hy' hy hys)) matchArgs_nil))

/-- The evaluated arguments `z, x, ε`. -/
theorem evalArgs_zxNil {env : Env} {ρ : VarEnv} {Z X : Value} (fz : ρ.findVal? "z" = some Z)
    (fx : ρ.findVal? "x" = some X) :
    EvalArgs env ρ [.expA (.varE "z"), .expA (.varE "x"), .expA (.listE [])]
      [.val Z, .val X, .val (.list [])] :=
  evalArgs_cons (evalExp_var fz) (evalArgs_cons (evalExp_var fx)
    (evalArgs_cons (by beval) evalArgs_nil))

/-- `$with_elem(z, x, ε)` at a segment in range, evaluated forward. -/
theorem withElem_eval {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {k a : Nat}
    {ei : ElemInst} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])))
    (ha : f.module.elems[k]? = some a) (hei : s.elems[a]? = some ei) :
    EvalExp (simEnv B) ρ (.callE "with_elem" [.expA (.varE "z"), .expA (.varE "x"),
      .expA (.listE [])]) (stateV hn (s.setElem a []) f) :=
  State.evalExp_withElem (State.stateDefs_simEnv B) (Prims.findDef_none_of_valsOnly hρ _)
    (evalExp_var fz) (evalExp_var fx) (by beval) (State.storeV_ELEMS hn s) (State.frameV_MODULE f)
    (State.moduleV_ELEMS _) (State.getElem?_map_natN ha) (by simp [hei])
    (State.elemInstV_drop ei) (State.storeV_setElem hn s hei)

/-- `$with_data(z, x, ε)` at a segment in range, evaluated forward. -/
theorem withData_eval {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {k a : Nat}
    {di : DataInst} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])))
    (ha : f.module.datas[k]? = some a) (hdi : s.datas[a]? = some di) :
    EvalExp (simEnv B) ρ (.callE "with_data" [.expA (.varE "z"), .expA (.varE "x"),
      .expA (.listE [])]) (stateV hn (s.setData a ByteArray.empty) f) :=
  State.evalExp_withData (State.stateDefs_simEnv B) (Prims.findDef_none_of_valsOnly hρ _)
    (evalExp_var fz) (evalExp_var fx) (by beval) (State.storeV_DATAS hn s) (State.frameV_MODULE f)
    (State.moduleV_DATAS _) (State.getElem?_map_natN ha) (by simp [hdi])
    (State.dataInstV_drop di) (State.storeV_setData hn s hdi)

variable {w : Value}

/-- `Backward.step 17` (`elem.drop`). -/
theorem bwd_elemDrop
    (hb : ∀ Z X R : Value, B.call "with_elem" [.val Z, .val X, .val R] = none) {c : Config H}
    (hf : Fires (simEnv B) "Step" 17 (.tuple [configV hn c, w])) : BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, -, fz, hes, hr, -⟩ := fires_step (hasStepRules_simEnv B).elemDrop hf
  obtain ⟨a₁, rfl, h₁⟩ := codes_one hes
  obtain ⟨y, rfl⟩ := head_elemDrop (head_of_caseE h₁)
  have fx := idx_of_var h₁ rfl
  obtain ⟨W, hW, rfl⟩ := rhs_nil hr
  have hρ := valsOnly_bindVals σ
  obtain ⟨a, ei, ha, hei⟩ := segUpd_addr B rfl rfl rfl rfl (State.moduleV_ELEMS _)
    (State.storeV_ELEMS hn s) (evalExp_call1_inv (State.stateDefs_simEnv B).withElem
      (Prims.findDef_none_of_valsOnly hρ _) (hb _ _ _) (evalArgs_zxNil fz fx)
      (matchArgs_zxNil (by decide) rfl rfl) hW)
  obtain ⟨ei, hei', -⟩ := Option.map_eq_some_iff.1 (List.getElem?_map ▸ hei)
  have e₁ := EvalExp.unique hW (withElem_eval B hρ fz fx ha hei')
  have hel : s.elem? f y = some (a, ei) := by simp [Store.elem?, ha, hei']
  exact ⟨⟨s.setElem a [], f, []⟩, by rw [e₁]; rfl, .table (.elemDrop hel)⟩

/-- `Backward.step 28` (`data.drop`). -/
theorem bwd_dataDrop
    (hb : ∀ Z X R : Value, B.call "with_data" [.val Z, .val X, .val R] = none) {c : Config H}
    (hf : Fires (simEnv B) "Step" 28 (.tuple [configV hn c, w])) : BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, -, fz, hes, hr, -⟩ := fires_step (hasStepRules_simEnv B).dataDrop hf
  obtain ⟨a₁, rfl, h₁⟩ := codes_one hes
  obtain ⟨y, rfl⟩ := head_dataDrop (head_of_caseE h₁)
  have fx := idx_of_var h₁ rfl
  obtain ⟨W, hW, rfl⟩ := rhs_nil hr
  have hρ := valsOnly_bindVals σ
  obtain ⟨a, di, ha, hdi⟩ := segUpd_addr B rfl rfl rfl rfl (State.moduleV_DATAS _)
    (State.storeV_DATAS hn s) (evalExp_call1_inv (State.stateDefs_simEnv B).withData
      (Prims.findDef_none_of_valsOnly hρ _) (hb _ _ _) (evalArgs_zxNil fz fx)
      (matchArgs_zxNil (by decide) rfl rfl) hW)
  obtain ⟨di, hdi', -⟩ := Option.map_eq_some_iff.1 (List.getElem?_map ▸ hdi)
  have e₁ := EvalExp.unique hW (withData_eval B hρ fz fx ha hdi')
  have hda : s.data? f y = some (a, di) := by simp [Store.data?, ha, hdi']
  exact ⟨⟨s.setData a ByteArray.empty, f, []⟩, by rw [e₁]; rfl, .memory (.dataDrop hda)⟩

end Silmaril.Wasm.SpecTec.Sim.BwdPureStep
