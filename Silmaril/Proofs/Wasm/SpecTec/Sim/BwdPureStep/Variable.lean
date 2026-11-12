module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdPureStep.Call
public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdPureStep.Refs

/-!
# Track bwd-pure-step: `local.set`, backward (`Step` 11)

`$with_local(z, x, v)` updates `LOCALS[x]` through `Value.setIdx`, which fails out of range; so
a firing `local.set` rule has `x` in range (`withLocal_bound`, through `evalExp_call1_inv` and
the path inversions), and the forward evaluation (`State.evalExp_withLocal`) then names the
successor. Needs `B` not to interpret `$with_local` (true of `Prims.builtins`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdPureStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge (moduleInstToValue)

theorem head_localSet {a : Admin} (h : Typing.adminHead a = "LOCAL.SET") :
    ∃ x, a = .plain (.localSet x) := by
  revert h
  admin_head_inv

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
variable (B : Builtins)

/-- Writing `LOCALS[x]` into an encoded frame succeeds only for `x` in range. -/
theorem localsSet_bound {env : Env} {ρ₀ : VarEnv} {f : Frame} {k : Nat} {O R : Value}
    (fx : ρ₀.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])))
    (h : PathSet env ρ₀ (frameV f) (.idxP (.dotP .rootP "LOCALS") State.idxPayload) O R) :
    k < f.locals.length := by
  obtain ⟨L, iv, i, L', hL, hiv, hi, hs, -⟩ := pathSet_idx_inv h
  obtain ⟨u₀, h₀, hu₀⟩ := pathGet_dot_inv hL
  have e₀ : u₀ = frameV f := pathGet_root_inv h₀
  have eL : L = .list (f.locals.map fun o => .opt (o.map valV)) :=
    Option.some.inj ((e₀ ▸ hu₀).symm.trans (State.frameV_LOCALS f))
  have eiv : iv = .num (.natN k) := EvalExp.unique hiv (State.evalExp_idxPayload fx)
  have ei : i = k := by simpa [eiv, Value.asNat?] using hi.symm
  have hs' : (Value.list (f.locals.map fun o => .opt (o.map valV))).setIdx k O = some L' :=
    ei ▸ eL ▸ hs
  by_contra hk
  simp [Value.setIdx, hk] at hs'

/-- A value of `$with_local((s; f), x, v)` has `x` in range of `f`'s locals. -/
theorem withLocal_bound
    (hb : ∀ Z X V : Value, B.call "with_local" [.val Z, .val X, .val V] = none) {ρ : VarEnv}
    (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {k : Nat} {V W : Value}
    (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])))
    (fv : ρ.findVal? "val" = some V)
    (h : EvalExp (simEnv B) ρ (.callE "with_local"
      [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE "val")]) W) :
    k < f.locals.length := by
  have hbody := evalExp_call1_inv (State.stateDefs_simEnv B).withLocal
    (Prims.findDef_none_of_valsOnly hρ _) (hb _ _ _)
    (evalArgs_cons (evalExp_var fz) (evalArgs_cons (evalExp_var fx)
      (evalArgs_cons (evalExp_var fv) evalArgs_nil))) State.matchArgs_zxvPat h
  obtain ⟨W₁, W₂, -, h₂, -⟩ := body_pair hbody
  obtain ⟨F₀, O, hF, -, hps⟩ := evalExp_updE_iff.1 h₂
  have eF : F₀ = frameV f :=
    EvalExp.unique hF (State.evalExp_fof (State.stateDefs_simEnv B) rfl (evalExp_var rfl))
  exact localsSet_bound rfl (eF ▸ hps)

variable {w : Value}

/-- `Backward.step 11` (`local.set`). -/
theorem bwd_localSet
    (hb : ∀ Z X V : Value, B.call "with_local" [.val Z, .val X, .val V] = none) {c : Config H}
    (hf : Fires (simEnv B) "Step" 11 (.tuple [configV hn c, w])) : BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, -⟩ := fires_step (hasStepRules_simEnv B).localSet hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes_two hes
  obtain ⟨v, rfl, fv⟩ := val_of_var hq (.tail _ (.head _)) h₁
  obtain ⟨x, rfl⟩ := head_localSet (head_of_caseE h₂)
  have fx := idx_of_var h₂ rfl
  obtain ⟨W, hW, rfl⟩ := rhs_nil hr
  have hx : x.toNat < f.locals.length := withLocal_bound B hb (valsOnly_bindVals σ) fz fx fv hW
  have e₁ : W = stateV hn s (f.setLocal x v) :=
    EvalExp.unique hW (State.evalExp_withLocal (State.stateDefs_simEnv B)
      (Prims.findDef_none_of_valsOnly (valsOnly_bindVals σ) _) (evalExp_var fz) (evalExp_var fx)
      (evalExp_var fv) (State.frameV_LOCALS f) (by simpa using hx) (State.frameV_setLocal f x v))
  exact ⟨⟨s, f.setLocal x v, []⟩, by rw [e₁]; rfl, .variable (.localSet hx)⟩

theorem head_globalSet {a : Admin} (h : Typing.adminHead a = "GLOBAL.SET") :
    ∃ x, a = .plain (.globalSet x) := by
  revert h
  admin_head_inv

/-- Reading entry `ie` of the store field `F`. -/
theorem storeIdx_inv {env : Env} {ρ₀ : VarEnv} {S G : Value} {F : AtomS} {ie : Exp}
    {Ls : List Value} (hS : S.field? F = some (.list Ls))
    (h : PathGet env ρ₀ S (.idxP (.dotP .rootP F) ie) G) :
    ∃ iv i, EvalExp env ρ₀ ie iv ∧ iv.asNat? = some i ∧ Ls[i]? = some G := by
  obtain ⟨L, iv, i, hL, hiv, hi, hLi⟩ := pathGet_idx_inv h
  obtain ⟨u₀, h₀, hu₀⟩ := pathGet_dot_inv hL
  have eL : L = .list Ls := Option.some.inj (((pathGet_root_inv h₀) ▸ hu₀).symm.trans hS)
  exact ⟨iv, i, hiv, hi, by simpa [eL, Value.idx?] using hLi⟩

/-- `$fof(z).MODULE.F[x!%.0]` resolves `x` in the module's field `F`. -/
theorem moduleIdx_inv {env : Env} {ρ₀ : VarEnv} (D : State.StateDefs env) {s : Store H}
    {f : Frame} {k : Nat} {iv : Value} {F : AtomS} {As : List Nat}
    (fz : ρ₀.findVal? "z" = some (stateV hn s f))
    (fx : ρ₀.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])))
    (hd : ρ₀.findDef? "fof" = none)
    (hM : (moduleInstToValue CT f.module).field? F = some (.list (As.map fun a => .num (.natN a))))
    (h : EvalExp env ρ₀ (.idxE (.dotE (.dotE (.callE "fof" [.expA (.varE "z")]) "MODULE")
      F) State.idxPayload) iv) :
    ∃ a, As[k]? = some a ∧ iv = .num (.natN a) := by
  obtain ⟨Bs, j, hBs, hj, hBj⟩ := evalExp_idxE_iff.1 h
  have eBs : Bs = .list (As.map fun a => .num (.natN a)) :=
    EvalExp.unique hBs (evalExp_dotE_iff.2 ⟨_, evalExp_dotE_iff.2 ⟨_,
      State.evalExp_fof D hd (evalExp_var fz), State.frameV_MODULE f⟩, hM⟩)
  have ej : Value.num (.natN j) = .num (.natN k) := EvalExp.unique hj (State.evalExp_idxPayload fx)
  have ej' : j = k := by simpa using ej
  have hAk : (As.map fun a => Value.num (.natN a))[k]? = some iv := by
    rw [eBs, ej'] at hBj
    exact hBj
  rw [List.getElem?_map] at hAk
  obtain ⟨a, ha, he⟩ := Option.map_eq_some_iff.1 hAk
  exact ⟨a, ha, he.symm⟩

/-- A value of `$with_global((s; f), x, v)` resolves `x` to a global of the store. -/
theorem withGlobal_addr
    (hb : ∀ Z X V : Value, B.call "with_global" [.val Z, .val X, .val V] = none) {ρ : VarEnv}
    (hρ : ValsOnly ρ) {s : Store H} {f : Frame} {k : Nat} {V W : Value}
    (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fx : ρ.findVal? "x" = some (.case "%" (.tuple [.num (.natN k)])))
    (fv : ρ.findVal? "val" = some V)
    (h : EvalExp (simEnv B) ρ (.callE "with_global"
      [.expA (.varE "z"), .expA (.varE "x"), .expA (.varE "val")]) W) :
    ∃ a g, f.module.globals[k]? = some a ∧ s.globals[a]? = some g := by
  have D := State.stateDefs_simEnv B
  have hbody := evalExp_call1_inv D.withGlobal (Prims.findDef_none_of_valsOnly hρ _) (hb _ _ _)
    (evalArgs_cons (evalExp_var fz) (evalArgs_cons (evalExp_var fx)
      (evalArgs_cons (evalExp_var fv) evalArgs_nil))) State.matchArgs_zxvPat h
  obtain ⟨W₁, W₂, h₁, -, -⟩ := body_pair hbody
  obtain ⟨S₀, O, hS, -, hps⟩ := evalExp_updE_iff.1 h₁
  have eS : S₀ = storeV hn s := EvalExp.unique hS (State.evalExp_sof D rfl (evalExp_var rfl))
  obtain ⟨G, -, hG, -, -⟩ := pathSet_dot_inv (eS ▸ hps)
  obtain ⟨iv, i, hiv, hi, hLa⟩ := storeIdx_inv (State.storeV_GLOBALS hn s) hG
  obtain ⟨a, ha, rfl⟩ := moduleIdx_inv D rfl rfl rfl (State.moduleV_GLOBALS _) hiv
  have hia : i = a := by simpa [Value.asNat?] using hi.symm
  rw [hia, List.getElem?_map] at hLa
  obtain ⟨g, hg, -⟩ := Option.map_eq_some_iff.1 hLa
  exact ⟨a, g, ha, hg⟩

/-- `Backward.step 12` (`global.set`). -/
theorem bwd_globalSet
    (hb : ∀ Z X V : Value, B.call "with_global" [.val Z, .val X, .val V] = none) {c : Config H}
    (hf : Fires (simEnv B) "Step" 12 (.tuple [configV hn c, w])) : BwdP hn P host c w := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨σ, hq, fz, hes, hr, -⟩ := fires_step (hasStepRules_simEnv B).globalSet hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes_two hes
  obtain ⟨v, rfl, fv⟩ := val_of_var hq (.tail _ (.head _)) h₁
  obtain ⟨x, rfl⟩ := head_globalSet (head_of_caseE h₂)
  have fx := idx_of_var h₂ rfl
  obtain ⟨W, hW, rfl⟩ := rhs_nil hr
  obtain ⟨a, g, ha, hg⟩ := withGlobal_addr B hb (valsOnly_bindVals σ) fz fx fv hW
  have e₁ : W = stateV hn (s.setGlobal a v) f :=
    EvalExp.unique hW (State.evalExp_withGlobal (State.stateDefs_simEnv B)
      (Prims.findDef_none_of_valsOnly (valsOnly_bindVals σ) _) (evalExp_var fz) (evalExp_var fx)
      (evalExp_var fv) (State.storeV_GLOBALS hn s) (State.frameV_MODULE f)
      (State.moduleV_GLOBALS _) (State.getElem?_map_natN ha) (by simp [hg])
      (State.globalInstV_setValue g v) (State.storeV_setGlobal hn s hg v))
  have hgl : s.global? f x = some (a, g) := by simp [Store.global?, ha, hg]
  exact ⟨⟨s.setGlobal a v, f, []⟩, by rw [e₁]; rfl, .variable (.globalSet hgl)⟩

end Silmaril.Wasm.SpecTec.Sim.BwdPureStep
