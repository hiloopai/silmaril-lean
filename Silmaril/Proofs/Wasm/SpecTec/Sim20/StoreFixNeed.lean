module

public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# Why the `STORE` erratum is needed: a storing function makes the corrected script stuck

Round 3 recorded, as an observation, that without an erratum binding `Inn` in `STORE`'s premise
no storing program is forward-simulated by the corrected 2.0 script `simEnv20S`. This module
proves it, and more: a storing function anywhere in the store blocks **every** step of
`simEnv20S`, whatever the code.

* `not_typedV_instrStore20`: no V2 store instruction (`intStore`, `floatStore`) has an IL type
  `instr` (from `not_typedV_store20` and `typedV_plain20_iff`).
* `not_typedV_store_storeFn20`: a store holding a Wasm function whose body has a store
  instruction at its top level (`StoreFn20`) has no IL type `store`, so the state has no IL type
  `state` (`not_typedV_state_storeFn20`). The same holds in `simEnv20S` at every scope that
  binds values only (`not_hasTyp_store20S`, `not_hasTyp_state20S`), since `simEnv20S` only
  changes the relation table.
* `stepRules20S_state` (kernel, `decide +kernel`): every one of the 23 rules of the corrected
  `Step` has a conclusion without an empty-domain option iteration, whose left-hand side is
  `z; …` with a quantifier `z : state`, or (`ctxt-frame`) `(s; f); …` with `s : store`.
* **`stuck_storeFn20S`**: so at every builtins, from the image of any configuration whose store
  has a storing function, `simEnv20S` has no step at all.
* `storeFnCfg`: such a configuration (one function whose body is `i32.store`, code `nop`).

The 1.0 consequence (`Fwd20` fails on every set of configurations that contains a storing one
that V2 can step) is in `Sim10/Route10Store`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim20.Whole
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly cfgV stateT storeT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB DDerivesB conclAlts hasOptNil)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S)
open Silmaril.Wasm.SpecTec.Sim20.RelFree (simEnv20S_eq defsGood_simEnv20 typsGood_simEnv20
  hasTyp_withRels_iff goodEvs_of_all)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Store instructions have no IL type -/

/-- A V2 store instruction (`Step` 11–14 of the script). -/
inductive IsStoreI : V2.Instr → Prop where
  | int (t : IntType) (p : Option PackSize) (ao : V2.MemArg) : IsStoreI (.intStore t p ao)
  | float (t : FloatType) (ao : V2.MemArg) : IsStoreI (.floatStore t ao)

/-- **No store instruction is a typed `instr`**, at every builtins. -/
theorem not_typedV_instrStore20 {i : V2.Instr} (hi : IsStoreI i) :
    ¬ TypedV (simEnv20 B) (.varT "instr" []) (instrToV i) := by
  intro h
  have ha := (typedV_plain20_iff i).2 h
  cases hi with
  | int t p ao => exact not_typedV_intStore20 t p ao ha
  | float t ao => exact not_typedV_floatStore20 t ao ha

/-- **A storing function**: a Wasm function of the store whose body has a store instruction at
its top level. -/
def StoreFn20 (s : Store H) : Prop :=
  ∃ a fi fn i, s.funcInst? a = some fi ∧ fi.code = .wasm fn ∧ i ∈ fn.body ∧ IsStoreI i

/-- **A store with a storing function has no IL type `store`.** -/
theorem not_typedV_store_storeFn20 {s : Store H} (hs : StoreFn20 s) :
    ¬ TypedV (simEnv20 B) storeT (storeV hn s) := by
  intro h
  obtain ⟨a, fi, fn, i, hf, hc, hi, hst⟩ := hs
  have hfi : TypedV (simEnv20 B) (.varT "funcinst" []) (funcInstV hn fi) :=
    typedV_of_getElem? (typedV_storeV_iff.1 h).funcs (by simpa [Store.funcInst?] using hf)
  have hb := typedV_body_of_func20 (typedV_funcInst_parts20 hc hfi).2
  have hmem : instrToV i ∈ instrsToV fn.body := by
    rw [instrsToV_map20]
    exact List.mem_map_of_mem hi
  exact not_typedV_instrStore20 hst (Sim.typedV_list_iff.1 hb _ hmem)

/-- **Nor does the state.** -/
theorem not_typedV_state_storeFn20 {s : Store H} (f : Frame) (hs : StoreFn20 s) :
    ¬ TypedV (simEnv20 B) stateT (stateV hn s f) :=
  fun h => not_typedV_store_storeFn20 hs (typedV_stateV_iff.1 h).1

/-- A closed type name types alike in `simEnv20S` and `simEnv20`, at a value-only scope. -/
theorem typedV_of_hasTyp20S {ρ : VarEnv} (hρ : ValsOnly ρ) {x : IL.Id}
    (hx : (Silmaril.Wasm.SpecTec.Sim.Round7.Script.evTyp (.varT x [])).all
      (RelFree.rfEvB RelFree.bad20) = true)
    {v : Value} (h : HasTyp (simEnv20S B) ρ (.varT x []) v) : TypedV (simEnv20 B) (.varT x []) v := by
  rw [simEnv20S_eq B] at h
  refine typedV_of_valsOnly20 hρ ((hasTyp_withRels_iff (defsGood_simEnv20 B) (typsGood_simEnv20 B)
    ?_ ?_ (goodEvs_of_all hx)).1 h)
  · intro p hp; rw [hρ.2.1] at hp; simp at hp
  · intro p hp; rw [hρ.1] at hp; simp at hp

theorem not_hasTyp_store20S {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} (hs : StoreFn20 s) :
    ¬ HasTyp (simEnv20S B) ρ storeT (storeV hn s) :=
  fun h => not_typedV_store_storeFn20 hs (typedV_of_hasTyp20S hρ (by decide) h)

theorem not_hasTyp_state20S {ρ : VarEnv} (hρ : ValsOnly ρ) {s : Store H} (f : Frame)
    (hs : StoreFn20 s) : ¬ HasTyp (simEnv20S B) ρ stateT (stateV hn s f) :=
  fun h => not_typedV_state_storeFn20 f hs (typedV_of_hasTyp20S hρ (by decide) h)

/-! ## Every rule of the corrected `Step` types its state -/

/-- `qs` has the quantifier `x : t`, with `t` a closed type name. -/
def hasQ (qs : List Param) (x t : String) : Bool :=
  qs.any fun p => match p with
    | .expP y (.varT u []) => y == x && u == t
    | _ => false

/-- The conclusion's left-hand side is `z; …` with `z : state`, or `(s; f); …` with
`s : store`, and the conclusion has a single reading. -/
def stateLhsB : Rule → Bool
  | .ruleD _ qs _ e _ => !hasOptNil e && match e with
    | .tupE [.caseE "%;%" (.tupE [.varE "z", _]), _] => hasQ qs "z" "state"
    | .tupE [.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE "s", .varE "f"]), _]), _] =>
        hasQ qs "s" "store"
    | _ => false

/-- **Every rule of the corrected `Step` types its state** (kernel). -/
theorem stepRules20S_state (B : Builtins) : ∃ t rules,
    (simEnv20S B).findRel? "Step" = some ([], "%~>%", t, rules) ∧
      rules.all stateLhsB = true :=
  ⟨_, _, rfl, by decide +kernel⟩

theorem hasQ_mem {qs : List Param} {x t : String} (h : hasQ qs x t = true) :
    Param.expP x (.varT t []) ∈ qs := by
  obtain ⟨p, hp, hq⟩ := List.any_eq_true.1 h
  split at hq
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    exact hp
  · exact absurd hq Bool.false_ne_true

/-- The two shapes `stateLhsB` accepts. -/
theorem stateLhsB_cases {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp}
    {prems : List Prem} (h : stateLhsB (.ruleD nm qs op e prems) = true) :
    hasOptNil e = false ∧
      ((∃ a b, e = .tupE [.caseE "%;%" (.tupE [.varE "z", a]), b] ∧
          Param.expP "z" stateT ∈ qs) ∨
        (∃ a b, e = .tupE [.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE "s", .varE "f"]), a]), b] ∧
          Param.expP "s" storeT ∈ qs)) := by
  simp only [stateLhsB, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  split at h2
  · exact Or.inl ⟨_, _, rfl, hasQ_mem h2⟩
  · exact Or.inr ⟨_, _, rfl, hasQ_mem h2⟩
  · exact absurd h2 Bool.false_ne_true

/-! ## Reading the state off a conclusion -/

/-- The two components of an evaluated pair. -/
theorem evalExp_pair {env : Env} {ρ : VarEnv} {op : MixopS} {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h : EvalExp env ρ (.caseE op (.tupE [e₁, e₂])) (.case op (.tuple [v₁, v₂]))) :
    EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ := by
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 h
  obtain ⟨u₁, u₂, rfl, h₁, h₂⟩ := evalExp_tup2_cases hu
  simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true, true_and] at hcu
  obtain ⟨rfl, rfl⟩ := hcu
  exact ⟨h₁, h₂⟩

/-- The value a pattern `x; …` binds to `x`, read off an evaluated pair of configurations. -/
theorem findVal_of_cfgLhs {env : Env} {ρ : VarEnv} {x : IL.Id} {a b : Exp} {z w : Value}
    {code : List Value}
    (he : EvalExp env ρ (.tupE [.caseE "%;%" (.tupE [.varE x, a]), b]) (.tuple [cfgV z code, w])) :
    ρ.findVal? x = some z := by
  obtain ⟨v₁, v₂, hv, h₁, -⟩ := evalExp_tup2_cases he
  have hv₁ : v₁ = cfgV z code := by simp_all
  subst hv₁
  exact evalExp_varE_iff.1 (evalExp_pair h₁).1

/-- The store a pattern `(s; f); …` binds to `s`. -/
theorem findVal_of_stLhs {env : Env} {ρ : VarEnv} {a b : Exp} {sv fv w : Value}
    {code : List Value}
    (he : EvalExp env ρ (.tupE [.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE "s", .varE "f"]), a]), b])
      (.tuple [cfgV (.case "%;%" (.tuple [sv, fv])) code, w])) :
    ρ.findVal? "s" = some sv := by
  obtain ⟨v₁, v₂, hv, h₁, -⟩ := evalExp_tup2_cases he
  have hv₁ : v₁ = cfgV (.case "%;%" (.tuple [sv, fv])) code := by simp_all
  subst hv₁
  exact evalExp_varE_iff.1 (evalExp_pair (evalExp_pair h₁).1).1

/-- A well-typed quantifier, at the value the scope gives it. -/
theorem hasTyp_of_quantsOk {env : Env} {ρ : VarEnv} {qs : List Param} {x : IL.Id} {t : Typ}
    {v : Value} (hq : Sim.QuantsOk env ρ qs) (hx : Param.expP x t ∈ qs)
    (hv : ρ.findVal? x = some v) : HasTyp env ρ t v := by
  obtain ⟨u, hu, ht⟩ := hq x t hx
  have huv : u = v := Option.some.inj (hu.symm.trans hv)
  exact huv ▸ ht

/-- **No rule whose conclusion types the state fires from a storing state.** -/
theorem not_rule_storeFn20S {s : Store H} {f : Frame} (hs : StoreFn20 s) {code : List Value}
    {w : Value} {nm : IL.Id} {qs : List Param} {op : MixopS} {e e' : Exp} {prems : List Prem}
    {σ : List (IL.Id × Value)} (hr : stateLhsB (.ruleD nm qs op e prems) = true)
    (halt : e' ∈ conclAlts e) (hq : Sim.QuantsOk (simEnv20S B) (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp (simEnv20S B) (VarEnv.empty.bindVals σ) e'
      (.tuple [cfgV (stateV hn s f) code, w])) : False := by
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  obtain ⟨hnil, hshape⟩ := stateLhsB_cases hr
  have he' : e' = e := by simpa [conclAlts, hnil] using halt
  subst he'
  rcases hshape with ⟨a, b, rfl, hz⟩ | ⟨a, b, rfl, hsq⟩
  · exact not_hasTyp_state20S hρ f hs (hasTyp_of_quantsOk hq hz (findVal_of_cfgLhs he))
  · exact not_hasTyp_store20S hρ hs (hasTyp_of_quantsOk hq hsq (findVal_of_stLhs he))

/-- **A storing function makes the corrected script stuck**: at every builtins, from the image
of a configuration whose store has a storing function, `simEnv20S` has no step. -/
theorem stuck_storeFn20S {s : Store H} (f : Frame) (hs : StoreFn20 s) (code : List Value)
    (w : Value) : ¬ SStepB (simEnv20S B) (cfgV (stateV hn s f) code) w := by
  intro h
  obtain ⟨t, rules, hrel, hall⟩ := stepRules20S_state B
  cases h with
  | rule hrel' hrule halt hps hq he _ =>
    rw [hrel] at hrel'
    obtain ⟨rfl, -, rfl⟩ := by simpa using hrel'
    obtain rfl := bindParams_nil hps
    exact not_rule_storeFn20S hs (List.all_eq_true.1 hall _ (List.mem_of_getElem? hrule))
      halt hq he

/-- The same for a V2 configuration's image. -/
theorem stuck_configV_storeFn20S {c : Config H} (hs : StoreFn20 c.store) (w : Value) :
    ¬ SStepB (simEnv20S B) (configV hn c) w :=
  stuck_storeFn20S c.frame hs _ w

/-! ## A storing configuration -/

/-- A store with one function, whose body is `i32.store` at offset 0. -/
def storeFnStore : Store H :=
  { funcs := [⟨⟨[], []⟩, {}, .wasm (V2.Func.mk ⟨0⟩ [] [.intStore .i32 none ⟨0, 0⟩])⟩] }

/-- **A storing configuration**: that store, the empty frame, and code `nop`. -/
def storeFnCfg : Config H := ⟨storeFnStore, {}, [.plain .nop]⟩

theorem storeFn_storeFnCfg : StoreFn20 (storeFnCfg (H := H)).store :=
  ⟨0, _, _, _, rfl, rfl, List.mem_singleton_self _, .int .i32 none ⟨0, 0⟩⟩

end Silmaril.Wasm.SpecTec.Sim20.StoreFix
