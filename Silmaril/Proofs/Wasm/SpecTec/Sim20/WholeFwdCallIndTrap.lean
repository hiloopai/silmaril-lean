module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdCallInd
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestCopyGt

/-!
# `call_indirect-trap` forward (`Step_read` 4)

2.0's `z; (CONST I32 i) (CALL_INDIRECT x y) ~> TRAP -- otherwise` fires where none of rules 0–3
fires on the same left-hand side. Rules 0–2 name `BLOCK`, `LOOP`, `CALL`, which the left-hand
side lacks (`readTags20`). Rule 3 (`call_indirect-call`) is refuted at every assignment where
V2 traps (`not_callIndBody`): its first premise reads the table entry at `i` as `REF.FUNC_ADDR a`,
its second compares `$type(z, y)` with `$funcinst(z)[a].TYPE`, and V2's trap premise says that no
such `a` names a function of that type.

V2's `ReadStep.callIndirectTrap` keeps the table lookup as a premise but allows the type index
`y` to be undefined. The forward statement here asks for `y` to be defined (`type? y = some ft`,
which validation guarantees), so that `$type(z, y)` has a value to compare.

* `fires_callIndirectTrap20`, `CallIndTrapFwd20`, `fwdBase20_callIndTrap`, and
  **`Task.wholeStepFwd20F`** (proved): at `storeB`, `FwdStep20E` plus the trap is matched forward.
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
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly stateT QuantsOk RuleBody otherwiseAt
  evalExp_tup2 evalExp_case evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (LhsIn otherwiseAt_of_table tags_of_take relRules ruleTags)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-- `Step_read/call_indirect-trap`, rule 4 (transcribed). -/
def callIndirectTrapRule20 : Rule :=
  .ruleD "call_indirect-trap" [.expP "z" (.varT "state" []),
      .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))]), .expP "x" (.varT "idx" []),
      .expP "y" (.varT "idx" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
        .caseE "CALL_INDIRECT" (.tupE [.varE "x", .varE "y"])]]), trapRhs])
    [.elsePr]

theorem hasRuleAt_callIndirectTrap20 :
    HasRuleAt (simEnv20 B) "Step_read" "%~>%" 4 callIndirectTrapRule20 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Injectivity of the type images -/

theorem valTypeV_inj20 {t t' : V2.ValType} (h : valTypeV t = valTypeV t') : t = t' := by
  rcases t with ((_ | _) | (_ | _)) | ⟨⟩ | (_ | _) <;>
    rcases t' with ((_ | _) | (_ | _)) | ⟨⟩ | (_ | _) <;>
    first | rfl | (simp [valTypeV, numTypeV, refTypeV, caseNilV] at h)

theorem funcTypeV_inj20 {t t' : V2.FuncType} (h : funcTypeV t = funcTypeV t') : t = t' := by
  have hinj : Function.Injective (List.map valTypeV) :=
    List.map_injective_iff.2 fun _ _ e => valTypeV_inj20 e
  simp only [funcTypeV, resultTypeV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
    Value.list.injEq, true_and, and_true] at h
  cases t
  cases t'
  simp only [V2.FuncType.mk.injEq]
  exact ⟨hinj h.1, hinj h.2⟩

/-! ## The left-hand side -/

/-- The tags of `call_indirect`'s code. -/
theorem lhsIn_callInd (s : Store H) (f : Frame) (i : BitVec 32) (x : TableIdx) (y : TypeIdx) :
    LhsIn ["CONST", "CALL_INDIRECT"]
      (configV hn ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩) := by
  refine Or.inr ⟨_, _, rfl, ?_⟩
  intro u hu op w hw
  simp only [adminsToV, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;>
  · rw [← adminToV_case20 hw]
    simp [adminHead20, instrHead20]

/-- A `call_indirect` left-hand side at a known code binds its operands. -/
theorem callIndScope_of {σ : List (IL.Id × Value)} {i : BitVec 32} {x : TableIdx} {y : TypeIdx}
    (hes : EvalExps (simEnv20 B) (VarEnv.empty.bindVals σ)
      [constIE, .caseE "CALL_INDIRECT" (.tupE [.varE "x", .varE "y"])]
      (adminsToV [constI32 i, .plain (.callIndirect x y)])) :
    (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) ∧
      (VarEnv.empty.bindVals σ).findVal? "x" = some (idxV x) ∧
      (VarEnv.empty.bindVals σ).findVal? "y" = some (idxV y) := by
  obtain ⟨w₁, ws, h₁, hws, he⟩ := evalExps_cons_iff.1 hes
  obtain ⟨w₂, ws', h₂, -, he'⟩ := evalExps_cons_iff.1 hws
  have e₁ : w₁ = adminToV (constI32 i) := (List.cons.inj he).1.symm
  have e₂ : w₂ = .case "CALL_INDIRECT" (.tuple [idxV x, idxV y]) := by
    have := (List.cons.inj he).2
    exact (List.cons.inj (this ▸ he' : _)).1.symm
  obtain ⟨c, hc, fi⟩ := constI_of_lhs (e₁ ▸ h₁)
  obtain rfl := constI32_inj hc.symm
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 (e₂ ▸ h₂)
  obtain ⟨u₁, u₂, hx, hy, hU⟩ := Sim.State.evalExp_tup2_inv (((Value.case.inj hcu).2) ▸ hu)
  have e : idxV x = u₁ ∧ idxV y = u₂ := by
    simpa only [Value.tuple.injEq, List.cons.injEq, and_true] using hU
  exact ⟨fi, e.1 ▸ evalExp_varE_iff.1 hx, e.2 ▸ evalExp_varE_iff.1 hy⟩


/-! ## Rule 3 is refuted where V2 traps -/

/-- `$funcinst(z)`. -/
theorem evalExp_funcinstList20 {ρ : VarEnv} {s : Store H} {f : Frame}
    (hρ : ρ.findDef? "funcinst" = none) (fz : ρ.findVal? "z" = some (stateV hn s f)) :
    EvalExp (simEnv20 B) ρ (.callE "funcinst" [.expA (.varE "z")])
      (.list (s.funcs.map (funcInstV hn))) :=
  evalExp_call1 hasClause_funcinst20 hρ (evalArgs_cons (evalExp_var fz) evalArgs_nil)
    State.matchArgs_sf (evalExp_dotE_iff.2 ⟨storeV hn s, evalExp_var rfl, rfl⟩)

/-- **The first premise of rule 3, read back**: the table entry at `i` is a function address,
bound to `a`. -/
theorem entry_of_callIndPrem {ρ : VarEnv} {s : Store H} {f : Frame} {x : TableIdx}
    {i : BitVec 32} {ta : Nat} {ti : TableInst}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV i.toNat))
    (fx : ρ.findVal? "x" = some (idxV x)) (hρ : ρ.findDef? "table" = none)
    (hta : f.module.tables[x.toNat]? = some ta) (htt : s.tables[ta]? = some ti)
    (h : EvalExp (simEnv20 B) ρ (.cmpE .eqOp .boolT (.idxE (.dotE tableE "REFS") iPay)
      (.caseE "REF.FUNC_ADDR" (.varE "a"))) (.bool true)) :
    ∃ a, ti.refs[i.toNat]? = some (.funcAddr a) ∧ ρ.findVal? "a" = some (.num (.natN a)) := by
  obtain ⟨v, h₁, h₂⟩ := Sim.Bwd.eq_of_cmp h
  obtain ⟨A, hA, rfl⟩ := evalExp_caseE_iff.1 h₂
  obtain ⟨wl, j, hwl, hj, hidx⟩ := evalExp_idxE_iff.1 h₁
  have ewl : wl = .list (ti.refs.map refV) :=
    EvalExp.unique hwl (evalExp_dotE_iff.2 ⟨_, evalExp_table20 hρ (evalExp_var fz)
      (evalExp_var fx) hta htt, rfl⟩)
  have ej : j = i.toNat := Sim.Bwd.natN_inj (EvalExp.unique hj (evalExp_iPay fi))
  have hget : (ti.refs.map refV)[i.toNat]? = some (.case "REF.FUNC_ADDR" A) := by
    rw [← ej]
    simpa [Value.idx?, ewl] using hidx
  rw [List.getElem?_map] at hget
  obtain ⟨r, hr, hrv⟩ := Option.map_eq_some_iff.1 hget
  obtain ⟨a, rfl, rfl⟩ : ∃ a, r = .funcAddr a ∧ A = .num (.natN a) := by
    cases r with
    | null t => cases t <;> simp [refV, refTypeV, caseNilV] at hrv
    | funcAddr a => exact ⟨a, rfl, by simpa [refV] using hrv.symm⟩
    | hostAddr a => simp [refV] at hrv
  exact ⟨a, hr, evalExp_varE_iff.1 hA⟩

/-- **The second premise of rule 3, read back**: `a` names a function whose type is `y`'s. -/
theorem type_of_callIndPrem {ρ : VarEnv} {s : Store H} {f : Frame} {y : TypeIdx}
    {ft : V2.FuncType} {a : FuncAddr} (fz : ρ.findVal? "z" = some (stateV hn s f))
    (fy : ρ.findVal? "y" = some (idxV y)) (fa : ρ.findVal? "a" = some (.num (.natN a)))
    (hρ₁ : ρ.findDef? "type" = none) (hρ₂ : ρ.findDef? "funcinst" = none)
    (hft : f.module.types[y.toNat]? = some ft)
    (h : EvalExp (simEnv20 B) ρ (.cmpE .eqOp .boolT
      (.callE "type" [.expA (.varE "z"), .expA (.varE "y")])
      (.dotE (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) "TYPE")) (.bool true)) :
    ∃ fi, s.funcInst? a = some fi ∧ fi.type = ft := by
  obtain ⟨v, h₁, h₂⟩ := Sim.Bwd.eq_of_cmp h
  have ev : v = funcTypeV ft :=
    EvalExp.unique h₁ (evalExp_type20 hρ₁ (evalExp_var fz) (evalExp_var fy) hft)
  obtain ⟨u, hu, hfld⟩ := evalExp_dotE_iff.1 h₂
  obtain ⟨wl, n, hwl, hn', hidx⟩ := evalExp_idxE_iff.1 hu
  have ewl : wl = .list (s.funcs.map (funcInstV hn)) :=
    EvalExp.unique hwl (evalExp_funcinstList20 hρ₂ fz)
  have en : n = a := Sim.Bwd.natN_inj (EvalExp.unique hn' (evalExp_var fa))
  have hget : (s.funcs.map (funcInstV hn))[a]? = some u := by
    rw [← en]
    simpa [Value.idx?, ewl] using hidx
  rw [List.getElem?_map] at hget
  obtain ⟨fi, hfi, rfl⟩ := Option.map_eq_some_iff.1 hget
  have hty : funcTypeV fi.type = funcTypeV ft := by
    rw [← ev]
    simpa [funcInstV, Value.field?] using hfld
  exact ⟨fi, by simpa [Store.funcInst?] using hfi, funcTypeV_inj20 hty⟩

/-- **Rule 3's body is refuted** where V2 traps and the type index is defined. -/
theorem not_callIndBody {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {s : Store H}
    {f : Frame} {x : TableIdx} {y : TypeIdx} {i : BitVec 32} {ti : TableInst} {ft : V2.FuncType}
    (ht : (⟨s, f⟩ : State H).table? x = some ti)
    (hft : (⟨s, f⟩ : State H).type? y = some ft)
    (h : ¬ ∃ (a : FuncAddr) (fi : FuncInst H), ti.refs[i.toNat]? = some (.funcAddr a) ∧
      s.funcInst? a = some fi ∧ (⟨s, f⟩ : State H).type? y = some fi.type) (c' : Value) :
    ¬ RuleBody (simEnv20 B) D els [] [] "%~>%" callIndirectCallRule20
      (.tuple [configV hn ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩, c']) := by
  intro hbody
  obtain ⟨σ, -, fz, hes, -, hp⟩ := bodyCfg_inv hbody
  obtain ⟨fi, fx, fy⟩ := callIndScope_of hes
  obtain ⟨ta, hta, htt⟩ := table?_some ht
  have hft' : f.module.types[y.toNat]? = some ft := by
    simpa [State.type?, ModuleInst.type?] using hft
  obtain ⟨a, hr, fa⟩ := entry_of_callIndPrem fz fi fx rfl hta htt
    (Pure.ifPrem (hp _ (List.mem_cons_self ..)))
  obtain ⟨fn, hfn, hty⟩ := type_of_callIndPrem fz fy fa rfl rfl hft'
    (Pure.ifPrem (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  exact h ⟨a, fn, hr, hfn, hty ▸ hft⟩

/-- **`otherwise` holds for rule 4** where V2 traps and the type index is defined. -/
theorem otherwise4 {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {i : BitVec 32}
    {ti : TableInst} {ft : V2.FuncType} (ht : (⟨s, f⟩ : State H).table? x = some ti)
    (hft : (⟨s, f⟩ : State H).type? y = some ft)
    (h : ¬ ∃ (a : FuncAddr) (fi : FuncInst H), ti.refs[i.toNat]? = some (.funcAddr a) ∧
      s.funcInst? a = some fi ∧ (⟨s, f⟩ : State H).type? y = some fi.type) (w : Value) :
    otherwiseAt (simEnv20 B) "Step_read" [] 4
      (.tuple [configV hn ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩, w]) := by
  obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAt_callIndirectCall20 (B := B)
  have hT : ((relRules (simEnv20 B) "Step_read").map ruleTags).take 47 = readTags20 := by
    rw [relRules_simEnv20, readTags20_eq]
    rfl
  refine otherwiseAt_of_table hrel (tags_of_take hrel hT) (by decide) (lhsIn_callInd s f i x y)
    (exc := [3]) (by decide) ?_
  intro k hk _ r hr w' hw
  obtain ⟨c', rfl⟩ := sameLhs_inv hw
  obtain rfl := List.mem_singleton.1 hk
  rw [rule_of_hasRuleAt hrel hasRuleAt_callIndirectCall20 hr]
  exact not_callIndBody ht hft h c'


/-! ## The rule fires -/

/-- **`Step_read/call_indirect-trap` fires forward** at the image of V2's
`ReadStep.callIndirectTrap`, from a typed state, where the type index is defined. -/
theorem fires_callIndirectTrap20 {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx}
    {i : BitVec 32} {ti : TableInst} {ft : V2.FuncType}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ht : (⟨s, f⟩ : State H).table? x = some ti) (hft : (⟨s, f⟩ : State H).type? y = some ft)
    (h : ¬ ∃ (a : FuncAddr) (fi : FuncInst H), ti.refs[i.toNat]? = some (.funcAddr a) ∧
      s.funcInst? a = some fi ∧ (⟨s, f⟩ : State H).type? y = some fi.type) :
    Fires (simEnv20 B) "Step_read" 4 (.tuple [
      configV hn ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩,
      .list (adminsToV [.trap])]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat), ("x", idxV x),
    ("y", idxV y)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match callIndirectTrapRule20 with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons rfl (typedV_idx20 x _ hρ) (QuantsOk.cons rfl (typedV_idx20 y _ hρ)
        QuantsOk.nil)))
  have hl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
        .caseE "CALL_INDIRECT" (.tupE [.varE "x", .varE "y"])]]))
      (configV hn ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩) :=
    evalExp_case (evalExp_tup2 (evalExp_var rfl) (evalExp_listE_iff.2 ⟨_, evalExps_cons
      (evalExp_constIE rfl) (evalExps_cons (evalExp_case (evalExp_tup2 (evalExp_var rfl)
        (evalExp_var rfl))) evalExps_nil), rfl⟩))
  refine Pure.fires_of_ruleAt hasRuleAt_callIndirectTrap20 σ hq (evalExp_tup2 hl evalExp_trapRhs) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .elsePr (otherwise4 ht hft h _)

/-! ## The fragment -/

/-- **V2's `call_indirect` that traps**, at a defined type index. -/
inductive CallIndTrapFwd20 : Config H → Config H → Prop where
  | mk {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {i : BitVec 32} {ti : TableInst}
      {ft : V2.FuncType} (ht : (⟨s, f⟩ : State H).table? x = some ti)
      (hft : (⟨s, f⟩ : State H).type? y = some ft)
      (h : ¬ ∃ (a : FuncAddr) (fi : FuncInst H), ti.refs[i.toNat]? = some (.funcAddr a) ∧
        s.funcInst? a = some fi ∧ (⟨s, f⟩ : State H).type? y = some fi.type) :
      CallIndTrapFwd20 ⟨s, f, [constI32 i, .plain (.callIndirect x y)]⟩ ⟨s, f, [.trap]⟩

theorem CallIndTrapFwd20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : CallIndTrapFwd20 c c') : Step P host c c' := by
  cases h with
  | mk ht _ h => exact .read (.callIndirectTrap ht h)

/-- **`call_indirect-trap` is a base**, at every builtins and any store condition. -/
theorem fwdBase20_callIndTrap {W : Store H → Prop} :
    FwdBase20 B hn W (CallIndTrapFwd20 (H := H)) where
  sr _ _ hc h := by
    cases h with
    | mk _ _ _ => exact typed20_iff.2 ⟨(typed20_iff.1 hc).1, typedV_admins_trap20⟩
  fwd c c' hc _ h := by
    have hz := typedV_state_of_typed20 hc
    cases h with
    | @mk s f x y i ti ft ht hft h =>
      have hc' : Typed20 (simEnv20 B) hn ⟨s, f, [.trap]⟩ :=
        typed20_iff.2 ⟨(typed20_iff.1 hc).1, typedV_admins_trap20⟩
      exact fwdS_read hc hc' (sread_of_firesB20 (firesB_read20_iff.2
        (fires_callIndirectTrap20 hz ht hft h)))

/-- **The base at `storeB`, with both `call_indirect` rules.** -/
inductive FwdStep20F (P : Profile) : Config H → Config H → Prop where
  | fwd {c c' : Config H} (h : FwdStep20E P c c') : FwdStep20F P c c'
  | callIndTrap {c c' : Config H} (h : CallIndTrapFwd20 c c') : FwdStep20F P c c'

theorem FwdStep20F.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : FwdStep20F P c c') : Step P host c c' := by
  cases h with
  | fwd h => exact h.step
  | callIndTrap h => exact h.step

/-- The widened base is a base at `storeB`. -/
theorem fwdBase20_fwdF (P : Profile) :
    FwdBase20 (storeB P) hn WholePages (FwdStep20F (H := H) P) where
  sr c c' hc h := by
    cases h with
    | fwd h => exact (fwdBase20_fwdE P).sr c c' hc h
    | callIndTrap h => exact (fwdBase20_callIndTrap (W := WholePages)).sr c c' hc h
  fwd c c' hc hw h := by
    cases h with
    | fwd h => exact (fwdBase20_fwdE P).fwd c c' hc hw h
    | callIndTrap h => exact fwdBase20_callIndTrap.fwd c c' hc hw h

/-- **The forward 2.0 half with both `call_indirect` rules** (stated and proved): at `storeB`,
every step of `Nest20 (FwdStep20F P)` from a configuration with typed image and whole pages is a
step of the corrected script between the images, with a typed successor image. -/
def Task.wholeStepFwd20F : Prop :=
  ∀ (H : Type) (hn : H → String) (P : Profile) (c c' : Config H),
    Typed20 (simEnv20 (storeB P)) hn c → WholePages c.store → Nest20 (FwdStep20F P) c c' →
    Typed20 (simEnv20 (storeB P)) hn c' ∧
      SStepB (simEnv20S (storeB P)) (configV hn c) (configV hn c')

/-- **`Task.wholeStepFwd20F` is proved**, at every profile. -/
theorem wholeStepFwd20F : Task.wholeStepFwd20F :=
  fun _ _ P _ _ hc hw h => fwd_nest20 (fwdBase20_fwdF P) h hc hw

end Silmaril.Wasm.SpecTec.Sim20.Whole
