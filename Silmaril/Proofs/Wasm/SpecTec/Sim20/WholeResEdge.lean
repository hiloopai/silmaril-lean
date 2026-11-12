module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeBwdW

/-!
# `memory.grow` without a memory: the 2.0 script fails the grow, V2 is stuck

`Step/memory.grow-fail` (rule 20 of wasm-2.0 `Step`) has no premise: it rewrites
`CONST I32 n; MEMORY.GROW` to `CONST I32 $inv_signed_(32, -1)` in any state, also in one whose
frame has no memory (`fires20_memGrowFail`). V2's `memoryGrowSucceed` and `memoryGrowFail` both
look the memory up (`memAddr? memIdx0`), so in a frame with no memory V2 has no step at all
(`not_step_memGrow`). The code is vector-free and has no conversion, so the statement of
`Task.wholeStepBwdW` without its resource hypothesis `ResOkL` is false
(`not_wholeStepBwd_noRes`). `Step/table.grow-fail` and the `otherwise` rules of `table.fill`,
`table.copy`, `table.init`, `memory.fill`, `memory.copy` and `memory.init` behave alike at a missing
table or memory; those are not formalized.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk Fires dderives_iff_fires)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

set_option maxRecDepth 100000

/-- `Step/memory.grow-fail`, rule 20 of `Step` in `Scripts.Wasm20.fixed` (verbatim). -/
def memGrowFailRule20 : Rule :=
  (Rule.ruleD "memory.grow-fail"
  [(Param.expP "z" (Typ.varT "state" [])), (Param.expP "n" (Typ.varT "n" []))] "%~>%" (Exp.tupE [(Exp.caseE "%;%"
  (Exp.tupE [(Exp.varE "z"), (Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.caseE "I32" (Exp.tupE
  [])), (Exp.caseE "%" (Exp.tupE [(Exp.varE "n")]))])), (Exp.caseE "MEMORY.GROW" (Exp.tupE []))])])),
  (Exp.caseE "%;%" (Exp.tupE [(Exp.varE "z"), (Exp.listE [(Exp.caseE "CONST" (Exp.tupE [(Exp.caseE "I32"
  (Exp.tupE [])), (Exp.caseE "%" (Exp.tupE [(Exp.callE "inv_signed_" [(Arg.expA (Exp.numE (Num.natN 32))),
  (Arg.expA (Exp.unE UnOp.minusOp (OpTyp.numT NumTyp.intT) (Exp.cvtE (Exp.numE (Num.natN 1)) NumTyp.natT NumTyp.intT)))])]))]))])]))])
  [])

/-- `memory.grow-fail` is rule 20 of `Step`. -/
theorem hasRuleAt_memGrowFail (B : Builtins) :
    HasRuleAt (simEnv20 B) "Step" "%~>%" 20 memGrowFailRule20 := ⟨_, _, _, rfl, rfl, rfl⟩

/-- `i32.const 0; memory.grow` in the empty store and frame: no memory. -/
abbrev memGrowCfg : Config Empty := ⟨{}, {}, [constI32 0, .plain .memoryGrow]⟩

/-- What `memory.grow-fail` gives: `i32.const -1`. -/
abbrev growFailCfg : Config Empty := ⟨{}, {}, [constI32 (BitVec.allOnes 32)]⟩

set_option maxHeartbeats 4000000 in
/-- **`memory.grow-fail` fires without a memory.** -/
theorem fires20_memGrowFail (B : Builtins) :
    Fires (simEnv20 B) "Step" 20
      (.tuple [configV Empty.elim memGrowCfg, configV Empty.elim growFailCfg]) :=
  Pure.fires_of_ruleAt (hasRuleAt_memGrowFail B)
    [("z", stateV Empty.elim {} {}), ("n", .num (.natN 0))]
    (QuantsOk.cons rfl ⟨100, by with_unfolding_all rfl⟩
      (QuantsOk.cons rfl ⟨100, by with_unfolding_all rfl⟩ QuantsOk.nil))
    ⟨200, by with_unfolding_all rfl⟩ (fun _ hp => by cases hp)

/-- **The 2.0 script steps from `memGrowCfg` to `growFailCfg`.** -/
theorem sstepB_memGrow (B : Builtins) :
    SStepB (simEnv20 B) (configV Empty.elim memGrowCfg) (configV Empty.elim growFailCfg) := by
  obtain ⟨t, rules, hrel⟩ : ∃ t rules,
      (simEnv20 B).findRel? "Step" = some ([], "%~>%", t, rules) := ⟨_, _, rfl⟩
  exact (sstepB20_iff B).2 ((dderives_iff_fires hrel).2 ⟨20, fires20_memGrowFail B⟩)

/-! ## V2 has no step without a memory -/

/-- `i32.const n; memory.grow`, or `memory.grow` alone. -/
def MemGrowCode (code : List Admin) : Prop :=
  (∃ n, code = [constI32 n, .plain .memoryGrow]) ∨ code = [.plain .memoryGrow]

/-- No `Step_pure` rule applies to `MemGrowCode`. -/
theorem not_pureStep_memGrow {P : Profile} {code code' : List Admin} (hc : MemGrowCode code) :
    ¬ PureStep P code code' := by
  intro h
  cases h <;> simp_all [MemGrowCode, vals, constI32, aref, vconst]
  case trapVals vs rest _ =>
    have hm : Admin.trap ∈ vals vs ++ Admin.trap :: rest := by simp
    rcases hc with ⟨n, hc⟩ | hc <;> simp_all [vals]

/-- No `Step_read` rule applies to `MemGrowCode`. -/
theorem not_readStep_memGrow {H : Type} {s : Store H} {f : Frame} {code code' : List Admin}
    (hc : MemGrowCode code) : ¬ ReadStep s f code code' := by
  intro h
  cases h <;> simp_all [MemGrowCode, vals, constI32, vconst]
  all_goals
    rcases hc with ⟨n, hc⟩ | hc <;>
      · have hl := congrArg List.getLast? hc
        simp at hl

/-- The context split of `MemGrowCode`: the non-value part is `memory.grow` alone. -/
theorem split_memGrow {vs : List Val} {is rest : List Admin} (hall : is.all Admin.isVal = false)
    (hne : vs ≠ [] ∨ rest ≠ []) (h : MemGrowCode (vals vs ++ is ++ rest)) :
    MemGrowCode is := by
  refine Or.inr ?_
  rcases h with ⟨n, h⟩ | h <;>
  rcases vs with _ | ⟨v, _ | ⟨v', vs⟩⟩ <;> rcases is with _ | ⟨i₁, _ | ⟨i₂, is⟩⟩ <;>
    simp_all [vals, constI32, Admin.isVal, Admin.val?]

/-- Code ending in `CALL_ADDR` is not `MemGrowCode`. -/
theorem not_memGrow_callAddr (vs : List Val) (a : FuncAddr) :
    ¬ MemGrowCode (vals vs ++ [.callAddr a]) := by
  have hl : ∀ l : List Admin, vals vs ++ [.callAddr a] = l → l.getLast? = some (.callAddr a) :=
    fun l hl => by rw [← hl]; simp
  rintro (⟨n, hc⟩ | hc)
  · exact absurd (hl _ hc) (by simp)
  · exact absurd (hl _ hc) (by simp)

/-- **Without a memory in the frame, V2 has no step from `i32.const n; memory.grow`.** -/
theorem not_step_memGrow {H : Type} {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hm : c.frame.module.mems = []) : ¬ MemGrowCode c.code := by
  induction h with
  | pure hp => exact fun hc => not_pureStep_memGrow hc hp
  | read hr => exact fun hc => not_readStep_memGrow hc hr
  | ctxtInstrs hs hne ih => exact fun hc => ih hm (split_memGrow hs.not_allVals hne hc)
  | ctxtLabel _ _ => simp [MemGrowCode, constI32]
  | ctxtFrame _ _ => simp [MemGrowCode, constI32]
  | callAddrHost => exact not_memGrow_callAddr _ _
  | callAddrHostDiv => exact not_memGrow_callAddr _ _
  | @memoryGrowSucceed _ f _ _ _ _ ha =>
    have hm' : f.module.mems = [] := hm
    exact fun _ => absurd ha (by simp [ModuleInst.memAddr?, hm'])
  | @memoryGrowFail _ f _ _ _ ha =>
    have hm' : f.module.mems = [] := hm
    exact fun _ => absurd ha (by simp [ModuleInst.memAddr?, hm'])
  | _ => simp [MemGrowCode, constI32, vconst]

set_option maxHeartbeats 4000000 in
/-- The image of `memGrowCfg` is IL-typed. -/
theorem typed20_memGrow (B : Builtins) : Typed20 (simEnv20 B) Empty.elim memGrowCfg :=
  ⟨100, by with_unfolding_all rfl⟩

/-- **The backward half without the resource hypothesis is false**: the statement of
`Task.wholeStepBwdW` with `ResOkL` dropped fails at `i32.const 0; memory.grow` in the empty store
and frame. -/
theorem not_wholeStepBwd_noRes :
    ¬ ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice) (c : Config H) (w : Value),
        Typed20 (simEnv20 (Sim.Floats.floatIntB (Profile.spec nd r))) hn c → CvtOkL c.code →
        NoVecL c.code →
        SStepB (simEnv20 (Sim.Floats.floatIntB (Profile.spec nd r))) (configV hn c) w →
        ∃ c', w = configV hn c' ∧ Step (Profile.spec nd r) host c c' := by
  intro h
  obtain ⟨c', -, hs⟩ := h Empty Empty.elim (fun a => a.elim) (fun _ _ _ _ => False) false {}
    memGrowCfg _ (typed20_memGrow _) (by simp [CvtOkL, CvtOkA])
    (by simp [NoVecL, NoVecA, vecOp20]) (sstepB_memGrow _)
  exact not_step_memGrow hs rfl (Or.inl ⟨0, rfl⟩)

end Silmaril.Wasm.SpecTec.Sim20.Whole
