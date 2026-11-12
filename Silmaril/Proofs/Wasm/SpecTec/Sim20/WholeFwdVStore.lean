module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdVar

/-!
# The restricted forward 2.0 half, widened to the vector-store trap rules

`Step` 15 (`vstore-oob`) and 17 (`vstore_lane-oob`) rewrite `z; CONST I32 i; VCONST V128 c;
VSTORE …` to `z; TRAP` when the access runs past the memory. They fire forward from the image of
V2's `vecStoreOob` and `vecStoreLaneOob`, at any builtins, from a typed state:

* the quantifiers are typed: `c : vec_(V128)` by `typedV_vecV128_20`, `ao : memarg` by
  `typedV_memarg20` (V2's `MemArg` has `Fin (2 ^ 32)` fields), `N : N` and `j : laneidx = u8`
  (V2's `LaneIdx` is `Fin (2 ^ 8)`);
* the premise `i + ao.OFFSET + w/8 > |$mem(z, 0).BYTES|` evaluates with `w = $size(V128) = 128`
  or the pack width (`evalExp_div8`, `evalExp_memLen20`).

`TopVStep20 P` adds V2's `vecStoreOob` and `vecStoreLaneOob` to `TopVarStep20 P`, and
**`Task.wholeStepTopVS20`** (proved, `wholeStepTopVS20`) is the forward/backward target on it at
`growB`.

**The two value rules do not fire at `growB`-like builtins.** `Step` 16 (`vstore-val`) and 18
(`vstore_lane-val`) compare a call to `$vbytes_`/`$ibytes_`/`$lanes_`, which `GrowLike20` keeps
inert (`InertEnv`, needed by the backward half). `not_fires_inert20` generalises pass 6's
`not_fires_inert` from `floatIntB` to every `InertEnv`, and `not_fires_vstoreVal_growLike`,
`not_fires_vstoreLaneVal_growLike` apply it. So the forward half on V2's `vecStoreVal` and
`vecStoreLaneVal` needs builtins answering the byte and lane primitives, and then the backward half
on rules 12, 14, 16, 18 is no longer vacuous; neither is attempted here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm (PackSize)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly stateT QuantsOk evalExp_tup2 evalExp_case
  evalExp_list1)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (relRules)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## The quantifier types -/

theorem findTyp_memarg20 : (simEnv20 B).findTyp? "memarg" = some ([], [.instD [] []
    (.structT [.mk "ALIGN" (.varT "u32" []) [] [], .mk "OFFSET" (.varT "u32" []) [] []])]) := rfl

theorem findTyp_N20 : (simEnv20 B).findTyp? "N" =
    some ([], [.instD [] [] (.aliasT (.numT .natT))]) := rfl

theorem findTyp_laneidx20 : (simEnv20 B).findTyp? "laneidx" =
    some ([], [.instD [] [] (.aliasT (.varT "u8" []))]) := rfl

theorem findTyp_u8_20 : (simEnv20 B).findTyp? "u8" =
    some ([], [.instD [] [] (.aliasT (.varT "uN" [.expA (.numE (.natN 8))]))]) := rfl

/-- **Every V2 memory argument is a `memarg`**: both fields are `Fin (2 ^ 32)`. -/
theorem typedV_memarg20 (a : V2.MemArg) : TypedV (simEnv20 B) (.varT "memarg" []) (memargV a) :=
  typedV_structG findTyp_memarg20 (hasTypFields_consG (typedV_u32_20 a.align.isLt)
    (hasTypFields_oneG (typedV_u32_20 a.offset.isLt)))

/-- `N` holds every natural. -/
theorem typedV_N20 (k : Nat) : TypedV (simEnv20 B) (.varT "N" []) (.num (.natN k)) :=
  typedV_aliasG findTyp_N20 (hasTyp_nat _ _ k)

/-- **Every V2 lane index is a `laneidx`**: `LaneIdx` is `Fin (2 ^ 8)`. -/
theorem typedV_laneidx20 (j : LaneIdx) : TypedV (simEnv20 B) (.varT "laneidx" []) (pctV j.val) :=
  typedV_aliasG findTyp_laneidx20 (typedV_aliasG findTyp_u8_20
    (Pure.hasTyp_uN20 evalExp_num j.isLt) _ ⟨rfl, rfl, rfl⟩)

/-! ## Left-hand sides and the premise -/

/-- `VCONST V128 c` at `c` bound to the pattern's image. -/
theorem evalExp_vconstE {env : Env} {ρ : VarEnv} {c : BitVec 128}
    (fc : ρ.findVal? "c" = some (pctV c.toNat)) :
    EvalExp env ρ (.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c"]))
      (adminToV (vconst c)) :=
  evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
    (evalExp_var fc))

/-- **The trap premise, forward**: `i + ao.OFFSET + w/8 > |$mem(z, 0).BYTES|`. -/
theorem prem_of_trap {ρ : VarEnv} {e : Exp} {s : Store H} {f : Frame} {i : BitVec 32}
    {a : V2.MemArg} {w ad : Nat} {mi : MemInst} (hρ : ρ.findDef? "mem" = none)
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fi : ρ.findVal? "i" = some (pctV i.toNat))
    (fa : ρ.findVal? "ao" = some (memargV a)) (he : EvalExp (simEnv20 B) ρ e (.num (.natN w)))
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128)
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hlt : mi.bytes.size < effAddr i.toNat a + w / 8) :
    EvalExp (simEnv20 B) ρ (.cmpE .gtOp (.numT .natT) (addrE (div8E e)) memLenE) (.bool true) := by
  refine evalExp_cmpNum (evalExp_addNat20 (evalExp_addNat20 (evalExp_iPay fi) (evalExp_off fa))
    (evalExp_div8 he hw)) (evalExp_memLen20 hρ fz ha hm) ?_
  simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]
  simpa [effAddr] using hlt

/-! ## The two trap rules, forward -/

/-- The scope of rule 15. -/
abbrev vstoreScope (s : Store H) (f : Frame) (i : BitVec 32) (c : BitVec 128) (ao : V2.MemArg) :
    List (IL.Id × Value) :=
  [("z", stateV hn s f), ("i", pctV i.toNat), ("c", pctV c.toNat), ("ao", memargV ao)]

/-- **`Step/vstore-oob` fires forward** at the image of V2's `vecStoreOob`. -/
theorem fires_vstoreOob {s : Store H} {f : Frame} {ao : V2.MemArg} {i : BitVec 32} {c : BitVec 128}
    {ad : MemAddr} {mi : MemInst} (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hlt : mi.bytes.size < effAddr i.toNat ao + 16) :
    Fires (simEnv20 B) "Step" 15 (.tuple [
      configV hn ⟨s, f, [constI32 i, vconst c, .plain (.vecStore ao)]⟩, configV hn ⟨s, f, [.trap]⟩]) := by
  let σ := vstoreScope (hn := hn) s f i c ao
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV c.toNat) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match vstoreOobRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons fc (typedV_vecV128_20 c _ hρ) (QuantsOk.cons fa (typedV_memarg20 ao _ hρ)
        QuantsOk.nil)))
  have hl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
        .caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c"]),
        .caseE "VSTORE" (.tupE [.caseE "V128" (.tupE []), .varE "ao"])]]))
      (configV hn ⟨s, f, [constI32 i, vconst c, .plain (.vecStore ao)]⟩) := by
    refine evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_listE_iff.2 ⟨_, evalExps_cons
      (evalExp_constIE fi) (evalExps_cons (evalExp_vconstE fc) (evalExps_cons
        (evalExp_case (evalExp_tup2 (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
          (evalExp_var fa))) evalExps_nil)), ?_⟩))
    rfl
  refine Pure.fires_of_ruleAt hasRuleAt_vstoreOob σ hq (evalExp_tup2 hl (evalExp_zTrap fz)) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (prem_of_trap rfl fz fi fa (evalExp_sizeV128 rfl) (by decide) ha hm hlt)

/-- The scope of rule 17. -/
abbrev vstoreLaneScope (s : Store H) (f : Frame) (i : BitVec 32) (c : BitVec 128) (sz : PackSize)
    (ao : V2.MemArg) (j : LaneIdx) : List (IL.Id × Value) :=
  [("z", stateV hn s f), ("i", pctV i.toNat), ("c", pctV c.toNat),
    ("N", .num (.natN sz.width)), ("ao", memargV ao), ("j", pctV j.val)]

/-- **`Step/vstore_lane-oob` fires forward** at the image of V2's `vecStoreLaneOob`. -/
theorem fires_vstoreLaneOob {s : Store H} {f : Frame} {sz : PackSize} {ao : V2.MemArg}
    {j : LaneIdx} {i : BitVec 32} {c : BitVec 128} {ad : MemAddr} {mi : MemInst}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hlt : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) :
    Fires (simEnv20 B) "Step" 17 (.tuple [
      configV hn ⟨s, f, [constI32 i, vconst c, .plain (.vecStoreLane sz ao j)]⟩,
      configV hn ⟨s, f, [.trap]⟩]) := by
  let σ := vstoreLaneScope (hn := hn) s f i c sz ao j
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV c.toNat) := rfl
  have fN : (VarEnv.empty.bindVals σ).findVal? "N" = some (.num (.natN sz.width)) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV j.val) := rfl
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match vstoreLaneOobRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons fc (typedV_vecV128_20 c _ hρ) (QuantsOk.cons fN (typedV_N20 _ _ hρ)
        (QuantsOk.cons fa (typedV_memarg20 ao _ hρ) (QuantsOk.cons fj (typedV_laneidx20 j _ hρ)
          QuantsOk.nil)))))
  have hsz : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (.caseE "%" (.tupE [.varE "N"]))
      (szV sz) :=
    evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_var fN) evalExps_nil, rfl⟩)
  have hl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
        .caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c"]),
        .caseE "VSTORE_LANE" (.tupE [.caseE "V128" (.tupE []), .caseE "%" (.tupE [.varE "N"]),
          .varE "ao", .varE "j"])]]))
      (configV hn ⟨s, f, [constI32 i, vconst c, .plain (.vecStoreLane sz ao j)]⟩) := by
    refine evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_listE_iff.2 ⟨_, evalExps_cons
      (evalExp_constIE fi) (evalExps_cons (evalExp_vconstE fc) (evalExps_cons
        (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons
          (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)) (evalExps_cons hsz
            (evalExps_cons (evalExp_var fa) (evalExps_cons (evalExp_var fj) evalExps_nil))),
          rfl⟩)) evalExps_nil)), ?_⟩))
    rfl
  refine Pure.fires_of_ruleAt hasRuleAt_vstoreLaneOob σ hq (evalExp_tup2 hl (evalExp_zTrap fz)) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (prem_of_trap rfl fz fi fa (evalExp_var fN) (packWidth_cases sz) ha hm hlt)

/-! ## The value rules do not fire at `growB`-like builtins -/

/-- **A rule with an inert premise does not fire** at any builtins keeping the byte and lane
primitives inert (pass 6's `not_fires_inert`, generalised from `floatIntB`). -/
theorem not_fires_inert20 (E : InertEnv (simEnv20 B)) {x : IL.Id} {l : List Nat}
    (hok : inertOk x l = true) {i : Nat} (hi : i ∈ l) {v : Value} :
    ¬ Fires (simEnv20 B) x i v := by
  rintro ⟨t, rules, r, hrel, hr, hb⟩
  have hrules : relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed) x = rules := by
    rw [← relRules_simEnv20 B]
    simp [relRules, hrel]
  have h₁ := List.all_eq_true.1 hok i hi
  rw [hrules, hr] at h₁
  exact not_body_inert E h₁ hb

/-- `Step/vstore-val` (16) never fires at `growB`-like builtins. -/
theorem not_fires_vstoreVal_growLike {P : Profile} (hB : GrowLike20 P B) {v : Value} :
    ¬ Fires (simEnv20 B) "Step" 16 v :=
  not_fires_inert20 hB.inert inertStep20_ok (by decide)

/-- `Step/vstore_lane-val` (18) never fires at `growB`-like builtins. -/
theorem not_fires_vstoreLaneVal_growLike {P : Profile} (hB : GrowLike20 P B) {v : Value} :
    ¬ Fires (simEnv20 B) "Step" 18 v :=
  not_fires_inert20 hB.inert inertStep20_ok (by decide)

/-! ## The fragment and the target -/

/-- **The top-level steps the forward half covers, with the vector-store traps**: `TopVarStep20`
and V2's `vecStoreOob` and `vecStoreLaneOob`, with their premises. -/
inductive TopVStep20 (P : Profile) : Config H → Config H → Prop where
  | var {c c' : Config H} (h : TopVarStep20 P c c') : TopVStep20 P c c'
  | vecStoreOob {s : Store H} {f : Frame} {ao : V2.MemArg} {i : BitVec 32} {c : BitVec 128}
      {a : MemAddr} {mi : MemInst} (ha : f.module.memAddr? memIdx0 = some a)
      (hm : s.memInst? a = some mi) (h : mi.bytes.size < effAddr i.toNat ao + 16) :
      TopVStep20 P ⟨s, f, [constI32 i, vconst c, .plain (.vecStore ao)]⟩ ⟨s, f, [.trap]⟩
  | vecStoreLaneOob {s : Store H} {f : Frame} {sz : PackSize} {ao : V2.MemArg} {j : LaneIdx}
      {i : BitVec 32} {c : BitVec 128} {a : MemAddr} {mi : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (h : mi.bytes.size < effAddr i.toNat ao + sz.width / 8) :
      TopVStep20 P ⟨s, f, [constI32 i, vconst c, .plain (.vecStoreLane sz ao j)]⟩
        ⟨s, f, [.trap]⟩

/-- Every step of the fragment is a V2 step. -/
theorem TopVStep20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : TopVStep20 P c c') : Step P host c c' := by
  cases h with
  | var h => exact h.step
  | vecStoreOob ha hm h => exact .vecStoreOob ha hm h
  | vecStoreLaneOob ha hm h => exact .vecStoreLaneOob ha hm h

/-- **The forward half on the fragment**, at builtins answering V2's growth. -/
theorem fwd_topVStep20 {P : Profile} (hG : GrowCalls20 B) {c c' : Config H}
    (hc : Typed20 (simEnv20 B) hn c) (hw : WholePages c.store) (h : TopVStep20 P c c') :
    SStepB (simEnv20 B) (configV hn c) (configV hn c') := by
  have hz := typedV_state_of_typed20 hc
  cases h with
  | var h => exact fwd_topVarStep20 hG hc hw h
  | vecStoreOob ha hm h => exact sstepB_of_fires20 (fires_vstoreOob hz ha hm h)
  | vecStoreLaneOob ha hm h => exact sstepB_of_fires20 (fires_vstoreLaneOob hz ha hm h)

/-- **`Task.wholeStepTopVar20` with the vector-store traps** (proved below). -/
def Task.wholeStepTopVS20 : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
      GrowLike20 (Profile.spec nd r) B ∧
      (∀ c c' : Config H, Typed20 (simEnv20 B) hn c → WholePages c.store →
        TopVStep20 (Profile.spec nd r) c c' →
        SStepB (simEnv20 B) (configV hn c) (configV hn c')) ∧
      (∀ (c : Config H) (w : Value), GoodW c → SStepB (simEnv20 B) (configV hn c) w →
        ∃ c', w = configV hn c' ∧ Step (Profile.spec nd r) host c c')

/-- **`Task.wholeStepTopVS20` holds**, at `growB`. -/
theorem wholeStepTopVS20 : Task.wholeStepTopVS20 := by
  intro H hn _ host nd r
  refine ⟨growB (Profile.spec nd r), growLike20_growB _, fun c c' hc hw h => ?_,
    fun c w hg hs => wholeStepBwdW_growB nd r c w hg hs⟩
  exact fwd_topVStep20 (growCalls20_growB _) hc hw h

end Silmaril.Wasm.SpecTec.Sim20.Whole
