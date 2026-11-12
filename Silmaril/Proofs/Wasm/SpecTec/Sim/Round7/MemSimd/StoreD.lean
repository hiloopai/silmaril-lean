module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.ReadMS
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.MemSimd.WithMemRes

/-!
# Round 7, memory SIMD: the vector stores as obligations of the generic dispatch at `configVD`

`BackwardUpToD.step` asks, for every store-changing rule `i` of `Step`, that a firing at the
`configVD` image of a configuration be the image of a Core step. This file discharges it for the
four memory SIMD stores (`stepMSRules`, `Step` 22–25), for every configuration:

* `bwd_vstoreValF`, `bwd_vstoreLaneValF`: rules 23 and 25 backward at `stateVF F s f`, with the
  memory recovered from the firing rule (`withMem_resolvesF`) instead of assumed, and the
  successor store's function list kept (`s'.funcs = s.funcs`), so that the successor state is the
  `stateVD` image of the successor store. Rules 22 and 24 (`bwd_vstoreOob`, `bwd_vstoreLaneOob`)
  are stated at `stateVF` since this pass and keep the store;
* `decode_vstoreD`: a vector store rule fires only at the image of `CONST at i; VCONST c; s` with
  `s` headed by the rule's store constructor;
* `stepMSD`: **the four obligations**;
* `backwardUpToD_of_restS`, `backward_upToD_restS`: the generic dispatch at `configVD` with every
  memory SIMD rule plugged in (loads by `readMSD`, stores by `stepMSD`), from the obligations
  `BackwardUpToDRestS` of the rules without memory SIMD.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV)
open FwdMem (bytesV leBytesV)
open Silmaril.SpecTec.Equiv.ExecStepRules (hasStepRules_wasm30)

variable {H : Type} {hn : H → String} {F : Value}

/-! ## Rules 23 and 25 at `stateVF`, with the memory recovered -/

/-- **`Step/vstore-val`, backward, at `stateVF`**: the rule resolves the memory, the result is the
image of Core's store, which keeps the store's functions, and Core's `vecStoreVal` steps there. -/
theorem bwd_vstoreValF {B : Builtins} (Vb : VBytes (simEnv B))
    (hwm : ∀ ws, B.call "with_mem" ws = none) {P : Numerics.Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {x : MemIdx} {arg : MemArg} {a : AddrType}
    {i : BitVec a.intType.width} {c : BitVec 128} {w : Value}
    (hf : Fires (simEnv B) "Step" 23 (.tuple [cfgV (stateVF F s f) [adminToV (aconst a i),
      valV (.vec c), Round6.MemSimd.instrToVM (.vecStore x arg)], w])) :
    ∃ s', s'.funcs = s.funcs ∧ w = cfgV (stateVF F s' f) [] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecStore x arg)]⟩
        ⟨s', f, []⟩ := by
  rw [State.adminToV_aconst, instrToVM_vecStore] at hf
  obtain ⟨σ, fz, hes, hr, hp⟩ := fires_cfg
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.vstoreVal |> hasRuleAt_simEnv B) hf
  have h₁ := RefsGC.evalExps_cons_inv hes
  have h₂ := RefsGC.evalExps_cons_inv h₁.2
  obtain ⟨fx, fao⟩ := vstore_fvs (RefsGC.evalExps_cons_inv h₂.2).1
  have fc := fc_of_vconst h₂.1
  obtain ⟨V, e₁, e₂⟩ := Bwd.eq_of_cmp (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
  have eV : V = .list (leBytesV 16 c.toNat) := Applies.unique ((applies_iff_callDef
    (Prims.findDef_none_of_valsOnly ⟨rfl, rfl, rfl⟩ _) (Equiv.evalArgs_cons evalExp_v128
      (Equiv.evalArgs_cons (evalExp_var fc) Equiv.evalArgs_nil))).2 (evalExp_callE_iff.1 e₂)) (Vb c)
  subst eV
  obtain ⟨W, hW, rfl⟩ := BwdPureStep.rhs_nil hr
  obtain ⟨ma, mi, hm⟩ := withMem_resolvesF hwm ⟨rfl, rfl, rfl⟩ fz fx (Memory.evalExp_effAddr
    (evalExp_var (fi_of_aconst h₁.1)) (evalExp_var fao)) (evalExp_vsize8 (B := B)) e₁ hW
  obtain ⟨b, hs, rfl⟩ := withMem_store' (w := c) (k := 16) hwm fz fx (fi_of_aconst h₁.1) fao hm
    (evalExp_vsize8 (B := B)) e₁ hW
  exact ⟨s.setMem ma { mi with bytes := b }, rfl, rfl, .memory (.vecStoreVal hm hs)⟩

/-- **`Step/vstore_lane-val`, backward, at `stateVF`** (at `withVBytes (Prims.builtins …)`): the
rule resolves the memory, the result is the image of Core's lane store, which keeps the store's
functions, and Core's `vecStoreLaneVal` steps there. -/
theorem bwd_vstoreLaneValF {P : Numerics.Profile} {host : HostSemantics H} {s : Store H}
    {f : Frame} {sz : PackSize} {x : MemIdx} {arg : MemArg} {j : LaneIdx} {a : AddrType}
    {i : BitVec a.intType.width} {c : BitVec 128} {w : Value}
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step" 25
      (.tuple [cfgV (stateVF F s f) [adminToV (aconst a i), valV (.vec c),
        Round6.MemSimd.instrToVM (.vecStoreLane sz x arg j)], w])) :
    ∃ s', s'.funcs = s.funcs ∧ w = cfgV (stateVF F s' f) [] ∧
      Step P host ⟨s, f, [aconst a i, .plain (.vecConst c), .plain (.vecStoreLane sz x arg j)]⟩
        ⟨s', f, []⟩ := by
  rw [State.adminToV_aconst, instrToVM_vecStoreLane] at hf
  obtain ⟨σ, fz, hes, hr, hp⟩ := fires_cfg
    (Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30.vstoreLaneVal |>
      hasRuleAt_simEnv _) hf
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  obtain ⟨fi, fc, fN, fx, fao, fj⟩ := vstoreLaneLhs_inv hes
  obtain ⟨V, eb, ecall⟩ := Bwd.eq_of_cmp (RefsGC.premW_if (hp _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))
  obtain ⟨sh, fJ, -, hV⟩ := ibytesLane_inv hρ fN fc fj ecall
  obtain rfl : sz = packOf sh :=
    packOf_of_jsize hρ fN fJ (RefsGC.premW_if (hp _ (List.mem_cons_self ..)))
  obtain ⟨W, hW, rfl⟩ := BwdPureStep.rhs_nil hr
  have hw8 : (packOf sh).width = 8 ∨ (packOf sh).width = 16 ∨ (packOf sh).width = 32 ∨
      (packOf sh).width = 64 := by cases sh <;> simp [packOf, PackSize.width]
  have hV' : V = .list (leBytesV ((packOf sh).width / 8)
      (((Numerics.lanes (packOf sh).width (128 / (packOf sh).width) c).getD j.val 0).setWidth
        (8 * ((packOf sh).width / 8))).toNat) := by
    rw [toNat_lane_setWidth]; exact hV
  obtain ⟨ma, mi, hm⟩ := withMem_resolvesF call_withMem_vb hρ fz fx
    (Memory.evalExp_effAddr (evalExp_var fi) (evalExp_var fao))
    (Memory.evalExp_div8 hw8 (evalExp_var fN)) (hV' ▸ eb) hW
  obtain ⟨b, hs, rfl⟩ := withMem_store' (k := (packOf sh).width / 8)
    (w := ((Numerics.lanes (packOf sh).width (128 / (packOf sh).width) c).getD j.val 0).setWidth
      (8 * ((packOf sh).width / 8)))
    call_withMem_vb fz fx fi fao hm (Memory.evalExp_div8 hw8 (evalExp_var fN)) (hV' ▸ eb) hW
  exact ⟨s.setMem ma { mi with bytes := b }, rfl, rfl, .memory (.vecStoreLaneVal hm hs)⟩

/-! ## The left-hand sides, decoded -/

theorem head_vecStore {a : Admin} (h : Typing.adminHead a = "VSTORE") :
    ∃ x arg, a = .plain (.vecStore x arg) := by
  revert h
  admin_head_inv

theorem head_vecStoreLane {a : Admin} (h : Typing.adminHead a = "VSTORE_LANE") :
    ∃ p x arg j, a = .plain (.vecStoreLane p x arg j) := by
  revert h
  admin_head_inv

/-- **A vector store rule fires only at the image of `CONST at i; VCONST c; s`**, with `s` headed
by the rule's third constructor. -/
theorem decode_vstoreD {B : Builtins} {k : Nat} {nm : IL.Id} {qs : List Param} {e₂ e₃ rh : Exp}
    {op : MixopS} {prems : List Prem} {Z : Value} {code : List Admin} {w : Value}
    (h : Equiv.Validation.HasRuleAt (simEnv B) "Step" "%~>%" k (.ruleD nm qs "%~>%"
      (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [.caseE "CONST" (.tupE [.subE (.varE "at")
        (.varT "addrtype" []) (.varT "numtype" []), .varE "i"]), .caseE "VCONST" e₂,
        .caseE op e₃]]), rh]) prems))
    (hat : Param.expP "at" (.varT "addrtype" []) ∈ qs)
    (hf : Fires (simEnv B) "Step" k (.tuple [cfgV Z (adminsToVD code), w])) :
    ∃ (a : AddrType) (b : BitVec a.intType.width) (c : BitVec 128) (a₃ : Admin),
      code = [aconst a b, .plain (.vecConst c), a₃] ∧ Typing.adminHead a₃ = op := by
  obtain ⟨σ, hq, he, -⟩ := State.Fires.rule_eq h hf
  obtain ⟨-, hc⟩ := RefsGC.cfgz_inv (RefsGC.lhs_of_concl he)
  obtain ⟨v₁, l₁, h₁, hl₁, hL⟩ := evalExps_cons_iff.1 (RefsGC.elems_of_list hc)
  obtain ⟨v₂, l₂, h₂, hl₂, rfl⟩ := evalExps_cons_iff.1 hl₁
  obtain ⟨v₃, l₃, h₃, hl₃, rfl⟩ := evalExps_cons_iff.1 hl₂
  obtain rfl := evalExps_nil_iff.1 hl₃
  obtain ⟨a₁, a₂, a₃, rfl, ha₁, ha₂, ha₃⟩ := adminsToVD_eq_triple hL
  obtain ⟨u₃, -, hv₃⟩ := evalExp_caseE_iff.1 h₃
  obtain ⟨u₂, -, hv₂⟩ := evalExp_caseE_iff.1 h₂
  obtain ⟨c, rfl⟩ := head_vconst (adminToVD_case (ha₂.trans hv₂)).symm
  obtain ⟨u₁, hu₁, hv₁⟩ := evalExp_caseE_iff.1 h₁
  obtain ⟨AT, I, rfl, hAT, -⟩ := Vec.inv_tup2 hu₁
  obtain ⟨AT', fat, hT⟩ := hq "at" _ hat
  have hA : AT' = AT :=
    Option.some.inj (fat.symm.trans (evalExp_varE_iff.1 (evalExp_subE_iff.1 hAT)))
  obtain ⟨t, b, rfl⟩ := decode_aconstD ⟨rfl, rfl, rfl⟩ (ha₁.trans hv₁) (hA ▸ hT)
  exact ⟨t, b, c, a₃, rfl, (adminToVD_case (ha₃.trans hv₃)).symm⟩

/-! ## The four obligations -/

/-- The `configVD` image of a vector store redex, at `stateVF`. -/
theorem configVD_store3 (s : Store H) (f : Frame) (a : AddrType) (b : BitVec a.intType.width)
    (c : BitVec 128) {j : Instr} (hj : Round6.MemSimd.memSimd j = true) :
    configVD hn ⟨s, f, [aconst a b, .plain (.vecConst c), .plain j]⟩ =
      cfgV (stateVF (.list (s.funcs.map (funcInstVD hn))) s f)
        [adminToV (aconst a b), valV (.vec c), Round6.MemSimd.instrToVM j] := by
  have e₁ : adminToVD (aconst a b) = adminToV (aconst a b) := adminToVD_eq _ (by
    cases a <;> exact rfl)
  have e₃ : adminToVD (.plain j) = Round6.MemSimd.instrToVM j := instrToVD_memSimd hj
  show cfgV _ [adminToVD (aconst a b), adminToVD (.plain (.vecConst c)), adminToVD (.plain j)] = _
  rw [e₁, e₃]
  rfl

/-- A successor with the same functions is a `configVD` image at the source's function list. -/
theorem bwdUpTo_of_funcs {P : Numerics.Profile} {host : HostSemantics H} {c : Config H}
    {s' : Store H} {w : Value} (he : s'.funcs = c.store.funcs)
    (hw : w = cfgV (stateVF (.list (c.store.funcs.map (funcInstVD hn))) s' c.frame) [])
    (hs : Step P host c ⟨s', c.frame, []⟩) : BwdUpToD hn P host c w :=
  ⟨_, _, Bwd.ConfigEq.refl _, by rw [hw, ← he]; rfl, hs⟩

section Rules

variable {P : Numerics.Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
  {code : List Admin} {w : Value}

/-- `Step` 22 (`vstore-oob`) at a `configVD` image. -/
theorem stepMSD_22
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step" 22
      (.tuple [configVD hn ⟨s, f, code⟩, w])) : BwdUpToD hn P host ⟨s, f, code⟩ w := by
  obtain ⟨a, b, cv, a₃, rfl, h₃⟩ := decode_vstoreD (
    hasStepRules_wasm30.vstoreOob |> hasRuleAt_simEnv _) (by simp) hf
  obtain ⟨x, arg, rfl⟩ := head_vecStore h₃
  rw [configVD_store3 s f a b cv rfl] at hf
  obtain ⟨rfl, hs⟩ := bwd_vstoreOob call_mem_vb hf
  exact ⟨_, _, Bwd.ConfigEq.refl _, rfl, hs⟩

/-- `Step` 23 (`vstore-val`) at a `configVD` image. -/
theorem stepMSD_23
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step" 23
      (.tuple [configVD hn ⟨s, f, code⟩, w])) : BwdUpToD hn P host ⟨s, f, code⟩ w := by
  obtain ⟨a, b, cv, a₃, rfl, h₃⟩ := decode_vstoreD (
    hasStepRules_wasm30.vstoreVal |> hasRuleAt_simEnv _) (by simp) hf
  obtain ⟨x, arg, rfl⟩ := head_vecStore h₃
  rw [configVD_store3 s f a b cv rfl] at hf
  obtain ⟨s', he, hw, hs⟩ := bwd_vstoreValF (vBytes_withVBytes _) call_withMem_vb hf
  exact bwdUpTo_of_funcs he hw hs

/-- `Step` 24 (`vstore_lane-oob`) at a `configVD` image. -/
theorem stepMSD_24
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step" 24
      (.tuple [configVD hn ⟨s, f, code⟩, w])) : BwdUpToD hn P host ⟨s, f, code⟩ w := by
  obtain ⟨a, b, cv, a₃, rfl, h₃⟩ := decode_vstoreD (
    hasStepRules_wasm30.vstoreLaneOob |> hasRuleAt_simEnv _) (by simp) hf
  obtain ⟨p, x, arg, j, rfl⟩ := head_vecStoreLane h₃
  rw [configVD_store3 s f a b cv rfl] at hf
  obtain ⟨rfl, hs⟩ := bwd_vstoreLaneOob call_mem_vb hf
  exact ⟨_, _, Bwd.ConfigEq.refl _, rfl, hs⟩

/-- `Step` 25 (`vstore_lane-val`) at a `configVD` image. -/
theorem stepMSD_25
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step" 25
      (.tuple [configVD hn ⟨s, f, code⟩, w])) : BwdUpToD hn P host ⟨s, f, code⟩ w := by
  obtain ⟨a, b, cv, a₃, rfl, h₃⟩ := decode_vstoreD (
    hasStepRules_wasm30.vstoreLaneVal |> hasRuleAt_simEnv _) (by simp) hf
  obtain ⟨p, x, arg, j, rfl⟩ := head_vecStoreLane h₃
  rw [configVD_store3 s f a b cv rfl] at hf
  obtain ⟨s', he, hw, hs⟩ := bwd_vstoreLaneValF hf
  exact bwdUpTo_of_funcs he hw hs

end Rules

/-- **The memory SIMD store obligations of the dispatch at `configVD`**, at
`withVBytes (Prims.builtins …)`, for every configuration: if one of `Step` 22–25 fires at the
`configVD` image, the result is the image of a configuration equivalent to a Core successor. -/
theorem stepMSD {P : Numerics.Profile} {host : HostSemantics H} {i : Nat} (hi : i ∈ stepMSRules)
    (c : Config H) (w : Value)
    (hf : Fires (simEnv (withVBytes (Prims.builtins P hn host))) "Step" i
      (.tuple [configVD hn c, w])) : BwdUpToD hn P host c w := by
  have h4 : i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 := by
    simpa only [stepMSRules, List.mem_cons, List.not_mem_nil, or_false] using hi
  rcases h4 with rfl | rfl | rfl | rfl
  · exact stepMSD_22 hf
  · exact stepMSD_23 hf
  · exact stepMSD_24 hf
  · exact stepMSD_25 hf

/-! ## The dispatch with every memory SIMD rule plugged in -/

/-- **The per-rule obligations at `configVD` from those of the rules without memory SIMD**: the
loads are `readMSD`, the stores `stepMSD`. -/
theorem backwardUpToD_of_restS {P : Numerics.Profile} {host : HostSemantics H}
    {V : Config H → Prop}
    (Rk : BackwardUpToDRestS V (simEnv (withVBytes (Prims.builtins P hn host))) hn P host) :
    BackwardUpToD V (simEnv (withVBytes (Prims.builtins P hn host))) hn P host where
  pure := Rk.pure
  read i c w hv hc hf := by
    by_cases hi : i ∈ msReadRules
    · exact readMSD hi c w hf
    · exact Rk.read i hi c w hv hc hf
  step i h6 c w hv hc hf := by
    by_cases hi : i ∈ stepMSRules
    · exact stepMSD hi c w hf
    · exact Rk.step i h6 hi c w hv hc hf

/-- **Round 6's backward recursion at `configVD`, with every memory SIMD rule discharged**
(`Step_read` 42–51 and `Step` 22–25), under any context-closed predicate: a declarative SpecTec
step from the `configVD` image of a typed configuration is the image of a configuration
equivalent to a Core successor, given the obligations of the rules without memory SIMD. -/
theorem backward_upToD_restS {P : Numerics.Profile} {host : HostSemantics H}
    {V : Config H → Prop} (CV : Round6.Target.CtxClosedVals V)
    (Rk : BackwardUpToDRestS V (simEnv (withVBytes (Prims.builtins P hn host))) hn P host)
    (c : Config H) (w : Value) (hv : V c)
    (hc : TypedD (simEnv (withVBytes (Prims.builtins P hn host))) hn c)
    (hs : SStep (simEnv (withVBytes (Prims.builtins P hn host))) (configVD hn c) w) :
    BwdUpToD hn P host c w :=
  backward_upToD CV (backwardUpToD_of_restS Rk) (structDecodeD_simEnv _)
    (typingFactsD_simEnv _ hn) (hasStepRules_simEnv _)
    (Bwd.findRel_of_ruleAt (simEnv_execRules _).unreachable)
    (Bwd.findRel_of_ruleAt (simEnv_readRules _).call) c w hv hc hs

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
