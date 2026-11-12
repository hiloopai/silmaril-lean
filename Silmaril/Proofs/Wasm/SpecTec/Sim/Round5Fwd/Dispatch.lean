module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.Bnd

/-!
# Round 5: the instruction families at the concrete `B`, without refuted bundles

For `B := Prims.builtins P hn host`, the forward cases of every rule family whose earlier
proof did not consume a refuted field, with each family structure taken from its proof for the
concrete `B` (no `Whole.Assumptions`, no `Integrate.Extra`):

* `fwd_numeric5`: round 2's `Whole.fwd_numeric_covered`, with `IntB` and `TypingFacts` proved;
* `fwd_vector5`: the bitwise vector operators proved, the others from `Obl.vector`;
* `fwd_memory5`: every scalar memory step (round 3's lemmas, with `MemTyping`, `GrowFuns`,
  `InstTyping`, `BytesFuns`, `FloatB` proved); the memory SIMD steps are excluded by `Bounded`;
* `fwd_reference5`: the reference steps, the casts from `Obl.refTest`/`Obl.refCast`;
* `fwd_call5`, `fwd_returnCall5`: `call`, `return_call`, with `$funcinst`/`$moduleinst`
  evaluated directly (the earlier proofs took the whole `CtrlState`, whose `blocktype` field
  needs the refuted `valtypes`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (Bounded)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## The discharged family structures at the concrete `B` -/

/-- `RStoreFuns` for every `simEnv B`'s `Prims.builtins`, with `$inst_reftype` from
`RefOk.instReftype_simEnv` (no `Residual`). -/
theorem rStore_builtins (hn : H → String) (host : HostSemantics H) :
    RefsGC.RStoreFuns (simEnv (BI P hn host)) :=
  have Pd := Prims.projDefs_simEnv (BI P hn host)
  ⟨fun hn' _ _ s f hρ he => evalExp_callArgs (Prims.findDef_none_of_valsOnly hρ _)
      (Equiv.evalArgs_cons he Equiv.evalArgs_nil) (Prims.applies_moduleinst Pd hn' s f),
    fun hn' _ _ s f hρ he => evalExp_callArgs (Prims.findDef_none_of_valsOnly hρ _)
      (Equiv.evalArgs_cons he Equiv.evalArgs_nil) (Prims.applies_arrayinst Pd hn' s f),
    fun hn' _ _ s f hρ he => evalExp_callArgs (Prims.findDef_none_of_valsOnly hρ _)
      (Equiv.evalArgs_cons he Equiv.evalArgs_nil) (Prims.applies_structinst Pd hn' s f),
    fun hn' ρ ez ey s f y ea ei hρ h hz hy =>
      Prims.evalExp_elem_stateV (State.stateDefs_simEnv _) hn' ρ ez ey s f y ea ei h
        (Prims.findDef_none_of_valsOnly hρ _) hz hy,
    fun ρ e₁ e₂ m rt hρ =>
      RefOk.instReftype_simEnv _ ρ e₁ e₂ m rt (Prims.findDef_none_of_valsOnly hρ _)⟩

/-! ## Numeric and vector steps -/

/-- The numeric steps (`Whole.fwd_numeric_covered`, with the structures proved). -/
theorem fwd_numeric5 {s : Store H} {f : Frame} {is is' : List Admin} (h : NumericStep P is is') :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  have hI : IntNumeric.IntB (BI P hn host) := Prims.intB_builtins hn host
  have hF : Floats.FloatB P (BI P hn host) := Prims.floatB_builtins hn host
  have TY : IntNumeric.IntTyping (simEnv (BI P hn host)) := IntNumeric.intTyping_simEnv _
  have Fy : Vec.FloatTyping (simEnv (BI P hn host)) := Floats.floatTyping_simEnv _
  have FA : Vec.FloatAgree (simEnv (BI P hn host)) P := Floats.floatAgree_simEnv hF
  have hr : HasRuleAt (simEnv (BI P hn host)) "Step" "%~>%" 0
      Silmaril.SpecTec.Equiv.ExecStepRules.pureRule := (hasStepRules_simEnv _).pure
  have N : Silmaril.SpecTec.Equiv.ExecNumeric.HasNumericRules (simEnv (BI P hn host)) :=
    Vec.hasNumericRules_simEnv _
  cases h with
  | @intUnOp t op x =>
    exact if hv : op.valid t = true then IntNumeric.fwd_intUnOp hI TY T hv
      else IntNumeric.fwd_intUnOp_invalid T (by simpa using hv)
  | intBinOp hz => exact IntNumeric.fwd_intBinOp hI TY T hz
  | intBinOpTrap he => exact IntNumeric.fwd_intBinOpTrap hI TY T he
  | intTestOp => exact IntNumeric.fwd_intTestOp TY T
  | intRelOp => exact IntNumeric.fwd_intRelOp TY T
  | floatUnOp hz => exact Vec.fwd_floatUnOp T hr N Fy FA hz
  | floatBinOp hz => exact Vec.fwd_floatBinOp T hr N Fy FA hz
  | floatRelOp => exact Vec.fwd_floatRelOp T hr N Fy FA
  | convert hz => exact Vec.fwd_convert T hr N Fy FA hz
  | convertTrap he => exact Vec.fwd_convertTrap T hr N Fy FA he

/-- The vector steps: the bitwise operators proved, the others from `Obl.vector`. -/
theorem fwd_vector5 (O : Obl (BI P hn host) hn P host) {s : Store H} {f : Frame}
    {is is' : List Admin} (h : VectorStep P is is') (hb : Bounded ⟨s, f, is⟩) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  have hV := FwdSimdAgg.vvB_builtins (prof := P) hn host
  have h' := h
  cases h with
  | vecUnOp op a => exact FwdSimdAgg.fwd_vecUnOp hV op a
  | vecBinOp op a b => exact FwdSimdAgg.fwd_vecBinOp (Prims.intB_builtins hn host) hV op a b
  | vecTernOp op a b c => exact FwdSimdAgg.fwd_vecTernOp hV op a b c
  | vecTestOp op a => exact FwdSimdAgg.fwd_vecTestOp op a
  | _ => exact O.vector _ _ _ _ h' (by simp [R4Fwd.VecArith, vconst]) hb

/-! ## Memory steps -/

/-- The memory steps: every scalar constructor proved; the memory SIMD constructors do not
start from a bounded configuration. -/
theorem fwd_memory5 {c c' : Config H} (h : MemoryStep P c c') (hb : Bounded c) :
    FwdP (simEnv (BI P hn host)) hn c c' := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have St : State.StateTyping (simEnv (BI P hn host)) := Typing.stateTyping_simEnv _
  have Mt : Memory.MemTyping (simEnv (BI P hn host)) := ConfigOk.memTyping_simEnv _
  have Gr : Memory.GrowFuns (simEnv (BI P hn host)) := RefOk.growFuns_builtins hn host
  have In : Memory.InstTyping (simEnv (BI P hn host)) := ConfigOk.instTyping_simEnv _
  have Bf : FwdMem.BytesFuns (simEnv (BI P hn host)) := FwdMem.bytesFuns_builtins P hn host
  have hF : Floats.FloatB P (BI P hn host) := Prims.floatB_builtins hn host
  have hT' : FwdMem.SliceTotal := FwdMem.sliceTotal
  have hs : Integrate.StoreOk c.store := hb.store
  have hx : (∃ i, Admin.plain i ∈ c.code ∧ R4Fwd.VecMemI i = true) → False :=
    fun ⟨_, hi, hv⟩ => not_vecMem hb.code hi hv
  cases h with
  | loadIntOob hm h₁ => exact Memory.fwd_loadIntOob _ T St Mt hm h₁
  | loadIntVal hm hl => exact FwdMem.fwd_loadIntVal _ T St Mt Bf (.inl hT') hm hl
  | loadPackOob hm h₁ => exact Memory.fwd_loadPackOob _ T St Mt hm h₁
  | loadPackVal hm hl => exact FwdMem.fwd_loadPackVal _ T St Mt Bf hF (.inl hT') hm hl
  | loadFloatOob hm h₁ => exact Memory.fwd_loadFloatOob _ T St Mt hm h₁
  | loadFloatVal hm hl => exact FwdMem.fwd_loadFloatVal _ T St Mt Bf (.inl hT') hm hl
  | storeIntOob hm h₁ => exact Memory.fwd_storeIntOob _ T St Mt hm h₁
  | storeIntVal hm h₁ => exact FwdMem.fwd_storeIntVal _ T St Mt Bf (.inl hT') hm h₁
  | storePackOob hm h₁ => exact Memory.fwd_storePackOob _ T St Mt hm h₁
  | storePackVal hm h₁ => exact FwdMem.fwd_storePackVal _ T St Mt Bf hF (.inl hT') hm h₁
  | storeFloatOob hm h₁ => exact FwdMem.fwd_storeFloatOob _ T St Mt hm h₁
  | storeFloatVal hm h₁ => exact FwdMem.fwd_storeFloatVal _ T St Mt Bf (.inl hT') hm h₁
  | size hm =>
    exact Memory.fwd_memorySize _ T St Mt hm (hs.mem hm).1 (Integrate.pages_lt (hs.mem hm).2 _)
  | growSucceed hm hg _ =>
    exact Memory.fwd_memoryGrowSucceed _ T St Gr In hm hg (hs.mem hm).1
      (Integrate.pages_lt (hs.mem hm).2 _)
  | growFail hm hp => exact State.fwd_memoryGrowFail _ T St hm hp
  | fillOob hm h₁ => exact Memory.fwd_memoryFillOob _ T St hm h₁
  | fillZero hm h₁ => exact Memory.fwd_memoryFillZero _ T St hm h₁
  | @fillSucc s f x a i n v ma mi hm h₁ hnz =>
    exact Memory.fwd_memoryFillSucc _ T St hm h₁ hnz
      (Integrate.succ_lt a hnz h₁ (hs.mem hm).2)
  | copyOob h₁ h₂ h₃ => exact Memory.fwd_memoryCopyOob _ T St h₁ h₂ h₃
  | copyZero h₁ h₂ h₃ => exact Memory.fwd_memoryCopyZero _ T St h₁ h₂ h₃
  | @copyLe s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ h₃ hnz hle =>
    exact Memory.fwd_memoryCopyLe _ T St h₁ h₂ h₃ hnz hle
      ⟨Integrate.succ_lt a₁ hnz h₃.1 (hs.mem h₁).2, Integrate.succ_lt a₂ hnz h₃.2 (hs.mem h₂).2⟩
  | @copyGt s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ma₁ ma₂ mi₁ mi₂ h₁ h₂ h₃ hnz hgt =>
    exact Memory.fwd_memoryCopyGt _ T St h₁ h₂ h₃ hnz hgt
      ⟨Integrate.add_le_pow a₁ h₃.1 (hs.mem h₁).2, Integrate.add_le_pow a₂ h₃.2 (hs.mem h₂).2⟩
  | initOob hm hd h₁ => exact Memory.fwd_memoryInitOob _ T St hm hd h₁
  | initZero hm hd h₁ => exact Memory.fwd_memoryInitZero _ T St hm hd h₁
  | @initSucc s f x y a i j n ma da mi di byte hm hd h₁ hnz hby =>
    exact Memory.fwd_memoryInitSucc _ T St hm hd h₁ hnz hby
      ⟨Integrate.succ_lt a hnz h₁.1 (hs.mem hm).2, Integrate.succ_lt .i32 hnz h₁.2 (hs.data hd)⟩
  | dataDrop h₁ => exact State.fwd_dataDrop _ T St h₁
  | _ => exact (hx (by simp [R4Fwd.VecMemI, aconst])).elim

/-! ## Reference steps -/

/-- The reference steps (`RefsGC.fwd_reference` without `RefOkBridge`): the casts from
`Obl.refTest`/`Obl.refCast`. -/
theorem fwd_reference5 (O : Obl (BI P hn host) hn P host) {c c' : Config H} (h : RefStep c c')
    (hb : Bounded c) : FwdP (simEnv (BI P hn host)) hn c c' := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  have R := Typing.rTyping_simEnv (BI P hn host)
  have F : RefsGC.RFuns (simEnv (BI P hn host)) := Prims.rFuns_builtins hn host
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := rStore_builtins hn host
  have Pr : HasRuleAt (simEnv (BI P hn host)) "Step" "%~>%" 0 Equiv.ExecStepRules.pureRule :=
    (hasStepRules_simEnv _).pure
  have Q : HasRuleAt (simEnv (BI P hn host)) "Step" "%~>%" 1 Equiv.ExecStepRules.readRule :=
    (hasStepRules_simEnv _).read
  have rr : Equiv.ExecRef.HasRefRules (envOfScript Specs.wasm30) := Equiv.ExecRef.hasRefRules_wasm30
  have rd : Equiv.ExecRead.HasReadRules (envOfScript Specs.wasm30) :=
    Equiv.ExecRead.hasReadRules_wasm30
  have pt := RefsGC.pureTable_simEnv (BI P hn host)
  cases h with
  | refNull ht =>
      exact RefsGC.fwd_of_sread T Q fun hz hc =>
        RefsGC.sread_refNull (hasRuleAt_simEnv _ rd.refNull) R hz hc
  | refFunc ha =>
      exact RefsGC.fwd_of_sread T Q fun hz hc =>
        RefsGC.sread_refFunc (hasRuleAt_simEnv _ rd.refFunc) R G ha hz hc
  | refI31 i =>
      exact RefsGC.fwd_of_spure T Pr fun _ => RefsGC.spure_refI31 (RefsGC.refRule _ rr.refI31) R F i
  | isNullTrue =>
      exact RefsGC.fwd_of_spure T Pr fun hc =>
        RefsGC.spure_isNullTrue (RefsGC.refRule _ rr.refIsNullTrue) (R.ref _ (RefsGC.typed_head T hc))
  | isNullFalse hr =>
      exact RefsGC.fwd_of_spure T Pr fun hc => RefsGC.spure_isNullFalse
        (RefsGC.refRule _ rr.refIsNullFalse) (RefsGC.refRule _ rr.refIsNullTrue) pt hr
        (R.ref _ (RefsGC.typed_head T hc))
  | asNonNullNull =>
      exact RefsGC.fwd_of_spure T Pr fun hc =>
        RefsGC.spure_asNonNullNull (RefsGC.refRule _ rr.refAsNonNullNull)
          (R.ref _ (RefsGC.typed_head T hc))
  | asNonNullAddr hr =>
      exact RefsGC.fwd_of_spure T Pr fun hc => RefsGC.spure_asNonNullAddr
        (RefsGC.refRule _ rr.refAsNonNullAddr) (RefsGC.refRule _ rr.refAsNonNullNull) pt hr
        (R.ref _ (RefsGC.typed_head T hc))
  | eqNull =>
      exact RefsGC.fwd_of_spure T Pr fun hc =>
        RefsGC.spure_eqNull (RefsGC.refRule _ rr.refEqNull) (R.ref _ (RefsGC.typed_head T hc))
  | eqTrue hr =>
      exact RefsGC.fwd_of_spure T Pr fun hc => RefsGC.spure_eqTrue (RefsGC.refRule _ rr.refEqTrue)
        (RefsGC.refRule _ rr.refEqNull) pt hr (R.ref _ (RefsGC.typed_head T hc))
  | eqFalse hr =>
      exact RefsGC.fwd_of_spure T Pr fun hc => RefsGC.spure_eqFalse
        (RefsGC.refRule _ rr.refEqFalse) (RefsGC.refRule _ rr.refEqNull)
        (RefsGC.refRule _ rr.refEqTrue) pt hr (R.ref _ (RefsGC.typed_head T hc))
        (R.ref _ (RefsGC.typed_head T (RefsGC.typed_tail T hc)))
  | testTrue hok => exact (O.refTest _ _ _ _ hb).1 hok
  | testFalse hok => exact (O.refTest _ _ _ _ hb).2 hok
  | castSucceed hok => exact (O.refCast _ _ _ _ hb).1 hok
  | castFail hok => exact (O.refCast _ _ _ _ hb).2 hok
  | i31GetNull sx =>
      exact RefsGC.fwd_of_spure T Pr fun _ =>
        RefsGC.spure_i31GetNull (RefsGC.refRule _ rr.i31GetNull) R sx
  | i31GetNum sx i =>
      exact RefsGC.fwd_of_spure T Pr fun _ =>
        RefsGC.spure_i31GetNum (RefsGC.refRule _ rr.i31GetNum) R F sx i
  | externConvertNull =>
      exact RefsGC.fwd_of_spure T Pr fun hc =>
        RefsGC.spure_externConvertNull (RefsGC.refRule _ rr.externConvertAnyNull)
          (R.ref _ (RefsGC.typed_head T hc))
  | externConvertAddr hr =>
      exact RefsGC.fwd_of_spure T Pr fun hc => RefsGC.spure_externConvertAddr
        (RefsGC.refRule _ rr.externConvertAnyAddr) (RefsGC.refRule _ rr.externConvertAnyNull) pt hr
        (R.ref _ (RefsGC.typed_head T hc))
  | anyConvertNull =>
      exact RefsGC.fwd_of_spure T Pr fun _ =>
        RefsGC.spure_anyConvertNull (RefsGC.refRule _ rr.anyConvertExternNull)
  | anyConvertAddr r =>
      exact RefsGC.fwd_of_spure T Pr fun hc =>
        RefsGC.spure_anyConvertAddr (RefsGC.refRule _ rr.anyConvertExternAddr)
          (R.externArg r (RefsGC.typed_head T hc))

/-! ## `call` and `return_call` -/

/-- `call`, with `$funcinst`/`$moduleinst` evaluated directly. -/
theorem fwd_call5 {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hfi : s.funcs[a]? = some fi) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, [.plain (.call x)]⟩
      ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  have Ty := Typing.ctrlTyping_simEnv (BI P hn host)
  have Pd := Prims.projDefs_simEnv (BI P hn host)
  refine fwd_of_sread' T (hasStepRules_simEnv _).read fun hz _ => ?_
  exact sread_call (simEnv_readRules _).call (k := x.toNat) hz (Ty.idx x) (Ty.addr a)
    (Prims.applies_funcinst Pd hn s f) (funcs_getElem_map hfi) rfl
    (Prims.applies_moduleinst Pd hn s f) rfl (moduleFuncs_getElem_map hx)

/-- `return_call`, with `$funcinst`/`$moduleinst` evaluated directly. -/
theorem fwd_returnCall5 {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hfi : s.funcs[a]? = some fi) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, [.plain (.returnCall x)]⟩
      ⟨s, f, [.ref (.func a), .returnCallRefType fi.type]⟩ := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  have Ty := Typing.ctrlTyping_simEnv (BI P hn host)
  have Pd := Prims.projDefs_simEnv (BI P hn host)
  refine fwd_of_sread' T (hasStepRules_simEnv _).read fun hz _ => ?_
  exact sread_returnCall (simEnv_readRules _).returnCall (k := x.toNat) hz (Ty.idx x) (Ty.addr a)
    (Prims.applies_funcinst Pd hn s f) (funcs_getElem_map hfi) rfl
    (Prims.applies_moduleinst Pd hn s f) rfl (moduleFuncs_getElem_map hx)

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
