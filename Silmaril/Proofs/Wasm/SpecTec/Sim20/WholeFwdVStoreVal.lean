module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdPR
public import Silmaril.Wasm.SpecTec.Sim.Memory.Thms

/-!
# `Step` 16 (`vstore-val`) forward, at builtins that answer `$vbytes_`

`vstore-val` compares its quantified bytes with a call to the builtin `$vbytes_`, which
`GrowLike20` builtins keep inert, so it never fires there (`not_fires_vstoreVal_growLike`).
This module answers it:

* `vbytesB P` is `growB P` with `$vbytes_(V128, c)` answered by V2's `vbytes c`
  (`vbytesB_vbytes`). It keeps `growB`'s integer, float and growth answers (`intB_vbytesB`,
  `floatB_vbytesB`, `growCalls20_vbytesB`). It is **not** `InertEnv`: the byte primitive is no
  longer inert. So the backward half of pass 2 (`wholeStepBwdW_at`) does not apply at it, and
  the backward rule 16 is not proved here.
* `evalExp_withMem20`: 2.0's `$with_mem((s; f), x, i, j, b*) = s[.MEMS[f.MODULE.MEMS[x]].BYTES[i : j]
  = b*]; f`, through a slice update. `setSlice_bytesV20` relates the slice update on the encoded
  bytes to V2's `writeBytes`, the boundary included.
* **`fires_vstoreVal`**: at builtins answering `$vbytes_` as V2 does (`VBytes20 B`), rule 16 fires
  from the image of V2's `vecStoreVal` to the image of its successor, from a typed state.
* `VStoreValFwd20` (V2's `vecStoreVal`) is a `FwdBase20` at such builtins (`fwdBase20_vstoreVal`).
  With the assembled base of `WholeFwdPR`, **`Task.wholeStepFwd20V`** (stated and proved,
  `wholeStepFwd20V`): at `vbytesB`, every `Nest20` step over `FwdStep20` or `vecStoreVal` from a
  typed image with whole pages is matched forward.

`Step` 18 (`vstore_lane-val`) is not treated: it needs `$lanes_` and `$ibytes_` answered too, and
its premises bind `Jnn` and `M` through `N = $jsize(Jnn)` and `M = 128/N`.
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
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly stateT QuantsOk evalExp_tup2 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.State (evalExp_call1 pathGet_root pathGet_dot pathGet_idx pathSet_idx
  pathSet_dot pathSet_root evalExp_idxPayload HasClause1 idxPayload iterVar matchExp_iterVar)
open Silmaril.Wasm.SpecTec.Sim20.Pure (NumAgree)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## The encoded bytes -/

/-- The bytes of a V2 byte array, as the list `bytesV` carries. -/
abbrev bytesL20 (b : ByteArray) : List Value := b.toList.map fun x => pctV x.toNat

theorem bytesV_eq_bytesL (b : ByteArray) : bytesV b = .list (Sim.Memory.bytesL b) := by
  simp [bytesV, Sim.Memory.bytesL, byteArray_toList_eq, pctV, percentV, caseV]

/-- **V2's `writeBytes`, on the encoded bytes**: `bytes[a : |w|] = w`, boundary included. -/
theorem setSlice_bytesV20 (m w : ByteArray) (a : Nat) :
    (bytesV m).setSlice a w.size (bytesV w) =
      (Silmaril.Wasm.Execution.Memory.writeBytes m a w).map bytesV := by
  rw [bytesV_eq_bytesL, bytesV_eq_bytesL, Sim.Memory.setSlice_bytesL]
  exact Option.map_congr (fun r _ => (bytesV_eq_bytesL r).symm)

/-- A memory instance with its bytes written. -/
theorem memInstV_writeBytes {mi mi' : MemInst} {a : Nat} {w : ByteArray}
    (hw : mi.writeBytes? a w.size w = some mi') :
    (bytesV mi.bytes).setSlice a w.size (bytesV w) = some (bytesV mi'.bytes) ∧
      (memInstV mi).setField "BYTES" (bytesV mi'.bytes) = some (memInstV mi') := by
  unfold MemInst.writeBytes? at hw
  simp only [↓reduceIte] at hw
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hw
  refine ⟨by rw [setSlice_bytesV20, hb]; rfl, ?_⟩
  simp [memInstV, Value.setField]

/-! ## Builtins answering `$vbytes_` -/

/-- **`B` answers `$vbytes_` as V2 does.** -/
def VBytes20 (B : Builtins) : Prop :=
  ∀ c : BitVec 128, B.call "vbytes_" [.val (caseNilV "V128"), .val (pctV c.toNat)] =
    some (bytesV (vbytes c))

open Classical in
/-- `$vbytes_(V128, c)`, V2's little-endian bytes. -/
noncomputable def vbytesCall20 (ws : List ArgV) : Option Value :=
  if h : ∃ c : BitVec 128, ws = [.val (caseNilV "V128"), .val (pctV c.toNat)] then
    some (bytesV (vbytes h.choose))
  else none

open Classical in
/-- **`growB P` with `$vbytes_` answered as V2 does.** -/
noncomputable def vbytesB (P : Profile) : Builtins :=
  ⟨fun x ws => if x = "vbytes_" then vbytesCall20 ws else (growB P).call x ws⟩

theorem vbytesB_call_of_ne {P : Profile} {x : IL.Id} (h : x ≠ "vbytes_") (ws : List ArgV) :
    (vbytesB P).call x ws = (growB P).call x ws := by
  simp [vbytesB, h]

theorem vbytes20_vbytesB (P : Profile) : VBytes20 (vbytesB P) := by
  intro c
  have h : ∃ c' : BitVec 128, [ArgV.val (caseNilV "V128"), .val (pctV c.toNat)] =
      [.val (caseNilV "V128"), .val (pctV c'.toNat)] := ⟨c, rfl⟩
  have e : h.choose = c := by
    obtain ⟨-, t⟩ := List.cons.inj h.choose_spec
    obtain ⟨a, -⟩ := List.cons.inj t
    exact BitVec.eq_of_toNat_eq (pctV_injective (ArgV.val.inj a)).symm
  simp only [vbytesB, vbytesCall20, ↓reduceIte, h, ↓reduceDIte, e]

theorem intB_vbytesB (P : Profile) : Sim.IntNumeric.IntB (vbytesB P) := by
  intro x ws v h
  by_cases hx : x = "vbytes_"
  · subst hx; simp [Sim.IntNumeric.intCall] at h
  rw [vbytesB_call_of_ne hx]
  exact intB_growB P x ws v h

theorem floatB_vbytesB (P : Profile) : Sim.Floats.FloatB P (vbytesB P) := by
  intro x ws v h
  by_cases hx : x = "vbytes_"
  · subst hx; simp [Sim.Floats.floatCall, Sim.Floats.floatNames] at h
  rw [vbytesB_call_of_ne hx]
  exact floatB_growB P x ws v h

theorem growCalls20_vbytesB (P : Profile) : GrowCalls20 (vbytesB P) where
  table ti ti' n r h := by
    rw [vbytesB_call_of_ne (by decide)]
    exact (growCalls20_growB P).table ti ti' n r h
  mem mi mi' n h := by
    rw [vbytesB_call_of_ne (by decide)]
    exact (growCalls20_growB P).mem mi mi' n h

/-! ## `$with_mem` and `$vbytes_`, evaluated -/

/-- The body of 2.0's `$with_mem`. -/
abbrev withMemBody20 : Exp :=
  .caseE "%;%" (.tupE [.updE (.varE "s") (.sliceP (.dotP (.idxP (.dotP .rootP "MEMS")
    (.idxE (.dotE (.dotE (.varE "f") "MODULE") "MEMS") idxPayload)) "BYTES") (.varE "i")
      (.varE "j")) (iterVar "b" "b*"), .varE "f"])

/-- The argument patterns of 2.0's `$with_mem`. -/
abbrev withMemPats20 : List Arg :=
  [.expA (.caseE "%;%" (.tupE [.varE "s", .varE "f"])), .expA (.varE "x"), .expA (.varE "i"),
    .expA (.varE "j"), .expA (iterVar "b" "b*")]

theorem hasClause_withMem20 : HasClause1 (simEnv20 B) "with_mem" withMemPats20 withMemBody20 :=
  ⟨_, _, _, rfl⟩

/-- Writing a slice through a path. -/
theorem pathSet_slice20 {env : Env} {ρ : VarEnv} {v u u' w r : Value} {p : Path} {e₁ e₂ : Exp}
    {i k : Nat} (hg : PathGet env ρ v p u) (h₁ : EvalExp env ρ e₁ (.num (.natN i)))
    (h₂ : EvalExp env ρ e₂ (.num (.natN k))) (hs : u.setSlice i k w = some u')
    (hr : PathSet env ρ v p u' r) : PathSet env ρ v (.sliceP p e₁ e₂) w r := by
  obtain ⟨n₁, hg⟩ := hg
  obtain ⟨n₂, h₁⟩ := h₁
  obtain ⟨n₃, h₂⟩ := h₂
  obtain ⟨n₄, hr⟩ := hr
  refine ⟨max (max n₁ n₂) (max n₃ n₄) + 1, ?_⟩
  simp only [pathSet, pathGet_ok_of_le (show n₁ ≤ max (max n₁ n₂) (max n₃ n₄) by omega) hg,
    Bind.bind, Except.bind, evalExp_ok_of_le (show n₂ ≤ max (max n₁ n₂) (max n₃ n₄) by omega) h₁,
    evalExp_ok_of_le (show n₃ ≤ max (max n₁ n₂) (max n₃ n₄) by omega) h₂, Value.asNat?,
    Res.ofOption, hs, pathSet_ok_of_le (show n₄ ≤ max (max n₁ n₂) (max n₃ n₄) by omega) hr]

/-- **`$with_mem((s; f), x, i, j, b*)`**, at a memory in range, through V2's `writeBytes?`. -/
theorem evalExp_withMem20 {ρ : VarEnv} {ez ex ei ej eb : Exp} {s : Store H} {f : Frame}
    {x : MemIdx} {a i : Nat} {mi mi' : MemInst} {w : ByteArray}
    (hρ : ρ.findDef? "with_mem" = none) (hz : EvalExp (simEnv20 B) ρ ez (stateV hn s f))
    (hx : EvalExp (simEnv20 B) ρ ex (idxV x)) (hi : EvalExp (simEnv20 B) ρ ei (.num (.natN i)))
    (hj : EvalExp (simEnv20 B) ρ ej (.num (.natN w.size)))
    (hb : EvalExp (simEnv20 B) ρ eb (bytesV w))
    (ha : f.module.mems[x.toNat]? = some a) (hm : s.mems[a]? = some mi)
    (hw : mi.writeBytes? i w.size w = some mi') :
    EvalExp (simEnv20 B) ρ (.callE "with_mem" [.expA ez, .expA ex, .expA ei, .expA ej, .expA eb])
      (stateV hn (s.setMemInst a mi') f) := by
  obtain ⟨hsl, hset⟩ := memInstV_writeBytes hw
  refine evalExp_call1 hasClause_withMem20 hρ
    (evalArgs_cons hz (evalArgs_cons hx (evalArgs_cons hi (evalArgs_cons hj
      (evalArgs_cons hb evalArgs_nil)))))
    (matchArgs_cons (matchArg_expA State.matchExp_state) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
          (matchArg_expA (matchExp_iterVar rfl (by decide) rfl)) matchArgs_nil))))) ?_
  refine evalExp_case (evalExp_tup2 ?_ (evalExp_var rfl))
  have ha' : a < s.mems.length := (List.getElem?_eq_some_iff.1 hm).1
  have hidx : EvalExp (simEnv20 B) ((((((VarEnv.empty.bindVal "s" (storeV hn s)).bindVal "f"
      (frameV f)).bindVal "x" (idxV x)).bindVal "i" (.num (.natN i))).bindVal "j"
      (.num (.natN w.size))).bindVal "b*" (bytesV w))
      (.idxE (.dotE (.dotE (.varE "f") "MODULE") "MEMS") idxPayload) (.num (.natN a)) :=
    evalExp_idxE_iff.2 ⟨_, x.toNat, evalExp_dotE_iff.2 ⟨moduleInstV f.module,
      evalExp_dotE_iff.2 ⟨frameV f, evalExp_var rfl, State.frameV_module f⟩, rfl⟩,
      evalExp_idxPayload rfl, by simp [Value.idx?, addrsV, List.getElem?_map, ha]⟩
  have hg : PathGet (simEnv20 B) ((((((VarEnv.empty.bindVal "s" (storeV hn s)).bindVal "f"
      (frameV f)).bindVal "x" (idxV x)).bindVal "i" (.num (.natN i))).bindVal "j"
      (.num (.natN w.size))).bindVal "b*" (bytesV w)) (storeV hn s)
      (.idxP (.dotP .rootP "MEMS") (.idxE (.dotE (.dotE (.varE "f") "MODULE") "MEMS") idxPayload))
      (memInstV mi) :=
    pathGet_idx (pathGet_dot pathGet_root rfl) hidx (by simp [Value.idx?, List.getElem?_map, hm])
  refine evalExp_updE_iff.2 ⟨storeV hn s, bytesV w, evalExp_var rfl,
    Equiv.Execution.evalExp_iterPat (by decide) rfl, ?_⟩
  refine pathSet_slice20 (pathGet_dot hg rfl) (evalExp_var rfl) (evalExp_var rfl) hsl ?_
  exact pathSet_dot hg hset (pathSet_idx (i := a) (pathGet_dot pathGet_root rfl) hidx
    (by simp [Value.setIdx, ha']) (pathSet_dot pathGet_root (storeV_setMem20 s a _) pathSet_root))

/-- `$vbytes_` has no clauses: it is a builtin. -/
theorem findDef_vbytes20 : ∃ ps t, (simEnv20 B).findDef? "vbytes_" = some (ps, t, []) :=
  ⟨_, _, rfl⟩

/-- **`$vbytes_(V128, c)`**, at builtins answering it as V2 does. -/
theorem evalExp_vbytes20 (hV : VBytes20 B) {ρ : VarEnv} (hd : ρ.findDef? "vbytes_" = none)
    {c : BitVec 128} (fc : ρ.findVal? "c" = some (pctV c.toNat)) :
    EvalExp (simEnv20 B) ρ (.callE "vbytes_" [.expA (.caseE "V128" (.tupE [])), .expA (.varE "c")])
      (bytesV (vbytes c)) := by
  obtain ⟨ps, t, hf⟩ := findDef_vbytes20 (B := B)
  exact evalExp_callE_iff.2 (Equiv.ExecBuiltins.callDef_of_builtin_nil hd hf
    (evalArgs_cons (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩))
      (evalArgs_cons (evalExp_var fc) evalArgs_nil))
    (by rw [simEnv20, Env.builtins_withBuiltins]; exact hV c))

/-! ## Rule 16 -/

/-- `Step/vstore-val`, rule 16 of `Step` (verbatim). -/
def vstoreValRule : Rule :=
  .ruleD "vstore-val" [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA
    (.caseE "I32" (.tupE []))]), .expP "c" (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]),
    .expP "ao" (.varT "memarg" []), .expP "b*" (.iterT (.varT "byte" []) .list)] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c"]),
      .caseE "VSTORE" (.tupE [.caseE "V128" (.tupE []), .varE "ao"])]]),
      .caseE "%;%" (.tupE [.callE "with_mem" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.binE .addOp (.numT .natT) iPay offE),
        .expA (div8E (.callE "size" [.expA (.caseE "V128" (.tupE []))])), .expA (iterVar "b" "b*")],
        .listE []])])
    [.ifPr (.cmpE .eqOp .boolT (iterVar "b" "b*")
      (.callE "vbytes_" [.expA (.caseE "V128" (.tupE [])), .expA (.varE "c")]))]

theorem hasRuleAt_vstoreVal : HasRuleAt (simEnv20 B) "Step" "%~>%" 16 vstoreValRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- **`Step/vstore-val` fires forward** at the image of V2's `vecStoreVal`, at builtins answering
`$vbytes_` as V2 does, from a typed state. -/
theorem fires_vstoreVal (hV : VBytes20 B) {s : Store H} {f : Frame} {ao : V2.MemArg}
    {i : BitVec 32} {c : BitVec 128} {ad : MemAddr} {mi mi' : MemInst}
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hw : mi.writeBytes? (effAddr i.toNat ao) 16 (vbytes c) = some mi') :
    Fires (simEnv20 B) "Step" 16 (.tuple [
      configV hn ⟨s, f, [constI32 i, vconst c, .plain (.vecStore ao)]⟩,
      configV hn ⟨s.setMemInst ad mi', f, []⟩]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("c", pctV c.toNat), ("ao", memargV ao), ("b*", bytesV (vbytes c))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV c.toNat) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have fb : (VarEnv.empty.bindVals σ).findVal? "b*" = some (bytesV (vbytes c)) := rfl
  have hsz : (vbytes c).size = 16 := by simp [vbytes]
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match vstoreValRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons fc (typedV_vecV128_20 c _ hρ) (QuantsOk.cons fa (typedV_memarg20 ao _ hρ)
        (QuantsOk.cons fb (typedV_bytes20 (vbytes c) _ hρ) QuantsOk.nil))))
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
  have hb : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (iterVar "b" "b*")
      (bytesV (vbytes c)) :=
    Equiv.Execution.evalExp_iterPat (by decide) fb
  have hmems : f.module.mems[memIdx0.toNat]? = some ad := by
    simpa [ModuleInst.memAddr?] using ha
  have hmi : s.mems[ad]? = some mi := by simpa [Store.memInst?] using hm
  have hw' : mi.writeBytes? (i.toNat + ao.offset.val) (vbytes c).size (vbytes c) = some mi' := by
    rw [hsz]; simpa [effAddr] using hw
  have hwm : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.callE "with_mem" [.expA (.varE "z"), .expA (.caseE "%" (.tupE [.numE (.natN 0)])),
        .expA (.binE .addOp (.numT .natT) iPay offE), .expA (div8E (.callE "size" [.expA (.caseE "V128" (.tupE []))])),
        .expA (iterVar "b" "b*")]) (stateV hn (s.setMemInst ad mi') f) :=
    evalExp_withMem20 (x := memIdx0) rfl (evalExp_var fz)
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil,
        rfl⟩))
      (evalExp_addNat20 (evalExp_iPay fi) (evalExp_off fa))
      (by rw [hsz]; exact evalExp_div8 (evalExp_sizeV128 rfl) (by decide)) hb hmems hmi hw'
  have hr : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.callE "with_mem" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.binE .addOp (.numT .natT) iPay offE),
        .expA (div8E (.callE "size" [.expA (.caseE "V128" (.tupE []))])), .expA (iterVar "b" "b*")],
        .listE []])) (configV hn ⟨s.setMemInst ad mi', f, []⟩) :=
    evalExp_case (evalExp_tup2 hwm (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩))
  refine Pure.fires_of_ruleAt hasRuleAt_vstoreVal σ hq (evalExp_tup2 hl hr) ?_
  intro pr hpr
  obtain rfl := List.mem_singleton.1 hpr
  exact .ifPr (evalExp_eqTrue hb (evalExp_vbytes20 hV rfl fc))

/-! ## The fragment and the target -/

/-- **V2's `vecStoreVal`.** -/
inductive VStoreValFwd20 : Config H → Config H → Prop where
  | mk {s : Store H} {f : Frame} {ao : V2.MemArg} {i : BitVec 32} {c : BitVec 128} {a : MemAddr}
      {mi mi' : MemInst} (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (hw : mi.writeBytes? (effAddr i.toNat ao) 16 (vbytes c) = some mi') :
      VStoreValFwd20 ⟨s, f, [constI32 i, vconst c, .plain (.vecStore ao)]⟩
        ⟨s.setMemInst a mi', f, []⟩

theorem VStoreValFwd20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : VStoreValFwd20 c c') : Step P host c c' := by
  cases h with
  | mk ha hm hw => exact .vecStoreVal ha hm hw

/-- **`vecStoreVal` is a base**, at builtins answering `$vbytes_`, at any store condition. -/
theorem fwdBase20_vstoreVal {W : Store H → Prop} (hV : VBytes20 B) :
    FwdBase20 B hn W (VStoreValFwd20 (H := H)) where
  sr c c' hc h := by
    cases h with
    | mk ha hm hw =>
      obtain ⟨hs, hf⟩ := typedV_stateV_iff.1 (typed20_iff.1 hc).1
      exact typed20_mk (storeTy20_setMem (typedV_storeV_iff.1 hs) _ _) hf typedV_admins_nil20
  fwd c c' hc _ h := by
    cases h with
    | mk ha hm hw =>
      exact sstepB20S_of_fires (stepAgreeS B 16 (by decide) _
        (fires_vstoreVal hV (typedV_state_of_typed20 hc) ha hm hw))

/-- The assembled base with `vecStoreVal`. -/
inductive FwdStep20V (P : Profile) : Config H → Config H → Prop where
  | fwd {c c' : Config H} (h : FwdStep20 P c c') : FwdStep20V P c c'
  | vstore {c c' : Config H} (h : VStoreValFwd20 c c') : FwdStep20V P c c'

theorem FwdStep20V.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : FwdStep20V P c c') : Step P host c c' := by
  cases h with
  | fwd h => exact h.step
  | vstore h => exact h.step

theorem fwdBase20_fwdV {P : Profile} (hG : GrowCalls20 B) (A : NumAgree (simEnv20 B) P)
    (hV : VBytes20 B) : FwdBase20 B hn WholePages (FwdStep20V (H := H) P) where
  sr c c' hc h := by
    cases h with
    | fwd h => exact (fwdBase20_fwd hG A).sr c c' hc h
    | vstore h => exact (fwdBase20_vstoreVal (W := WholePages) hV).sr c c' hc h
  fwd c c' hc hw h := by
    cases h with
    | fwd h => exact (fwdBase20_fwd hG A).fwd c c' hc hw h
    | vstore h => exact (fwdBase20_vstoreVal hV).fwd c c' hc hw h

/-- **The forward 2.0 half on the assembled nested fragment with `vstore-val`** (stated and
proved): at `vbytesB`, every step of `Nest20 (FwdStep20V P)` from a configuration with typed image
and whole pages is a step of the corrected script between the images, with a typed successor
image. -/
def Task.wholeStepFwd20V : Prop :=
  ∀ (H : Type) (hn : H → String) (nd : Bool) (r : RelaxedChoice) (c c' : Config H),
    Typed20 (simEnv20 (vbytesB (Profile.spec nd r))) hn c → WholePages c.store →
    Nest20 (FwdStep20V (Profile.spec nd r)) c c' →
    Typed20 (simEnv20 (vbytesB (Profile.spec nd r))) hn c' ∧
      SStepB (simEnv20S (vbytesB (Profile.spec nd r))) (configV hn c) (configV hn c')

/-- **`Task.wholeStepFwd20V` is proved.** -/
theorem wholeStepFwd20V : Task.wholeStepFwd20V := by
  intro H hn nd r c c' hc hw h
  have A : NumAgree (simEnv20 (vbytesB (Profile.spec nd r))) (Profile.spec nd r) :=
    Pure.numAgree_simEnv20 (intB_vbytesB _) (floatB_vbytesB _)
  exact fwd_nest20 (fwdBase20_fwdV (growCalls20_vbytesB _) A (vbytes20_vbytesB _)) h hc hw

end Silmaril.Wasm.SpecTec.Sim20.Whole
