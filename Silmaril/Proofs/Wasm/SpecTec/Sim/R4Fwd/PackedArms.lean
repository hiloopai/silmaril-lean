module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.PackEval

/-!
# Field reads and writes at packed storage types, forward

The round-2 lemmas `Aggregates.sread_arrayGetArrayVal`, `fwd_arraySetArrayVal`,
`sread_structGetStructVal`, `fwd_structSetStructVal` cover an unpacked field `.val t`. Here are
their packed counterparts, at a field `.pack p`, through the second clauses of `$packfield_` and
`$unpackfield_` (`PackEval.lean`). Only the field's storage type matters, not the frame: the
`*_any` arms below need no `Aggregates.Unpacked` hypothesis.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.R4Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV mutV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.SpecTec.Equiv.ExecStepRules
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open RefsGC
open Aggregates (AggTypes AggDefs fieldMut evalExp_type evalExp_arrayFieldsAt
  evalExp_structFieldsAt typed_fieldLists evalExp_expandStruct evalExp_withArray evalExp_withStruct
  findDef_none)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty

variable {B : Builtins} {H : Type} {hn : H → String} {P : Numerics.Profile}

/-! ## Reads -/

/-- **`array.get-array` (rule 79), forward, at a packed field.** -/
theorem sread_arrayGetArrayPack (hF : Floats.FloatB P B) (R : RTyping (simEnv B))
    (A : AggTypes (simEnv B)) {s : Store H} {f : Frame} {x : TypeIdx} {i : BitVec 32} {a : Nat}
    {ai : ArrayInst} {sx : Signedness} {p : PackType} {c : BitVec p.width} {d : DefType}
    {m : Mutability} (ha : s.arrays[a]? = some ai) (hf : ai.fields[i.toNat]? = some (.pack p c))
    (hd : f.type? x = some d) (he : Expand d (.array (.field m (.pack p))))
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [arrRef a, constI32 i, .plain (.arrayGet (some sx) x)]⟩)
      (adminsToV [(unpackField (some sx) (.pack p c)).toAdmin]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("sx?", .opt (some (Equiv.sxV sx))), ("x", Encode.toValue x),
    ("zt", tyV (Ty.pack p : CStorageType)), ("mut?", mutV m)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hfv : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.idxE (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
        (.projE (.uncaseE (.varE "i") "%") 0)) (fieldValV (.pack p c)) :=
    evalExp_idx (evalExp_arrayFieldsAt (Aggregates.aggDefs_simEnv B) hρ (by eval_tac)
      (by eval_tac) ha) (evalExp_unpct (by eval_tac)) (by simp [hf])
  have hun : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "unpackfield_" [.expA (.varE "zt"),
        .expA (.iterE (.varE "sx") (.mk .opt [.mk "sx" (.varE "sx?")])),
        .expA (.idxE (.dotE (.idxE (.callE "arrayinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
          (.projE (.uncaseE (.varE "i") "%") 0))]) (valV (unpackField (some sx) (.pack p c))) :=
    Vec.evalExp_call (findDef_none hρ _) (evalArgs_cons (by eval_tac)
      (evalArgs_cons (by eval_tac) (evalArgs_cons hfv evalArgs_nil)))
      (applies_unpackfield_pack hF p sx c)
  have hty := evalExp_type (Aggregates.aggDefs_simEnv B) (State.stateDefs_simEnv B)
    (findDef_none hρ _) hd (e := .varE "z") (ex := .varE "x") (by eval_tac) (by eval_tac)
  have hex : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x")],
        .caseE "ARRAY" (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
          .varE "zt"]))])
      (.tuple [CT.defType d, tyV ((Ty.field m (Ty.pack p)).array : CCompType)]) := by
    cases m <;> exact evalExp_tupE_of (evalExps_cons' hty (by eval_tac))
  refine dderives_of_ruleAt (Aggregates.rd B).arrayGetArray σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (R.sxOpt (some sx) _ hρ)
      (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) (QuantsOk.cons rfl (A.storagetype _ _ hρ)
      (QuantsOk.cons rfl (A.mut_ m _ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (by eval_tac) (evalExp_list1 (evalExp_sub_of ?_)))
    (prems_one (.rulePr evalArgs_nil hex (A.expand _ _ he)))
  rw [adminToV_toAdmin]
  exact hun

/-- **`struct.get-struct` (rule 71), forward, at a packed field.** -/
theorem sread_structGetStructPack (hF : Floats.FloatB P B) (R : RTyping (simEnv B))
    (A : AggTypes (simEnv B)) {s : Store H} {f : Frame} {x : TypeIdx} {i : FieldIdx} {a : Nat}
    {si : StructInst} {sx : Signedness} {p : PackType} {c : BitVec p.width} {d : DefType}
    {fs : Ty (.list .field)} {m : Mutability} (hs : s.structs[a]? = some si)
    (hf : si.fields[i.toNat]? = some (.pack p c)) (hd : f.type? x = some d)
    (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some (.field m (.pack p)))
    (hz : TypedV (simEnv B) stateT (stateV hn s f)) :
    SRead (simEnv B) (configV hn ⟨s, f, [.ref (.struct a), .plain (.structGet (some sx) x i)]⟩)
      (adminsToV [(unpackField (some sx) (.pack p c)).toAdmin]) := by
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("sx?", .opt (some (Equiv.sxV sx))), ("x", Encode.toValue x), ("i", Encode.toValue i),
    ("zt*", .list (fs.toList.map (tyV ∘ fieldStorage))),
    ("mut?*", .list (fs.toList.map (mutV ∘ fieldMut)))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hii : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.projE (.uncaseE (.varE "i") "%") 0)
      (.num (.natN i.toNat)) := evalExp_unpct (by eval_tac)
  have hfv : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.idxE (.dotE (.idxE (.callE "structinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
        (.projE (.uncaseE (.varE "i") "%") 0)) (fieldValV (.pack p c)) :=
    evalExp_idx (evalExp_structFieldsAt (Aggregates.aggDefs_simEnv B) hρ (by eval_tac)
      (by eval_tac) hs) hii (by simp [hf])
  have hzt : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.idxE (.iterE (.varE "zt") (.mk .list [.mk "zt" (.varE "zt*")]))
        (.projE (.uncaseE (.varE "i") "%") 0)) (tyV (Ty.pack p : CStorageType)) :=
    evalExp_idx (by eval_tac) hii (by simp [hi, fieldStorage])
  have hun : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "unpackfield_" [.expA (.idxE (.iterE (.varE "zt") (.mk .list [.mk "zt" (.varE "zt*")]))
          (.projE (.uncaseE (.varE "i") "%") 0)),
        .expA (.iterE (.varE "sx") (.mk .opt [.mk "sx" (.varE "sx?")])),
        .expA (.idxE (.dotE (.idxE (.callE "structinst" [.expA (.varE "z")]) (.varE "a")) "FIELDS")
          (.projE (.uncaseE (.varE "i") "%") 0))]) (valV (unpackField (some sx) (.pack p c))) :=
    Vec.evalExp_call (findDef_none hρ _) (evalArgs_cons hzt
      (evalArgs_cons (by eval_tac) (evalArgs_cons hfv evalArgs_nil)))
      (applies_unpackfield_pack hF p sx c)
  obtain ⟨tz, tm⟩ := typed_fieldLists A fs.toList
  refine dderives_of_ruleAt (Aggregates.rd B).structGetStruct σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.sxOpt (some sx) _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.fieldidx _ i.value.isLt _ hρ) (QuantsOk.cons rfl (tz _ hρ)
      (QuantsOk.cons rfl (tm _ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (by eval_tac) (evalExp_list1 (evalExp_sub_of ?_)))
    (prems_one (.rulePr evalArgs_nil (evalExp_expandStruct (Aggregates.aggDefs_simEnv B)
      (State.stateDefs_simEnv B) hρ hd rfl rfl rfl rfl) (A.expand _ _ he)))
  rw [adminToV_toAdmin]
  exact hun

/-! ## Writes -/

/-- **`array.set-array` (`Step` rule 35), forward, at any storage type** (packed ones through
`$packfield_`'s second clause), for a `packable` value. -/
theorem fwd_arraySetArrayAny (hF : Floats.FloatB P B) (T : TypingFacts (simEnv B) hn)
    (R : RTyping (simEnv B)) (A : AggTypes (simEnv B)) {s : Store H} {f : Frame} {x : TypeIdx}
    {i : BitVec 32} {v : Val} {a : Nat} {ai : ArrayInst} {d : DefType} {m : Mutability}
    {zt : CStorageType} (ha : s.arrays[a]? = some ai) (h : i.toNat < ai.fields.length)
    (hd : f.type? x = some d) (he : Expand d (.array (.field m zt))) (hp : packable zt v = true) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x)]⟩
      ⟨s.setArrayField a i.toNat (packField zt v), f, []⟩ := by
  intro hc _
  obtain ⟨hz, hcode⟩ := (T.config _).1 hc
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("i", pctV i.toNat), ("val", adminToV v.toAdmin), ("x", Encode.toValue x),
    ("zt", tyV zt), ("mut?", mutV m)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hv : TypedV (simEnv B) valT (adminToV v.toAdmin) :=
    typed_toAdmin R v (typed_head T (typed_tail T (typed_tail T hcode)))
  have hpk : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "packfield_" [.expA (.varE "zt"), .expA (.varE "val")])
      (fieldValV (packField zt v)) :=
    Vec.evalExp_call (findDef_none hρ _) (evalArgs_cons (by eval_tac)
      (evalArgs_cons (evalExp_var (by show some (adminToV v.toAdmin) = some (valV v); rw [adminToV_toAdmin])) evalArgs_nil))
      (applies_packfield hF zt v hp)
  have hw := evalExp_withArray (Aggregates.aggDefs_simEnv B) (State.stateDefs_simEnv B)
    (findDef_none hρ _) (ez := .varE "z") (ea := .varE "a")
    (ei := .projE (.uncaseE (.varE "i") "%") 0) ha h (by eval_tac) (by eval_tac)
    (evalExp_unpct (by eval_tac)) hpk
  have hty := evalExp_type (Aggregates.aggDefs_simEnv B) (State.stateDefs_simEnv B)
    (findDef_none hρ _) hd (e := .varE "z") (ex := .varE "x") (by eval_tac) (by eval_tac)
  have hex : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.tupE [.callE "type" [.expA (.varE "z"), .expA (.varE "x")],
        .caseE "ARRAY" (.caseE "%%" (.tupE [.iterE (.varE "mut") (.mk .opt [.mk "mut" (.varE "mut?")]),
          .varE "zt"]))])
      (.tuple [CT.defType d, tyV ((Ty.field m zt).array : CCompType)]) := by
    cases m <;> exact evalExp_tupE_of (evalExps_cons' hty (by eval_tac))
  exact dderives_of_ruleAt (Aggregates.st B).arraySetArray σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 i _ hρ) (QuantsOk.cons rfl (hv _ hρ)
      (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ) (QuantsOk.cons rfl (A.storagetype _ _ hρ)
      (QuantsOk.cons rfl (A.mut_ m _ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (by eval_tac) (evalExp_case (evalExp_tup2 hw (by eval_tac))))
    (prems_one (.rulePr evalArgs_nil hex (A.expand _ _ he)))

/-- **`struct.set-struct` (`Step` rule 31), forward, at any storage type**, for a `packable`
value. -/
theorem fwd_structSetStructAny (hF : Floats.FloatB P B) (T : TypingFacts (simEnv B) hn)
    (R : RTyping (simEnv B)) (A : AggTypes (simEnv B)) {s : Store H} {f : Frame} {x : TypeIdx}
    {i : FieldIdx} {v : Val} {a : Nat} {d : DefType} {fs : Ty (.list .field)} {m : Mutability}
    {zt : CStorageType} {si : StructInst} (hd : f.type? x = some d) (he : Expand d (.struct fs))
    (hi : fs.toList[i.toNat]? = some (.field m zt)) (hs : s.structs[a]? = some si)
    (hf : i.toNat < si.fields.length) (hp : packable zt v = true) :
    FwdP (simEnv B) hn ⟨s, f, [.ref (.struct a), v.toAdmin, .plain (.structSet x i)]⟩
      ⟨s.setStructField a i.toNat (packField zt v), f, []⟩ := by
  intro hc _
  obtain ⟨hz, hcode⟩ := (T.config _).1 hc
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("a", .num (.natN a)),
    ("val", adminToV v.toAdmin), ("x", Encode.toValue x), ("i", Encode.toValue i),
    ("zt*", .list (fs.toList.map (tyV ∘ fieldStorage))),
    ("mut?*", .list (fs.toList.map (mutV ∘ fieldMut)))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hv : TypedV (simEnv B) valT (adminToV v.toAdmin) :=
    typed_toAdmin R v (typed_head T (typed_tail T hcode))
  have hii : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.projE (.uncaseE (.varE "i") "%") 0)
      (.num (.natN i.toNat)) := evalExp_unpct (by eval_tac)
  have hzt : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.idxE (.iterE (.varE "zt") (.mk .list [.mk "zt" (.varE "zt*")]))
        (.projE (.uncaseE (.varE "i") "%") 0)) (tyV zt) :=
    evalExp_idx (by eval_tac) hii (by simp [hi, fieldStorage])
  have hpk : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.callE "packfield_" [.expA (.idxE (.iterE (.varE "zt") (.mk .list [.mk "zt" (.varE "zt*")]))
        (.projE (.uncaseE (.varE "i") "%") 0)), .expA (.varE "val")])
      (fieldValV (packField zt v)) :=
    Vec.evalExp_call (findDef_none hρ _) (evalArgs_cons hzt
      (evalArgs_cons (evalExp_var (by show some (adminToV v.toAdmin) = some (valV v); rw [adminToV_toAdmin])) evalArgs_nil))
      (applies_packfield hF zt v hp)
  have hw := evalExp_withStruct (Aggregates.aggDefs_simEnv B) (State.stateDefs_simEnv B)
    (findDef_none hρ _) (ez := .varE "z") (ea := .varE "a")
    (ei := .projE (.uncaseE (.varE "i") "%") 0) hs hf (by eval_tac) (by eval_tac) hii hpk
  obtain ⟨tz, tm⟩ := typed_fieldLists A fs.toList
  exact dderives_of_ruleAt (Aggregates.st B).structSetStruct σ
    (QuantsOk.cons rfl (hz _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (hv _ hρ) (QuantsOk.cons rfl (R.idx _ x.value.isLt _ hρ)
      (QuantsOk.cons rfl (R.fieldidx _ i.value.isLt _ hρ) (QuantsOk.cons rfl (tz _ hρ)
      (QuantsOk.cons rfl (tm _ hρ) QuantsOk.nil)))))))
    (evalExp_tup2 (by eval_tac) (evalExp_case (evalExp_tup2 hw (by eval_tac))))
    (prems_one (.rulePr evalArgs_nil (evalExp_expandStruct (Aggregates.aggDefs_simEnv B)
      (State.stateDefs_simEnv B) hρ hd rfl rfl rfl rfl) (A.expand _ _ he)))

/-! ## The arms, at every frame -/

section Arms

variable (hF : Floats.FloatB P B) (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B))
  (A : AggTypes (simEnv B))
include hF T R A

/-- The `array.get-array` arm, at every storage type. -/
theorem fwd_arrayGetArray_any {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx}
    {i : BitVec 32} {a : Nat} {ai : ArrayInst} {fv : FieldVal} {d : DefType} {ft : CFieldType}
    (ha : s.arrays[a]? = some ai) (hf : ai.fields[i.toNat]? = some fv)
    (hd : f.type? x = some d) (he : Expand d (.array ft))
    (hu' : unpackable (fieldStorage ft) sx fv = true) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, .plain (.arrayGet sx x)]⟩
      ⟨s, f, [(unpackField sx fv).toAdmin]⟩ := by
  cases ft with | field m zt => ?_
  cases zt with
  | val t =>
    obtain ⟨rfl, v, rfl⟩ := Aggregates.unpackable_val hu'
    exact RefsGC.fwd_of_sread T (Aggregates.st B).read fun hz _ => by
      simpa only [unpackField] using Aggregates.sread_arrayGetArrayVal (hn := hn)
        (Aggregates.rd B).arrayGetArray R (Aggregates.aggDefs_simEnv B)
        (State.stateDefs_simEnv B) A (Aggregates.unpackDef_simEnv B) ha hf hd he hz
  | pack p =>
    cases sx with
    | none => cases fv <;> simp [unpackable, fieldStorage] at hu'
    | some sx =>
      cases fv with
      | val _ => simp [unpackable, fieldStorage] at hu'
      | pack p' c =>
        obtain rfl : p = p' := by simpa [unpackable, fieldStorage] using hu'
        exact RefsGC.fwd_of_sread T (Aggregates.st B).read fun hz _ =>
          sread_arrayGetArrayPack hF R A ha hf hd he hz

/-- The `struct.get-struct` arm, at every storage type. -/
theorem fwd_structGetStruct_any {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx}
    {i : FieldIdx} {a : Nat} {si : StructInst} {fv : FieldVal} {d : DefType}
    {fs : Ty (.list .field)} {ft : CFieldType}
    (hs : s.structs[a]? = some si) (hf : si.fields[i.toNat]? = some fv)
    (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some ft)
    (hu' : unpackable (fieldStorage ft) sx fv = true) :
    FwdP (simEnv B) hn ⟨s, f, [.ref (.struct a), .plain (.structGet sx x i)]⟩
      ⟨s, f, [(unpackField sx fv).toAdmin]⟩ := by
  cases ft with | field m zt => ?_
  cases zt with
  | val t =>
    obtain ⟨rfl, v, rfl⟩ := Aggregates.unpackable_val hu'
    exact RefsGC.fwd_of_sread T (Aggregates.st B).read fun hz _ => by
      simpa only [unpackField] using Aggregates.sread_structGetStructVal (hn := hn)
        (Aggregates.rd B).structGetStruct R (Aggregates.aggDefs_simEnv B)
        (State.stateDefs_simEnv B) A (Aggregates.unpackDef_simEnv B) hs hf hd he hi hz
  | pack p =>
    cases sx with
    | none => cases fv <;> simp [unpackable, fieldStorage] at hu'
    | some sx =>
      cases fv with
      | val _ => simp [unpackable, fieldStorage] at hu'
      | pack p' c =>
        obtain rfl : p = p' := by simpa [unpackable, fieldStorage] using hu'
        exact RefsGC.fwd_of_sread T (Aggregates.st B).read fun hz _ =>
          sread_structGetStructPack hF R A hs hf hd he hi hz

/-- The `array.set-array` arm, at every storage type. -/
theorem fwd_arraySetArray_any {s : Store H} {f : Frame} {x : TypeIdx} {i : BitVec 32} {v : Val}
    {a : Nat} {ai : ArrayInst} {d : DefType} {ft : CFieldType}
    (ha : s.arrays[a]? = some ai) (h : i.toNat < ai.fields.length) (hd : f.type? x = some d)
    (he : Expand d (.array ft)) (hp : packable (fieldStorage ft) v = true) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x)]⟩
      ⟨s.setArrayField a i.toNat (packField (fieldStorage ft) v), f, []⟩ := by
  obtain ⟨m, zt⟩ := ft
  exact fwd_arraySetArrayAny hF T R A ha h hd he hp

/-- The `struct.set-struct` arm, at every storage type. -/
theorem fwd_structSetStruct_any {s : Store H} {f : Frame} {x : TypeIdx} {i : FieldIdx} {v : Val}
    {a : Nat} {d : DefType} {fs : Ty (.list .field)} {ft : CFieldType} {si : StructInst}
    (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some ft)
    (hs : s.structs[a]? = some si) (hf : i.toNat < si.fields.length)
    (hp : packable (fieldStorage ft) v = true) :
    FwdP (simEnv B) hn ⟨s, f, [.ref (.struct a), v.toAdmin, .plain (.structSet x i)]⟩
      ⟨s.setStructField a i.toNat (packField (fieldStorage ft) v), f, []⟩ := by
  obtain ⟨m, zt⟩ := ft
  exact fwd_structSetStructAny hF T R A hd he hi hs hf hp

end Arms

end Silmaril.Wasm.SpecTec.Sim.R4Fwd
