module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.Module

/-!
# Round 5: the store's instances are typed

Each kind of instance a store holds is typed in every `simEnv B` from the bounds `Round4.StoreBnd`
puts on its types, and without validity: tag, global, memory, table, data, element, structure and
array instances (`typedV_taginst`, …, `typedV_arrayinst`). Field values are `val`s or `PACK`s, both
`fieldval`s (`typedV_fieldval`). Function instances, whose code needs the `instr` field, are in
`Store.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Pos

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.RuntimeBridge (tagInstToValue memInstToValue tableInstToValue
  dataInstToValue elemInstToValue)
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d269 Original.d567 Original.d115)

variable {B : Builtins}

/-- A closed record type, field by field. -/
theorem typedV_struct {x : IL.Id} {fs : List TypField} {gs : List (AtomS × Value)}
    (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.structT fs)]))
    (hf : HasTypFields (simEnv B) VarEnv.empty fs gs) :
    TypedV (simEnv B) (.varT x []) (.struct gs) := fun _ hρ =>
  hasTyp_varT_struct (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) htd Equiv.evalArgs_nil
    matchArgs_nil hf

/-- The last field of a record. -/
theorem hasTypFields_one {a : AtomS} {t : Typ} {v : Value} (hv : TypedV (simEnv B) t v) :
    HasTypFields (simEnv B) VarEnv.empty [.mk a t [] []] [(a, v)] :=
  hasTypFields_cons_of hv (hasTypFields_nil_iff.2 rfl)

set_option maxRecDepth 100000 in
theorem findTyp_taginst : (simEnv B).findTyp? "taginst" = some ([], [.instD [] [] (.structT
    [.mk "TYPE" (.varT "tagtype" []) [] []])]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_tagtype : (simEnv B).findTyp? "tagtype" =
    some ([], [.instD [] [] (.aliasT (.varT "typeuse" []))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_globalinst : (simEnv B).findTyp? "globalinst" = some ([], [.instD [] [] (.structT
    [.mk "TYPE" (.varT "globaltype" []) [] [], .mk "VALUE" (.varT "val" []) [] []])]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_globaltype : (simEnv B).findTyp? "globaltype" = some ([], [.instD [] []
    (.variantT [.mk "%%" (.tupT [.mk "mut?" (.iterT (.varT "mut" []) .opt),
      .mk "valtype" (.varT "valtype" [])]) [] []])]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_limits : (simEnv B).findTyp? "limits" = some ([], [.instD [] []
    (.variantT [.mk "[%..%]" (.tupT [.mk "u64" (.varT "u64" []),
      .mk "u64?" (.iterT (.varT "u64" []) .opt)]) [] []])]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_datainst : (simEnv B).findTyp? "datainst" = some ([], [.instD [] [] (.structT
    [.mk "BYTES" (.iterT (.varT "byte" []) .list) [] []])]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_eleminst : (simEnv B).findTyp? "eleminst" = some ([], [.instD [] [] (.structT
    [.mk "TYPE" (.varT "elemtype" []) [] [], .mk "REFS" (.iterT (.varT "ref" []) .list) [] []])]) :=
  rfl
set_option maxRecDepth 100000 in
theorem findTyp_elemtype : (simEnv B).findTyp? "elemtype" =
    some ([], [.instD [] [] (.aliasT (.varT "reftype" []))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_structinst : (simEnv B).findTyp? "structinst" = some ([], [.instD [] [] (.structT
    [.mk "TYPE" (.varT "deftype" []) [] [],
     .mk "FIELDS" (.iterT (.varT "fieldval" []) .list) [] []])]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_arrayinst : (simEnv B).findTyp? "arrayinst" = some ([], [.instD [] [] (.structT
    [.mk "TYPE" (.varT "deftype" []) [] [],
     .mk "FIELDS" (.iterT (.varT "fieldval" []) .list) [] []])]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_fieldval : (simEnv B).findTyp? "fieldval" =
    some ([], [.instD [] [] (.variantT (IntNumeric.instCases Original.d567 0))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_packtype : (simEnv B).findTyp? "packtype" =
    some ([], [.instD [] [] (.variantT (IntNumeric.instCases Original.d115 0))]) := rfl

/-- A closed alias of a closed type name, as `TypedV`. -/
theorem typedV_aliasOf {x y : IL.Id}
    (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.aliasT (.varT y []))]))
    {v : Value} (h : TypedV (simEnv B) (.varT y []) v) : TypedV (simEnv B) (.varT x []) v :=
  Typing.typedV_alias htd h

/-- **A tag instance with a bounded type is a typed `taginst`.** -/
theorem typedV_taginst (ti : TagInst) (h : Round4.tyBnd ti.type = true) :
    TypedV (simEnv B) (.varT "taginst" []) (tagInstToValue CT ti) :=
  typedV_struct findTyp_taginst (hasTypFields_one
    (typedV_aliasOf findTyp_tagtype (tyT_tyV ti.type h).2.1))

/-- `mut?`, as `Encode` writes it. -/
theorem typedV_mutEnc (m : Mutability) :
    TypedV (simEnv B) (.iterT (.varT "mut" []) .opt) (Encode.toValue m) := by
  cases m
  · exact ConfigOk.typedV_mut .const
  · exact ConfigOk.typedV_mut .var

/-- **A global instance with a bounded type is a typed `globalinst`.** -/
theorem typedV_globalinst (gi : GlobalInst) (h : Round4.tyBnd gi.type.type = true) :
    TypedV (simEnv B) (.varT "globalinst" []) (globalInstV gi) :=
  typedV_struct findTyp_globalinst (hasTypFields_cons_of
    (Typing.typedV_closedCase findTyp_globaltype rfl
      (hasTyp_tup2 (typedV_mutEnc gi.type.mutability) (tyT_tyV gi.type.type h).1))
    (hasTypFields_one (Typing.typedV_val gi.value)))

/-- A `u64`, as `Encode` writes it. -/
theorem typedV_u64Enc (n : Fin (2 ^ 64)) :
    TypedV (simEnv B) (.varT "u64" []) (Encode.toValue n) := ConfigOk.typedV_u64 n.isLt

/-- **Every limits pair is a `limits`.** -/
theorem typedV_limits (l : Limits) : TypedV (simEnv B) (.varT "limits" []) (Encode.toValue l) := by
  have hmax : TypedV (simEnv B) (.iterT (.varT "u64" []) .opt) (Encode.toValue l.max) := by
    rcases hl : l.max with _ | m
    · exact fun _ _ => hasTyp_iterT_opt_iff.2 (.inl rfl)
    · exact fun ρ hρ => hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, typedV_u64Enc m ρ hρ⟩)
  exact Typing.typedV_closedCase findTyp_limits rfl (hasTyp_tup2 (typedV_u64Enc l.min) hmax)

/-- **Every memory instance is a typed `meminst`.** -/
theorem typedV_meminst (mi : MemInst) :
    TypedV (simEnv B) (.varT "meminst" []) (memInstToValue mi) :=
  typedV_struct ConfigOk.findTyp_meminst (hasTypFields_cons_of
    (Typing.typedV_closedCase ConfigOk.findTyp_memtype rfl
      (hasTyp_tup2 (Typing.typedV_addrtype mi.type.address) (typedV_limits mi.type.limits)))
    (hasTypFields_one fun _ hρ => FwdMem.hasTyp_bytes hρ mi.bytes))

/-- A list of references is a `ref*`. -/
theorem typedV_refs (rs : List Ref) :
    TypedV (simEnv B) (.iterT (.varT "ref" []) .list)
      (.list (rs.map Silmaril.SpecTec.Equiv.RuntimeBridge.refToValue)) :=
  typedV_list_iff.2 fun u hu => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hu
    exact Typing.typedV_ref r

/-- **A table instance with a bounded element type is a typed `tableinst`.** -/
theorem typedV_tableinst (ti : TableInst) (h : Round4.tyBnd ti.type.element = true) :
    TypedV (simEnv B) (.varT "tableinst" []) (tableInstToValue CT ti) :=
  typedV_struct ConfigOk.findTyp_tableinst (hasTypFields_cons_of
    (Typing.typedV_closedCase ConfigOk.findTyp_tabletype rfl
      (hasTyp_tup3 (Typing.typedV_addrtype ti.type.address) (typedV_limits ti.type.limits)
        (tyT_tyV ti.type.element h).1))
    (hasTypFields_one (typedV_refs ti.refs)))

/-- **Every data instance is a typed `datainst`.** -/
theorem typedV_datainst (di : DataInst) :
    TypedV (simEnv B) (.varT "datainst" []) (dataInstToValue di) :=
  typedV_struct findTyp_datainst (hasTypFields_one fun _ hρ => FwdMem.hasTyp_bytes hρ di.bytes)

/-- **An element instance with a bounded type is a typed `eleminst`.** -/
theorem typedV_eleminst (ei : ElemInst) (h : Round4.tyBnd ei.type = true) :
    TypedV (simEnv B) (.varT "eleminst" []) (elemInstToValue CT ei) :=
  typedV_struct findTyp_eleminst (hasTypFields_cons_of
    (typedV_aliasOf findTyp_elemtype (tyT_tyV ei.type h).1)
    (hasTypFields_one (typedV_refs ei.refs)))

/-- A case typed in `val` with the same case type in `fieldval` is typed in `fieldval`. -/
theorem typedV_fieldval_of_val {op : MixopS} {t : Typ} {w : Value}
    (hv : IntNumeric.findCase (IntNumeric.instCases Original.d269 0) op = some (t, []))
    (hf : IntNumeric.findCase (IntNumeric.instCases Original.d567 0) op = some (t, []))
    (h : TypedV (simEnv B) (.varT "val" []) (.case op w)) :
    TypedV (simEnv B) (.varT "fieldval" []) (.case op w) :=
  Typing.typedV_closedCase findTyp_fieldval hf (IntNumeric.hasTyp_of_hasTypCase
    (Typing.hasTypCase_of_closedVariant Typing.findTyp_val (h _ ⟨rfl, rfl, rfl⟩)) hv)

set_option maxRecDepth 100000 in
/-- Every value is a typed `fieldval`. -/
theorem typedV_fieldval_val (v : Val) :
    TypedV (simEnv B) (.varT "fieldval" []) (valV v) := by
  rcases v with n | b | r
  · exact typedV_fieldval_of_val rfl rfl (Typing.typedV_val (.num n))
  · exact typedV_fieldval_of_val rfl rfl (Typing.typedV_val (.vec b))
  · have h := Typing.typedV_val (B := B) (.ref r)
    cases r <;> exact typedV_fieldval_of_val rfl rfl h

/-- `iN($psizenn(packtype))`, with `packtype` bound to `p`. -/
theorem hasTyp_packBits (p : PackType) (b : BitVec p.width) :
    HasTyp (simEnv B) (VarEnv.empty.bindVal "packtype" (Encode.toValue p))
      (.varT "iN" [.expA (.callE "psizenn" [.expA (.varE "packtype")])])
      (Silmaril.SpecTec.Equiv.Execution.pctV b.toNat) := by
  obtain ⟨ps', qs', htn⟩ := IntNumeric.findTyp_iN (B := B)
  have hp : (VarEnv.empty.bindVal "packtype" (Encode.toValue p)).findVal? "packtype" =
      some (tyV (Ty.pack p : CStorageType)) := by
    rw [R4Fwd.toValue_pack]
    simp [Equiv.Execution.findVal?_bindVal_lit]
  exact hasTyp_varT_of_insts (by simp [localTyp?]) htn
    (Equiv.evalArgs_cons (Vec.evalExp_call rfl (Equiv.evalArgs_cons (evalExp_var hp)
      Equiv.evalArgs_nil) (R4Fwd.applies_psizenn p)) Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 (IntNumeric.hasTyp_uN
        (evalExp_var (v := Equiv.natV p.width)
          (by simp [Equiv.Execution.findVal?_bindVal_lit])) b.isLt)))

set_option maxRecDepth 100000 in
/-- **Every field value is a typed `fieldval`.** -/
theorem typedV_fieldval (fv : FieldVal) :
    TypedV (simEnv B) (.varT "fieldval" []) (fieldValV fv) := by
  rcases fv with v | ⟨p, b⟩
  · exact typedV_fieldval_val v
  · have hpt : TypedV (simEnv B) (.varT "packtype" []) (Encode.toValue p) := by
      cases p <;> exact Typing.typedV_closedCase findTyp_packtype rfl hasTyp_tupT_nil
    exact Typing.typedV_closedCase findTyp_fieldval rfl (hasTyp_tupT_iff.2 ⟨_, rfl,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, hpt _ ⟨rfl, rfl, rfl⟩,
        hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_packBits p b, hasTypTup_nil_iff.2 rfl⟩⟩⟩)

/-- A list of field values is a `fieldval*`. -/
theorem typedV_fieldvals (fs : List FieldVal) :
    TypedV (simEnv B) (.iterT (.varT "fieldval" []) .list) (.list (fs.map fieldValV)) :=
  typedV_list_iff.2 fun u hu => by
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hu
    exact typedV_fieldval f

/-- **A structure instance with a bounded type is a typed `structinst`.** -/
theorem typedV_structinst (si : StructInst) (h : Round4.tyBnd si.type = true) :
    TypedV (simEnv B) (.varT "structinst" []) (structInstV si) :=
  typedV_struct findTyp_structinst (hasTypFields_cons_of (typedV_deftype si.type h)
    (hasTypFields_one (typedV_fieldvals si.fields)))

/-- **An array instance with a bounded type is a typed `arrayinst`.** -/
theorem typedV_arrayinst (ai : ArrayInst) (h : Round4.tyBnd ai.type = true) :
    TypedV (simEnv B) (.varT "arrayinst" []) (arrayInstV ai) :=
  typedV_struct findTyp_arrayinst (hasTypFields_cons_of (typedV_deftype ai.type h)
    (hasTypFields_one (typedV_fieldvals ai.fields)))

end Silmaril.Wasm.SpecTec.Sim.Round5.Pos
