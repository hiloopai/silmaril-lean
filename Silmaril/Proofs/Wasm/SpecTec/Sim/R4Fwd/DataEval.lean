module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.PackEval

/-!
# The storage-type functions of `array.new_data` and `array.init_data`

`Step_read/array.new_data-*` and `array.init_data-*` (rules 75, 76, 100–102) read fields from a
data segment through `$zsize(zt)`, `$zbytes_(zt, c)`, `$cunpack(zt)`, `$cunpacknum_(zt, c)` and
`$const(ct, c)`. This file evaluates each of them, by its clauses, at the image of every storage
type with a byte size (`0 < storageSize zt`: numeric, vector and packed types; Core's rules carry
that premise):

* `applies_size`, `applies_vsize`, `applies_zsize`: `$zsize(zt) = storageSize zt`;
* `applies_cunpack`: `$cunpack(zt)` is `zt` at a numeric or vector type and `I32` at a packed one;
* `applies_cunpacknum`, `applies_const`: `$const($cunpack(zt), $cunpacknum_(zt, c))` is the image
  of the field value Core's `readField?` builds from the same bytes.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.R4Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil bvV natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty

variable {B : Builtins}

/-! ## Sizes -/

/-- The pattern `numtype <: storagetype`. -/
abbrev numtypePatZ : Exp := .subE (.varE "numtype") (.varT "numtype" []) (.varT "storagetype" [])

/-- The pattern `vectype <: storagetype`. -/
abbrev vectypePatZ : Exp := .subE (.varE "vectype") (.varT "vectype" []) (.varT "storagetype" [])

/-- The pattern `consttype <: storagetype`. -/
abbrev consttypePatZ : Exp :=
  .subE (.varE "consttype") (.varT "consttype" []) (.varT "storagetype" [])

set_option maxRecDepth 100000 in
theorem findDef_size (B : Builtins) : (simEnv B).findDef? "size" = some
    ([.expP "numtype" (.varT "numtype" [])], .numT .natT,
      [.defD [] [.expA (.caseE "I32" (.tupE []))] (.numE (.natN 32)) [],
       .defD [] [.expA (.caseE "I64" (.tupE []))] (.numE (.natN 64)) [],
       .defD [] [.expA (.caseE "F32" (.tupE []))] (.numE (.natN 32)) [],
       .defD [] [.expA (.caseE "F64" (.tupE []))] (.numE (.natN 64)) []]) := rfl

set_option maxRecDepth 100000 in
theorem findDef_vsize (B : Builtins) : (simEnv B).findDef? "vsize" = some
    ([.expP "vectype" (.varT "vectype" [])], .numT .natT,
      [.defD [] [.expA (.caseE "V128" (.tupE []))] (.numE (.natN 128)) []]) := rfl

set_option maxRecDepth 100000 in
theorem findDef_zsize (B : Builtins) : (simEnv B).findDef? "zsize" = some
    ([.expP "storagetype" (.varT "storagetype" [])], .numT .natT,
      [.defD [.expP "numtype" (.varT "numtype" [])] [.expA numtypePatZ]
          (.callE "size" [.expA (.varE "numtype")]) [],
       .defD [.expP "vectype" (.varT "vectype" [])] [.expA vectypePatZ]
          (.callE "vsize" [.expA (.varE "vectype")]) [],
       .defD [.expP "packtype" (.varT "packtype" [])] [.expA packtypePat]
          (.callE "psize" [.expA (.varE "packtype")]) []]) := rfl

/-- A clause whose `caseE` pattern names another constructor is skipped. -/
theorem skip_case {q : List Param} {op op' : MixopS} {e body : Exp} {cs : List Clause}
    {w v : Value} (hne : op' ≠ op) (h : TryClauses (simEnv B) cs [.val (.case op' w)] v) :
    TryClauses (simEnv B) (.defD q [.expA (.caseE op e)] body [] :: cs) [.val (.case op' w)] v :=
  tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef hne))) h

/-- A nullary `caseE` pattern with a numeral body. -/
theorem hit_case {q : List Param} {op : MixopS} {k : Nat} {cs : List Clause} :
    TryClauses (simEnv B) (.defD q [.expA (.caseE op (.tupE []))] (.numE (.natN k)) [] :: cs)
      [.val (.case op (.tuple []))] (natV k) :=
  tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil)
    premsHold_nil RefsGC.evalExp_num'

/-- `$size(nt)` is the width. -/
theorem applies_size : ∀ t : NumType,
    Applies (simEnv B) "size" [.val (tyV (Ty.num t : CValType))] (natV t.width)
  | .int .i32 => ⟨_, _, _, findDef_size B, Or.inl hit_case⟩
  | .int .i64 => ⟨_, _, _, findDef_size B, Or.inl (skip_case (by decide) hit_case)⟩
  | .float .f32 => ⟨_, _, _, findDef_size B, Or.inl (skip_case (by decide)
      (skip_case (by decide) hit_case))⟩
  | .float .f64 => ⟨_, _, _, findDef_size B, Or.inl (skip_case (by decide)
      (skip_case (by decide) (skip_case (by decide) hit_case)))⟩

/-- `$vsize(V128) = 128`. -/
theorem applies_vsize (t : VecType) :
    Applies (simEnv B) "vsize" [.val (tyV (Ty.vec t : CValType))] (natV 128) := by
  cases t
  exact ⟨_, _, _, findDef_vsize B, Or.inl hit_case⟩

set_option maxRecDepth 100000 in
/-- `$zsize(zt) = storageSize zt` at every storage type with a byte size. -/
theorem applies_zsize : ∀ zt : CStorageType, 0 < storageSize zt →
    Applies (simEnv B) "zsize" [.val (tyV zt)] (natV (storageSize zt))
  | .val (.num t), _ => by
    refine ⟨_, _, _, findDef_zsize B, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
      (Prims.matchExp_subE (matchExp_varE (by simp))) ?_) matchArgs_nil) premsHold_nil
      (Vec.evalExp_call rfl (evalArgs_cons (evalExp_var rfl) evalArgs_nil)
        (applies_size t)))⟩
    rcases t with t | t <;> cases t <;> rfl
  | .val (.vec t), _ => by
    refine ⟨_, _, _, findDef_zsize B, Or.inl (tryClauses_skip_match (matchArgs_cons_undef
      (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub ?_)) (tryClauses_hit (matchArgs_cons
        (matchArg_expA (Prims.matchExp_subE (matchExp_varE (by simp))) ?_) matchArgs_nil)
        premsHold_nil (Vec.evalExp_call rfl (evalArgs_cons (evalExp_var rfl)
          evalArgs_nil) (applies_vsize t))))⟩ <;> cases t <;> rfl
  | .pack p, _ => by
    refine ⟨_, _, _, findDef_zsize B, Or.inl (tryClauses_skip_match (matchArgs_cons_undef
      (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub ?_)) (tryClauses_skip_match
        (matchArgs_cons_undef (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub ?_))
        (tryClauses_hit (matchArgs_cons (matchArg_expA (Prims.matchExp_subE
          (matchExp_varE (by simp))) (argSubOk_packtypePat_pack p rfl)) matchArgs_nil)
          premsHold_nil (Vec.evalExp_call rfl (evalArgs_cons (evalExp_var rfl)
            evalArgs_nil) (applies_psize p)))))⟩ <;> cases p <;> rfl
  | .val (.refv _), h => by simp [storageSize] at h
  | .val .botv, h => by simp [storageSize] at h

/-! ## Unpacking to a constant type -/

set_option maxRecDepth 100000 in
theorem findDef_cunpack (B : Builtins) : ∃ ps t c₃, (simEnv B).findDef? "cunpack" = some (ps, t,
    [.defD [.expP "consttype" (.varT "consttype" [])] [.expA consttypePatZ]
        (.varE "consttype") [],
     .defD [.expP "packtype" (.varT "packtype" [])] [.expA packtypePat]
        (.caseE "I32" (.tupE [])) [], c₃]) := ⟨_, _, _, rfl⟩

/-- The image of `$cunpack(zt)`: the type itself at a numeric or vector type, `I32` at a packed
one. -/
def cunpackV : CStorageType → Value
  | .val t => tyV t
  | .pack _ => caseNilV "I32"

set_option maxRecDepth 100000 in
/-- `$cunpack(zt)` at every storage type with a byte size. -/
theorem applies_cunpack : ∀ zt : CStorageType, 0 < storageSize zt →
    Applies (simEnv B) "cunpack" [.val (tyV zt)] (cunpackV zt)
  | .val (.num t), _ => by
    obtain ⟨ps, ty, c₃, hd⟩ := findDef_cunpack B
    refine ⟨_, _, _, hd, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
      (Prims.matchExp_subE (matchExp_varE (by simp))) ?_) matchArgs_nil) premsHold_nil
      (evalExp_var rfl))⟩
    rcases t with t | t <;> cases t <;> rfl
  | .val (.vec t), _ => by
    obtain ⟨ps, ty, c₃, hd⟩ := findDef_cunpack B
    refine ⟨_, _, _, hd, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
      (Prims.matchExp_subE (matchExp_varE (by simp))) ?_) matchArgs_nil) premsHold_nil
      (evalExp_var rfl))⟩
    cases t; rfl
  | .pack p, _ => by
    obtain ⟨ps, ty, c₃, hd⟩ := findDef_cunpack B
    refine ⟨_, _, _, hd, Or.inl (tryClauses_skip_match (matchArgs_cons_undef
      (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub ?_)) (tryClauses_hit (matchArgs_cons
        (matchArg_expA (Prims.matchExp_subE (matchExp_varE (by simp)))
          (argSubOk_packtypePat_pack p rfl)) matchArgs_nil) premsHold_nil
        (evalExp_case (RefsGC.evalExp_tupE_of RefsGC.evalExps_nil'))))⟩
    cases p <;> rfl
  | .val (.refv _), h => by simp [storageSize] at h
  | .val .botv, h => by simp [storageSize] at h

/-! ## `$cunpacknum_`, `$lunpack`, `$const` -/

set_option maxRecDepth 100000 in
theorem findDef_lunpack (B : Builtins) : ∃ ps t, (simEnv B).findDef? "lunpack" = some (ps, t,
    [.defD [.expP "numtype" (.varT "numtype" [])]
        [.expA (.subE (.varE "numtype") (.varT "numtype" []) (.varT "lanetype" []))]
        (.varE "numtype") [],
     .defD [.expP "packtype" (.varT "packtype" [])]
        [.expA (.subE (.varE "packtype") (.varT "packtype" []) (.varT "lanetype" []))]
        (.caseE "I32" (.tupE [])) []]) := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
/-- `$lunpack(I8|I16) = I32`. -/
theorem applies_lunpack_pack (p : PackType) :
    Applies (simEnv B) "lunpack" [.val (tyV (Ty.pack p : CStorageType))] (caseNilV "I32") := by
  obtain ⟨ps, t, hd⟩ := findDef_lunpack B
  refine ⟨ps, t, _, hd, Or.inl (tryClauses_skip_match (matchArgs_cons_undef
    (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub ?_)) (tryClauses_hit (matchArgs_cons
      (matchArg_expA (Prims.matchExp_subE (matchExp_varE (by simp))) ?_) matchArgs_nil)
      premsHold_nil (evalExp_case (RefsGC.evalExp_tupE_of RefsGC.evalExps_nil'))))⟩ <;>
    cases p <;> rfl

set_option maxRecDepth 100000 in
theorem findDef_cunpacknum (B : Builtins) : ∃ ps t c₂, (simEnv B).findDef? "cunpacknum_" =
    some (ps, t, [.defD [.expP "consttype" (.varT "consttype" []),
        .expP "c" (.varT "lit_" [.expA consttypePatZ])]
        [.expA consttypePatZ, .expA (.varE "c")] (.varE "c") [], c₂]) := ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
/-- `$cunpacknum_(zt, c) = c` at a numeric or vector type. -/
theorem applies_cunpacknum_val (t : CValType) (ht : 0 < storageSize (.val t)) (c : Value) :
    Applies (simEnv B) "cunpacknum_" [.val (tyV (Ty.val t : CStorageType)), .val c] c := by
  obtain ⟨ps, ty, c₂, hd⟩ := findDef_cunpacknum B
  refine ⟨ps, ty, _, hd, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
    (Prims.matchExp_subE (matchExp_varE (by simp))) ?_) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)) premsHold_nil
    (evalExp_var rfl))⟩
  cases t with
  | num t => rcases t with t | t <;> cases t <;> rfl
  | vec t => cases t; rfl
  | refv r => simp [storageSize] at ht
  | botv => simp [storageSize] at ht

set_option maxRecDepth 100000 in
theorem findDef_cunpacknum₂ (B : Builtins) : ∃ ps t, (simEnv B).findDef? "cunpacknum_" =
    some (ps, t, [.defD [.expP "consttype" (.varT "consttype" []),
        .expP "c" (.varT "lit_" [.expA consttypePatZ])]
        [.expA consttypePatZ, .expA (.varE "c")] (.varE "c") [], .defD [.expP "packtype" (.varT "packtype" []),
        .expP "c" (.varT "lit_" [.expA packtypePat])]
        [.expA packtypePat, .expA (.varE "c")]
        (.callE "extend__" [.expA (.callE "psize" [.expA (.varE "packtype")]),
          .expA (.callE "size" [.expA (.callE "lunpack" [.expA (.subE (.varE "packtype")
            (.varT "packtype" []) (.varT "lanetype" []))])]),
          .expA (.caseE "U" (.tupE [])), .expA (.varE "c")]) []]) := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
/-- `$cunpacknum_(I8|I16, c)`: zero extension to 32 bits. -/
theorem applies_cunpacknum_pack {P : Numerics.Profile} (hF : Floats.FloatB P B) (p : PackType)
    (b : BitVec p.width) :
    Applies (simEnv B) "cunpacknum_" [.val (tyV (Ty.pack p : CStorageType)), .val (bvV b)]
      (bvV (b.setWidth 32)) := by
  obtain ⟨ps, ty, hd⟩ := findDef_cunpacknum₂ B
  refine ⟨ps, ty, _, hd, Or.inl (tryClauses_skip_match (matchArgs_cons_undef
    (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub ?_)) (tryClauses_hit (matchArgs_cons
      (matchArg_expA (Prims.matchExp_subE (matchExp_varE (by simp)))
        (argSubOk_packtypePat_pack p rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
      premsHold_nil ?_))⟩
  · cases p <;> rfl
  · have he := applies_extend hF p.width .unsigned b
    exact Vec.evalExp_call rfl (evalArgs_cons
      (Vec.evalExp_call rfl (evalArgs_cons (evalExp_var rfl) evalArgs_nil)
        (applies_psize p))
      (evalArgs_cons (Vec.evalExp_call rfl (evalArgs_cons (Vec.evalExp_call rfl
          (evalArgs_cons (RefsGC.evalExp_sub_of (evalExp_var rfl)) evalArgs_nil)
          (applies_lunpack_pack p)) evalArgs_nil)
        (applies_size (B := B) (.int .i32)))
      (evalArgs_cons (evalExp_case (RefsGC.evalExp_tupE_of RefsGC.evalExps_nil'))
        (evalArgs_cons (evalExp_var rfl) evalArgs_nil)))) he

set_option maxRecDepth 100000 in
theorem findDef_const (B : Builtins) : ∃ ps t, (simEnv B).findDef? "const" = some (ps, t,
    [.defD [.expP "numtype" (.varT "numtype" []), .expP "c" (.varT "lit_" [.expA (.subE (.subE
        (.varE "numtype") (.varT "numtype" []) (.varT "consttype" [])) (.varT "consttype" [])
        (.varT "storagetype" []))])]
        [.expA (.subE (.varE "numtype") (.varT "numtype" []) (.varT "consttype" [])),
          .expA (.varE "c")] (.caseE "CONST" (.tupE [.varE "numtype", .varE "c"])) [],
     .defD [.expP "vectype" (.varT "vectype" []), .expP "c" (.varT "lit_" [.expA (.subE (.subE
        (.varE "vectype") (.varT "vectype" []) (.varT "consttype" [])) (.varT "consttype" [])
        (.varT "storagetype" []))])]
        [.expA (.subE (.varE "vectype") (.varT "vectype" []) (.varT "consttype" [])),
          .expA (.varE "c")] (.caseE "VCONST" (.tupE [.varE "vectype", .varE "c"])) []]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
/-- `$const(nt, c) = CONST nt c`. -/
theorem applies_const_num (t : NumType) (c : Value) :
    Applies (simEnv B) "const" [.val (tyV (Ty.num t : CValType)), .val c]
      (.case "CONST" (.tuple [tyV (Ty.num t : CValType), c])) := by
  obtain ⟨ps, ty, hd⟩ := findDef_const B
  refine ⟨ps, ty, _, hd, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
    (Prims.matchExp_subE (matchExp_varE (by simp))) ?_) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)) premsHold_nil
    (evalExp_case (RefsGC.evalExp_tupE_of (RefsGC.evalExps_cons' (evalExp_var rfl)
      (RefsGC.evalExps_cons' (evalExp_var rfl) RefsGC.evalExps_nil')))))⟩
  rcases t with t | t <;> cases t <;> rfl

set_option maxRecDepth 100000 in
/-- `$const(V128, c) = VCONST V128 c`. -/
theorem applies_const_vec (t : VecType) (c : Value) :
    Applies (simEnv B) "const" [.val (tyV (Ty.vec t : CValType)), .val c]
      (.case "VCONST" (.tuple [tyV (Ty.vec t : CValType), c])) := by
  obtain ⟨ps, ty, hd⟩ := findDef_const B
  refine ⟨ps, ty, _, hd, Or.inl (tryClauses_skip_match (matchArgs_cons_undef
    (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub ?_)) (tryClauses_hit (matchArgs_cons
      (matchArg_expA (Prims.matchExp_subE (matchExp_varE (by simp))) ?_) (matchArgs_cons
        (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)) premsHold_nil
      (evalExp_case (RefsGC.evalExp_tupE_of (RefsGC.evalExps_cons' (evalExp_var rfl)
        (RefsGC.evalExps_cons' (evalExp_var rfl) RefsGC.evalExps_nil'))))))⟩ <;>
    cases t <;> rfl

/-! ## A field read from bytes -/

/-- The SpecTec literal `c : lit_(zt)` of the field value whose little-endian encoding is `k`. -/
def litV : CStorageType → Nat → Value
  | .val (.num t), k => numV ⟨t, BitVec.ofNat t.width k⟩
  | _, k => pctV k

/-- Core's field value read from bytes encoding `k` (`readField?`, with the word as `k`). -/
def fieldOfLit : CStorageType → Nat → Val
  | .val (.num t), k => .num ⟨t, BitVec.ofNat t.width k⟩
  | .val (.vec _), k => .vec (BitVec.ofNat 128 k)
  | .pack _, k => .i32 (BitVec.ofNat 32 k)
  | _, _ => .i32 0

theorem storageSize_div8 : ∀ zt : CStorageType, 0 < storageSize zt →
    8 * (storageSize zt / 8) = storageSize zt
  | .val (.num (.int .i32)), _ | .val (.num (.int .i64)), _ | .val (.num (.float .f32)), _
  | .val (.num (.float .f64)), _ | .val (.vec .v128), _ | .pack .i8, _ | .pack .i16, _ => rfl
  | .val (.refv _), h | .val .botv, h => by simp [storageSize] at h

/-- What `readField?` reads, as one predicate. -/
def ReadSpec (zt : CStorageType) (bytes : ByteArray) (off : Nat) (v : Val) : Prop :=
  ∃ k, k < 2 ^ storageSize zt ∧ off + storageSize zt / 8 ≤ bytes.size ∧
    FwdMem.leBytesV (storageSize zt / 8) k =
      ((FwdMem.bytesV bytes).drop off).take (storageSize zt / 8) ∧ v = fieldOfLit zt k

theorem readSpec_pack {p : PackType} {bytes : ByteArray} {off : Nat} {v : Val}
    (h : readField? (.pack p) bytes off = some v) : ReadSpec (.pack p) bytes off v := by
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hb, hs⟩ := FwdMem.load_bytesV hc
  have hlt : c.toNat < 2 ^ p.width := lt_of_lt_of_eq c.isLt (by cases p <;> rfl)
  have hv : Val.i32 (c.setWidth 32) = fieldOfLit (.pack p) c.toNat :=
    congrArg Val.i32 (BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_setWidth]))
  exact ⟨c.toNat, hlt, hb, hs, hv⟩

theorem readSpec_num {t : NumType} {bytes : ByteArray} {off : Nat} {v : Val}
    (h : readField? (.val (.num t)) bytes off = some v) : ReadSpec (.val (.num t)) bytes off v := by
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hb, hs⟩ := FwdMem.load_bytesV hc
  have hlt : c.toNat < 2 ^ t.width := lt_of_lt_of_eq c.isLt
    (by rcases t with t | t <;> cases t <;> rfl)
  have hv : Val.num ⟨t, c.setWidth t.width⟩ = fieldOfLit (.val (.num t)) c.toNat :=
    congrArg Val.num (congrArg _ (BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_setWidth])))
  exact ⟨c.toNat, hlt, hb, hs, hv⟩

theorem readSpec_vec {vt : VecType} {bytes : ByteArray} {off : Nat} {v : Val}
    (h : readField? (.val (.vec vt)) bytes off = some v) : ReadSpec (.val (.vec vt)) bytes off v := by
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hb, hs⟩ := FwdMem.load_bytesV hc
  have hv : Val.vec c = fieldOfLit (.val (.vec vt)) c.toNat :=
    congrArg Val.vec (BitVec.eq_of_toNat_eq (by simp))
  exact ⟨c.toNat, c.isLt, by simpa [storageSize] using hb, by simpa [storageSize] using hs, hv⟩

/-- **What Core's `readField?` reads**: an in-bounds slice whose little-endian value `k` is below
`2 ^ storageSize zt`, and the field value `fieldOfLit zt k`. -/
theorem readField_spec : ∀ {zt : CStorageType} {bytes : ByteArray} {off : Nat} {v : Val},
    readField? zt bytes off = some v → ReadSpec zt bytes off v
  | .pack _, _, _, _, h => readSpec_pack h
  | .val (.num _), _, _, _, h => readSpec_num h
  | .val (.vec _), _, _, _, h => readSpec_vec h
  | .val (.refv _), _, _, _, h | .val .botv, _, _, _, h => by simp [readField?] at h

/-- **`$zbytes_(zt, c)`** on the literal of `k`: its `storageSize zt / 8`-byte encoding. -/
theorem zbytesCall_litV : ∀ (zt : CStorageType), 0 < storageSize zt → ∀ k, k < 2 ^ storageSize zt →
    ZBytes.zbytesCall (tyV zt) (litV zt k) =
      some (.list (FwdMem.leBytesV (storageSize zt / 8) k))
  | .val (.num t), _, k, hk => by
    have hnt : tyV (Ty.val (Ty.num t) : CStorageType) = Vec.numTypeV t := by
      rcases t with t | t <;> cases t <;> rfl
    have hz : ZBytes.zbytesCall (tyV (Ty.val (Ty.num t) : CStorageType)) (litV (.val (.num t)) k) =
        FwdMem.nbytesCall (Vec.numTypeV t) (numV ⟨t, BitVec.ofNat t.width k⟩) := by
      rw [hnt]; rcases t with t | t <;> cases t <;> rfl
    rw [hz]
    simp only [FwdMem.nbytesCall, Floats.decNumType_numTypeV, Floats.decNum_numV, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by simpa [storageSize] using hk)]
    rfl
  | .val (.vec .v128), _, k, _ => rfl
  | .pack .i8, _, k, _ => rfl
  | .pack .i16, _, k, _ => rfl
  | .val (.refv _), h, _, _ | .val .botv, h, _, _ => by simp [storageSize] at h

/-- **`$const($cunpack(zt), $cunpacknum_(zt, c))`** at the literal of `k`: the image of Core's
field value. -/
theorem evalExp_constField {P : Numerics.Profile} (hF : Floats.FloatB P B) {ρ : VarEnv}
    (hρ : ValsOnly ρ) {zt : CStorageType} {k : Nat} (h0 : 0 < storageSize zt)
    (hk : k < 2 ^ storageSize zt) (hz : ρ.findVal? "zt" = some (tyV zt))
    (hc : ρ.findVal? "c" = some (litV zt k)) :
    EvalExp (simEnv B) ρ (.callE "const" [.expA (.callE "cunpack" [.expA (.varE "zt")]),
      .expA (.callE "cunpacknum_" [.expA (.varE "zt"), .expA (.varE "c")])])
      (valV (fieldOfLit zt k)) := by
  have hcu := Vec.evalExp_call (env := simEnv B) (Aggregates.findDef_none hρ "cunpack")
    (evalArgs_cons (evalExp_var hz) evalArgs_nil) (applies_cunpack zt h0)
  match zt, h0, hk, hcu with
  | .val (.num t), h0', hk, hcu =>
    show EvalExp (simEnv B) ρ _ (valV (fieldOfLit (.val (.num t)) k))
    have hcn := Vec.evalExp_call (env := simEnv B) (Aggregates.findDef_none hρ "cunpacknum_")
      (evalArgs_cons (evalExp_var hz) (evalArgs_cons (evalExp_var hc) evalArgs_nil))
      (applies_cunpacknum_val (.num t) h0' _)
    have := Vec.evalExp_call (env := simEnv B) (Aggregates.findDef_none hρ "const")
      (evalArgs_cons hcu (evalArgs_cons hcn evalArgs_nil)) (applies_const_num t _)
    have e : valV (fieldOfLit (.val (.num t)) k) = .case "CONST" (.tuple
        [tyV (Ty.num t : CValType), litV (.val (.num t)) k]) := by
      simp only [fieldOfLit, valV, litV]
      rw [Typing.toValue_numType]
      rcases t with t | t <;> cases t <;> rfl
    rw [e]; exact this
  | .val (.vec t), h0', hk, hcu =>
    show EvalExp (simEnv B) ρ _ (valV (fieldOfLit (.val (.vec t)) k))
    have hcn := Vec.evalExp_call (env := simEnv B) (Aggregates.findDef_none hρ "cunpacknum_")
      (evalArgs_cons (evalExp_var hz) (evalArgs_cons (evalExp_var hc) evalArgs_nil))
      (applies_cunpacknum_val (.vec t) h0' _)
    have := Vec.evalExp_call (env := simEnv B) (Aggregates.findDef_none hρ "const")
      (evalArgs_cons hcu (evalArgs_cons hcn evalArgs_nil)) (applies_const_vec t _)
    have e : valV (fieldOfLit (.val (.vec t)) k) = .case "VCONST" (.tuple
        [tyV (Ty.vec t : CValType), litV (.val (.vec t)) k]) := by
      cases t
      simp only [fieldOfLit, valV, litV, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by simpa [storageSize] using hk)]
      rfl
    rw [e]; exact this
  | .pack p, _, hk, hcu =>
    show EvalExp (simEnv B) ρ _ (valV (fieldOfLit (.pack p) k))
    have hk' : (BitVec.ofNat p.width k).toNat = k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa [storageSize] using hk)]
    have hc' : ρ.findVal? "c" = some (bvV (BitVec.ofNat p.width k)) := by
      rw [hc]; simp only [litV, bvV, natV, pctV, hk']
    have hcn := Vec.evalExp_call (env := simEnv B) (Aggregates.findDef_none hρ "cunpacknum_")
      (evalArgs_cons (evalExp_var hz) (evalArgs_cons (evalExp_var hc') evalArgs_nil))
      (applies_cunpacknum_pack hF p _)
    have := Vec.evalExp_call (env := simEnv B) (Aggregates.findDef_none hρ "const")
      (evalArgs_cons hcu (evalArgs_cons hcn evalArgs_nil)) (applies_const_num (.int .i32) _)
    have e : valV (fieldOfLit (.pack p) k) = .case "CONST" (.tuple
        [tyV (Ty.num (.int .i32) : CValType), bvV ((BitVec.ofNat p.width k).setWidth 32)]) := by
      have h32 : k < 2 ^ 32 := lt_of_lt_of_le (by simpa [storageSize] using hk)
        (Nat.pow_le_pow_right (by decide) (by cases p <;> decide))
      have t₁ : ((BitVec.ofNat p.width k).setWidth 32).toNat = k := by
        rw [BitVec.toNat_setWidth, hk', Nat.mod_eq_of_lt h32]
      have t₂ : (BitVec.ofNat 32 k).toNat = k := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32]
      simp only [fieldOfLit, valV, Val.i32, numV, bvV, natV, pctV, t₁]
      exact congrArg (fun z => Value.case "CONST" (Value.tuple [tyV (Ty.num (NumType.int IntType.i32) :
        CValType), Value.case "%" (Value.tuple [Value.num (Num.natN z)])])) t₂
    rw [e]; exact this

end Silmaril.Wasm.SpecTec.Sim.R4Fwd
