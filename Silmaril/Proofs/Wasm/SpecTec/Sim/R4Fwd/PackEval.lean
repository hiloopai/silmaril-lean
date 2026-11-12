module

public import Silmaril.Wasm.SpecTec.Sim.R4Fwd.Defs

/-!
# Track r4-fwd: `$packfield_`, `$unpackfield_`, `$psize` on packed storage types

Round 2's aggregates track proved the field reads and writes for unpacked storage types only:
under the evaluator then, `$packfield_`'s first clause `valtype <: storagetype` caught every
storage type (finding 2 of that track). Since the typing track's fix (`Sem.argSubOk`), a `SubE`
argument pattern tests its subtype, so at a packed type `I8`/`I16` the first clauses of
`$packfield_` and `$unpackfield_` definitely fail and their second clauses fire:

* `$packfield_(packtype, CONST I32 i) = PACK packtype $wrap__(32, $psize(packtype), i)`;
* `$unpackfield_(packtype, sx, PACK packtype i) = CONST I32 $extend__($psize(packtype), 32, sx, i)`.

This file evaluates both at every storage type, given that `B` interprets `$wrap__` and
`$extend__` as the float track's `floatCall` does (`Floats.FloatB`): `applies_packfield` is Core's
`packField` on `packable` arguments, `applies_unpackfield` is Core's `unpackField` on
`unpackable` ones.
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
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## The clauses -/

/-- The pattern `packtype <: storagetype`. -/
abbrev packtypePat : Exp := .subE (.varE "packtype") (.varT "packtype" []) (.varT "storagetype" [])

/-- `$packfield_`'s second clause. -/
abbrev packClause₂ : Clause :=
  .defD [.expP "packtype" (.varT "packtype" []),
      .expP "i" (.varT "num_" [.expA (.caseE "I32" (.tupE []))])]
    [.expA packtypePat, .expA (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i"]))]
    (.caseE "PACK" (.tupE [.varE "packtype", .callE "wrap__" [.expA (.numE (.natN 32)),
      .expA (.callE "psize" [.expA (.varE "packtype")]), .expA (.varE "i")]])) []

/-- `$unpackfield_`'s second clause. -/
abbrev unpackClause₂ : Clause :=
  .defD [.expP "packtype" (.varT "packtype" []), .expP "sx" (.varT "sx" []),
      .expP "i" (.varT "iN" [.expA (.callE "psizenn" [.expA (.varE "packtype")])])]
    [.expA packtypePat, .expA (.optE (some (.varE "sx"))),
      .expA (.caseE "PACK" (.tupE [.varE "packtype", .varE "i"]))]
    (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .callE "extend__" [.expA (.callE "psize"
      [.expA (.varE "packtype")]), .expA (.numE (.natN 32)), .expA (.varE "sx"),
      .expA (.varE "i")]])) []

set_option maxRecDepth 100000 in
theorem findDef_packfield (B : Builtins) :
    ∃ ps t q, (simEnv B).findDef? "packfield_" = some (ps, t,
      [.defD q Aggregates.packPats (.subE (.varE "val") (.varT "val" []) (.varT "fieldval" [])) [],
       packClause₂]) := ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_unpackfield (B : Builtins) :
    ∃ ps t q, (simEnv B).findDef? "unpackfield_" = some (ps, t,
      [.defD q Aggregates.unpackPats (.varE "val") [], unpackClause₂]) := ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_psize (B : Builtins) :
    (simEnv B).findDef? "psize" = some ([.expP "packtype" (.varT "packtype" [])], .numT .natT,
      [.defD [] [.expA (.caseE "I8" (.tupE []))] (.numE (.natN 8)) [],
       .defD [] [.expA (.caseE "I16" (.tupE []))] (.numE (.natN 16)) []]) := rfl

set_option maxRecDepth 100000 in
theorem findDef_wrap (B : Builtins) : ∃ ps t, (simEnv B).findDef? "wrap__" = some (ps, t, []) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_extend (B : Builtins) :
    ∃ ps t, (simEnv B).findDef? "extend__" = some (ps, t, []) := ⟨_, _, rfl⟩

/-! ## Subtype tests at packed types -/

set_option maxRecDepth 100000 in
theorem argSubOk_valtypePat_pack (p : PackType) {ρ : VarEnv} (hρ : ρ.typs = []) :
    argSubOk (simEnv B) ρ Aggregates.valtypePat (tyV (Ty.pack p : CStorageType)) = false := by
  simp only [argSubOk]
  rw [Aggregates.subCaseOk_typs_nil hρ]
  cases p <;> rfl

set_option maxRecDepth 100000 in
theorem argSubOk_packtypePat_pack (p : PackType) {ρ : VarEnv} (hρ : ρ.typs = []) :
    argSubOk (simEnv B) ρ packtypePat (tyV (Ty.pack p : CStorageType)) = true := by
  simp only [argSubOk]
  rw [Aggregates.subCaseOk_typs_nil hρ]
  cases p <;> rfl

/-! ## `$psize`, `$wrap__`, `$extend__` -/

/-- `$psize(pt)` is the packed width. -/
theorem applies_psize (p : PackType) :
    Applies (simEnv B) "psize" [.val (tyV (Ty.pack p : CStorageType))] (natV p.width) := by
  refine ⟨_, _, _, findDef_psize B, Or.inl ?_⟩
  cases p with
  | i8 => exact tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
      matchArgs_nil) premsHold_nil RefsGC.evalExp_num'
  | i16 => exact tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
      (matchExp_caseE_undef (by decide)))) (tryClauses_hit (matchArgs_cons (matchArg_expA
        (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil) premsHold_nil RefsGC.evalExp_num')

/-- `$wrap__(32, N, i)` under `FloatB`. -/
theorem applies_wrap {P : Numerics.Profile} (hF : Floats.FloatB P B) (N : Nat) (b : BitVec 32) :
    Applies (simEnv B) "wrap__" [.val (natV 32), .val (natV N), .val (bvV b)]
      (bvV (b.setWidth N)) :=
  Prims.applies_of_noClause (findDef_wrap B) (hF _ _ _ (by
    simp only [Floats.floatCall, show "wrap__" ∈ Floats.floatNames by decide, ite_true]
    show Floats.wrapBits 32 N (bvV b) = _
    simp [Floats.wrapBits]))

/-- `$extend__(N, 32, sx, i)` under `FloatB`. -/
theorem applies_extend {P : Numerics.Profile} (hF : Floats.FloatB P B) (N : Nat)
    (sx : Signedness) (b : BitVec N) :
    Applies (simEnv B) "extend__" [.val (natV N), .val (natV 32), .val (Equiv.sxV sx), .val (bvV b)]
      (bvV (match sx with | .signed => b.signExtend 32 | .unsigned => b.setWidth 32)) :=
  Prims.applies_of_noClause (findDef_extend B) (hF _ _ _ (by
    simp only [Floats.floatCall, show "extend__" ∈ Floats.floatNames by decide, ite_true]
    show Floats.extendBits N 32 (Equiv.sxV sx) (bvV b) = _
    cases sx <;> simp [Floats.extendBits, IntNumeric.asSx?, Equiv.sxV]))

/-! ## `$packfield_` -/

theorem toValue_pack (p : PackType) : Encode.toValue p = tyV (Ty.pack p : CStorageType) := by
  cases p <;> rfl

/-- `$packfield_(I8|I16, CONST I32 b)`: the second clause. -/
theorem applies_packfield_pack {P : Numerics.Profile} (hF : Floats.FloatB P B) (p : PackType)
    (b : BitVec 32) :
    Applies (simEnv B) "packfield_" [.val (tyV (Ty.pack p : CStorageType)), .val (valV (.i32 b))]
      (fieldValV (.pack p (b.setWidth p.width))) := by
  obtain ⟨ps, t, q, hd⟩ := findDef_packfield B
  refine ⟨ps, t, _, hd, Or.inl (tryClauses_skip_match (matchArgs_cons_undef
    (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (argSubOk_valtypePat_pack p rfl))) ?_)⟩
  refine tryClauses_hit (ρ₀ := (VarEnv.empty.bindVal "packtype" (tyV (Ty.pack p : CStorageType))).bindVal
      "i" (pctV b.toNat))
    (matchArgs_cons (matchArg_expA (Prims.matchExp_subE (matchExp_varE (by simp)))
      (argSubOk_packtypePat_pack p rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE (Equiv.Validation.matchExp_tup_iff.2
        ⟨_, rfl, Equiv.Execution.matchExps_two_iff.2 ⟨_, _, _, rfl,
          matchExp_caseE matchExp_tupE_nil, matchExp_varE rfl⟩⟩))) matchArgs_nil))
    premsHold_nil ?_
  have hw := applies_wrap hF p.width b
  simp only [fieldValV, toValue_pack]
  exact evalExp_case (evalExp_tup2 (evalExp_var rfl)
    (Vec.evalExp_call rfl (evalArgs_cons RefsGC.evalExp_num' (evalArgs_cons
      (Vec.evalExp_call rfl (evalArgs_cons (evalExp_var rfl) evalArgs_nil)
        (applies_psize p))
      (evalArgs_cons (evalExp_var rfl) evalArgs_nil))) hw))

/-- **`$packfield_(zt, val)` is Core's `packField`**, on its domain `packable`. -/
theorem applies_packfield {P : Numerics.Profile} (hF : Floats.FloatB P B) :
    ∀ (zt : CStorageType) (v : Val), packable zt v = true →
      Applies (simEnv B) "packfield_" [.val (tyV zt), .val (valV v)] (fieldValV (packField zt v))
  | .val t, v, _ => by
    obtain ⟨ps, ty, q, hd⟩ := findDef_packfield B
    refine ⟨ps, ty, _, hd, Or.inl (tryClauses_hit
      (ρ₀ := (VarEnv.empty.bindVal "valtype" (tyV (Ty.val t : CStorageType))).bindVal "val" (valV v))
      (matchArgs_cons (matchArg_expA (Prims.matchExp_subE (matchExp_varE (by simp)))
        (Aggregates.argSubOk_valtypePat B rfl t))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
      premsHold_nil ?_)⟩
    simpa [packField, fieldValV] using
      (RefsGC.evalExp_sub_of (evalExp_var rfl) :
        EvalExp (simEnv B) ((VarEnv.empty.bindVal "valtype" (tyV (Ty.val t : CStorageType))).bindVal
          "val" (valV v)) (.subE (.varE "val") (.varT "val" []) (.varT "fieldval" [])) (valV v))
  | .pack p, .num ⟨.int .i32, b⟩, _ => applies_packfield_pack hF p b
  | .pack _, .num ⟨.int .i64, _⟩, h => by simp [packable] at h
  | .pack _, .num ⟨.float _, _⟩, h => by simp [packable] at h
  | .pack _, .vec _, h => by simp [packable] at h
  | .pack _, .ref _, h => by simp [packable] at h

/-! ## `$unpackfield_` -/

/-- `$unpackfield_(I8|I16, sx, PACK pt c)`: the second clause. -/
theorem applies_unpackfield_pack {P : Numerics.Profile} (hF : Floats.FloatB P B) (p : PackType)
    (sx : Signedness) (c : BitVec p.width) :
    Applies (simEnv B) "unpackfield_" [.val (tyV (Ty.pack p : CStorageType)),
      .val (.opt (some (Equiv.sxV sx))), .val (fieldValV (.pack p c))]
      (valV (unpackField (some sx) (.pack p c))) := by
  obtain ⟨ps, t, q, hd⟩ := findDef_unpackfield B
  refine ⟨ps, t, _, hd, Or.inl (tryClauses_skip_match (matchArgs_cons_undef
    (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (argSubOk_valtypePat_pack p rfl))) ?_)⟩
  let ρ₀ : VarEnv := ((VarEnv.empty.bindVal "packtype" (tyV (Ty.pack p : CStorageType))).bindVal
      "sx" (Equiv.sxV sx)).bindVal "i" (pctV c.toNat)
  refine tryClauses_hit (ρ₀ := ρ₀)
    (matchArgs_cons (matchArg_expA (Prims.matchExp_subE (matchExp_varE (by simp)))
      (argSubOk_packtypePat_pack p rfl))
      (matchArgs_cons (matchArg_expA ⟨2, by simp [matchExp, Res.ofOption, Value.asOpt?]⟩)
        (matchArgs_cons (matchArg_expA (matchExp_caseE (Equiv.Validation.matchExp_tup_iff.2
          ⟨_, rfl, Equiv.Execution.matchExps_two_iff.2 ⟨_, _, _, rfl,
            (Equiv.Execution.matchExp_boundVar_iff rfl).2 ⟨toValue_pack p, rfl⟩,
            matchExp_varE rfl⟩⟩))) matchArgs_nil)))
    premsHold_nil ?_
  have he := applies_extend hF p.width sx c
  have hv : valV (unpackField (some sx) (.pack p c)) = .case "CONST" (.tuple [caseNilV "I32",
      bvV (match sx with | .signed => c.signExtend 32 | .unsigned => c.setWidth 32)]) := by
    cases sx <;> rfl
  rw [hv]
  exact evalExp_case (evalExp_tup2 (evalExp_case (RefsGC.evalExp_tupE_of RefsGC.evalExps_nil'))
    (Vec.evalExp_call rfl (evalArgs_cons
      (Vec.evalExp_call rfl (evalArgs_cons (evalExp_var rfl) evalArgs_nil)
        (applies_psize p))
      (evalArgs_cons RefsGC.evalExp_num' (evalArgs_cons (evalExp_var rfl)
        (evalArgs_cons (evalExp_var rfl) evalArgs_nil)))) he))

end Silmaril.Wasm.SpecTec.Sim.R4Fwd
