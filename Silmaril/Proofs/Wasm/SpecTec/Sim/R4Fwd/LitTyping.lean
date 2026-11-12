module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.InitData

/-!
# The literal quantifier `c : lit_(zt)` is typed (`LitTyping`)

`lit_(storagetype)` has three instances, by subtype patterns: `num_(numtype)`, `vec_(vectype)`,
`pack_(packtype) = iN($psizenn(packtype))`. With the typing track's `Sem.argSubOk`, the image of a
storage type selects exactly its instance, and the literal of a word that fits is typed there
(`Typing.typedDep_num`, `Typing.hasTyp_vec`, `uN`). So `LitTyping` holds in every `simEnv B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.R4Fwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findTyp_lit (B : Builtins) : ∃ ps q₁ q₂ q₃, (simEnv B).findTyp? "lit_" = some (ps,
    [.instD q₁ [.expA numtypePatZ] (.aliasT (.varT "num_" [.expA (.varE "numtype")])),
     .instD q₂ [.expA vectypePatZ] (.aliasT (.varT "vec_" [.expA (.varE "vectype")])),
     .instD q₃ [.expA packtypePat] (.aliasT (.varT "pack_" [.expA (.varE "packtype")]))]) :=
  ⟨_, _, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_pack (B : Builtins) : ∃ ps q, (simEnv B).findTyp? "pack_" = some (ps,
    [.instD q [.expA (.varE "Pnn")]
      (.aliasT (.varT "iN" [.expA (.callE "psizenn" [.expA (.varE "Pnn")])]))]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_psizenn (B : Builtins) : (simEnv B).findDef? "psizenn" = some
    ([.expP "packtype" (.varT "packtype" [])], .numT .natT,
      [.defD [.expP "pt" (.varT "packtype" [])] [.expA (.varE "pt")]
        (.callE "psize" [.expA (.varE "pt")]) []]) := rfl

/-- `$psizenn(pt)` is the packed width. -/
theorem applies_psizenn (p : PackType) :
    Applies (simEnv B) "psizenn" [.val (tyV (Ty.pack p : CStorageType))] (natV p.width) :=
  ⟨_, _, _, findDef_psizenn B, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
    (matchExp_varE (by simp))) matchArgs_nil) premsHold_nil
    (Vec.evalExp_call rfl (evalArgs_cons (evalExp_var rfl) evalArgs_nil)
      (applies_psize p)))⟩

/-- A failing subtype test fails a one-pattern instance definitely. -/
theorem skip_inst {q : List Param} {e : Exp} {dt : DefTyp} {is : List Inst} {w v : Value}
    (hs : argSubOk (simEnv B) VarEnv.empty e w = false)
    (h : HasTypInsts (simEnv B) is [.val w] v) :
    HasTypInsts (simEnv B) (.instD q [.expA e] dt :: is) [.val w] v := by
  obtain ⟨n, hn⟩ : MatchArgsUndef (simEnv B) VarEnv.empty [.expA e] [.val w] :=
    matchArgs_cons_undef (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub hs)
  exact hasTypInsts_tail hn h

set_option maxRecDepth 100000 in
/-- **`LitTyping` holds in every `simEnv B`.** -/
theorem litTyping_simEnv (B : Builtins) : LitTyping (simEnv B) := by
  intro zt k ρ hρ hz h0 hk
  obtain ⟨ps, q₁, q₂, q₃, htd⟩ := findTyp_lit B
  have hl : localTyp? ρ "lit_" [.expA (.varE "zt")] = none := by
    simp [localTyp?]
  refine hasTyp_varT_of_insts hl htd (evalArgs_cons (evalExp_var hz) evalArgs_nil) ?_
  match zt, h0, hk with
  | .val (.num t), _, hk =>
    have hs : argSubOk (simEnv B) VarEnv.empty numtypePatZ (tyV (Ty.val (Ty.num t) : CStorageType))
        = true := by rcases t with t | t <;> cases t <;> rfl
    refine hasTypInsts_head (matchArgs_cons (matchArg_expA (Prims.matchExp_subE
      (matchExp_varE (by simp))) hs) matchArgs_nil) (hasTypDef_aliasT_iff.2 ?_)
    exact Typing.typedDep_num "numtype" ⟨t, BitVec.ofNat t.width k⟩ _ ⟨rfl, rfl, rfl⟩
      (by simp; rcases t with t | t <;> cases t <;> rfl)
  | .val (.vec .v128), _, hk =>
    refine skip_inst rfl (hasTypInsts_head (matchArgs_cons (matchArg_expA (Prims.matchExp_subE
      (matchExp_varE (by simp))) rfl) matchArgs_nil) (hasTypDef_aliasT_iff.2 ?_))
    have h128 : k < 2 ^ 128 := by simpa [storageSize] using hk
    have := Typing.hasTyp_vec (B := B) (ρ := VarEnv.empty.bindVal "vectype" (caseNilV "V128"))
      (e := .varE "vectype") (BitVec.ofNat 128 k) (evalExp_var (by simp))
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h128] at this
    exact this
  | .pack p, _, hk =>
    show HasTypInsts (simEnv B) _ [.val (tyV (Ty.pack p : CStorageType))] (litV (.pack p) k)
    refine skip_inst (by cases p <;> rfl) (skip_inst (by cases p <;> rfl)
      (hasTypInsts_head (matchArgs_cons (matchArg_expA (Prims.matchExp_subE
        (matchExp_varE (by simp))) (argSubOk_packtypePat_pack p rfl)) matchArgs_nil)
        (hasTypDef_aliasT_iff.2 ?_)))
    obtain ⟨ps', q', htp⟩ := findTyp_pack B
    obtain ⟨ps'', q'', htn⟩ := IntNumeric.findTyp_iN (B := B)
    refine hasTyp_varT_of_insts (by simp [localTyp?]) htp
      (evalArgs_cons (evalExp_var (v := tyV (Ty.pack p : CStorageType)) (by simp)) evalArgs_nil)
      (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
        (hasTypDef_aliasT_iff.2 ?_))
    exact hasTyp_varT_of_insts (by simp [localTyp?]) htn
      (evalArgs_cons (Vec.evalExp_call rfl (evalArgs_cons
        (evalExp_var (v := tyV (Ty.pack p : CStorageType)) (by simp)) evalArgs_nil)
        (applies_psizenn p)) evalArgs_nil)
      (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
        (hasTypDef_aliasT_iff.2 (IntNumeric.hasTyp_uN (evalExp_var (v := natV p.width) (by simp))
          (by simpa [storageSize] using hk))))
  | .val (.refv _), h, _ | .val .botv, h, _ => simp [storageSize] at h

end Silmaril.Wasm.SpecTec.Sim.R4Fwd
