module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.Common

/-!
# Round 5, pass 3, track read: `$unpackfield_`, inverted

`$unpackfield_(zt, sx?, fv)` evaluates only on Core's domain `unpackable zt sx? fv`, to the image
of `unpackField sx? fv` (`unpackfield_inv`). Off the domain each clause fails definitely:

* the first clause `(valtype, ε, val)` on a packed storage type (subtype test), a present `sx`, or a
  packed field value (subtype test of `val`);
* the second clause `(packtype, sx, PACK packtype i)` on an unpacked storage type (subtype test),
  an absent `sx`, an unpacked field value (`PACK` against another injection) or a field packed at
  another type (the bound `packtype` compared);

and `B` does not answer `$unpackfield_`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read2

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round4Int (BI)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

theorem call_unpackfield_none (ws : List ArgV) : (BI P hn host).call "unpackfield_" ws = none := by
  simp [Round4Int.BI, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

set_option maxRecDepth 100000 in
/-- The image of an unpacked storage type fails `packtype`'s subtype test. -/
theorem argSubOk_packtypePat_val (B : Builtins) {ρ : VarEnv} (hρ : ρ.typs = []) (t : CValType) :
    argSubOk (simEnv B) ρ R4Fwd.packtypePat (tyV (Ty.val t : CStorageType)) = false := by
  simp only [argSubOk]
  rw [Aggregates.subCaseOk_typs_nil hρ]
  cases t with
  | num t => rcases t with t | t <;> cases t <;> rfl
  | vec t => cases t; rfl
  | refv r => cases r; rfl
  | botv => rfl

set_option maxRecDepth 100000 in
/-- The image of a packed field value fails `val`'s subtype test. -/
theorem argSubOk_valPat_pack (B : Builtins) {ρ : VarEnv} (hρ : ρ.typs = []) (p : PackType)
    (c : BitVec p.width) :
    argSubOk (simEnv B) ρ Aggregates.valPat (fieldValV (.pack p c)) = false := by
  simp only [argSubOk]
  rw [Aggregates.subCaseOk_typs_nil hρ]
  show subCaseOk _ _ _ (.case "PACK" _) = false
  rw [Aggregates.subCaseOk_case]
  rfl

theorem optNone_undef {env : Env} {ρ : VarEnv} {v : Value} :
    MatchExpUndef env ρ (.optE none) (.opt (some v)) :=
  ⟨1, by simp [matchExp, Res.assert]⟩

theorem optSome_undef {env : Env} {ρ : VarEnv} {e : Exp} :
    MatchExpUndef env ρ (.optE (some e)) (.opt none) :=
  ⟨2, by simp [matchExp, Res.ofOption, Value.asOpt?, Bind.bind, Except.bind]⟩

/-- `PACK (packtype, i)` against the image of a value fails definitely. -/
theorem packPat_val_undef {env : Env} {ρ : VarEnv} (v : Val) :
    MatchExpUndef env ρ (.caseE "PACK" (.tupE [.varE "packtype", .varE "i"])) (valV v) := by
  rcases v with ⟨t, b⟩ | b | r
  · rcases t with t | t <;> cases t <;>
      exact Equiv.ExecBuiltins.matchExp_caseE_undef_of_ne (by decide)
  · exact Equiv.ExecBuiltins.matchExp_caseE_undef_of_ne (by decide)
  · cases r <;> exact Equiv.ExecBuiltins.matchExp_caseE_undef_of_ne (by decide)

/-- `PACK (packtype, i)` with `packtype` bound to another packed type fails definitely. -/
theorem packPat_bound_undef {env : Env} {ρ : VarEnv} {p p' : PackType} (hp : p ≠ p')
    (c : BitVec p'.width) (h : ρ.findVal? "packtype" = some (tyV (Ty.pack p : CStorageType))) :
    MatchExpUndef env ρ (.caseE "PACK" (.tupE [.varE "packtype", .varE "i"]))
      (fieldValV (.pack p' c)) := by
  refine ⟨6, ?_⟩
  have hne : tyV (Ty.pack p : CStorageType) ≠ Encode.toValue p' := by
    cases p <;> cases p' <;> first
      | exact absurd rfl hp
      | exact fun h => absurd (Value.case.inj h).1 (by decide)
  simp [matchExp, fieldValV, Value.asCase?, Value.asTuple?, Res.ofOption, Res.assert, matchExps,
    h, hne, Bind.bind, Except.bind]

/-- **`$unpackfield_` is undefined off Core's domain.** -/
theorem not_applies_unpackfield {zt : CStorageType} {sx : Option Signedness} {fv : FieldVal}
    (hu : unpackable zt sx fv = false) {u : Value} :
    ¬ Applies (simEnv (BI P hn host)) "unpackfield_" [.val (tyV zt),
      .val (.opt (sx.map Equiv.sxV)), .val (fieldValV fv)] u := by
  rintro ⟨ps, ty, cs, hd, hc⟩
  obtain ⟨ps', ty', q, hd'⟩ := R4Fwd.findDef_unpackfield (BI P hn host)
  rw [hd'] at hd
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hd
  have m₁ : ∀ t : CValType, MatchArg (simEnv (BI P hn host)) VarEnv.empty
      (.expA Aggregates.valtypePat) (.val (tyV (Ty.val t : CStorageType)))
      (VarEnv.empty.bindVal "valtype" (tyV (Ty.val t : CStorageType))) := fun t =>
    matchArg_expA (Aggregates.matchExp_subE (matchExp_varE rfl))
      (Aggregates.argSubOk_valtypePat _ rfl t)
  have m₂ : ∀ p : PackType, MatchArg (simEnv (BI P hn host)) VarEnv.empty
      (.expA R4Fwd.packtypePat) (.val (tyV (Ty.pack p : CStorageType)))
      (VarEnv.empty.bindVal "packtype" (tyV (Ty.pack p : CStorageType))) := fun p =>
    matchArg_expA (Aggregates.matchExp_subE (matchExp_varE rfl))
      (R4Fwd.argSubOk_packtypePat_pack p rfl)
  have hU : TryClausesUndef (simEnv (BI P hn host))
      [.defD q Aggregates.unpackPats (.varE "val") [], R4Fwd.unpackClause₂]
      [.val (tyV zt), .val (.opt (sx.map Equiv.sxV)), .val (fieldValV fv)] := by
    cases zt with
    | val t =>
      refine IntNumeric.tryClausesUndef_skip_match ?_ (IntNumeric.tryClausesUndef_skip_match
        (matchArgs_cons_undef (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub
          (argSubOk_packtypePat_val _ rfl t))) IntNumeric.tryClausesUndef_nil)
      rcases sx with _ | sx
      · cases fv with
        | val v => simp [unpackable] at hu
        | pack p c => exact matchArgs_cons_undef_tail (m₁ t) (matchArgs_cons_undef_tail
            (matchArg_expA Aggregates.matchExp_optNone) (matchArgs_cons_undef
              (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (argSubOk_valPat_pack _ rfl p c))))
      · exact matchArgs_cons_undef_tail (m₁ t) (matchArgs_cons_undef
          (matchArg_expA_undef optNone_undef))
    | pack p =>
      refine IntNumeric.tryClausesUndef_skip_match (matchArgs_cons_undef
        (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (R4Fwd.argSubOk_valtypePat_pack p rfl)))
        (IntNumeric.tryClausesUndef_skip_match ?_ IntNumeric.tryClausesUndef_nil)
      rcases sx with _ | sx
      · exact matchArgs_cons_undef_tail (m₂ p) (matchArgs_cons_undef
          (matchArg_expA_undef optSome_undef))
      · have m₃ : MatchArg (simEnv (BI P hn host))
            (VarEnv.empty.bindVal "packtype" (tyV (Ty.pack p : CStorageType)))
            (.expA (.optE (some (.varE "sx")))) (.val (.opt ((some sx).map Equiv.sxV)))
            ((VarEnv.empty.bindVal "packtype" (tyV (Ty.pack p : CStorageType))).bindVal "sx"
              (Equiv.sxV sx)) :=
          matchArg_expA ⟨2, by simp [matchExp, Res.ofOption, Value.asOpt?]⟩
        refine matchArgs_cons_undef_tail (m₂ p) (matchArgs_cons_undef_tail m₃
          (matchArgs_cons_undef (matchArg_expA_undef ?_)))
        cases fv with
        | val v => exact packPat_val_undef v
        | pack p' c =>
          have hp : p ≠ p' := by
            intro e
            subst e
            simp [unpackable] at hu
          exact packPat_bound_undef hp c (by simp)
  rcases hc with hc | ⟨-, hb⟩
  · exact Equiv.ExecNumeric.not_tryClauses_and_undef hc hU
  · rw [simEnv, Env.builtins_withBuiltins, call_unpackfield_none] at hb
    cases hb

/-- **`$unpackfield_(zt, sx?, fv)`, read back**: Core's domain, and the image of `unpackField`. -/
theorem unpackfield_inv (zt : CStorageType) (sx : Option Signedness) (fv : FieldVal) {u : Value}
    (h : Applies (simEnv (BI P hn host)) "unpackfield_" [.val (tyV zt),
      .val (.opt (sx.map Equiv.sxV)), .val (fieldValV fv)] u) :
    unpackable zt sx fv = true ∧ u = valV (unpackField sx fv) := by
  by_cases hu : unpackable zt sx fv = true
  · refine ⟨hu, ?_⟩
    cases zt with
    | val t =>
      cases sx with
      | some sx => simp [unpackable] at hu
      | none =>
      cases fv with
      | pack p' c => simp [unpackable] at hu
      | val v =>
      obtain ⟨⟨ps, t', q, rest, hd⟩, hzt, hv⟩ := Aggregates.unpackDef_simEnv (BI P hn host)
      exact Applies.unique h ⟨ps, t', _, hd, Or.inl (tryClauses_hit
        (ρ₀ := ((VarEnv.empty.bindVal "valtype" (tyV (Ty.val t : CStorageType))).bindVal
          "val" (valV v)))
        (matchArgs_cons (matchArg_expA (Aggregates.matchExp_subE (matchExp_varE rfl))
          (hzt _ rfl t)) (matchArgs_cons (matchArg_expA Aggregates.matchExp_optNone)
          (matchArgs_cons (matchArg_expA (Aggregates.matchExp_subE (matchExp_varE rfl))
            (hv _ rfl v)) matchArgs_nil)))
        premsHold_nil (evalExp_var rfl))⟩
    | pack p =>
      cases sx with
      | none => simp [unpackable] at hu
      | some sx =>
      cases fv with
      | val v => simp [unpackable] at hu
      | pack p' c =>
      obtain rfl : p = p' := by simpa [unpackable] using hu
      exact Applies.unique h (R4Fwd.applies_unpackfield_pack (Prims.floatB_builtins hn host) p sx c)
  · exact absurd h (not_applies_unpackfield (Bool.of_not_eq_true hu))

end Silmaril.Wasm.SpecTec.Sim.Round5.Read2
