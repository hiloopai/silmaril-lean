module

public import Silmaril.Wasm.SpecTec.Sim.Floats.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Float

/-!
# Float track: number-type patterns and size functions

The dispatchers and type families of the scalar numerics (`$unop_`, `$cvtop__`, `unop_`,
`cvtop__`, …) select their clause or instance with argument patterns `X <: numtype` for a
variable `X` of `Inn` or `Fnn`. After the typing track's fix (`Sem.argSubOk`) such a pattern
matches exactly the number types of its kind (`argSubOk_kindPat`). This file also evaluates
`$size`, `$sizenn`, `$sizenn1`, `$sizenn2` at every number type.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Floats

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.Wasm

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-- The kind `Inn` or `Fnn` of a number type. -/
def kindOf : NumType → IL.Id
  | .int _ => "Inn"
  | .float _ => "Fnn"

/-- The pattern `X <: numtype` with `X : K`. -/
abbrev kindPat (X K : IL.Id) : Exp := .subE (.varE X) (.varT K []) (.varT "numtype" [])

set_option maxRecDepth 100000 in
/-- A number type passes the subtype test of an `Inn` pattern exactly when it is an integer
type. -/
theorem argSubOk_inn (X : IL.Id) (t : NumType) {ρ : VarEnv} (hρ : ρ.findTyp? "Inn" = none) :
    argSubOk (simEnv B) ρ (kindPat X "Inn") (Vec.numTypeV t) = decide (kindOf t = "Inn") := by
  rcases t with t | t <;> cases t <;>
    simp only [argSubOk, subCaseOk, Vec.numTypeV, Equiv.Execution.caseNilV, hρ,
      Typing.findTyp_Inn, kindOf] <;> rfl

set_option maxRecDepth 100000 in
/-- A number type passes the subtype test of an `Fnn` pattern exactly when it is a float type. -/
theorem argSubOk_fnn (X : IL.Id) (t : NumType) {ρ : VarEnv} (hρ : ρ.findTyp? "Fnn" = none) :
    argSubOk (simEnv B) ρ (kindPat X "Fnn") (Vec.numTypeV t) = decide (kindOf t = "Fnn") := by
  rcases t with t | t <;> cases t <;>
    simp only [argSubOk, subCaseOk, Vec.numTypeV, Equiv.Execution.caseNilV, hρ,
      Typing.findTyp_Fnn, kindOf] <;> rfl

/-- `argSubOk` of a kind pattern, for both kinds. -/
theorem argSubOk_kindPat (X : IL.Id) (t : NumType) {K : IL.Id} (hK : K = "Inn" ∨ K = "Fnn")
    {ρ : VarEnv} (hρ : ρ.typs = []) :
    argSubOk (simEnv B) ρ (kindPat X K) (Vec.numTypeV t) = decide (kindOf t = K) := by
  have hf : ∀ y, ρ.findTyp? y = none := fun y => by simp [VarEnv.findTyp?, hρ]
  rcases hK with rfl | rfl
  · exact argSubOk_inn X t (hf _)
  · exact argSubOk_fnn X t (hf _)

/-- A kind pattern matching its kind binds the variable. -/
theorem matchArg_kindPat {X K : IL.Id} (hK : K = "Inn" ∨ K = "Fnn") {ρ : VarEnv}
    (hρ : ρ.typs = []) (hx : ρ.findVal? X = none) {t : NumType} (ht : kindOf t = K) :
    MatchArg (simEnv B) ρ (.expA (kindPat X K)) (.val (Vec.numTypeV t))
      (ρ.bindVal X (Vec.numTypeV t)) :=
  matchArg_expA (Equiv.Validation.matchExp_sub_iff.2
    ((Equiv.Execution.matchExp_freshVar_iff hx).2 rfl))
    (by rw [argSubOk_kindPat X t hK hρ]; exact decide_eq_true ht)

/-- A kind pattern of the other kind fails definitely. -/
theorem matchArg_kindPat_undef {X K : IL.Id} (hK : K = "Inn" ∨ K = "Fnn") {ρ : VarEnv}
    (hρ : ρ.typs = []) {t : NumType} (ht : kindOf t ≠ K) :
    ∃ n, matchArg n (simEnv B) ρ (.expA (kindPat X K)) (.val (Vec.numTypeV t)) = .error .undef :=
  Equiv.ExecBuiltins.matchArg_expA_undef_of_sub
    (by rw [argSubOk_kindPat X t hK hρ]; exact decide_eq_false ht)

/-! ## Two kind patterns (the instances of `cvtop__`, the clauses of `$cvtop__`) -/

/-- The scope after two kind patterns. -/
abbrev kscope (X₁ X₂ : IL.Id) (t₁ t₂ : NumType) : VarEnv :=
  (VarEnv.empty.bindVal X₁ (Vec.numTypeV t₁)).bindVal X₂ (Vec.numTypeV t₂)

/-- Two kind patterns match number types of their kinds. -/
theorem matchArg_kinds {X₁ X₂ K₁ K₂ : IL.Id} (hK₁ : K₁ = "Inn" ∨ K₁ = "Fnn")
    (hK₂ : K₂ = "Inn" ∨ K₂ = "Fnn") (hX₁ : X₁ ≠ "_") (hX : X₁ ≠ X₂) {t₁ t₂ : NumType}
    (ht₁ : kindOf t₁ = K₁) (ht₂ : kindOf t₂ = K₂) {pats : List Arg} {ws : List ArgV}
    {ρ : VarEnv} (h : MatchArgs (simEnv B) (kscope X₁ X₂ t₁ t₂) pats ws ρ) :
    MatchArgs (simEnv B) VarEnv.empty (.expA (kindPat X₁ K₁) :: .expA (kindPat X₂ K₂) :: pats)
      (.val (Vec.numTypeV t₁) :: .val (Vec.numTypeV t₂) :: ws) ρ :=
  matchArgs_cons (matchArg_kindPat hK₁ rfl (by simp) ht₁)
    (matchArgs_cons (matchArg_kindPat hK₂ rfl
      (by simp [Equiv.Execution.findVal?_bindVal_lit hX₁, hX]) ht₂) h)

/-- Two kind patterns fail definitely when a kind differs. -/
theorem matchArgs_kinds_undef {X₁ X₂ K₁ K₂ : IL.Id} (hK₁ : K₁ = "Inn" ∨ K₁ = "Fnn")
    (hK₂ : K₂ = "Inn" ∨ K₂ = "Fnn") (_hX₁ : X₁ ≠ "_") (_hX : X₁ ≠ X₂) {t₁ t₂ : NumType}
    (h : kindOf t₁ ≠ K₁ ∨ kindOf t₂ ≠ K₂) {pats : List Arg} {ws : List ArgV} :
    MatchArgsUndef (simEnv B) VarEnv.empty (.expA (kindPat X₁ K₁) :: .expA (kindPat X₂ K₂) :: pats)
      (.val (Vec.numTypeV t₁) :: .val (Vec.numTypeV t₂) :: ws) := by
  by_cases h₁ : kindOf t₁ = K₁
  · exact matchArgs_cons_undef_tail (matchArg_kindPat hK₁ rfl (by simp) h₁)
      (matchArgs_cons_undef (matchArg_kindPat_undef hK₂ rfl (h.resolve_left (not_not.2 h₁))))
  · exact matchArgs_cons_undef (matchArg_kindPat_undef hK₁ rfl h₁)

/-! ## `$size` and its variants -/

/-- `ntV` is `numTypeV`. -/
theorem ntV_eq (t : IntType) : IntNumeric.ntV t = Vec.numTypeV (.int t) := by cases t <;> rfl

/-- `$size(nt)` is the width, at every number type. -/
theorem callDef_size_num (t : NumType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "size" = none) (ha : EvalArgs (simEnv B) ρ args [.val (Vec.numTypeV t)]) :
    CallDef (simEnv B) ρ "size" args (natV t.width) := by
  rcases t with t | t
  · exact IntNumeric.callDef_size_int t hρ (by rw [ntV_eq]; exact ha)
  · exact Typing.callDef_size_float t hρ ha

/-- The one clause of `$sizenn`, `$sizenn1`, `$sizenn2`: `$x(nt) = $size(nt)`. -/
abbrev sizeClause : Clause :=
  .defD [.expP "nt" (.varT "numtype" [])] [.expA (.varE "nt")]
    (.callE "size" [.expA (.varE "nt")]) []

set_option maxRecDepth 100000 in
theorem findDef_sizenn : ∃ ps ty, (simEnv B).findDef? "sizenn" = some (ps, ty, [sizeClause]) :=
  ⟨_, _, rfl⟩
set_option maxRecDepth 100000 in
theorem findDef_sizenn1 : ∃ ps ty, (simEnv B).findDef? "sizenn1" = some (ps, ty, [sizeClause]) :=
  ⟨_, _, rfl⟩
set_option maxRecDepth 100000 in
theorem findDef_sizenn2 : ∃ ps ty, (simEnv B).findDef? "sizenn2" = some (ps, ty, [sizeClause]) :=
  ⟨_, _, rfl⟩

/-- A size function `$x(nt) = $size(nt)` is the width. -/
theorem callDef_sizeFun {x : IL.Id} (hd : ∃ ps ty, (simEnv B).findDef? x = some (ps, ty, [sizeClause]))
    (t : NumType) {ρ : VarEnv} {args : List Arg} (hρ : ρ.findDef? x = none)
    (ha : EvalArgs (simEnv B) ρ args [.val (Vec.numTypeV t)]) :
    CallDef (simEnv B) ρ x args (natV t.width) := by
  obtain ⟨ps, ty, hd⟩ := hd
  exact callDef_of_tryClauses hρ hd ha (tryClauses_hit (ρ₀ := VarEnv.empty.bindVal "nt" _)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) premsHold_nil
    (evalExp_callE_iff.2 (callDef_size_num t rfl
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil))))

/-- `sx` holds both signednesses (`Sim.sxV`). -/
theorem hasTyp_sxV {σ : VarEnv} (hσ : ValsOnly σ) (s : Signedness) :
    HasTyp (simEnv B) σ (.varT "sx" []) (sxV s) := by
  cases s with
  | signed => exact IntNumeric.hasTyp_sx hσ .signed
  | unsigned => exact IntNumeric.hasTyp_sx hσ .unsigned

/-- `$x(X <: numtype)` for a size function `x`, in a scope binding `X`. -/
theorem evalExp_sizeFun {x X : IL.Id}
    (hd : ∃ ps ty, (simEnv B).findDef? x = some (ps, ty, [sizeClause])) (t : NumType) {t₁ t₂ : Typ}
    {ρ : VarEnv} (hρ : ρ.findDef? x = none) (hX : ρ.findVal? X = some (Vec.numTypeV t)) :
    EvalExp (simEnv B) ρ (.callE x [.expA (.subE (.varE X) t₁ t₂)]) (natV t.width) :=
  evalExp_callE_iff.2 (callDef_sizeFun hd t hρ
    (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 hX)) Equiv.evalArgs_nil))

end Silmaril.Wasm.SpecTec.Sim.Floats
