module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.ConvCall
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Dispatch

/-!
# Float track: `$cvtop__`, every conversion

`$cvtop__(nt_1, nt_2, cvtop, c)` (`Original.d507`) has nine clauses, selected by the kinds of
the two number types and by the operator: `EXTEND`, `WRAP` (`Inn`, `Inn`), `TRUNC`, `TRUNC_SAT`
(`Fnn`, `Inn`), `CONVERT` (`Inn`, `Fnn`), `PROMOTE`, `DEMOTE` (`Fnn`, `Fnn`), and two
`REINTERPRET` clauses guarded by `$size(nt_1) = $size(nt_2)`. At the encoding of each Core
`ConvertOp`, every earlier clause fails on a kind or on the operator (`skipCvt`) and the clause
of the operator calls its primitive.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Floats

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.Execution (pctV findVal?_bindVal_lit)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d507)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit
  ConvertOp.source ConvertOp.target numV

variable {B : Builtins} {P : Profile}

set_option maxRecDepth 100000 in
theorem findDef_cvtop : (simEnv B).findDef? "cvtop__" = IntNumeric.defOf Original.d507 := rfl

/-- A `$cvtop__` clause of other kinds, or for another operator, is skipped. -/
theorem skipCvt {X₁ X₂ K₁ K₂ : IL.Id} (hK₁ : K₁ = "Inn" ∨ K₁ = "Fnn")
    (hK₂ : K₂ = "Inn" ∨ K₂ = "Fnn") (hX₁ : X₁ ≠ "_") (hX : X₁ ≠ X₂) {o o' : MixopS}
    {inner : Exp} {pats : List Arg} {t₁ t₂ : NumType} {p : Value} {ws : List ArgV}
    (h : kindOf t₁ ≠ K₁ ∨ kindOf t₂ ≠ K₂ ∨ o ≠ o') :
    MatchArgsUndef (simEnv B) VarEnv.empty
      (.expA (kindPat X₁ K₁) :: .expA (kindPat X₂ K₂) :: .expA (.caseE o' inner) :: pats)
      (.val (Vec.numTypeV t₁) :: .val (Vec.numTypeV t₂) :: .val (.case o p) :: ws) := by
  by_cases h₁ : kindOf t₁ = K₁
  · have m₁ := matchArg_kindPat (B := B) (X := X₁) hK₁ (ρ := VarEnv.empty) rfl (by simp) h₁
    by_cases h₂ : kindOf t₂ = K₂
    · have hne : o ≠ o' := (h.resolve_left (not_not.2 h₁)).resolve_left (not_not.2 h₂)
      exact matchArgs_cons_undef_tail m₁ (matchArgs_cons_undef_tail
        (matchArg_kindPat hK₂ rfl (by simp [findVal?_bindVal_lit hX₁, hX]) h₂)
        (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef hne))))
    · exact matchArgs_cons_undef_tail m₁ (matchArgs_cons_undef (matchArg_kindPat_undef hK₂ rfl h₂))
  · exact matchArgs_cons_undef (matchArg_kindPat_undef hK₁ rfl h₁)

/-- The operator pattern `o sx` and the operand pattern of a `$cvtop__` clause. -/
theorem matchArgs_opSx {s : Signedness} {ρ : VarEnv} (hs : ρ.findVal? "sx" = none) {v : IL.Id}
    (hv : (ρ.bindVal "sx" (sxV s)).findVal? v = none) {o : MixopS} {a : Value} :
    MatchArgs (simEnv B) ρ [.expA (.caseE o (.varE "sx")), .expA (.varE v)]
      [.val (.case o (sxV s)), .val a] ((ρ.bindVal "sx" (sxV s)).bindVal v a) :=
  matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE hs)))
    (matchArgs_cons (matchArg_expA (matchExp_varE hv)) matchArgs_nil)

/-- The operator pattern `o` and the operand pattern of a `$cvtop__` clause. -/
theorem matchArgs_opNil {ρ : VarEnv} {v : IL.Id} (hv : ρ.findVal? v = none) {o : MixopS}
    {a : Value} :
    MatchArgs (simEnv B) ρ [.expA (.caseE o (.tupE [])), .expA (.varE v)]
      [.val (.case o (.tuple [])), .val a] (ρ.bindVal v a) :=
  matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
    (matchArgs_cons (matchArg_expA (matchExp_varE hv)) matchArgs_nil)

/-- `$sizenn1(X₁), $sizenn2(X₂)` and the rest of the arguments. -/
theorem evalArgs_sizes {X₁ X₂ : IL.Id} {t₁ t₂ : NumType} {ρ : VarEnv}
    (h₁ : ρ.findVal? X₁ = some (Vec.numTypeV t₁)) (h₂ : ρ.findVal? X₂ = some (Vec.numTypeV t₂))
    (hd₁ : ρ.findDef? "sizenn1" = none) (hd₂ : ρ.findDef? "sizenn2" = none) {u₁ u₂ u₃ u₄ : Typ}
    {rest : List Arg} {ws : List ArgV} (hr : EvalArgs (simEnv B) ρ rest ws) :
    EvalArgs (simEnv B) ρ (.expA (.callE "sizenn1" [.expA (.subE (.varE X₁) u₁ u₂)]) ::
      .expA (.callE "sizenn2" [.expA (.subE (.varE X₂) u₃ u₄)]) :: rest)
      (.val (natV t₁.width) :: .val (natV t₂.width) :: ws) :=
  Equiv.evalArgs_cons (evalExp_sizeFun findDef_sizenn1 t₁ hd₁ h₁)
    (Equiv.evalArgs_cons (evalExp_sizeFun findDef_sizenn2 t₂ hd₂ h₂) hr)

/-- Variables, as trailing arguments. -/
theorem evalArgs_vars {ρ : VarEnv} {x y : IL.Id} {a b : Value} (hx : ρ.findVal? x = some a)
    (hy : ρ.findVal? y = some b) :
    EvalArgs (simEnv B) ρ [.expA (.varE x), .expA (.varE y)] [.val a, .val b] :=
  Equiv.evalArgs_cons (evalExp_varE_iff.2 hx)
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 hy) Equiv.evalArgs_nil)

/-- A variable, as the trailing argument. -/
theorem evalArgs_var1 {ρ : VarEnv} {x : IL.Id} {a : Value} (hx : ρ.findVal? x = some a) :
    EvalArgs (simEnv B) ρ [.expA (.varE x)] [.val a] :=
  Equiv.evalArgs_cons (evalExp_varE_iff.2 hx) Equiv.evalArgs_nil

/-- The arguments of `$cvtop__`. -/
abbrev cvtArgs (op : ConvertOp) (x : BitVec op.source.width) : List ArgV :=
  [.val (Vec.numTypeV op.source), .val (Vec.numTypeV op.target), .val (Vec.cvtOpV op),
    .val (numV ⟨op.source, x⟩)]

/-- A clause skipped on its first kind. -/
theorem skipK1 {X₁ X₂ K₁ K₂ : IL.Id} (hK₁ : K₁ = "Inn" ∨ K₁ = "Fnn")
    (hK₂ : K₂ = "Inn" ∨ K₂ = "Fnn") (hX₁ : X₁ ≠ "_") (hX : X₁ ≠ X₂) {o o' : MixopS}
    {inner : Exp} {pats : List Arg} {t₁ t₂ : NumType} {p : Value} {ws : List ArgV}
    (h : kindOf t₁ ≠ K₁) :
    MatchArgsUndef (simEnv B) VarEnv.empty
      (.expA (kindPat X₁ K₁) :: .expA (kindPat X₂ K₂) :: .expA (.caseE o' inner) :: pats)
      (.val (Vec.numTypeV t₁) :: .val (Vec.numTypeV t₂) :: .val (.case o p) :: ws) :=
  skipCvt hK₁ hK₂ hX₁ hX (.inl h)

/-- A clause skipped on its second kind. -/
theorem skipK2 {X₁ X₂ K₁ K₂ : IL.Id} (hK₁ : K₁ = "Inn" ∨ K₁ = "Fnn")
    (hK₂ : K₂ = "Inn" ∨ K₂ = "Fnn") (hX₁ : X₁ ≠ "_") (hX : X₁ ≠ X₂) {o o' : MixopS}
    {inner : Exp} {pats : List Arg} {t₁ t₂ : NumType} {p : Value} {ws : List ArgV}
    (h : kindOf t₂ ≠ K₂) :
    MatchArgsUndef (simEnv B) VarEnv.empty
      (.expA (kindPat X₁ K₁) :: .expA (kindPat X₂ K₂) :: .expA (.caseE o' inner) :: pats)
      (.val (Vec.numTypeV t₁) :: .val (Vec.numTypeV t₂) :: .val (.case o p) :: ws) :=
  skipCvt hK₁ hK₂ hX₁ hX (.inr (.inl h))

/-- A clause skipped on its operator. -/
theorem skipOpC {X₁ X₂ K₁ K₂ : IL.Id} (hK₁ : K₁ = "Inn" ∨ K₁ = "Fnn")
    (hK₂ : K₂ = "Inn" ∨ K₂ = "Fnn") (hX₁ : X₁ ≠ "_") (hX : X₁ ≠ X₂) {o o' : MixopS}
    {inner : Exp} {pats : List Arg} {t₁ t₂ : NumType} {p : Value} {ws : List ArgV}
    (h : o ≠ o') :
    MatchArgsUndef (simEnv B) VarEnv.empty
      (.expA (kindPat X₁ K₁) :: .expA (kindPat X₂ K₂) :: .expA (.caseE o' inner) :: pats)
      (.val (Vec.numTypeV t₁) :: .val (Vec.numTypeV t₂) :: .val (.case o p) :: ws) :=
  skipCvt hK₁ hK₂ hX₁ hX (.inr (.inr h))

/-- `$size(X₁) = $size(X₂)` holds at two number types of the same width. -/
theorem premsHold_sameSize {ρ : VarEnv} {X₁ X₂ : IL.Id} {t₁ t₂ : NumType}
    (h₁ : ρ.findVal? X₁ = some (Vec.numTypeV t₁)) (h₂ : ρ.findVal? X₂ = some (Vec.numTypeV t₂))
    (hd : ρ.findDef? "size" = none) (hw : t₁.width = t₂.width) {u₁ u₂ u₃ u₄ : Typ} :
    PremsHold (simEnv B) ρ [.ifPr (.cmpE .eqOp .boolT
      (.callE "size" [.expA (.subE (.varE X₁) u₁ u₂)])
      (.callE "size" [.expA (.subE (.varE X₂) u₃ u₄)]))] ρ := by
  have e₁ : EvalExp (simEnv B) ρ (.callE "size" [.expA (.subE (.varE X₁) u₁ u₂)])
      (natV t₁.width) := evalExp_callE_iff.2 (callDef_size_num t₁ hd
        (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 h₁)) Equiv.evalArgs_nil))
  have e₂ : EvalExp (simEnv B) ρ (.callE "size" [.expA (.subE (.varE X₂) u₃ u₄)])
      (natV t₁.width) := hw ▸ evalExp_callE_iff.2 (callDef_size_num t₂ hd
        (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 h₂)) Equiv.evalArgs_nil))
  have hc : EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT
      (.callE "size" [.expA (.subE (.varE X₁) u₁ u₂)])
      (.callE "size" [.expA (.subE (.varE X₂) u₃ u₄)])) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, e₁, e₂, by simp [cmpValues]⟩
  exact Equiv.Validation.premsHold_cons_iff.2 ⟨_, Equiv.Validation.premHolds_if_iff.2 ⟨rfl, hc⟩,
    Equiv.Validation.premsHold_nil_iff.2 rfl⟩

/-- `Det` for every conversion other than `promote`, `demote`. -/
theorem det_of {op : ConvertOp} (h₁ : op ≠ .promote) (h₂ : op ≠ .demote) : Det op := ⟨h₁, h₂⟩

/-- What `FloatAgree.cvtop` asks of a result list. -/
def CvtOk (P : Profile) (op : ConvertOp) (x : BitVec op.source.width) (L : List Value) : Prop :=
  (∀ c, c ∈ L ↔ ∃ z, convertP P op x (.ok z) ∧ c = numV ⟨op.target, z⟩) ∧
    (L = [] ↔ ∃ e, convertP P op x (.error e))

/-- The clause of a deterministic, always successful conversion. -/
theorem cvtOk_single {op : ConvertOp} (hop : Det op) {x : BitVec op.source.width}
    {w : BitVec op.target.width} (hw : convert op x = .ok w) :
    CvtOk P op x [numV ⟨op.target, w⟩] := agree_single hop hw

set_option maxRecDepth 100000 in
/-- `wrap`. -/
theorem cvtop_wrap (hB : FloatB P B) (x : BitVec 64) :
    Applies (simEnv B) "cvtop__" (cvtArgs .wrap x) (.list [bvV (x.setWidth 32)]) := by
  refine ⟨_, _, _, findDef_cvtop, Or.inl ?_⟩
  refine tryClauses_skip_match (skipOpC (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by decide)) ?_
  exact tryClauses_hit (matchArg_kinds (.inl rfl) (.inl rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opNil (by simp))) premsHold_nil
    (IntNumeric.evalExp_list1Call (callDef_floatPrim hB ⟨_, _, rfl⟩ rfl
      (evalArgs_sizes (t₁ := .int .i64) (t₂ := .int .i32) (by simp) (by simp) rfl rfl (evalArgs_var1 (by simp; rfl)))
      (floatCall_wrap P 64 32 x)))

set_option maxRecDepth 100000 in
/-- `extend`. -/
theorem cvtop_extend (hB : FloatB P B) (s : Signedness) (x : BitVec 32) :
    Applies (simEnv B) "cvtop__" (cvtArgs (.extend s) x)
      (.list [bvV (match s with
        | .signed => x.signExtend 64 | .unsigned => x.setWidth 64)]) := by
  refine ⟨_, _, _, findDef_cvtop, Or.inl ?_⟩
  exact tryClauses_hit (matchArg_kinds (.inl rfl) (.inl rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opSx (by simp) (by simp))) premsHold_nil
    (IntNumeric.evalExp_list1Call (callDef_floatPrim hB ⟨_, _, rfl⟩ rfl
      (evalArgs_sizes (t₁ := .int .i32) (t₂ := .int .i64) (by simp) (by simp) rfl rfl (evalArgs_vars (by simp) (by simp; rfl)))
      (floatCall_extend P 32 64 s x)))

set_option maxRecDepth 100000 in
/-- `trunc`. -/
theorem cvtop_trunc (hB : FloatB P B) (f : FloatType) (i : IntType) (s : Signedness)
    (x : BitVec f.width) :
    Applies (simEnv B) "cvtop__" (cvtArgs (.trunc f i s) x)
      (.list (((convRes P (.trunc f i s) x).map fun z => numV ⟨.int i, z⟩).toList)) := by
  refine ⟨_, _, _, findDef_cvtop, Or.inl ?_⟩
  refine tryClauses_skip_match (skipK1 (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK1 (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  exact tryClauses_hit (matchArg_kinds (.inr rfl) (.inl rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opSx (by simp) (by simp))) premsHold_nil
    (IntNumeric.evalExp_liftCall (callDef_floatPrim hB ⟨_, _, rfl⟩ rfl
      (evalArgs_sizes (t₁ := .float f) (t₂ := .int i) (by simp) (by simp) rfl rfl (evalArgs_vars (by simp) (by simp)))
      (floatCall_trunc P f i s x)))

set_option maxRecDepth 100000 in
/-- `trunc_sat`. -/
theorem cvtop_truncSat (hB : FloatB P B) (f : FloatType) (i : IntType) (s : Signedness)
    (x : BitVec f.width) :
    Applies (simEnv B) "cvtop__" (cvtArgs (.truncSat f i s) x)
      (.list (((convRes P (.truncSat f i s) x).map fun z => numV ⟨.int i, z⟩).toList)) := by
  refine ⟨_, _, _, findDef_cvtop, Or.inl ?_⟩
  refine tryClauses_skip_match (skipK1 (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK1 (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipOpC (.inr rfl) (.inl rfl) (by decide) (by decide)
    (by decide)) ?_
  exact tryClauses_hit (matchArg_kinds (.inr rfl) (.inl rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opSx (by simp) (by simp))) premsHold_nil
    (IntNumeric.evalExp_liftCall (callDef_floatPrim hB ⟨_, _, rfl⟩ rfl
      (evalArgs_sizes (t₁ := .float f) (t₂ := .int i) (by simp) (by simp) rfl rfl (evalArgs_vars (by simp) (by simp)))
      (floatCall_truncSat P f i s x)))

set_option maxRecDepth 100000 in
/-- `convert`. -/
theorem cvtop_convert (hB : FloatB P B) (i : IntType) (f : FloatType) (s : Signedness)
    (x : BitVec i.width) :
    Applies (simEnv B) "cvtop__" (cvtArgs (.convert i f s) x)
      (.list [numV ⟨.float f, convertInt i f s x⟩]) := by
  have hr : convRes P (.convert i f s) x = some (convertInt i f s x) :=
    (convRes_det (op := .convert i f s) (det_of nofun nofun) x).trans rfl
  have hc : floatCall P "convert__" [.val (natV i.width), .val (natV f.width), .val (sxV s),
      .val (pctV x.toNat)] = some (numV ⟨.float f, convertInt i f s x⟩) := by
    rw [floatCall_convert, hr]
    rfl
  refine ⟨_, _, _, findDef_cvtop, Or.inl ?_⟩
  refine tryClauses_skip_match (skipK2 (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK2 (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK1 (.inr rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK1 (.inr rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  exact tryClauses_hit (matchArg_kinds (.inl rfl) (.inr rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opSx (by simp) (by simp))) premsHold_nil
    (IntNumeric.evalExp_list1Call (callDef_floatPrim hB ⟨_, _, rfl⟩ rfl
      (evalArgs_sizes (t₁ := .int i) (t₂ := .float f) (by simp) (by simp) rfl rfl (evalArgs_vars (by simp) (by simp; rfl))) hc))

set_option maxRecDepth 100000 in
/-- `promote`. -/
theorem cvtop_promote (hB : FloatB P B) (x : BitVec 32) :
    Applies (simEnv B) "cvtop__" (cvtArgs .promote x)
      (.list ((bitsWhere 64 (fun z => convertP P .promote x (.ok z))).map
        fun z => numV ⟨.float .f64, z⟩)) := by
  refine ⟨_, _, _, findDef_cvtop, Or.inl ?_⟩
  refine tryClauses_skip_match (skipK1 (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK1 (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK2 (.inr rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK2 (.inr rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK1 (.inl rfl) (.inr rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  exact tryClauses_hit (matchArg_kinds (.inr rfl) (.inr rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opNil (by simp))) premsHold_nil
    (evalExp_callE_iff.2 (callDef_floatPrim hB ⟨_, _, rfl⟩ rfl
      (evalArgs_sizes (t₁ := .float .f32) (t₂ := .float .f64) (by simp) (by simp) rfl rfl (evalArgs_var1 (by simp)))
      (floatCall_promote P x)))

set_option maxRecDepth 100000 in
/-- `demote`. -/
theorem cvtop_demote (hB : FloatB P B) (x : BitVec 64) :
    Applies (simEnv B) "cvtop__" (cvtArgs .demote x)
      (.list ((bitsWhere 32 (fun z => convertP P .demote x (.ok z))).map
        fun z => numV ⟨.float .f32, z⟩)) := by
  refine ⟨_, _, _, findDef_cvtop, Or.inl ?_⟩
  refine tryClauses_skip_match (skipK1 (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK1 (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK2 (.inr rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK2 (.inr rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK1 (.inl rfl) (.inr rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipOpC (.inr rfl) (.inr rfl) (by decide) (by decide)
    (by decide)) ?_
  exact tryClauses_hit (matchArg_kinds (.inr rfl) (.inr rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opNil (by simp))) premsHold_nil
    (evalExp_callE_iff.2 (callDef_floatPrim hB ⟨_, _, rfl⟩ rfl
      (evalArgs_sizes (t₁ := .float .f64) (t₂ := .float .f32) (by simp) (by simp) rfl rfl (evalArgs_var1 (by simp)))
      (floatCall_demote P x)))

/-- The arguments of `$reinterpret__`. -/
theorem evalArgs_reinterp {ρ : VarEnv} {X₁ X₂ y : IL.Id} {t₁ t₂ : NumType} {a : Value}
    (h₁ : ρ.findVal? X₁ = some (Vec.numTypeV t₁)) (h₂ : ρ.findVal? X₂ = some (Vec.numTypeV t₂))
    (hy : ρ.findVal? y = some a) {u₁ u₂ u₃ u₄ : Typ} :
    EvalArgs (simEnv B) ρ [.expA (.subE (.varE X₁) u₁ u₂), .expA (.subE (.varE X₂) u₃ u₄),
      .expA (.varE y)] [.val (Vec.numTypeV t₁), .val (Vec.numTypeV t₂), .val a] :=
  Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 h₁))
    (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 h₂)) (evalArgs_var1 hy))

/-- `$reinterpret__` at a reinterpretation returns the bits unchanged. -/
theorem floatCall_reinterpret_eq {op : ConvertOp} (hop : reinterpOp? op.source op.target = some op)
    (hd : Det op) {x : BitVec op.source.width} {w : BitVec op.target.width}
    (hw : convert op x = .ok w) :
    floatCall P "reinterpret__" [.val (Vec.numTypeV op.source), .val (Vec.numTypeV op.target),
      .val (numV ⟨op.source, x⟩)] = some (numV ⟨op.target, w⟩) := by
  rw [floatCall_reinterpret P hop, convRes_det hd, hw]
  rfl

set_option maxRecDepth 100000 in
/-- `reinterpret` from an integer. -/
theorem cvtop_reinterpretFloat (hB : FloatB P B) (i : IntType) (x : BitVec i.width)
    {w : BitVec (ConvertOp.reinterpretFloat i).target.width}
    (hw : convert (.reinterpretFloat i) x = .ok w) :
    Applies (simEnv B) "cvtop__" (cvtArgs (.reinterpretFloat i) x)
      (.list [numV ⟨(ConvertOp.reinterpretFloat i).target, w⟩]) := by
  have hc : floatCall P "reinterpret__" [.val (Vec.numTypeV (ConvertOp.reinterpretFloat i).source),
      .val (Vec.numTypeV (ConvertOp.reinterpretFloat i).target),
      .val (numV ⟨(ConvertOp.reinterpretFloat i).source, x⟩)] =
      some (numV ⟨(ConvertOp.reinterpretFloat i).target, w⟩) :=
    floatCall_reinterpret_eq (op := .reinterpretFloat i) (by cases i <;> rfl)
      (det_of (op := .reinterpretFloat i) nofun nofun) hw
  refine ⟨_, _, _, findDef_cvtop, Or.inl ?_⟩
  refine tryClauses_skip_match (skipK2 (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by cases i <;> simp [kindOf, ConvertOp.target])) ?_
  refine tryClauses_skip_match (skipK2 (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by cases i <;> simp [kindOf, ConvertOp.target])) ?_
  refine tryClauses_skip_match (skipK1 (.inr rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK1 (.inr rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  show TryClauses (simEnv B) _ (cvtArgs (.reinterpretFloat i) x) _
  refine tryClauses_skip_match (skipOpC (.inl rfl) (.inr rfl) (by decide) (by decide)
    (by decide)) ?_
  refine tryClauses_skip_match (skipK1 (.inr rfl) (.inr rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK1 (.inr rfl) (.inr rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  cases i
  · exact tryClauses_hit
        (matchArg_kinds (X₁ := "Inn_1") (X₂ := "Fnn_2") (.inl rfl) (.inr rfl) (by decide)
          (by decide) rfl rfl (matchArgs_opNil (by simp)))
        (premsHold_sameSize (t₁ := .int .i32) (t₂ := .float .f32) (by simp) (by simp) rfl rfl)
        (IntNumeric.evalExp_list1Call (callDef_floatPrim hB ⟨_, _, rfl⟩ rfl
          (evalArgs_reinterp (t₁ := .int .i32) (t₂ := .float .f32) (by simp) (by simp)
            (by simp)) hc))
  · exact tryClauses_hit
        (matchArg_kinds (X₁ := "Inn_1") (X₂ := "Fnn_2") (.inl rfl) (.inr rfl) (by decide)
          (by decide) rfl rfl (matchArgs_opNil (by simp)))
        (premsHold_sameSize (t₁ := .int .i64) (t₂ := .float .f64) (by simp) (by simp) rfl rfl)
        (IntNumeric.evalExp_list1Call (callDef_floatPrim hB ⟨_, _, rfl⟩ rfl
          (evalArgs_reinterp (t₁ := .int .i64) (t₂ := .float .f64) (by simp) (by simp)
            (by simp)) hc))

set_option maxRecDepth 100000 in
/-- `reinterpret` from a float. -/
theorem cvtop_reinterpretInt (hB : FloatB P B) (f : FloatType) (x : BitVec f.width)
    {w : BitVec (ConvertOp.reinterpretInt f).target.width}
    (hw : convert (.reinterpretInt f) x = .ok w) :
    Applies (simEnv B) "cvtop__" (cvtArgs (.reinterpretInt f) x)
      (.list [numV ⟨(ConvertOp.reinterpretInt f).target, w⟩]) := by
  have hc : floatCall P "reinterpret__" [.val (Vec.numTypeV (ConvertOp.reinterpretInt f).source),
      .val (Vec.numTypeV (ConvertOp.reinterpretInt f).target),
      .val (numV ⟨(ConvertOp.reinterpretInt f).source, x⟩)] =
      some (numV ⟨(ConvertOp.reinterpretInt f).target, w⟩) :=
    floatCall_reinterpret_eq (op := .reinterpretInt f) (by cases f <;> rfl)
      (det_of (op := .reinterpretInt f) nofun nofun) hw
  refine ⟨_, _, _, findDef_cvtop, Or.inl ?_⟩
  refine tryClauses_skip_match (skipK1 (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK1 (.inl rfl) (.inl rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipOpC (.inr rfl) (.inl rfl) (by decide) (by decide)
    (by decide)) ?_
  refine tryClauses_skip_match (skipOpC (.inr rfl) (.inl rfl) (by decide) (by decide)
    (by decide)) ?_
  show TryClauses (simEnv B) _ (cvtArgs (.reinterpretInt f) x) _
  refine tryClauses_skip_match (skipK1 (.inl rfl) (.inr rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  refine tryClauses_skip_match (skipK2 (.inr rfl) (.inr rfl) (by decide) (by decide)
    (by cases f <;> simp [kindOf, ConvertOp.target])) ?_
  refine tryClauses_skip_match (skipK2 (.inr rfl) (.inr rfl) (by decide) (by decide)
    (by cases f <;> simp [kindOf, ConvertOp.target])) ?_
  refine tryClauses_skip_match (skipK1 (.inl rfl) (.inr rfl) (by decide) (by decide)
    (by simp [kindOf])) ?_
  cases f
  · exact tryClauses_hit
        (matchArg_kinds (X₁ := "Fnn_1") (X₂ := "Inn_2") (.inr rfl) (.inl rfl) (by decide)
          (by decide) rfl rfl (matchArgs_opNil (by simp)))
        (premsHold_sameSize (t₁ := .float .f32) (t₂ := .int .i32) (by simp) (by simp) rfl rfl)
        (IntNumeric.evalExp_list1Call (callDef_floatPrim hB ⟨_, _, rfl⟩ rfl
          (evalArgs_reinterp (t₁ := .float .f32) (t₂ := .int .i32) (by simp) (by simp)
            (by simp)) hc))
  · exact tryClauses_hit
        (matchArg_kinds (X₁ := "Fnn_1") (X₂ := "Inn_2") (.inr rfl) (.inl rfl) (by decide)
          (by decide) rfl rfl (matchArgs_opNil (by simp)))
        (premsHold_sameSize (t₁ := .float .f64) (t₂ := .int .i64) (by simp) (by simp) rfl rfl)
        (IntNumeric.evalExp_list1Call (callDef_floatPrim hB ⟨_, _, rfl⟩ rfl
          (evalArgs_reinterp (t₁ := .float .f64) (t₂ := .int .i64) (by simp) (by simp)
            (by simp)) hc))

/-- **`$cvtop__` at every Core conversion**: the result list is the profile's, and empty exactly
when the conversion traps (family V's `FloatAgree.cvtop`). -/
theorem cvtop_agree (hB : FloatB P B) (op : ConvertOp) (x : BitVec op.source.width) :
    ∃ L, Applies (simEnv B) "cvtop__" (cvtArgs op x) (.list L) ∧ CvtOk P op x L := by
  cases op with
  | wrap => exact ⟨_, cvtop_wrap hB x, cvtOk_single (op := .wrap) (w := x.setWidth 32) (det_of nofun nofun) rfl⟩
  | extend s =>
      cases s
      · exact ⟨_, cvtop_extend hB .signed x,
          cvtOk_single (op := .extend .signed) (w := x.signExtend 64) (det_of nofun nofun) rfl⟩
      · exact ⟨_, cvtop_extend hB .unsigned x,
          cvtOk_single (op := .extend .unsigned) (w := x.setWidth 64) (det_of nofun nofun) rfl⟩
  | trunc f i s => exact ⟨_, cvtop_trunc hB f i s x, agree_opt (op := .trunc f i s) (det_of nofun nofun) x⟩
  | truncSat f i s => exact ⟨_, cvtop_truncSat hB f i s x,
      agree_opt (op := .truncSat f i s) (det_of nofun nofun) x⟩
  | convert i f s => exact ⟨_, cvtop_convert hB i f s x,
      cvtOk_single (op := .convert i f s) (det_of nofun nofun) rfl⟩
  | promote => exact ⟨_, cvtop_promote hB x, agree_list (op := .promote) (.inl rfl) rfl⟩
  | demote => exact ⟨_, cvtop_demote hB x, agree_list (op := .demote) (.inr rfl) rfl⟩
  | reinterpretInt f =>
      cases f
      · exact ⟨_, cvtop_reinterpretInt hB .f32 x rfl,
          cvtOk_single (op := .reinterpretInt .f32) (w := x) (det_of nofun nofun) rfl⟩
      · exact ⟨_, cvtop_reinterpretInt hB .f64 x rfl,
          cvtOk_single (op := .reinterpretInt .f64) (w := x) (det_of nofun nofun) rfl⟩
  | reinterpretFloat i =>
      cases i
      · exact ⟨_, cvtop_reinterpretFloat hB .i32 x rfl,
          cvtOk_single (op := .reinterpretFloat .i32) (w := x) (det_of nofun nofun) rfl⟩
      · exact ⟨_, cvtop_reinterpretFloat hB .i64 x rfl,
          cvtOk_single (op := .reinterpretFloat .i64) (w := x) (det_of nofun nofun) rfl⟩

/-- **`FloatAgree (simEnv B) P`** for every `B` extending the float primitives of `P`. -/
theorem floatAgree_simEnv (hB : FloatB P B) : Vec.FloatAgree (simEnv B) P where
  unop t op x := ⟨_, applies_unop_float hB t op x, fun _ => mem_map_bitsWhere⟩
  binop t op x y := ⟨_, applies_binop_float hB t op x y, fun _ => mem_map_bitsWhere⟩
  relop t op x y := applies_relop_float hB t op x y
  cvtop op x := cvtop_agree hB op x

end Silmaril.Wasm.SpecTec.Sim.Floats
