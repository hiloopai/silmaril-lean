module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumTyping
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Convert

/-!
# `CvtAgree` for the wasm-2.0 script, discharged

The wasm-2.0 `$cvtop__` (`Original.d224`) dispatches on two number kinds and the conversion
operator, in the order `EXTEND`, `WRAP`, `TRUNC`, `TRUNC_SAT`, `CONVERT`, `PROMOTE`, `DEMOTE`,
`REINTERPRET` (`Inn → Fnn`), `REINTERPRET` (`Fnn → Inn`). Its clauses call the builtins `$extend__`,
`$wrap__`, `$trunc__`, `$trunc_sat__`, `$convert__`, `$promote__`, `$demote__`,
`$reinterpret__` on `$sizenn1`/`$sizenn2` of the kinds, which `B` answers through
`Floats.FloatB P B`; `TRUNC`/`TRUNC_SAT` lift the option with `$list_` (3.0 writes a lift), and
the `REINTERPRET` clauses check `$size(X₁) = $size(X₂)`.

`applies_cvt_*20` evaluate each clause; with the result lemmas of the 3.0 float track
(`Floats.agree_single`, `agree_opt`, `agree_list`) this gives

  `cvtAgree_simEnv20 : FloatB P B → CvtAgree (simEnv20 B) P`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (defOf evalExp_list1Call NoClauses)
open Silmaril.Wasm.SpecTec.Sim.Floats (FloatB floatCall convRes bitsWhere)
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d88 Original.d224)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins} {P : Profile}

/-! ## Lookups and the size functions -/

set_option maxRecDepth 100000 in
theorem findDef_cvtop20 : (simEnv20 B).findDef? "cvtop__" = defOf Original.d224 := rfl

set_option maxRecDepth 100000 in
/-- `$sizenn1` is `$sizenn` under another name. -/
theorem findDef_sizenn1_20 : (simEnv20 B).findDef? "sizenn1" = defOf Original.d88 := rfl

set_option maxRecDepth 100000 in
/-- `$sizenn2` is `$sizenn` under another name. -/
theorem findDef_sizenn2_20 : (simEnv20 B).findDef? "sizenn2" = defOf Original.d88 := rfl

/-- A function defined as `$sizenn` is the width, at every number type. -/
theorem evalExp_sizennAs20 {x : IL.Id} (hx : (simEnv20 B).findDef? x = defOf Original.d88)
    (t : NumType) {ρ : VarEnv} {X : IL.Id} {t₁ t₂ : Typ}
    (hρ : ρ.findDef? x = none) (hX : ρ.findVal? X = some (numTypeV t)) :
    EvalExp (simEnv20 B) ρ (.callE x [.expA (.subE (.varE X) t₁ t₂)]) (natV t.width) := by
  refine evalExp_callE_iff.2 (callDef_of_tryClauses hρ hx
    (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 hX)) Equiv.evalArgs_nil) ?_)
  exact tryClauses_hit (ρ₀ := VarEnv.empty.bindVal "nt" (numTypeV t))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) premsHold_nil
    (evalExp_callE_iff.2 (callDef_size20 t rfl
      (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 (by simp)))
        Equiv.evalArgs_nil)))

/-! ## Kinds -/

/-- The kind of a number type, as the `$cvtop__` patterns name it. -/
def kind20 : NumType → IL.Id
  | .int _ => "Inn"
  | .float _ => "Fnn"

/-- A kind pattern `X <: K`. -/
abbrev kpat20 (X K : IL.Id) : Exp := .subE (.varE X) (.varT K []) (.varT "numtype" [])

set_option maxRecDepth 100000 in
/-- The subtype test of a kind pattern is the kind. -/
theorem argSubOk_kind20 {X K : IL.Id} (hK : K = "Inn" ∨ K = "Fnn") (t : NumType) :
    argSubOk (simEnv20 B) VarEnv.empty (kpat20 X K) (numTypeV t) = decide (kind20 t = K) := by
  rcases hK with rfl | rfl <;> rcases t with (_ | _) | (_ | _) <;> rfl

/-- The same, in a scope binding one value (the test reads only type bindings). -/
theorem argSubOk_kind20_bind {X K : IL.Id} (hK : K = "Inn" ∨ K = "Fnn") (t : NumType)
    (Y : IL.Id) (w : Value) :
    argSubOk (simEnv20 B) (VarEnv.empty.bindVal Y w) (kpat20 X K) (numTypeV t) =
      decide (kind20 t = K) :=
  argSubOk_kind20 (X := X) hK t

/-- A kind pattern of the value's kind matches and binds. -/
theorem matchArg_kind20 {ρ : VarEnv} {X K : IL.Id} {t : NumType}
    (hs : argSubOk (simEnv20 B) ρ (kpat20 X K) (numTypeV t) = decide (kind20 t = K))
    (hx : ρ.findVal? X = none) (h : kind20 t = K) :
    MatchArg (simEnv20 B) ρ (.expA (kpat20 X K)) (.val (numTypeV t)) (ρ.bindVal X (numTypeV t)) :=
  matchArg_subVar20 hx (by rw [hs]; exact decide_eq_true h)

/-- A kind pattern of another kind definitely fails. -/
theorem matchArg_kind20_undef {ρ : VarEnv} {X K : IL.Id} {t : NumType}
    (hs : argSubOk (simEnv20 B) ρ (kpat20 X K) (numTypeV t) = decide (kind20 t = K))
    (h : kind20 t ≠ K) :
    ∃ n, matchArg n (simEnv20 B) ρ (.expA (kpat20 X K)) (.val (numTypeV t)) = .error .undef :=
  Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (by rw [hs]; exact decide_eq_false h)

/-- A `$cvtop__` clause of other kinds, or for another operator, is skipped. -/
theorem skipC20 {X₁ X₂ K₁ K₂ : IL.Id} (hK₁ : K₁ = "Inn" ∨ K₁ = "Fnn")
    (hK₂ : K₂ = "Inn" ∨ K₂ = "Fnn") (hX₁ : X₁ ≠ "_") (hX : X₁ ≠ X₂) {o o' : MixopS}
    {inner : Exp} {pats : List Arg} {t₁ t₂ : NumType} {p : Value} {ws : List ArgV}
    (h : kind20 t₁ ≠ K₁ ∨ kind20 t₂ ≠ K₂ ∨ o ≠ o') :
    MatchArgsUndef (simEnv20 B) VarEnv.empty
      (.expA (kpat20 X₁ K₁) :: .expA (kpat20 X₂ K₂) :: .expA (.caseE o' inner) :: pats)
      (.val (numTypeV t₁) :: .val (numTypeV t₂) :: .val (.case o p) :: ws) := by
  by_cases h₁ : kind20 t₁ = K₁
  · have m₁ := matchArg_kind20 (B := B) (X := X₁) (argSubOk_kind20 hK₁ t₁) (by simp) h₁
    have hs₂ := argSubOk_kind20_bind (B := B) (X := X₂) hK₂ t₂ X₁ (numTypeV t₁)
    by_cases h₂ : kind20 t₂ = K₂
    · have hne : o ≠ o' := (h.resolve_left (not_not.2 h₁)).resolve_left (not_not.2 h₂)
      exact matchArgs_cons_undef_tail m₁ (matchArgs_cons_undef_tail
        (matchArg_kind20 hs₂ (by simp [Equiv.Execution.findVal?_bindVal_lit hX₁, hX]) h₂)
        (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef hne))))
    · exact matchArgs_cons_undef_tail m₁ (matchArgs_cons_undef (matchArg_kind20_undef hs₂ h₂))
  · exact matchArgs_cons_undef (matchArg_kind20_undef (argSubOk_kind20 hK₁ t₁) h₁)

/-- Skip every `$cvtop__` clause before the one for the kinds and the operator. -/
macro "skipCvt20" : tactic =>
  `(tactic|
    repeat (refine tryClauses_skip_match (skipC20 (of_decide_eq_true rfl)
      (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_true rfl)
      (of_decide_eq_true rfl)) ?_))

/-! ## The matching clause -/

/-- The scope two kind patterns bind. -/
abbrev cscope (X₁ X₂ : IL.Id) (t₁ t₂ : NumType) : VarEnv :=
  (VarEnv.empty.bindVal X₁ (numTypeV t₁)).bindVal X₂ (numTypeV t₂)

/-- The two kind patterns of the clause for the kinds match. -/
theorem matchArgs_kinds20 {X₁ X₂ K₁ K₂ : IL.Id} (hK₁ : K₁ = "Inn" ∨ K₁ = "Fnn")
    (hK₂ : K₂ = "Inn" ∨ K₂ = "Fnn") (hX₁ : X₁ ≠ "_") (hX : X₁ ≠ X₂) {t₁ t₂ : NumType}
    (h₁ : kind20 t₁ = K₁)
    (h₂ : kind20 t₂ = K₂) {pats : List Arg} {ws : List ArgV} {ρ' : VarEnv}
    (hr : MatchArgs (simEnv20 B) (cscope X₁ X₂ t₁ t₂) pats ws ρ') :
    MatchArgs (simEnv20 B) VarEnv.empty (.expA (kpat20 X₁ K₁) :: .expA (kpat20 X₂ K₂) :: pats)
      (.val (numTypeV t₁) :: .val (numTypeV t₂) :: ws) ρ' :=
  matchArgs_cons (matchArg_kind20 (argSubOk_kind20 hK₁ t₁) rfl h₁)
    (matchArgs_cons (matchArg_kind20 (argSubOk_kind20_bind hK₂ t₂ X₁ (numTypeV t₁))
      (by simp [Equiv.Execution.findVal?_bindVal_lit hX₁, hX]) h₂) hr)

/-- The operator pattern `o sx` and the operand. -/
theorem matchArgs_opSx20 {s : Signedness} {ρ : VarEnv} (hs : ρ.findVal? "sx" = none) {v : IL.Id}
    (hv : (ρ.bindVal "sx" (sxV s)).findVal? v = none) {o : MixopS} {a : Value} :
    MatchArgs (simEnv20 B) ρ [.expA (.caseE o (.varE "sx")), .expA (.varE v)]
      [.val (.case o (sxV s)), .val a] ((ρ.bindVal "sx" (sxV s)).bindVal v a) :=
  matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE hs)))
    (matchArgs_cons (matchArg_expA (matchExp_varE hv)) matchArgs_nil)

/-- The operator pattern `o` and the operand. -/
theorem matchArgs_opNil20 {ρ : VarEnv} {v : IL.Id} (hv : ρ.findVal? v = none) {o : MixopS}
    {a : Value} :
    MatchArgs (simEnv20 B) ρ [.expA (.caseE o (.tupE [])), .expA (.varE v)]
      [.val (.case o (.tuple [])), .val a] (ρ.bindVal v a) :=
  matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
    (matchArgs_cons (matchArg_expA (matchExp_varE hv)) matchArgs_nil)

/-- `$sizenn1(X₁), $sizenn2(X₂)` and the rest of the arguments. -/
theorem evalArgs_sizes20 {X₁ X₂ : IL.Id} {t₁ t₂ : NumType} {ρ : VarEnv}
    (h₁ : ρ.findVal? X₁ = some (numTypeV t₁)) (h₂ : ρ.findVal? X₂ = some (numTypeV t₂))
    (hd₁ : ρ.findDef? "sizenn1" = none) (hd₂ : ρ.findDef? "sizenn2" = none) {u₁ u₂ u₃ u₄ : Typ}
    {rest : List Arg} {ws : List ArgV} (hr : EvalArgs (simEnv20 B) ρ rest ws) :
    EvalArgs (simEnv20 B) ρ (.expA (.callE "sizenn1" [.expA (.subE (.varE X₁) u₁ u₂)]) ::
      .expA (.callE "sizenn2" [.expA (.subE (.varE X₂) u₃ u₄)]) :: rest)
      (.val (natV t₁.width) :: .val (natV t₂.width) :: ws) :=
  Equiv.evalArgs_cons (evalExp_sizennAs20 findDef_sizenn1_20 t₁ hd₁ h₁)
    (Equiv.evalArgs_cons (evalExp_sizennAs20 findDef_sizenn2_20 t₂ hd₂ h₂) hr)

/-- Variables, as trailing arguments. -/
theorem evalArgs_vars20 {ρ : VarEnv} {x y : IL.Id} {a b : Value} (hx : ρ.findVal? x = some a)
    (hy : ρ.findVal? y = some b) :
    EvalArgs (simEnv20 B) ρ [.expA (.varE x), .expA (.varE y)] [.val a, .val b] :=
  Equiv.evalArgs_cons (evalExp_varE_iff.2 hx)
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 hy) Equiv.evalArgs_nil)

/-- A variable, as the trailing argument. -/
theorem evalArgs_var20 {ρ : VarEnv} {x : IL.Id} {a : Value} (hx : ρ.findVal? x = some a) :
    EvalArgs (simEnv20 B) ρ [.expA (.varE x)] [.val a] :=
  Equiv.evalArgs_cons (evalExp_varE_iff.2 hx) Equiv.evalArgs_nil

/-- `$size(X₁) = $size(X₂)` holds at two number types of the same width. -/
theorem premsHold_sameSize20 {ρ : VarEnv} {X₁ X₂ : IL.Id} {t₁ t₂ : NumType}
    (h₁ : ρ.findVal? X₁ = some (numTypeV t₁)) (h₂ : ρ.findVal? X₂ = some (numTypeV t₂))
    (hd : ρ.findDef? "size" = none) (hw : t₁.width = t₂.width) {u₁ u₂ u₃ u₄ : Typ} :
    PremsHold (simEnv20 B) ρ [.ifPr (.cmpE .eqOp .boolT
      (.callE "size" [.expA (.subE (.varE X₁) u₁ u₂)])
      (.callE "size" [.expA (.subE (.varE X₂) u₃ u₄)]))] ρ := by
  have e₁ : EvalExp (simEnv20 B) ρ (.callE "size" [.expA (.subE (.varE X₁) u₁ u₂)])
      (natV t₁.width) := evalExp_callE_iff.2 (callDef_size20 t₁ hd
        (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 h₁)) Equiv.evalArgs_nil))
  have e₂ : EvalExp (simEnv20 B) ρ (.callE "size" [.expA (.subE (.varE X₂) u₃ u₄)])
      (natV t₁.width) := hw ▸ evalExp_callE_iff.2 (callDef_size20 t₂ hd
        (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 h₂)) Equiv.evalArgs_nil))
  have hc : EvalExp (simEnv20 B) ρ (.cmpE .eqOp .boolT
      (.callE "size" [.expA (.subE (.varE X₁) u₁ u₂)])
      (.callE "size" [.expA (.subE (.varE X₂) u₃ u₄)])) (.bool true) :=
    evalExp_cmpE_iff.2 ⟨_, _, e₁, e₂, by simp [cmpValues]⟩
  exact Equiv.Validation.premsHold_cons_iff.2 ⟨_, Equiv.Validation.premHolds_if_iff.2 ⟨rfl, hc⟩,
    Equiv.Validation.premsHold_nil_iff.2 rfl⟩

/-- The arguments of `$cvtop__` at a V2 conversion. -/
abbrev cvtArgs20 (target source : NumType) (op : V2.CvtOp) (x : BitVec source.width) :
    List ArgV :=
  [.val (numTypeV source), .val (numTypeV target), .val (cvtOpV op), .val (numV ⟨source, x⟩)]

/-! ## The clauses, one by one -/

/-- The 2.0 and 3.0 encodings of a signedness agree. -/
theorem sxV_eq20 (s : Signedness) : sxV s = Sim.sxV s := by cases s <;> rfl

set_option maxRecDepth 100000 in
/-- `EXTEND sx` (`i32 → i64`). -/
theorem applies_cvt_extend20 (hB : FloatB P B) (s : Signedness) (x : BitVec 32) :
    Applies (simEnv20 B) "cvtop__" (cvtArgs20 (.int .i64) (.int .i32) (.extend s) x)
      (.list [bvV (match s with | .signed => x.signExtend 64 | .unsigned => x.setWidth 64)]) := by
  have hc : floatCall P "extend__" [.val (natV 32), .val (natV 64), .val (sxV s),
      .val (Equiv.Execution.pctV x.toNat)] =
      some (bvV (match s with | .signed => x.signExtend 64 | .unsigned => x.setWidth 64)) := by
    cases s
    · exact Sim.Floats.floatCall_extend P 32 64 .signed x
    · exact Sim.Floats.floatCall_extend P 32 64 .unsigned x
  refine ⟨_, _, _, findDef_cvtop20, Or.inl ?_⟩
  exact tryClauses_hit (matchArgs_kinds20 (.inl rfl) (.inl rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opSx20 (by simp) (by simp))) premsHold_nil
    (evalExp_list1Call (callDef_floatPrim20 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_sizes20 (t₁ := .int .i32) (t₂ := .int .i64) (by simp) (by simp) rfl rfl
        (evalArgs_vars20 (by simp) (by simp; rfl))) hc))

set_option maxRecDepth 100000 in
/-- `WRAP` (`i64 → i32`). -/
theorem applies_cvt_wrap20 (hB : FloatB P B) (x : BitVec 64) :
    Applies (simEnv20 B) "cvtop__" (cvtArgs20 (.int .i32) (.int .i64) .wrap x)
      (.list [bvV (x.setWidth 32)]) := by
  refine ⟨_, _, _, findDef_cvtop20, Or.inl ?_⟩
  skipCvt20
  exact tryClauses_hit (matchArgs_kinds20 (.inl rfl) (.inl rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opNil20 (by simp))) premsHold_nil
    (evalExp_list1Call (callDef_floatPrim20 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_sizes20 (t₁ := .int .i64) (t₂ := .int .i32) (by simp) (by simp) rfl rfl
        (evalArgs_var20 (by simp; rfl)))
      (Sim.Floats.floatCall_wrap P 64 32 x)))

/-- `$list_(X, $f(…))` of an option-valued call. -/
theorem evalExp_listOpt20 {ρ : VarEnv} {T : Typ} {f : IL.Id} {args : List Arg} {o : Option Value}
    (hρ : ρ.findDef? "list_" = none) (hc : CallDef (simEnv20 B) ρ f args (.opt o)) :
    EvalExp (simEnv20 B) ρ (.callE "list_" [.typA T, .expA (.callE f args)]) (.list o.toList) :=
  evalExp_callE_iff.2 (callDef_list20 hρ (Sim.Round5.FwdRef.evalArgs_typA
    (Equiv.evalArgs_cons (evalExp_callE_iff.2 hc) Equiv.evalArgs_nil)))

set_option maxRecDepth 100000 in
/-- `TRUNC sx` (`Fnn → Inn`), through `$list_`. -/
theorem applies_cvt_trunc20 (hB : FloatB P B) (f : FloatType) (i : IntType) (s : Signedness)
    (x : BitVec f.width) :
    Applies (simEnv20 B) "cvtop__" (cvtArgs20 (.int i) (.float f) (.trunc s) x)
      (.list (((convRes P (.trunc f i s) x).map fun z => numV ⟨.int i, z⟩).toList)) := by
  have hc : floatCall P "trunc__" [.val (natV f.width), .val (natV i.width), .val (sxV s),
      .val (numV ⟨.float f, x⟩)] =
      some (.opt ((convRes P (.trunc f i s) x).map fun z => numV ⟨.int i, z⟩)) := by
    rw [sxV_eq20]; exact Sim.Floats.floatCall_trunc P f i s x
  refine ⟨_, _, _, findDef_cvtop20, Or.inl ?_⟩
  skipCvt20
  exact tryClauses_hit (matchArgs_kinds20 (.inr rfl) (.inl rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opSx20 (by simp) (by simp))) premsHold_nil
    (evalExp_listOpt20 rfl (callDef_floatPrim20 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_sizes20 (t₁ := .float f) (t₂ := .int i) (by simp) (by simp) rfl rfl
        (evalArgs_vars20 (by simp) (by simp))) hc))

set_option maxRecDepth 100000 in
/-- `TRUNC_SAT sx` (`Fnn → Inn`), through `$list_`. -/
theorem applies_cvt_truncSat20 (hB : FloatB P B) (f : FloatType) (i : IntType) (s : Signedness)
    (x : BitVec f.width) :
    Applies (simEnv20 B) "cvtop__" (cvtArgs20 (.int i) (.float f) (.truncSat s) x)
      (.list (((convRes P (.truncSat f i s) x).map fun z => numV ⟨.int i, z⟩).toList)) := by
  have hc : floatCall P "trunc_sat__" [.val (natV f.width), .val (natV i.width), .val (sxV s),
      .val (numV ⟨.float f, x⟩)] =
      some (.opt ((convRes P (.truncSat f i s) x).map fun z => numV ⟨.int i, z⟩)) := by
    rw [sxV_eq20]; exact Sim.Floats.floatCall_truncSat P f i s x
  refine ⟨_, _, _, findDef_cvtop20, Or.inl ?_⟩
  skipCvt20
  exact tryClauses_hit (matchArgs_kinds20 (.inr rfl) (.inl rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opSx20 (by simp) (by simp))) premsHold_nil
    (evalExp_listOpt20 rfl (callDef_floatPrim20 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_sizes20 (t₁ := .float f) (t₂ := .int i) (by simp) (by simp) rfl rfl
        (evalArgs_vars20 (by simp) (by simp))) hc))

set_option maxRecDepth 100000 in
/-- `CONVERT sx` (`Inn → Fnn`). -/
theorem applies_cvt_convert20 (hB : FloatB P B) (i : IntType) (f : FloatType) (s : Signedness)
    (x : BitVec i.width) :
    Applies (simEnv20 B) "cvtop__" (cvtArgs20 (.float f) (.int i) (.convert s) x)
      (.list [numV ⟨.float f, convertInt i f s x⟩]) := by
  have hr : convRes P (.convert i f s) x = some (convertInt i f s x) :=
    (Sim.Floats.convRes_det (op := .convert i f s) (Sim.Floats.det_of nofun nofun) x).trans rfl
  have hc : floatCall P "convert__" [.val (natV i.width), .val (natV f.width), .val (sxV s),
      .val (Equiv.Execution.pctV x.toNat)] = some (numV ⟨.float f, convertInt i f s x⟩) := by
    have hs : sxV s = Sim.sxV s := by cases s <;> rfl
    rw [hs, Sim.Floats.floatCall_convert, hr]
    rfl
  refine ⟨_, _, _, findDef_cvtop20, Or.inl ?_⟩
  skipCvt20
  exact tryClauses_hit (matchArgs_kinds20 (.inl rfl) (.inr rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opSx20 (by simp) (by simp))) premsHold_nil
    (evalExp_list1Call (callDef_floatPrim20 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_sizes20 (t₁ := .int i) (t₂ := .float f) (by simp) (by simp) rfl rfl
        (evalArgs_vars20 (by simp) (by simp; rfl))) hc))

set_option maxRecDepth 100000 in
/-- `PROMOTE` (`f32 → f64`). -/
theorem applies_cvt_promote20 (hB : FloatB P B) (x : BitVec 32) :
    Applies (simEnv20 B) "cvtop__" (cvtArgs20 (.float .f64) (.float .f32) .promote x)
      (.list ((bitsWhere 64 (fun z => convertP P .promote x (.ok z))).map
        fun z => numV ⟨.float .f64, z⟩)) := by
  have hc : floatCall P "promote__" [.val (natV 32), .val (natV 64),
      .val (numV ⟨.float .f32, x⟩)] =
      some (.list ((bitsWhere 64 (fun z => convertP P .promote x (.ok z))).map
        fun z => numV ⟨.float .f64, z⟩)) := Sim.Floats.floatCall_promote P x
  refine ⟨_, _, _, findDef_cvtop20, Or.inl ?_⟩
  skipCvt20
  exact tryClauses_hit (matchArgs_kinds20 (.inr rfl) (.inr rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opNil20 (by simp))) premsHold_nil
    (evalExp_callE_iff.2 (callDef_floatPrim20 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_sizes20 (t₁ := .float .f32) (t₂ := .float .f64) (by simp) (by simp) rfl rfl
        (evalArgs_var20 (by simp)))
      hc))

set_option maxRecDepth 100000 in
/-- `DEMOTE` (`f64 → f32`). -/
theorem applies_cvt_demote20 (hB : FloatB P B) (x : BitVec 64) :
    Applies (simEnv20 B) "cvtop__" (cvtArgs20 (.float .f32) (.float .f64) .demote x)
      (.list ((bitsWhere 32 (fun z => convertP P .demote x (.ok z))).map
        fun z => numV ⟨.float .f32, z⟩)) := by
  have hc : floatCall P "demote__" [.val (natV 64), .val (natV 32),
      .val (numV ⟨.float .f64, x⟩)] =
      some (.list ((bitsWhere 32 (fun z => convertP P .demote x (.ok z))).map
        fun z => numV ⟨.float .f32, z⟩)) := Sim.Floats.floatCall_demote P x
  refine ⟨_, _, _, findDef_cvtop20, Or.inl ?_⟩
  skipCvt20
  exact tryClauses_hit (matchArgs_kinds20 (.inr rfl) (.inr rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opNil20 (by simp))) premsHold_nil
    (evalExp_callE_iff.2 (callDef_floatPrim20 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_sizes20 (t₁ := .float .f64) (t₂ := .float .f32) (by simp) (by simp) rfl rfl
        (evalArgs_var20 (by simp)))
      hc))

/-- The arguments of `$reinterpret__`. -/
theorem evalArgs_reinterp20 {ρ : VarEnv} {X₁ X₂ y : IL.Id} {t₁ t₂ : NumType} {a : Value}
    (h₁ : ρ.findVal? X₁ = some (numTypeV t₁)) (h₂ : ρ.findVal? X₂ = some (numTypeV t₂))
    (hy : ρ.findVal? y = some a) {u₁ u₂ u₃ u₄ : Typ} :
    EvalArgs (simEnv20 B) ρ [.expA (.subE (.varE X₁) u₁ u₂), .expA (.subE (.varE X₂) u₃ u₄),
      .expA (.varE y)] [.val (numTypeV t₁), .val (numTypeV t₂), .val a] :=
  Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 h₁))
    (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 h₂)) (evalArgs_var20 hy))

set_option maxRecDepth 100000 in
/-- `REINTERPRET` (`i32 → f32`). -/
theorem applies_cvt_reinterp_i32_20 (hB : FloatB P B) (x : BitVec 32) :
    Applies (simEnv20 B) "cvtop__" (cvtArgs20 (.float .f32) (.int .i32) .reinterpret x)
      (.list [numV ⟨.float .f32, x⟩]) := by
  have hc : floatCall P "reinterpret__" [.val (numTypeV (.int .i32)), .val (numTypeV (.float .f32)),
      .val (numV ⟨.int .i32, x⟩)] = some (numV ⟨.float .f32, x⟩) :=
    Sim.Floats.floatCall_reinterpret_eq (P := P) (op := .reinterpretFloat .i32) rfl
      (Sim.Floats.det_of nofun nofun) (x := x) (w := x) rfl
  refine ⟨_, _, _, findDef_cvtop20, Or.inl ?_⟩
  skipCvt20
  exact tryClauses_hit (matchArgs_kinds20 (.inl rfl) (.inr rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opNil20 (by simp))) (premsHold_sameSize20
      (t₁ := .int .i32) (t₂ := .float .f32) (by simp) (by simp) rfl rfl)
    (evalExp_list1Call (callDef_floatPrim20 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_reinterp20 (t₁ := .int .i32) (t₂ := .float .f32) (by simp) (by simp) (by simp)) hc))

set_option maxRecDepth 100000 in
/-- `REINTERPRET` (`i64 → f64`). -/
theorem applies_cvt_reinterp_i64_20 (hB : FloatB P B) (x : BitVec 64) :
    Applies (simEnv20 B) "cvtop__" (cvtArgs20 (.float .f64) (.int .i64) .reinterpret x)
      (.list [numV ⟨.float .f64, x⟩]) := by
  have hc : floatCall P "reinterpret__" [.val (numTypeV (.int .i64)), .val (numTypeV (.float .f64)),
      .val (numV ⟨.int .i64, x⟩)] = some (numV ⟨.float .f64, x⟩) :=
    Sim.Floats.floatCall_reinterpret_eq (P := P) (op := .reinterpretFloat .i64) rfl
      (Sim.Floats.det_of nofun nofun) (x := x) (w := x) rfl
  refine ⟨_, _, _, findDef_cvtop20, Or.inl ?_⟩
  skipCvt20
  exact tryClauses_hit (matchArgs_kinds20 (.inl rfl) (.inr rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opNil20 (by simp))) (premsHold_sameSize20
      (t₁ := .int .i64) (t₂ := .float .f64) (by simp) (by simp) rfl rfl)
    (evalExp_list1Call (callDef_floatPrim20 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_reinterp20 (t₁ := .int .i64) (t₂ := .float .f64) (by simp) (by simp) (by simp)) hc))

set_option maxRecDepth 100000 in
/-- `REINTERPRET` (`f32 → i32`). -/
theorem applies_cvt_reinterp_f32_20 (hB : FloatB P B) (x : BitVec 32) :
    Applies (simEnv20 B) "cvtop__" (cvtArgs20 (.int .i32) (.float .f32) .reinterpret x)
      (.list [numV ⟨.int .i32, x⟩]) := by
  have hc : floatCall P "reinterpret__" [.val (numTypeV (.float .f32)), .val (numTypeV (.int .i32)),
      .val (numV ⟨.float .f32, x⟩)] = some (numV ⟨.int .i32, x⟩) :=
    Sim.Floats.floatCall_reinterpret_eq (P := P) (op := .reinterpretInt .f32) rfl
      (Sim.Floats.det_of nofun nofun) (x := x) (w := x) rfl
  refine ⟨_, _, _, findDef_cvtop20, Or.inl ?_⟩
  skipCvt20
  exact tryClauses_hit (matchArgs_kinds20 (.inr rfl) (.inl rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opNil20 (by simp))) (premsHold_sameSize20
      (t₁ := .float .f32) (t₂ := .int .i32) (by simp) (by simp) rfl rfl)
    (evalExp_list1Call (callDef_floatPrim20 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_reinterp20 (t₁ := .float .f32) (t₂ := .int .i32) (by simp) (by simp) (by simp)) hc))

set_option maxRecDepth 100000 in
/-- `REINTERPRET` (`f64 → i64`). -/
theorem applies_cvt_reinterp_f64_20 (hB : FloatB P B) (x : BitVec 64) :
    Applies (simEnv20 B) "cvtop__" (cvtArgs20 (.int .i64) (.float .f64) .reinterpret x)
      (.list [numV ⟨.int .i64, x⟩]) := by
  have hc : floatCall P "reinterpret__" [.val (numTypeV (.float .f64)), .val (numTypeV (.int .i64)),
      .val (numV ⟨.float .f64, x⟩)] = some (numV ⟨.int .i64, x⟩) :=
    Sim.Floats.floatCall_reinterpret_eq (P := P) (op := .reinterpretInt .f64) rfl
      (Sim.Floats.det_of nofun nofun) (x := x) (w := x) rfl
  refine ⟨_, _, _, findDef_cvtop20, Or.inl ?_⟩
  skipCvt20
  exact tryClauses_hit (matchArgs_kinds20 (.inr rfl) (.inl rfl) (by decide) (by decide) rfl rfl
    (matchArgs_opNil20 (by simp))) (premsHold_sameSize20
      (t₁ := .float .f64) (t₂ := .int .i64) (by simp) (by simp) rfl rfl)
    (evalExp_list1Call (callDef_floatPrim20 hB ⟨_, _, rfl⟩ rfl
      (evalArgs_reinterp20 (t₁ := .float .f64) (t₂ := .int .i64) (by simp) (by simp) (by simp)) hc))

/-! ## `CvtAgree` -/

/-- What `CvtAgree` asks of the result list `vs` of a conversion. -/
def CvtOk20 (P : Profile) (target source : NumType) (op : V2.CvtOp) (x : BitVec source.width)
    (vs : List Value) : Prop :=
  (∀ c, c ∈ vs ↔ ∃ z, V2.Execution.CvtOpResult P target source op x z ∧ c = numV ⟨target, z⟩) ∧
    (vs = [] ↔ V2.Execution.CvtOpTraps P target source op x)

/-- A deterministic conversion that cannot trap, from the 3.0 track's `CvtOk`. -/
theorem cvtOk20_of_det {op : ConvertOp} (hop : Sim.Floats.Det op) {x : BitVec op.source.width}
    {w : BitVec op.target.width} (hw : convert op x = .ok w) {L : List Value}
    (hL : Sim.Floats.CvtOk P op x L) :
    (L = [] ↔ False) := by
  refine ⟨fun h => ?_, False.elim⟩
  obtain ⟨e, he⟩ := hL.2.1 h
  have h2 : Except.error e = convert op x := (Sim.Floats.convertP_iff_det hop x _).1 he
  rw [hw] at h2
  cases h2

theorem cvtOk20_extend (s : Signedness) (x : BitVec 32) :
    CvtOk20 P (.int .i64) (.int .i32) (.extend s)  x
      [bvV (match s with | .signed => x.signExtend 64 | .unsigned => x.setWidth 64)] := by
  cases s
  · have h := Sim.Floats.cvtOk_single (P := P) (op := .extend .signed) (w := x.signExtend 64)
      (Sim.Floats.det_of nofun nofun) rfl
    exact ⟨h.1, cvtOk20_of_det (op := .extend .signed) (Sim.Floats.det_of nofun nofun) rfl h⟩
  · have h := Sim.Floats.cvtOk_single (P := P) (op := .extend .unsigned) (w := x.setWidth 64)
      (Sim.Floats.det_of nofun nofun) rfl
    exact ⟨h.1, cvtOk20_of_det (op := .extend .unsigned) (Sim.Floats.det_of nofun nofun) rfl h⟩

theorem cvtOk20_wrap (x : BitVec 64) :
    CvtOk20 P (.int .i32) (.int .i64) .wrap x [bvV (x.setWidth 32)] := by
  have h := Sim.Floats.cvtOk_single (P := P) (op := .wrap) (w := x.setWidth 32)
    (Sim.Floats.det_of nofun nofun) rfl
  exact ⟨h.1, cvtOk20_of_det (op := .wrap) (Sim.Floats.det_of nofun nofun) rfl h⟩

theorem cvtOk20_trunc (f : FloatType) (i : IntType) (s : Signedness) (x : BitVec f.width) :
    CvtOk20 P (.int i) (.float f) (.trunc s) x
      (((convRes P (.trunc f i s) x).map fun z => numV ⟨.int i, z⟩).toList) := by
  have h := Sim.Floats.agree_opt (P := P) (op := .trunc f i s) (Sim.Floats.det_of nofun nofun) x
  cases f <;> cases i <;> exact h

theorem cvtOk20_truncSat (f : FloatType) (i : IntType) (s : Signedness) (x : BitVec f.width) :
    CvtOk20 P (.int i) (.float f) (.truncSat s) x
      (((convRes P (.truncSat f i s) x).map fun z => numV ⟨.int i, z⟩).toList) := by
  have h := Sim.Floats.agree_opt (P := P) (op := .truncSat f i s) (Sim.Floats.det_of nofun nofun) x
  have hn := cvtOk20_of_det (P := P) (op := .truncSat f i s) (Sim.Floats.det_of nofun nofun) rfl h
  cases f <;> cases i <;> exact ⟨h.1, hn⟩

theorem cvtOk20_convert (i : IntType) (f : FloatType) (s : Signedness) (x : BitVec i.width) :
    CvtOk20 P (.float f) (.int i) (.convert s) x [numV ⟨.float f, convertInt i f s x⟩] := by
  have h := Sim.Floats.cvtOk_single (P := P) (op := .convert i f s) (x := x)
    (w := convertInt i f s x) (Sim.Floats.det_of nofun nofun) rfl
  have hn := cvtOk20_of_det (P := P) (op := .convert i f s) (Sim.Floats.det_of nofun nofun) rfl h
  cases f <;> cases i <;> exact ⟨h.1, hn⟩

theorem cvtOk20_promote (x : BitVec 32) :
    CvtOk20 P (.float .f64) (.float .f32) .promote x
      ((bitsWhere 64 (fun z => convertP P .promote x (.ok z))).map
        fun z => numV ⟨.float .f64, z⟩) := by
  have h := Sim.Floats.agree_list (P := P) (op := .promote) (x := x) (.inl rfl) rfl
  refine ⟨h.1, fun hL => ?_, False.elim⟩
  obtain ⟨e, he⟩ := h.2.1 hL
  exact Sim.Floats.convertP_error_resize (.inl rfl) x e he

theorem cvtOk20_demote (x : BitVec 64) :
    CvtOk20 P (.float .f32) (.float .f64) .demote x
      ((bitsWhere 32 (fun z => convertP P .demote x (.ok z))).map
        fun z => numV ⟨.float .f32, z⟩) := by
  have h := Sim.Floats.agree_list (P := P) (op := .demote) (x := x) (.inr rfl) rfl
  refine ⟨h.1, fun hL => ?_, False.elim⟩
  obtain ⟨e, he⟩ := h.2.1 hL
  exact Sim.Floats.convertP_error_resize (.inr rfl) x e he

theorem cvtOk20_reinterpI32 (x : BitVec (NumType.width (.int .i32))) :
    CvtOk20 P (.float .f32) (.int .i32) .reinterpret x [numV ⟨.float .f32, x⟩] := by
  have h := Sim.Floats.cvtOk_single (P := P) (op := .reinterpretFloat .i32) (x := x) (w := x)
    (Sim.Floats.det_of nofun nofun) rfl
  exact ⟨h.1, cvtOk20_of_det (op := .reinterpretFloat .i32) (Sim.Floats.det_of nofun nofun) rfl h⟩

theorem cvtOk20_reinterpI64 (x : BitVec (NumType.width (.int .i64))) :
    CvtOk20 P (.float .f64) (.int .i64) .reinterpret x [numV ⟨.float .f64, x⟩] := by
  have h := Sim.Floats.cvtOk_single (P := P) (op := .reinterpretFloat .i64) (x := x) (w := x)
    (Sim.Floats.det_of nofun nofun) rfl
  exact ⟨h.1, cvtOk20_of_det (op := .reinterpretFloat .i64) (Sim.Floats.det_of nofun nofun) rfl h⟩

theorem cvtOk20_reinterpF32 (x : BitVec (NumType.width (.float .f32))) :
    CvtOk20 P (.int .i32) (.float .f32) .reinterpret x [numV ⟨.int .i32, x⟩] := by
  have h := Sim.Floats.cvtOk_single (P := P) (op := .reinterpretInt .f32) (x := x) (w := x)
    (Sim.Floats.det_of nofun nofun) rfl
  exact ⟨h.1, cvtOk20_of_det (op := .reinterpretInt .f32) (Sim.Floats.det_of nofun nofun) rfl h⟩

theorem cvtOk20_reinterpF64 (x : BitVec (NumType.width (.float .f64))) :
    CvtOk20 P (.int .i64) (.float .f64) .reinterpret x [numV ⟨.int .i64, x⟩] := by
  have h := Sim.Floats.cvtOk_single (P := P) (op := .reinterpretInt .f64) (x := x) (w := x)
    (Sim.Floats.det_of nofun nofun) rfl
  exact ⟨h.1, cvtOk20_of_det (op := .reinterpretInt .f64) (Sim.Floats.det_of nofun nofun) rfl h⟩

/-- What `CvtAgree` asks at one conversion operator. -/
def CvtGoal20 (B : Builtins) (P : Profile) (op : V2.CvtOp) : Prop :=
  ∀ (target source : NumType) (x : BitVec source.width),
    (V2.CvtOp.toShared target source op).isSome →
    ∃ vs, Applies (simEnv20 B) "cvtop__" (cvtArgs20 target source op x) (.list vs) ∧
      CvtOk20 P target source op x vs

theorem cvtGoal20_extend (hB : FloatB P B) (s : Signedness) : CvtGoal20 B P (.extend s) := by
  intro target source x hop
  rcases target with (_ | _) | (_ | _) <;> rcases source with (_ | _) | (_ | _) <;>
    simp [V2.CvtOp.toShared] at hop
  exact ⟨_, applies_cvt_extend20 hB s x, cvtOk20_extend (P := P) s x⟩

theorem cvtGoal20_wrap (hB : FloatB P B) : CvtGoal20 B P .wrap := by
  intro target source x hop
  rcases target with (_ | _) | (_ | _) <;> rcases source with (_ | _) | (_ | _) <;>
    simp [V2.CvtOp.toShared] at hop
  exact ⟨_, applies_cvt_wrap20 hB x, cvtOk20_wrap (P := P) x⟩

theorem cvtGoal20_convert (hB : FloatB P B) (s : Signedness) : CvtGoal20 B P (.convert s) := by
  intro target source x hop
  rcases target with i | f <;> rcases source with i' | f' <;>
    simp [V2.CvtOp.toShared] at hop
  exact ⟨_, applies_cvt_convert20 hB i' f s x, cvtOk20_convert (P := P) i' f s x⟩

theorem cvtGoal20_trunc (hB : FloatB P B) (s : Signedness) : CvtGoal20 B P (.trunc s) := by
  intro target source x hop
  rcases target with i | f <;> rcases source with i' | f' <;>
    simp [V2.CvtOp.toShared] at hop
  exact ⟨_, applies_cvt_trunc20 hB f' i s x, cvtOk20_trunc (P := P) f' i s x⟩

theorem cvtGoal20_truncSat (hB : FloatB P B) (s : Signedness) : CvtGoal20 B P (.truncSat s) := by
  intro target source x hop
  rcases target with i | f <;> rcases source with i' | f' <;>
    simp [V2.CvtOp.toShared] at hop
  exact ⟨_, applies_cvt_truncSat20 hB f' i s x, cvtOk20_truncSat (P := P) f' i s x⟩

theorem cvtGoal20_promote (hB : FloatB P B) : CvtGoal20 B P .promote := by
  intro target source x hop
  rcases target with (_ | _) | (_ | _) <;> rcases source with (_ | _) | (_ | _) <;>
    simp [V2.CvtOp.toShared] at hop
  exact ⟨_, applies_cvt_promote20 hB x, cvtOk20_promote (P := P) x⟩

theorem cvtGoal20_demote (hB : FloatB P B) : CvtGoal20 B P .demote := by
  intro target source x hop
  rcases target with (_ | _) | (_ | _) <;> rcases source with (_ | _) | (_ | _) <;>
    simp [V2.CvtOp.toShared] at hop
  exact ⟨_, applies_cvt_demote20 hB x, cvtOk20_demote (P := P) x⟩

theorem cvtGoal20_reinterpret (hB : FloatB P B) : CvtGoal20 B P .reinterpret := by
  intro target source x hop
  rcases target with (_ | _) | (_ | _) <;> rcases source with (_ | _) | (_ | _) <;>
    simp [V2.CvtOp.toShared, IntType.width, FloatType.width] at hop
  · exact ⟨_, applies_cvt_reinterp_f32_20 hB x, cvtOk20_reinterpF32 (P := P) x⟩
  · exact ⟨_, applies_cvt_reinterp_f64_20 hB x, cvtOk20_reinterpF64 (P := P) x⟩
  · exact ⟨_, applies_cvt_reinterp_i32_20 hB x, cvtOk20_reinterpI32 (P := P) x⟩
  · exact ⟨_, applies_cvt_reinterp_i64_20 hB x, cvtOk20_reinterpI64 (P := P) x⟩

/-- **`CvtAgree` holds for the wasm-2.0 script** under the float and conversion primitives of
the profile (`FloatB`). -/
theorem cvtAgree_simEnv20 (hB : FloatB P B) : CvtAgree (simEnv20 B) P where
  cvt target source op x hop := by
    cases op with
    | extend s => exact cvtGoal20_extend hB s target source x hop
    | wrap => exact cvtGoal20_wrap hB target source x hop
    | convert s => exact cvtGoal20_convert hB s target source x hop
    | trunc s => exact cvtGoal20_trunc hB s target source x hop
    | truncSat s => exact cvtGoal20_truncSat hB s target source x hop
    | promote => exact cvtGoal20_promote hB target source x hop
    | demote => exact cvtGoal20_demote hB target source x hop
    | reinterpret => exact cvtGoal20_reinterpret hB target source x hop

/-- In particular for the concrete interpretation of the primitives at the profile `P`. -/
theorem cvtAgree_floatIntB20 : CvtAgree (simEnv20 (Sim.Floats.floatIntB P)) P :=
  cvtAgree_simEnv20 (Sim.Floats.floatB_floatIntB P)

/-- **All four numeric hypotheses of the 2.0 rule-level theorems hold** under the builtins the
3.0 simulation takes (`IntB`, `FloatB`): every numeric iff of `Sim20.Pure` (`intUnOp_iff` …
`cvtOpTrap_iff`) is unconditional at such `B`. -/
theorem numericHyps_simEnv20 (hI : Sim.IntNumeric.IntB B) (hF : FloatB P B) :
    NumAgree (simEnv20 B) P ∧ CvtAgree (simEnv20 B) P ∧ NumTyped (simEnv20 B) ∧
      CvtTyped (simEnv20 B) :=
  ⟨numAgree_simEnv20 hI hF, cvtAgree_simEnv20 hF, numTyped_simEnv20 B, cvtTyped_simEnv20 B⟩

end Silmaril.Wasm.SpecTec.Sim20.Pure
