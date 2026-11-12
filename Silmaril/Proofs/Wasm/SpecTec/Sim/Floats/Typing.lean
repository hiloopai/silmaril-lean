module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Common

/-!
# Float track: `FloatTyping (simEnv B)`, for every `B`

Family V's typing interface for the scalar float operators and the conversions, proved through
the fixed script's own type definitions: `unop_`, `binop_`, `relop_` (`Original.d217`, `d218`,
`d220`, whose second instance is the `Fnn` variant) and `cvtop__` (`Original.d221`, four
instances by the kinds of the two number types, with the premises `$sizenn1(·) < $sizenn2(·)`
of `EXTEND`/`PROMOTE`, `>` of `WRAP`/`DEMOTE` and `=` of `REINTERPRET`). The `InstrTyped`
premise of `FloatTyping.cvtop` is not needed: every Core `ConvertOp` is well formed.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Floats

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d217 Original.d218 Original.d220 Original.d221)
open IntNumeric (instCases findCase hasTypCase_of_findCase hasTypCase_nullary premsOk_if)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## The `Fnn` instances of the operator families -/

/-- An operator family with an `Inn` instance and an `Fnn` instance. -/
def TwoKinds (x : IL.Id) (d : Def) : Prop :=
  ∃ ps qs qs', (simEnv B).findTyp? x = some (ps,
    [.instD qs [.expA Typing.innPat] (.variantT (instCases d 0)),
     .instD qs' [.expA Typing.fnnPat] (.variantT (instCases d 1))])

set_option maxRecDepth 100000 in
theorem twoKinds_unop : TwoKinds (B := B) "unop_" Original.d217 := ⟨_, _, _, rfl⟩
set_option maxRecDepth 100000 in
theorem twoKinds_binop : TwoKinds (B := B) "binop_" Original.d218 := ⟨_, _, _, rfl⟩
set_option maxRecDepth 100000 in
theorem twoKinds_relop : TwoKinds (B := B) "relop_" Original.d220 := ⟨_, _, _, rfl⟩

/-- The `Fnn` instance of a two-kind family holds its cases, at a float type. -/
theorem hasTyp_fnnVariant {x : IL.Id} {d : Def} (htd : TwoKinds (B := B) x d) {ρ : VarEnv}
    {e : Exp} {t : FloatType} (he : EvalExp (simEnv B) ρ e (Typing.fntV t)) {op : MixopS}
    {w : Value}
    (hc : HasTypCase (simEnv B) (VarEnv.empty.bindVal "Fnn" (Typing.fntV t)) (instCases d 1) op w) :
    HasTyp (simEnv B) ρ (.varT x [.expA e]) (.case op w) := by
  obtain ⟨ps, qs, qs', htd⟩ := htd
  obtain ⟨n, hn⟩ : MatchArgsUndef (simEnv B) VarEnv.empty [.expA Typing.innPat]
      [.val (Typing.fntV t)] :=
    matchArgs_cons_undef (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub
      (Typing.argSubOk_inn_float t rfl))
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_tail hn (hasTypInsts_head (matchArgs_cons (matchArg_expA
      (Equiv.Validation.matchExp_sub_iff.2 (matchExp_varE (by simp)))
      (Typing.argSubOk_fnn_float t rfl)) matchArgs_nil)
      (hasTypDef_variantT_iff.2 ⟨_, _, rfl, hc⟩)))

/-- `unop_(Fnn)` holds every float unary operator. -/
theorem typedDep_unop (t : FloatType) (op : FloatUnOp) :
    Vec.TypedDep (simEnv B) "nt" (Vec.numTypeV (.float t)) (Vec.opT "unop_" "nt") (Vec.fUnOpV op) :=
  fun _ _ hx => by
    cases op <;> exact hasTyp_fnnVariant twoKinds_unop (evalExp_var hx) (hasTypCase_nullary rfl)

/-- `binop_(Fnn)` holds every float binary operator. -/
theorem typedDep_binop (t : FloatType) (op : FloatBinOp) :
    Vec.TypedDep (simEnv B) "nt" (Vec.numTypeV (.float t)) (Vec.opT "binop_" "nt")
      (Vec.fBinOpV op) :=
  fun _ _ hx => by
    cases op <;> exact hasTyp_fnnVariant twoKinds_binop (evalExp_var hx) (hasTypCase_nullary rfl)

/-- `relop_(Fnn)` holds every float comparison. -/
theorem typedDep_relop (t : FloatType) (op : FloatRelOp) :
    Vec.TypedDep (simEnv B) "nt" (Vec.numTypeV (.float t)) (Vec.opT "relop_" "nt")
      (Vec.vFloatRelOpV op) :=
  fun _ _ hx => by
    cases op <;> exact hasTyp_fnnVariant twoKinds_relop (evalExp_var hx) (hasTypCase_nullary rfl)

/-! ## `cvtop__(nt_1, nt_2)` -/

/-- The instance patterns of `cvtop__`. -/
abbrev cvtPats (X₁ K₁ X₂ K₂ : IL.Id) : List Arg := [.expA (kindPat X₁ K₁), .expA (kindPat X₂ K₂)]

set_option maxRecDepth 100000 in
theorem findTyp_cvtop : ∃ ps q₁ q₂ q₃ q₄, (simEnv B).findTyp? "cvtop__" = some (ps,
    [.instD q₁ (cvtPats "Inn_1" "Inn" "Inn_2" "Inn") (.variantT (instCases Original.d221 0)),
     .instD q₂ (cvtPats "Inn_1" "Inn" "Fnn_2" "Fnn") (.variantT (instCases Original.d221 1)),
     .instD q₃ (cvtPats "Fnn_1" "Fnn" "Inn_2" "Inn") (.variantT (instCases Original.d221 2)),
     .instD q₄ (cvtPats "Fnn_1" "Fnn" "Fnn_2" "Fnn") (.variantT (instCases Original.d221 3))]) :=
  ⟨_, _, _, _, _, rfl⟩

/-- An instance of `cvtop__` of the given kinds matches. -/
theorem matchArgs_cvt {X₁ X₂ K₁ K₂ : IL.Id} (hK₁ : K₁ = "Inn" ∨ K₁ = "Fnn")
    (hK₂ : K₂ = "Inn" ∨ K₂ = "Fnn") (hX₁ : X₁ ≠ "_") (hX : X₁ ≠ X₂) {t₁ t₂ : NumType}
    (ht₁ : kindOf t₁ = K₁) (ht₂ : kindOf t₂ = K₂) :
    MatchArgs (simEnv B) VarEnv.empty (cvtPats X₁ K₁ X₂ K₂)
      [.val (Vec.numTypeV t₁), .val (Vec.numTypeV t₂)] (kscope X₁ X₂ t₁ t₂) :=
  matchArg_kinds hK₁ hK₂ hX₁ hX ht₁ ht₂ matchArgs_nil

/-- An instance of `cvtop__` of other kinds fails definitely. -/
theorem matchArgs_cvt_undef {X₁ X₂ K₁ K₂ : IL.Id} (hK₁ : K₁ = "Inn" ∨ K₁ = "Fnn")
    (hK₂ : K₂ = "Inn" ∨ K₂ = "Fnn") (hX₁ : X₁ ≠ "_") (hX : X₁ ≠ X₂) {t₁ t₂ : NumType}
    (h : kindOf t₁ ≠ K₁ ∨ kindOf t₂ ≠ K₂) :
    ∃ n, matchArgs n (simEnv B) VarEnv.empty (cvtPats X₁ K₁ X₂ K₂)
      [.val (Vec.numTypeV t₁), .val (Vec.numTypeV t₂)] = .error .undef :=
  matchArgs_kinds_undef hK₁ hK₂ hX₁ hX h

/-- `cvtop__(nt_1, nt_2)` from its instance list. -/
theorem hasTyp_cvtop_of_insts {ρ : VarEnv} {t₁ t₂ : NumType}
    (h₁ : ρ.findVal? "nt_1" = some (Vec.numTypeV t₁)) (h₂ : ρ.findVal? "nt_2" = some (Vec.numTypeV t₂))
    {v : Value} {ps : List Param} {is : List Inst} (htd : (simEnv B).findTyp? "cvtop__" = some (ps, is))
    (hi : HasTypInsts (simEnv B) is [.val (Vec.numTypeV t₁), .val (Vec.numTypeV t₂)] v) :
    HasTyp (simEnv B) ρ Vec.cvtopT v :=
  hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd
    (Equiv.evalArgs_cons (evalExp_var h₁) (Equiv.evalArgs_cons (evalExp_var h₂) Equiv.evalArgs_nil))
    hi

/-- The `variantT` instance at the head, from a case. -/
theorem hasTypInsts_case {q : List Param} {pats : List Arg} {cs : List TypCase} {is : List Inst}
    {ws : List ArgV} {σ : VarEnv} {op : MixopS} {w : Value}
    (hm : MatchArgs (simEnv B) VarEnv.empty pats ws σ) (hc : HasTypCase (simEnv B) σ cs op w) :
    HasTypInsts (simEnv B) (.instD q pats (.variantT cs) :: is) ws (.case op w) :=
  hasTypInsts_head hm (hasTypDef_variantT_iff.2 ⟨_, _, rfl, hc⟩)

/-- A case of `cvtop__`'s `(Inn, Inn)` instance. -/
theorem hasTyp_cvtII {ρ : VarEnv} {i₁ i₂ : IntType}
    (h₁ : ρ.findVal? "nt_1" = some (Vec.numTypeV (.int i₁)))
    (h₂ : ρ.findVal? "nt_2" = some (Vec.numTypeV (.int i₂))) {op : MixopS} {w : Value}
    (hc : HasTypCase (simEnv B) (kscope "Inn_1" "Inn_2" (.int i₁) (.int i₂))
      (instCases Original.d221 0) op w) :
    HasTyp (simEnv B) ρ Vec.cvtopT (.case op w) := by
  obtain ⟨ps, q₁, q₂, q₃, q₄, htd⟩ := findTyp_cvtop (B := B)
  exact hasTyp_cvtop_of_insts h₁ h₂ htd (hasTypInsts_case
    (matchArgs_cvt (.inl rfl) (.inl rfl) (by decide) (by decide) rfl rfl) hc)

/-- A case of `cvtop__`'s `(Inn, Fnn)` instance. -/
theorem hasTyp_cvtIF {ρ : VarEnv} {i : IntType} {f : FloatType}
    (h₁ : ρ.findVal? "nt_1" = some (Vec.numTypeV (.int i)))
    (h₂ : ρ.findVal? "nt_2" = some (Vec.numTypeV (.float f))) {op : MixopS} {w : Value}
    (hc : HasTypCase (simEnv B) (kscope "Inn_1" "Fnn_2" (.int i) (.float f))
      (instCases Original.d221 1) op w) :
    HasTyp (simEnv B) ρ Vec.cvtopT (.case op w) := by
  obtain ⟨ps, q₁, q₂, q₃, q₄, htd⟩ := findTyp_cvtop (B := B)
  obtain ⟨n, hn⟩ := matchArgs_cvt_undef (B := B) (X₁ := "Inn_1") (X₂ := "Inn_2") (.inl rfl)
    (.inl rfl) (by decide) (by decide) (t₁ := .int i) (t₂ := .float f) (.inr (by simp [kindOf]))
  exact hasTyp_cvtop_of_insts h₁ h₂ htd (hasTypInsts_tail hn (hasTypInsts_case
    (matchArgs_cvt (.inl rfl) (.inr rfl) (by decide) (by decide) rfl rfl) hc))

/-- A case of `cvtop__`'s `(Fnn, Inn)` instance. -/
theorem hasTyp_cvtFI {ρ : VarEnv} {f : FloatType} {i : IntType}
    (h₁ : ρ.findVal? "nt_1" = some (Vec.numTypeV (.float f)))
    (h₂ : ρ.findVal? "nt_2" = some (Vec.numTypeV (.int i))) {op : MixopS} {w : Value}
    (hc : HasTypCase (simEnv B) (kscope "Fnn_1" "Inn_2" (.float f) (.int i))
      (instCases Original.d221 2) op w) :
    HasTyp (simEnv B) ρ Vec.cvtopT (.case op w) := by
  obtain ⟨ps, q₁, q₂, q₃, q₄, htd⟩ := findTyp_cvtop (B := B)
  obtain ⟨n, hn⟩ := matchArgs_cvt_undef (B := B) (X₁ := "Inn_1") (X₂ := "Inn_2") (.inl rfl)
    (.inl rfl) (by decide) (by decide) (t₁ := .float f) (t₂ := .int i) (.inl (by simp [kindOf]))
  obtain ⟨n', hn'⟩ := matchArgs_cvt_undef (B := B) (X₁ := "Inn_1") (X₂ := "Fnn_2") (.inl rfl)
    (.inr rfl) (by decide) (by decide) (t₁ := .float f) (t₂ := .int i) (.inl (by simp [kindOf]))
  exact hasTyp_cvtop_of_insts h₁ h₂ htd (hasTypInsts_tail hn (hasTypInsts_tail hn'
    (hasTypInsts_case (matchArgs_cvt (.inr rfl) (.inl rfl) (by decide) (by decide) rfl rfl) hc)))

/-- A case of `cvtop__`'s `(Fnn, Fnn)` instance. -/
theorem hasTyp_cvtFF {ρ : VarEnv} {f₁ f₂ : FloatType}
    (h₁ : ρ.findVal? "nt_1" = some (Vec.numTypeV (.float f₁)))
    (h₂ : ρ.findVal? "nt_2" = some (Vec.numTypeV (.float f₂))) {op : MixopS} {w : Value}
    (hc : HasTypCase (simEnv B) (kscope "Fnn_1" "Fnn_2" (.float f₁) (.float f₂))
      (instCases Original.d221 3) op w) :
    HasTyp (simEnv B) ρ Vec.cvtopT (.case op w) := by
  obtain ⟨ps, q₁, q₂, q₃, q₄, htd⟩ := findTyp_cvtop (B := B)
  obtain ⟨n, hn⟩ := matchArgs_cvt_undef (B := B) (X₁ := "Inn_1") (X₂ := "Inn_2") (.inl rfl)
    (.inl rfl) (by decide) (by decide) (t₁ := .float f₁) (t₂ := .float f₂)
    (.inl (by simp [kindOf]))
  obtain ⟨n', hn'⟩ := matchArgs_cvt_undef (B := B) (X₁ := "Inn_1") (X₂ := "Fnn_2") (.inl rfl)
    (.inr rfl) (by decide) (by decide) (t₁ := .float f₁) (t₂ := .float f₂)
    (.inl (by simp [kindOf]))
  obtain ⟨n'', hn''⟩ := matchArgs_cvt_undef (B := B) (X₁ := "Fnn_1") (X₂ := "Inn_2") (.inr rfl)
    (.inl rfl) (by decide) (by decide) (t₁ := .float f₁) (t₂ := .float f₂)
    (.inr (by simp [kindOf]))
  exact hasTyp_cvtop_of_insts h₁ h₂ htd (hasTypInsts_tail hn (hasTypInsts_tail hn'
    (hasTypInsts_tail hn'' (hasTypInsts_case
      (matchArgs_cvt (.inr rfl) (.inr rfl) (by decide) (by decide) rfl rfl) hc))))

/-- `$sizenn1(X₁) ⋈ $sizenn2(X₂)` in a `cvtop__` case scope. -/
theorem evalExp_sizeCmp {op : CmpOp} {ot : OpTyp} {X₁ X₂ : IL.Id} {t₁ t₂ : NumType} {b : Bool}
    (hX₁ : X₁ ≠ "_") (hX₂ : X₂ ≠ "_") (hne : X₂ ≠ X₁)
    (hb : cmpValues op (natV t₁.width) (natV t₂.width) = .ok (.bool b)) {u₁ u₂ u₃ u₄ : Typ} :
    EvalExp (simEnv B) (kscope X₁ X₂ t₁ t₂)
      (.cmpE op ot (.callE "sizenn1" [.expA (.subE (.varE X₁) u₁ u₂)])
        (.callE "sizenn2" [.expA (.subE (.varE X₂) u₃ u₄)])) (.bool b) :=
  evalExp_cmpE_iff.2 ⟨_, _, evalExp_sizeFun findDef_sizenn1 t₁ rfl
      (by simp [Equiv.Execution.findVal?_bindVal_lit hX₂, Equiv.Execution.findVal?_bindVal_lit hX₁,
        hne]),
    evalExp_sizeFun findDef_sizenn2 t₂ rfl (by simp [Equiv.Execution.findVal?_bindVal_lit hX₂]),
    hb⟩

/-- A nullary `cvtop__` case whose one premise compares the sizes. -/
theorem hasTypCase_sizeCmp {X₁ X₂ : IL.Id} {t₁ t₂ : NumType} {cs : List TypCase} {o : MixopS}
    {op : CmpOp} {ot : OpTyp} {u₁ u₂ u₃ u₄ : Typ} (hX₁ : X₁ ≠ "_") (hX₂ : X₂ ≠ "_")
    (hne : X₂ ≠ X₁)
    (hf : findCase cs o = some (.tupT [], [.ifPr (.cmpE op ot
      (.callE "sizenn1" [.expA (.subE (.varE X₁) u₁ u₂)])
      (.callE "sizenn2" [.expA (.subE (.varE X₂) u₃ u₄)]))]))
    (hb : cmpValues op (natV t₁.width) (natV t₂.width) = .ok (.bool true))
    (hq : IntNumeric.quantFreeAt cs o = true := by rfl) :
    HasTypCase (simEnv B) (kscope X₁ X₂ t₁ t₂) cs o (.tuple []) :=
  hasTypCase_of_findCase hf hasTyp_tupT_nil (premsOk_if (evalExp_sizeCmp hX₁ hX₂ hne hb)) hq

/-- A `cvtop__` case carrying an `sx`, without premise. -/
theorem hasTypCase_cvtSx {X₁ X₂ : IL.Id} {t₁ t₂ : NumType} {cs : List TypCase} {o : MixopS}
    (hf : findCase cs o = some (.varT "sx" [], [])) (s : Signedness) :
    HasTypCase (simEnv B) (kscope X₁ X₂ t₁ t₂) cs o (sxV s) := by
  exact hasTypCase_of_findCase hf (hasTyp_sxV ⟨rfl, rfl, rfl⟩ s) premsOk_nil
    (IntNumeric.quantFreeAt_of_findCase_nil hf)

/-- **`cvtop__(nt_1, nt_2)` holds every Core conversion operator**, at its own number types. -/
theorem typedDep2_cvtop (op : ConvertOp) :
    Vec.TypedDep2 (simEnv B) "nt_1" (Vec.numTypeV op.source) "nt_2" (Vec.numTypeV op.target)
      Vec.cvtopT (Vec.cvtOpV op) := by
  intro ρ _ h₁ h₂
  cases op with
  | wrap => exact hasTyp_cvtII h₁ h₂ (hasTypCase_sizeCmp (by decide) (by decide) (by decide) rfl rfl)
  | extend s =>
      exact hasTyp_cvtII h₁ h₂ (hasTypCase_of_findCase rfl
        (hasTyp_sxV ⟨rfl, rfl, rfl⟩ s) (premsOk_if (evalExp_sizeCmp (by decide) (by decide) (by decide) rfl)))
  | trunc f i s => exact hasTyp_cvtFI h₁ h₂ (hasTypCase_cvtSx rfl s)
  | truncSat f i s => exact hasTyp_cvtFI h₁ h₂ (hasTypCase_cvtSx rfl s)
  | convert i f s => exact hasTyp_cvtIF h₁ h₂ (hasTypCase_cvtSx rfl s)
  | demote => exact hasTyp_cvtFF h₁ h₂ (hasTypCase_sizeCmp (by decide) (by decide) (by decide) rfl rfl)
  | promote => exact hasTyp_cvtFF h₁ h₂ (hasTypCase_sizeCmp (by decide) (by decide) (by decide) rfl rfl)
  | reinterpretInt f =>
      cases f <;> exact hasTyp_cvtFI h₁ h₂ (hasTypCase_sizeCmp (by decide) (by decide) (by decide) rfl (by simp [cmpValues, NumType.width, FloatType.width, IntType.width]))
  | reinterpretFloat i =>
      cases i <;> exact hasTyp_cvtIF h₁ h₂ (hasTypCase_sizeCmp (by decide) (by decide) (by decide) rfl (by simp [cmpValues, NumType.width, FloatType.width, IntType.width]))

/-- **`FloatTyping (simEnv B)`**, for every `B`. -/
theorem floatTyping_simEnv (B : Builtins) : Vec.FloatTyping (simEnv B) where
  numtype t := fun _ hρ => Typing.hasTyp_numtype hρ t
  num := Typing.typedDep_num
  i32 a := fun _ _ => IntNumeric.hasTyp_num (t := .i32) a
    (evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], Equiv.Validation.evalExps_nil_iff.2 rfl,
      rfl⟩, rfl⟩)
  unop := typedDep_unop
  binop := typedDep_binop
  relop := typedDep_relop
  cvtop op _ := typedDep2_cvtop op

end Silmaril.Wasm.SpecTec.Sim.Floats
