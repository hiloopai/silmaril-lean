module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.Instr

/-!
# Round 5: the scalar numeric instructions are typed

Every valid scalar numeric instruction is a typed `instr`, in every `simEnv B`: the integer and
float `UNOP`/`BINOP`/`TESTOP`/`RELOP` (through the operator-family lemmas of the integer and float
tracks; `iN.extendN_s` needs `N` below the width, which validity gives) and every conversion
`CVTOP` (through `Floats.typedDep2_cvtop`, moved to the instruction's variable names by
`hasTyp_varT_transfer`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Pos

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {B : Builtins}

/-- A named type applied to arguments depends only on their values. -/
theorem hasTyp_varT_transfer {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {args args' : List Arg}
    {v : Value} {ws : List ArgV} (hl : localTyp? ρ x args = none)
    (hl' : localTyp? ρ' x args' = none) (h : HasTyp env ρ (.varT x args) v)
    (ha : EvalArgs env ρ args ws) (ha' : EvalArgs env ρ' args' ws) :
    HasTyp env ρ' (.varT x args') v := by
  obtain ⟨td, ws₁, htd, hargs, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  obtain ⟨n₁, h₁⟩ := hargs
  obtain ⟨n₂, h₂⟩ := ha
  have e₁ := evalArgs_ok_of_le (le_max_left n₁ n₂) h₁
  have e₂ := evalArgs_ok_of_le (le_max_right n₁ n₂) h₂
  have hws : ws₁ = ws := Except.ok.inj (e₁.symm.trans e₂)
  exact (hasTyp_varT_global_iff hl').2 ⟨td, ws, htd, ha', hws ▸ hi⟩

/-- The payload `numtype; op_(numtype)` of a numeric instruction. -/
theorem hasTyp_numOp {X : IL.Id} {nv ov : Value}
    (hnt : HasTyp (simEnv B) VarEnv.empty (.varT "numtype" []) nv)
    (hop : HasTyp (simEnv B) (VarEnv.empty.bindVal "numtype" nv) (.varT X [.expA (.varE "numtype")])
      ov) :
    HasTyp (simEnv B) VarEnv.empty
      (.tupT [.mk "numtype" (.varT "numtype" []), .mk "_" (.varT X [.expA (.varE "numtype")])])
      (.tuple [nv, ov]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hnt,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, hop, hasTypTup_nil_iff.2 rfl⟩⟩⟩

/-- `numtype` is bound in the scope of the operator. -/
theorem findVal_numtype (nv : Value) :
    (VarEnv.empty.bindVal "numtype" nv).findVal? "numtype" = some nv := by
  simp [Equiv.Execution.findVal?_bindVal_lit]

/-- A valid integer unary operator is valid at its type. -/
theorem intUnOp_valid {C : Context} {t : IntType} {op : IntUnOp} {it : InstrType}
    (h : InstrOk C (.intUnOp t op) it) : op.valid t = true := by
  cases h with
  | numeric hp => cases hp with | intUnOp hv => exact hv
  | parametric hp => cases hp
  | vector hp => cases hp
  | «variable» hp => cases hp
  | memory hp => cases hp
  | table hp => cases hp
  | reference hp => cases hp

set_option maxRecDepth 100000 in
/-- **Every valid integer numeric instruction is typed.** -/
theorem typedV_intNumeric {C : Context} {i : Instr} {it : InstrType} (hok : InstrOk C i it)
    (hi : (∃ t op, i = .intUnOp t op) ∨ (∃ t op, i = .intBinOp t op) ∨
      (∃ t op, i = .intTestOp t op) ∨ (∃ t op, i = .intRelOp t op)) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV i) := by
  have hnt (t : IntType) : HasTyp (simEnv B) VarEnv.empty (.varT "numtype" []) (IntNumeric.ntV t) :=
    IntNumeric.hasTyp_numtype ⟨rfl, rfl, rfl⟩ t
  rcases hi with ⟨t, op, rfl⟩ | ⟨t, op, rfl⟩ | ⟨t, op, rfl⟩ | ⟨t, op, rfl⟩
  · rw [IntNumeric.instrToV_intUnOp t op (intUnOp_valid hok)]
    exact FwdMem.typedV_instrCase rfl rfl (hasTyp_numOp (hnt t)
      (IntNumeric.hasTyp_unop (evalExp_var (findVal_numtype _)) op (intUnOp_valid hok)))
  · rw [IntNumeric.instrToV_intBinOp]
    exact FwdMem.typedV_instrCase rfl rfl (hasTyp_numOp (hnt t)
      (IntNumeric.hasTyp_binop (evalExp_var (findVal_numtype _)) op))
  · rw [IntNumeric.instrToV_intTestOp]
    exact FwdMem.typedV_instrCase rfl rfl (hasTyp_numOp (hnt t)
      (IntNumeric.hasTyp_testop (evalExp_var (findVal_numtype _)) op))
  · rw [IntNumeric.instrToV_intRelOp]
    exact FwdMem.typedV_instrCase rfl rfl (hasTyp_numOp (hnt t)
      (IntNumeric.hasTyp_relop (evalExp_var (findVal_numtype _)) op))

/-- A dependent operator type over `nt`, moved to the instruction's variable `numtype`. -/
theorem hasTyp_dep_numtype {X : IL.Id} {v w : Value}
    (h : Vec.TypedDep (simEnv B) "nt" v (Vec.opT X "nt") w) :
    HasTyp (simEnv B) (VarEnv.empty.bindVal "numtype" v) (.varT X [.expA (.varE "numtype")]) w := by
  have hv : (VarEnv.empty.bindVal "nt" v).findVal? "nt" = some v := by
    simp [Equiv.Execution.findVal?_bindVal_lit]
  exact hasTyp_varT_transfer rfl rfl (h _ ⟨rfl, rfl, rfl⟩ hv)
    (Equiv.evalArgs_cons (evalExp_var hv) Equiv.evalArgs_nil)
    (Equiv.evalArgs_cons (evalExp_var (findVal_numtype v)) Equiv.evalArgs_nil)

set_option maxRecDepth 100000 in
/-- **Every float numeric instruction is typed.** -/
theorem typedV_floatNumeric {i : Instr}
    (hi : (∃ t op, i = .floatUnOp t op) ∨ (∃ t op, i = .floatBinOp t op) ∨
      (∃ t op, i = .floatRelOp t op)) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV i) := by
  have hnt (t : FloatType) :
      HasTyp (simEnv B) VarEnv.empty (.varT "numtype" []) (Vec.numTypeV (.float t)) :=
    Typing.hasTyp_numtype ⟨rfl, rfl, rfl⟩ (.float t)
  rcases hi with ⟨t, op, rfl⟩ | ⟨t, op, rfl⟩ | ⟨t, op, rfl⟩
  · rw [Vec.instrToV_floatUnOp]
    exact FwdMem.typedV_instrCase rfl rfl
      (hasTyp_numOp (hnt t) (hasTyp_dep_numtype (Floats.typedDep_unop t op)))
  · rw [Vec.instrToV_floatBinOp]
    exact FwdMem.typedV_instrCase rfl rfl
      (hasTyp_numOp (hnt t) (hasTyp_dep_numtype (Floats.typedDep_binop t op)))
  · rw [Vec.instrToV_floatRelOp]
    exact FwdMem.typedV_instrCase rfl rfl
      (hasTyp_numOp (hnt t) (hasTyp_dep_numtype (Floats.typedDep_relop t op)))

/-- The scope of `CVTOP`'s operator: `numtype_1` (the target) and then `numtype_2`. -/
abbrev cvtScope (op : ConvertOp) : VarEnv :=
  (VarEnv.empty.bindVal "numtype_1" (Vec.numTypeV op.target)).bindVal "numtype_2"
    (Vec.numTypeV op.source)

/-- Two variable arguments evaluate to their values. -/
theorem evalArgs_vars {env : Env} {ρ : VarEnv} {x y : IL.Id} {u v : Value}
    (hx : ρ.findVal? x = some u) (hy : ρ.findVal? y = some v) :
    EvalArgs env ρ [.expA (.varE x), .expA (.varE y)] [.val u, .val v] :=
  Equiv.evalArgs_cons (evalExp_var hx) (Equiv.evalArgs_cons (evalExp_var hy) Equiv.evalArgs_nil)

set_option maxRecDepth 100000 in
/-- **Every conversion is typed.** -/
theorem typedV_convert (op : ConvertOp) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.convert op)) := by
  let ρ₁ : VarEnv := (VarEnv.empty.bindVal "nt_1" (Vec.numTypeV op.source)).bindVal "nt_2"
    (Vec.numTypeV op.target)
  have h₁ : ρ₁.findVal? "nt_1" = some (Vec.numTypeV op.source) := by
    simp [ρ₁, Equiv.Execution.findVal?_bindVal_lit]
  have h₂ : ρ₁.findVal? "nt_2" = some (Vec.numTypeV op.target) := by
    simp [ρ₁, Equiv.Execution.findVal?_bindVal_lit]
  have hc : HasTyp (simEnv B) ρ₁ Vec.cvtopT (Vec.cvtOpV op) :=
    Floats.typedDep2_cvtop op ρ₁ ⟨rfl, rfl, rfl⟩ h₁ h₂
  have hs : (cvtScope op).findVal? "numtype_2" = some (Vec.numTypeV op.source) := by
    simp [cvtScope, Equiv.Execution.findVal?_bindVal_lit]
  have ht : (cvtScope op).findVal? "numtype_1" = some (Vec.numTypeV op.target) := by
    simp [cvtScope, Equiv.Execution.findVal?_bindVal_lit]
  have hc' : HasTyp (simEnv B) (cvtScope op)
      (.varT "cvtop__" [.expA (.varE "numtype_2"), .expA (.varE "numtype_1")]) (Vec.cvtOpV op) :=
    hasTyp_varT_transfer rfl rfl hc (evalArgs_vars h₁ h₂) (evalArgs_vars hs ht)
  exact FwdMem.typedV_instrCase rfl rfl (hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    Typing.hasTyp_numtype ⟨rfl, rfl, rfl⟩ op.target, hasTypTup_cons_iff.2 ⟨_, _, rfl,
      Typing.hasTyp_numtype ⟨rfl, rfl, rfl⟩ op.source,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, hc', hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩)

/-! ## Scalar loads and stores -/

set_option maxRecDepth 100000 in
theorem findTyp_loadop : ∃ ps qs, (simEnv B).findTyp? "loadop_" = some (ps,
    [.instD qs [.expA IntNumeric.innPat] (.variantT
      [.mk "%_%" (.tupT [.mk "sz" (.varT "sz" []), .mk "sx" (.varT "sx" [])]) []
        [.ifPr (.cmpE .ltOp (.numT .natT) (.projE (.uncaseE (.varE "sz") "%") 0)
          (.callE "sizenn" [.expA IntNumeric.innPat]))]])]) := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_storeop : ∃ ps qs, (simEnv B).findTyp? "storeop_" = some (ps,
    [.instD qs [.expA IntNumeric.innPat] (.variantT
      [.mk "%" (.tupT [.mk "sz" (.varT "sz" [])]) []
        [.ifPr (.cmpE .ltOp (.numT .natT) (.projE (.uncaseE (.varE "sz") "%") 0)
          (.callE "sizenn" [.expA IntNumeric.innPat]))]])]) := ⟨_, _, rfl⟩

/-- The scope of `loadop_`'s case after its pattern matched `Inn`. -/
abbrev innScope (t : IntType) : VarEnv := VarEnv.empty.bindVal "Inn" (IntNumeric.ntV t)

/-- `sz < $sizenn(Inn)`, in a scope binding `sz` to a smaller width. -/
theorem evalExp_szPrem {t : IntType} {p : PackSize} (hlt : p.width < t.width) {σ : VarEnv}
    (hsz : σ.findVal? "sz" = some (.case "%" (.tuple [.num (.natN p.width)])))
    (hinn : σ.findVal? "Inn" = some (IntNumeric.ntV t)) (hd : σ.findDef? "sizenn" = none) :
    EvalExp (simEnv B) σ (.cmpE .ltOp (.numT .natT) (.projE (.uncaseE (.varE "sz") "%") 0)
      (.callE "sizenn" [.expA IntNumeric.innPat])) (.bool true) :=
  evalExp_cmpNum (IntNumeric.evalExp_pctPayload hsz) (IntNumeric.evalExp_sizennInn t hd hinn)
    (by simp [Num.cmp, hlt])

/-- **A packed load's `sz _ sx` is a `loadop_(Inn)`** below the type's width. -/
theorem hasTyp_loadop {t : IntType} {p : PackSize} (s : Signedness) (hlt : p.width < t.width) :
    HasTyp (simEnv B) (VarEnv.empty.bindVal "numtype" (Encode.toValue (NumType.int t)))
      (.varT "loadop_" [.expA (.varE "numtype")]) (.case "%_%" (.tuple [szV p, sxV s])) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_loadop (B := B)
  have he : EvalExp (simEnv B) (VarEnv.empty.bindVal "numtype" (Encode.toValue (NumType.int t)))
      (.varE "numtype") (IntNumeric.ntV t) := by
    rw [← ConfigOk.encode_int_ntV]
    exact evalExp_var (findVal_numtype _)
  have hσ : ValsOnly (innScope t) := ⟨rfl, rfl, rfl⟩
  have htup : HasTyp (simEnv B) (innScope t) (.tupT [.mk "sz" (.varT "sz" []), .mk "sx" (.varT "sx" [])])
      (.tuple [szV p, sxV s]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, IntNumeric.hasTyp_sz hσ p,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, ConfigOk.typedV_sx s _ ⟨rfl, rfl, rfl⟩,
        hasTypTup_nil_iff.2 rfl⟩⟩⟩
  exact IntNumeric.hasTyp_innVariant (rest := []) htd he
    (IntNumeric.hasTypCase_of_findCase rfl htup (IntNumeric.premsOk_if
      (evalExp_szPrem hlt
        (by simp [caseScope, typBinds, Equiv.Execution.findVal?_bindVal_lit, szV, Equiv.Execution.pctV])
        (by simp [caseScope, typBinds, Equiv.Execution.findVal?_bindVal_lit]) rfl)))

/-- **A packed store's `sz` is a `storeop_(Inn)`** below the type's width. -/
theorem hasTyp_storeop {t : IntType} {p : PackSize} (hlt : p.width < t.width) :
    HasTyp (simEnv B) (VarEnv.empty.bindVal "numtype" (Encode.toValue (NumType.int t)))
      (.varT "storeop_" [.expA (.varE "numtype")]) (.case "%" (.tuple [szV p])) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_storeop (B := B)
  have he : EvalExp (simEnv B) (VarEnv.empty.bindVal "numtype" (Encode.toValue (NumType.int t)))
      (.varE "numtype") (IntNumeric.ntV t) := by
    rw [← ConfigOk.encode_int_ntV]
    exact evalExp_var (findVal_numtype _)
  have hσ : ValsOnly (innScope t) := ⟨rfl, rfl, rfl⟩
  have htup : HasTyp (simEnv B) (innScope t) (.tupT [.mk "sz" (.varT "sz" [])]) (.tuple [szV p]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, IntNumeric.hasTyp_sz hσ p,
      hasTypTup_nil_iff.2 rfl⟩⟩
  exact IntNumeric.hasTyp_innVariant (rest := []) htd he
    (IntNumeric.hasTypCase_of_findCase rfl htup (IntNumeric.premsOk_if
      (evalExp_szPrem hlt
        (by simp [caseScope, typBinds, Equiv.Execution.findVal?_bindVal_lit, szV, Equiv.Execution.pctV])
        (by simp [caseScope, typBinds, Equiv.Execution.findVal?_bindVal_lit]) rfl)))

/-- The payload `numtype; op?; memidx; memarg` of a scalar load or store. -/
theorem hasTyp_memOp {X : IL.Id} {nt : NumType} {o : Option Value} (m : MemIdx) (a : MemArg)
    (ho : ∀ w, o = some w →
      HasTyp (simEnv B) (VarEnv.empty.bindVal "numtype" (Encode.toValue nt))
        (.varT X [.expA (.varE "numtype")]) w) :
    HasTyp (simEnv B) VarEnv.empty
      (.tupT [.mk "numtype" (.varT "numtype" []),
        .mk "_" (.iterT (.varT X [.expA (.varE "numtype")]) .opt),
        .mk "memidx" (.varT "memidx" []), .mk "memarg" (.varT "memarg" [])])
      (.tuple [Encode.toValue nt, .opt o, Encode.toValue m, memargV a]) := by
  have hopt : HasTyp (simEnv B) (VarEnv.empty.bindVal "numtype" (Encode.toValue nt))
      (.iterT (.varT X [.expA (.varE "numtype")]) .opt) (.opt o) := by
    rcases o with _ | w
    · exact hasTyp_iterT_opt_iff.2 (.inl rfl)
    · exact hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, ho w rfl⟩)
  exact hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    ConfigOk.typedV_numtype nt _ ⟨rfl, rfl, rfl⟩, hasTypTup_cons_iff.2 ⟨_, _, rfl, hopt,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, typedV_xidx "memidx" (by simp [idxNames]) m _ ⟨rfl, rfl, rfl⟩,
        hasTypTup_cons_iff.2 ⟨_, _, rfl, ConfigOk.typedV_memarg a _ ⟨rfl, rfl, rfl⟩,
          hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩⟩

/-- A valid packed integer load is narrower than its type. -/
theorem intLoad_width {C : Context} {t : IntType} {p : PackSize} {s : Signedness} {m : MemIdx}
    {a : MemArg} {it : InstrType} (h : InstrOk C (.intLoad t (some (p, s)) m a) it) :
    p.width < t.width := by
  cases h with
  | memory hp => cases hp with | intLoadPack _ hsz _ => exact hsz
  | parametric hp => cases hp
  | numeric hp => cases hp
  | vector hp => cases hp
  | «variable» hp => cases hp
  | table hp => cases hp
  | reference hp => cases hp

/-- A valid packed integer store is narrower than its type. -/
theorem intStore_width {C : Context} {t : IntType} {p : PackSize} {m : MemIdx} {a : MemArg}
    {it : InstrType} (h : InstrOk C (.intStore t (some p) m a) it) : p.width < t.width := by
  cases h with
  | memory hp => cases hp with | intStorePack _ hsz _ => exact hsz
  | parametric hp => cases hp
  | numeric hp => cases hp
  | vector hp => cases hp
  | «variable» hp => cases hp
  | table hp => cases hp
  | reference hp => cases hp

set_option maxRecDepth 100000 in
/-- **Every valid scalar load is typed.** -/
theorem typedV_intLoad {C : Context} {t : IntType} {p : Option (PackSize × Signedness)}
    {m : MemIdx} {a : MemArg} {it : InstrType} (hok : InstrOk C (.intLoad t p m a) it) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.intLoad t p m a)) := by
  refine FwdMem.typedV_instrCase rfl rfl (hasTyp_memOp m a fun w hw => ?_)
  rcases p with _ | ⟨q, s⟩
  · cases hw
  · obtain rfl := (Option.some.inj hw).symm
    exact hasTyp_loadop s (intLoad_width hok)

set_option maxRecDepth 100000 in
/-- **Every valid scalar store is typed.** -/
theorem typedV_intStore {C : Context} {t : IntType} {p : Option PackSize} {m : MemIdx}
    {a : MemArg} {it : InstrType} (hok : InstrOk C (.intStore t p m a) it) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.intStore t p m a)) := by
  refine FwdMem.typedV_instrCase rfl rfl (hasTyp_memOp m a fun w hw => ?_)
  rcases p with _ | q
  · cases hw
  · obtain rfl := (Option.some.inj hw).symm
    exact hasTyp_storeop (intStore_width hok)

set_option maxRecDepth 100000 in
/-- Every float load is typed. -/
theorem typedV_floatLoad (t : FloatType) (m : MemIdx) (a : MemArg) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.floatLoad t m a)) :=
  FwdMem.typedV_instrCase rfl rfl
    (hasTyp_memOp (X := "loadop_") (o := none) m a fun _ h => by cases h)

set_option maxRecDepth 100000 in
/-- Every float store is typed. -/
theorem typedV_floatStore (t : FloatType) (m : MemIdx) (a : MemArg) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.floatStore t m a)) :=
  FwdMem.typedV_instrCase rfl rfl
    (hasTyp_memOp (X := "storeop_") (o := none) m a fun _ h => by cases h)

/-! ## The open classes, reduced to SIMD -/

set_option linter.unusedTactic false in
set_option maxRecDepth 100000 in
/-- **`OpenTyping` from SIMD**: the numeric, conversion, load and store classes are typed. -/
theorem openTyping_of_simd (hS : SimdTyping B) : OpenTyping B := by
  intro C i it hok hb hop
  by_cases hs : InstrSimd i = true
  · exact hS C i it hok hb hs
  · cases i <;> (try simp [InstrOpen, InstrSimd] at hop hs)
    all_goals first
      | exact typedV_intNumeric hok (.inl ⟨_, _, rfl⟩)
      | exact typedV_intNumeric hok (.inr (.inl ⟨_, _, rfl⟩))
      | exact typedV_intNumeric hok (.inr (.inr (.inl ⟨_, _, rfl⟩)))
      | exact typedV_intNumeric hok (.inr (.inr (.inr ⟨_, _, rfl⟩)))
      | exact typedV_floatNumeric (.inl ⟨_, _, rfl⟩)
      | exact typedV_floatNumeric (.inr (.inl ⟨_, _, rfl⟩))
      | exact typedV_floatNumeric (.inr (.inr ⟨_, _, rfl⟩))
      | exact typedV_convert _
      | exact typedV_intLoad hok
      | exact typedV_intStore hok
      | exact typedV_floatLoad _ _ _
      | exact typedV_floatStore _ _ _

/-- **`PosTypingNE` from `SimdTyping`.** -/
theorem posTypingNE_of_simd {H : Type} (hS : SimdTyping B) (hn : H → String) :
    PosTypingNE B hn :=
  posTypingNE_of_open (openTyping_of_simd hS) hn

end Silmaril.Wasm.SpecTec.Sim.Round5.Pos
