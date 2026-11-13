module

public import Silmaril.Wasm.SpecTec.Institution.Instr30X.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms
public import Silmaril.Wasm.SpecTec.Sim.State.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.ConfigOk.Thms

/-!
# Module typing of the wasm-3.0 script, `Limits_ok`, `Memtype_ok`, `Mem_ok`

The three rules a memory definition is validated by, located in `simEnv B` by a kernel `rfl`, and
fired at Core's valid memory types in every typed context value:

* `dd_limitsOk`: `Limits_ok(C, l, k)` holds whenever `l.Valid k` (Core's `Limits.Valid`), with
  both side conditions (`n ≤ k`, and `n ≤ m ∧ m ≤ k` iterated over the optional maximum)
  evaluated;
* `evalExp_memBound`: the bound `2 ^ ($size(at) - 16)` of `Memtype_ok` evaluates to
  `2 ^ (at.width - 16)`, through the script's `$size` clauses;
* `dd_memtypeOk`, `dd_memOk`: `Memtype_ok(C, mt)` and `Mem_ok(C, MEMORY mt, mt)` hold at every
  memory type that Core validates (`MemoryType.Valid`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Z

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv (natV)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (CtxT ctxP)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## The rules -/

/-- `Limits_ok`'s rule (definition 341). -/
def limitsOkRule : Rule :=
  .ruleD "" [ctxP, .expP "n" (.varT "n" []), .expP "m?" (.iterT (.varT "m" []) .opt),
      .expP "k" (.numT .natT)] "%|-%:%"
    (.tupE [.varE "C", .caseE "[%..%]" (.tupE [.caseE "%" (.tupE [.varE "n"]),
      .iterE (.caseE "%" (.tupE [.varE "m"])) (.mk .opt [.mk "m" (.varE "m?")])]), .varE "k"])
    [.ifPr (.cmpE .leOp (.numT .natT) (.varE "n") (.varE "k")),
     .iterPr (.ifPr (.binE .andOp .boolT (.cmpE .leOp (.numT .natT) (.varE "n") (.varE "m"))
       (.cmpE .leOp (.numT .natT) (.varE "m") (.varE "k")))) (.mk .opt [.mk "m" (.varE "m?")])]

set_option maxRecDepth 100000 in
/-- **`Limits_ok`'s rule**, rule 0 of `simEnv B`. -/
theorem ruleAt_limitsOk : HasRuleAt (simEnv B) "Limits_ok" "%|-%:%" 0 limitsOkRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- The bound of `Memtype_ok`, `2 ^ ($size(addrtype) - 16)`. -/
def memBoundE : Exp :=
  .binE .powOp (.numT .natT) (.numE (.natN 2)) (.cvtE (.binE .subOp (.numT .intT)
    (.cvtE (.callE "size" [.expA (.subE (.varE "addrtype") (.varT "addrtype" []) (.varT "numtype" []))])
      .natT .intT) (.cvtE (.numE (.natN 16)) .natT .intT)) .intT .natT)

/-- `Memtype_ok`'s rule (definition 344). -/
def memtypeOkRule : Rule :=
  .ruleD "" [ctxP, .expP "addrtype" (.varT "addrtype" []), .expP "limits" (.varT "limits" [])]
    "%|-%:OK" (.tupE [.varE "C", .caseE "%%PAGE" (.tupE [.varE "addrtype", .varE "limits"])])
    [.rulePr "Limits_ok" [] "%|-%:%" (.tupE [.varE "C", .varE "limits", memBoundE])]

set_option maxRecDepth 100000 in
/-- **`Memtype_ok`'s rule**, rule 0 of `simEnv B`. -/
theorem ruleAt_memtypeOk : HasRuleAt (simEnv B) "Memtype_ok" "%|-%:OK" 0 memtypeOkRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Mem_ok`'s rule (definition 369). -/
def memOkRule : Rule :=
  .ruleD "" [ctxP, .expP "memtype" (.varT "memtype" [])] "%|-%:%"
    (.tupE [.varE "C", .caseE "MEMORY" (.varE "memtype"), .varE "memtype"])
    [.rulePr "Memtype_ok" [] "%|-%:OK" (.tupE [.varE "C", .varE "memtype"])]

set_option maxRecDepth 100000 in
/-- **`Mem_ok`'s rule**, rule 0 of `simEnv B`. -/
theorem ruleAt_memOk : HasRuleAt (simEnv B) "Mem_ok" "%|-%:%" 0 memOkRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## `Limits_ok` -/

/-- The image of a limits bound, `%(n)`. -/
theorem toValue_fin64 (n : Fin (2 ^ 64)) :
    (Encode.toValue n : Value) = .case "%" (.tuple [natV n.val]) := rfl

/-- The image of limits. -/
theorem toValue_limits (l : Silmaril.Wasm.Limits) :
    (Encode.toValue l : Value) = .case "[%..%]" (.tuple [.case "%" (.tuple [natV l.min.val]),
      .opt (l.max.map fun m => .case "%" (.tuple [natV m.val]))]) := by
  rcases l with ⟨a, _ | b⟩ <;> rfl

/-- `Limits_ok`'s scope at `(c, l, k)`. -/
def limσ (c : Value) (l : Silmaril.Wasm.Limits) (k : Nat) : List (IL.Id × Value) :=
  [("C", c), ("n", natV l.min.val), ("m?", .opt (l.max.map fun m => natV m.val)), ("k", natV k)]

/-- `limσ` is a well-typed assignment of `Limits_ok`'s quantifiers. -/
theorem quantsOk_lim {c : Value} (hc : CtxT B c) (l : Silmaril.Wasm.Limits) (k : Nat) :
    QuantsOk (simEnv B) (VarEnv.empty.bindVals (limσ c l k))
      [ctxP, .expP "n" (.varT "n" []), .expP "m?" (.iterT (.varT "m" []) .opt),
        .expP "k" (.numT .natT)] := by
  have hρ := valsOnly_bind (limσ c l k)
  have hm : HasTyp (simEnv B) (VarEnv.empty.bindVals (limσ c l k)) (.iterT (.varT "m" []) .opt)
      (.opt (l.max.map fun m => natV m.val)) := by
    rcases l.max with _ | m
    · exact hasTyp_iterT_opt_iff.2 (.inl rfl)
    · exact hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, Typing.typedV_natAlias Typing.findTyp_m _ _ hρ⟩)
  exact QuantsOk.cons rfl (hc _ hρ) <|
    QuantsOk.cons rfl (Typing.typedV_natAlias Typing.findTyp_n _ _ hρ) <|
    QuantsOk.cons rfl hm <| QuantsOk.cons rfl (hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩) QuantsOk.nil

/-- `Limits_ok`'s conclusion evaluates to `(c, l, k)` in `limσ`. -/
theorem evalExp_limConcl (c : Value) (l : Silmaril.Wasm.Limits) (k : Nat) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (limσ c l k))
      (.tupE [.varE "C", .caseE "[%..%]" (.tupE [.caseE "%" (.tupE [.varE "n"]),
        .iterE (.caseE "%" (.tupE [.varE "m"])) (.mk .opt [.mk "m" (.varE "m?")])]), .varE "k"])
      (.tuple [c, Encode.toValue l, natV k]) := by
  rw [toValue_limits]
  rcases l with ⟨n, _ | m⟩
  · exact ⟨10, by simp [limσ, evalExp, evalExps, evalIterE, evalDoms, domSrc, domVar,
      VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, Map.find?, Value.asOpt?, Bind.bind,
      Except.bind, Res.ofOption, Pure.pure, Except.pure, Functor.map, Except.map]⟩
  · exact ⟨20, by simp [limσ, evalExp, evalExps, evalIterE, evalDoms, domSrc, domVar,
      VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, Map.find?, Value.asOpt?, Bind.bind,
      Except.bind, Res.ofOption, Pure.pure, Except.pure, Functor.map, Except.map]⟩

/-- `Limits_ok`'s first side condition, `n ≤ k`. -/
theorem dprem_limLe (O : ElseI) (els : Prop) (c : Value) (n : Fin (2 ^ 64))
    (mx : Option (Fin (2 ^ 64))) {k : Nat} (hn : n.val ≤ k) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals (limσ c ⟨n, mx⟩ k))
      (.ifPr (.cmpE .leOp (.numT .natT) (.varE "n") (.varE "k"))) :=
  .ifPr ⟨10, by simp [limσ, evalExp, VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind,
    Map.find?, Bind.bind, Except.bind, Res.ofOption, cmpValues, Num.cmp, natV, hn]⟩

/-- The rule's iterated premise `(n ≤ m ∧ m ≤ k)?` over the optional maximum. -/
abbrev limMaxPr : Prem :=
  .iterPr (.ifPr (.binE .andOp .boolT (.cmpE .leOp (.numT .natT) (.varE "n") (.varE "m"))
    (.cmpE .leOp (.numT .natT) (.varE "m") (.varE "k")))) (.mk .opt [.mk "m" (.varE "m?")])

/-- `Limits_ok`'s second side condition, vacuous without a maximum. -/
theorem dprem_limMaxNone (O : ElseI) (els : Prop) (c : Value) (n : Fin (2 ^ 64)) (k : Nat) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals (limσ c ⟨n, none⟩ k)) limMaxPr :=
  .iterOptNone (xvs := [("m", .opt none)]) ⟨5, by simp [limσ, evalDoms, domSrc, domVar,
    evalExp, VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, Map.find?, Bind.bind,
    Except.bind, Res.ofOption, Pure.pure, Except.pure]⟩ (by simp) (by simp)

/-- `Limits_ok`'s second side condition at a maximum `m`: `n ≤ m ∧ m ≤ k`. -/
theorem dprem_limMaxSome (O : ElseI) (els : Prop) (c : Value) (n m : Fin (2 ^ 64)) {k : Nat}
    (h₁ : n.val ≤ m.val) (h₂ : m.val ≤ k) :
    DPremB (simEnv B) O els (VarEnv.empty.bindVals (limσ c ⟨n, some m⟩ k)) limMaxPr :=
  .iterOptSome (xvs := [("m", .opt (some (natV m.val)))]) (row := [("m", natV m.val)])
    ⟨5, by simp [limσ, evalDoms, domSrc, domVar, evalExp, VarEnv.findVal?, VarEnv.bindVals,
      Map.binds, Map.bind, Map.find?, Bind.bind, Except.bind, Res.ofOption, Pure.pure,
      Except.pure]⟩ (by simp) (by simp [domSomes]) (.ifPr ⟨10, by
      simp [limσ, evalExp, VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, Map.find?,
        Bind.bind, Except.bind, Res.ofOption, cmpValues, Num.cmp, natV, boolShort, binValues,
        boolBin, h₁, h₂]⟩)

/-- Both side conditions of `Limits_ok` hold when Core's `l.Valid k` does. -/
theorem dprem_limMax (O : ElseI) (els : Prop) (c : Value) {l : Silmaril.Wasm.Limits} {k : Nat}
    (hv : l.Valid k) : DPremB (simEnv B) O els (VarEnv.empty.bindVals (limσ c l k)) limMaxPr :=
  match l, hv with
  | ⟨n, none⟩, _ => dprem_limMaxNone O els c n k
  | ⟨n, some m⟩, hv => dprem_limMaxSome O els c n m hv.2.1 hv.2.2

/-- **`Limits_ok(C, l, k)` holds when Core's `l.Valid k` does**, in every typed context. -/
theorem dd_limitsOk (O : ElseI) {c : Value} (hc : CtxT B c) (l : Silmaril.Wasm.Limits) {k : Nat}
    (hv : l.Valid k) :
    DDerivesB (simEnv B) O "Limits_ok" "%|-%:%" [] (.tuple [c, Encode.toValue l, natV k]) :=
  dderivesB_of_ruleAt ruleAt_limitsOk (self_mem_conclAlts _) (limσ c l k)
    (quantsOk_lim hc l k) (evalExp_limConcl c l k) fun pr hpr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
      rcases hpr with rfl | rfl
      exacts [dprem_limLe O _ c l.min l.max hv.1, dprem_limMax O _ c hv]

/-! ## `Memtype_ok` and `Mem_ok` -/

/-- The image of a memory type, `%%PAGE(at, l)`. -/
theorem toValue_memtype (mt : Silmaril.Wasm.MemoryType) :
    (Encode.toValue mt : Value) =
      .case "%%PAGE" (.tuple [Encode.toValue mt.address, Encode.toValue mt.limits]) := rfl

/-- **The bound of `Memtype_ok` is `2 ^ (at.width - 16)`**, wherever `addrtype` is bound to the
image of `at`: `$size` is evaluated through the script's clauses. -/
theorem evalExp_memBound {ρ : VarEnv} (hρ : ρ.findDef? "size" = none)
    (a : Silmaril.Wasm.AddrType) (ha : ρ.findVal? "addrtype" = some (Encode.toValue a)) :
    EvalExp (simEnv B) ρ memBoundE (natV (2 ^ (a.width - 16))) := by
  have hs := State.evalExp_size (State.growDefs_simEnv B) hρ a
    (e := .subE (.varE "addrtype") (.varT "addrtype" []) (.varT "numtype" []))
    (evalExp_subE_iff.2 (Sim.evalExp_var ha))
  have hw : EvalExp (simEnv B) ρ (.binE .subOp (.numT .intT)
      (.cvtE (.callE "size" [.expA (.subE (.varE "addrtype") (.varT "addrtype" [])
        (.varT "numtype" []))]) .natT .intT) (.cvtE (.numE (.natN 16)) .natT .intT))
      (.num (.intN ((a.intType.width : Int) - 16))) :=
    evalExp_binE_iff.2 ⟨_, evalExp_cvtNum hs rfl, .inr ⟨rfl, _, evalExp_cvtNum evalExp_num rfl,
      rfl⟩⟩
  refine evalExp_binE_iff.2 ⟨_, evalExp_num, .inr ⟨rfl, _,
    evalExp_cvtNum (m' := .natN (a.width - 16)) hw ?_, ?_⟩⟩
  · cases a <;> rfl
  · cases a <;> rfl

/-- `Memtype_ok`'s scope at `(c, mt)`. -/
def mtσ (c : Value) (mt : Silmaril.Wasm.MemoryType) : List (IL.Id × Value) :=
  [("C", c), ("addrtype", Encode.toValue mt.address), ("limits", Encode.toValue mt.limits)]

/-- **`Memtype_ok(C, mt)` holds when Core validates `mt`**, in every typed context. -/
theorem dd_memtypeOk (O : ElseI) {c : Value} (hc : CtxT B c) {mt : Silmaril.Wasm.MemoryType}
    (hv : mt.Valid) :
    DDerivesB (simEnv B) O "Memtype_ok" "%|-%:OK" [] (.tuple [c, Encode.toValue mt]) := by
  have hρ := valsOnly_bind (mtσ c mt)
  refine dderivesB_of_ruleAt ruleAt_memtypeOk (self_mem_conclAlts _) (mtσ c mt)
    (QuantsOk.cons rfl (hc _ hρ) <| QuantsOk.cons rfl (Typing.typedV_addrtype _ _ hρ) <|
      QuantsOk.cons rfl (Round5.Pos.typedV_limits _ _ hρ) QuantsOk.nil)
    (evalExp_tup2 (Sim.evalExp_var rfl) (evalExp_case (evalExp_tup2 (Sim.evalExp_var rfl)
      (Sim.evalExp_var rfl)))) ?_
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  subst hpr
  exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)
    (evalExp_memBound (Memory.findDef_bindVals_empty _ _) mt.address rfl))
    (dd_limitsOk O hc mt.limits hv)

/-- **Every memory type is a `memtype`.** -/
theorem typedV_memtype (mt : Silmaril.Wasm.MemoryType) :
    TypedV (simEnv B) (.varT "memtype" []) (Encode.toValue mt) := by
  rw [toValue_memtype]
  exact Typing.typedV_closedCase ConfigOk.findTyp_memtype rfl
    (Round5.Pos.hasTyp_tup2 (Typing.typedV_addrtype _) (Round5.Pos.typedV_limits _))

/-- **`Mem_ok(C, MEMORY mt, mt)` holds when Core validates `mt`**, in every typed context. -/
theorem dd_memOk (O : ElseI) {c : Value} (hc : CtxT B c) {mt : Silmaril.Wasm.MemoryType}
    (hv : mt.Valid) :
    DDerivesB (simEnv B) O "Mem_ok" "%|-%:%" []
      (.tuple [c, .case "MEMORY" (Encode.toValue mt), Encode.toValue mt]) := by
  have hρ := valsOnly_bind [("C", c), ("memtype", Encode.toValue mt)]
  refine dderivesB_of_ruleAt ruleAt_memOk (self_mem_conclAlts _)
    [("C", c), ("memtype", Encode.toValue mt)]
    (QuantsOk.cons rfl (hc _ hρ) <| QuantsOk.cons rfl (typedV_memtype mt _ hρ) QuantsOk.nil)
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (Sim.evalExp_var rfl)) (Sim.evalExp_var rfl)) ?_
  intro pr hpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
  subst hpr
  exact .rulePr (evalArgs_nil _ _) (evalExp_tup2 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl))
    (dd_memtypeOk O hc hv)

end Silmaril.Wasm.SpecTec.Institution.Instr30Z
