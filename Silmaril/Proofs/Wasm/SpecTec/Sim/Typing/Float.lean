module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Typing
public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Defs

/-!
# Encoded floats and vectors have their IL types

With the two ported-code fixes of this track (`Sem.argSubOk`: a `SubE` argument pattern tests
its subtype; `Sem.bindQuants`: a case quantifier bound by a defining equation), the encodings of
Core's float constants (`floatV`, every IEEE shape: normal, subnormal including `±0`, infinite,
NaN with any payload) inhabit `num_(Fnn)` and `fN(N)`, and the encodings of `v128` constants
inhabit `vec_(V128)`. Hence every numeric or vector `Val` is a typed `val`
(`typedV_val_num`, `typedV_val_vec`).

The proofs read the fixed script's own type definitions (`Original.d34`–`d40`, `d47`, `d132`,
`d133`, `d146`, `d210`, `d213`, `d269`) and evaluate the case premises of `fNmag` with the
script's `$M`, `$E`, `$signif`, `$expon`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Typing

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV intV)
open Silmaril.Wasm.SpecTecEnc (floatFraction floatExponent floatSign floatFractionWidth
  floatExponentWidth)
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d34 Original.d35 Original.d36 Original.d37
  Original.d38 Original.d39 Original.d40 Original.d47 Original.d90 Original.d99 Original.d100
  Original.d101 Original.d132 Original.d133 Original.d143 Original.d146 Original.d210
  Original.d213 Original.d269)
open IntNumeric (instCases findCase hasTypCase_of_findCase premsOk_if evalExp_and defOf
  hasTyp_closedNullary findTyp_numtype)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## The script's definitions -/

set_option maxRecDepth 100000 in
theorem findDef_size : (simEnv B).findDef? "size" = defOf Original.d132 := rfl
set_option maxRecDepth 100000 in
theorem findDef_sizenn : (simEnv B).findDef? "sizenn" = defOf Original.d143 := rfl
set_option maxRecDepth 100000 in
theorem findDef_vsize : (simEnv B).findDef? "vsize" = defOf Original.d133 := rfl
set_option maxRecDepth 100000 in
theorem findDef_vsizenn : (simEnv B).findDef? "vsizenn" = defOf Original.d146 := rfl
set_option maxRecDepth 100000 in
theorem findDef_signif : (simEnv B).findDef? "signif" = defOf Original.d34 := rfl
set_option maxRecDepth 100000 in
theorem findDef_expon : (simEnv B).findDef? "expon" = defOf Original.d35 := rfl
set_option maxRecDepth 100000 in
theorem findDef_M : (simEnv B).findDef? "M" = defOf Original.d36 := rfl
set_option maxRecDepth 100000 in
theorem findDef_E : (simEnv B).findDef? "E" = defOf Original.d37 := rfl

/-- The `Inn` argument pattern. -/
abbrev innPat : Exp := .subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" [])
/-- The `Fnn` argument pattern. -/
abbrev fnnPat : Exp := .subE (.varE "Fnn") (.varT "Fnn" []) (.varT "numtype" [])

set_option maxRecDepth 100000 in
theorem findTyp_Inn :
    (simEnv B).findTyp? "Inn" = some ([], [.instD [] [] (.variantT (instCases Original.d99 0))]) :=
  rfl

set_option maxRecDepth 100000 in
theorem findTyp_Fnn :
    (simEnv B).findTyp? "Fnn" =
      some ([], [.instD [] [] (.variantT (instCases Original.d100 0))]) :=
  rfl

set_option maxRecDepth 100000 in
theorem findTyp_num_full : ∃ ps qs qs', (simEnv B).findTyp? "num_" = some (ps,
    [.instD qs [.expA innPat] (.aliasT (.varT "iN" [.expA (.callE "sizenn" [.expA innPat])])),
     .instD qs' [.expA fnnPat] (.aliasT (.varT "fN" [.expA (.callE "sizenn" [.expA fnnPat])]))]) :=
  ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_fN : ∃ ps qs, (simEnv B).findTyp? "fN" =
    some (ps, [.instD qs [.expA (.varE "N")] (.variantT (instCases Original.d40 0))]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_fNmag : ∃ ps qs, (simEnv B).findTyp? "fNmag" =
    some (ps, [.instD qs [.expA (.varE "N")] (.variantT (instCases Original.d39 0))]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_exp : (simEnv B).findTyp? "exp" =
    some ([], [.instD [] [] (.aliasT (.numT .intT))]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_m : (simEnv B).findTyp? "m" =
    some ([], [.instD [] [] (.aliasT (.numT .natT))]) := rfl

/-! ## The subtype tests of `num_`'s instances -/

/-- `F32`, `F64`, as `numtype` values. -/
abbrev fntV (t : Silmaril.Wasm.FloatType) : Value := Vec.numTypeV (.float t)

set_option maxRecDepth 100000 in
/-- A float type fails `Inn`'s subtype test. -/
theorem argSubOk_inn_float (t : Silmaril.Wasm.FloatType) {ρ : VarEnv}
    (hρ : ρ.findTyp? "Inn" = none) : argSubOk (simEnv B) ρ innPat (fntV t) = false := by
  cases t <;> simp only [argSubOk, subCaseOk, fntV, Vec.numTypeV, Equiv.Execution.caseNilV, hρ,
    findTyp_Inn] <;> rfl

set_option maxRecDepth 100000 in
/-- A float type passes `Fnn`'s subtype test. -/
theorem argSubOk_fnn_float (t : Silmaril.Wasm.FloatType) {ρ : VarEnv}
    (hρ : ρ.findTyp? "Fnn" = none) : argSubOk (simEnv B) ρ fnnPat (fntV t) = true := by
  cases t <;> simp only [argSubOk, subCaseOk, fntV, Vec.numTypeV, Equiv.Execution.caseNilV, hρ,
    findTyp_Fnn] <;> rfl

/-! ## The size functions -/

/-- A natural-literal clause pattern. -/
theorem matchArgs_numLit {n : Nat} :
    MatchArgs (simEnv B) VarEnv.empty [.expA (.numE (.natN n))] [.val (natV n)] VarEnv.empty :=
  matchArgs_cons (matchArg_expA matchExp_numE) matchArgs_nil

/-- A natural-literal clause pattern definitely fails on another natural. -/
theorem matchArgs_numLit_undef {n k : Nat} (h : n ≠ k) :
    MatchArgsUndef (simEnv B) VarEnv.empty [.expA (.numE (.natN n))] [.val (natV k)] :=
  matchArgs_cons_undef (matchArg_expA_undef (matchExp_numE_undef (by simp [natV, h.symm])))

/-- A literal-case clause pattern definitely fails on another case. -/
theorem matchArgs_caseLit_undef {op op' : MixopS} (h : op' ≠ op) :
    MatchArgsUndef (simEnv B) VarEnv.empty [.expA (.caseE op (.tupE []))]
      [.val (.case op' (.tuple []))] :=
  matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef h))

/-- A literal-case clause pattern matches its case. -/
theorem matchArgs_caseLit {op : MixopS} :
    MatchArgs (simEnv B) VarEnv.empty [.expA (.caseE op (.tupE []))]
      [.val (.case op (.tuple []))] VarEnv.empty :=
  matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil

set_option maxRecDepth 100000 in
/-- `$size(Fnn)` is the width. -/
theorem callDef_size_float (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "size" = none) (ha : EvalArgs (simEnv B) ρ args [.val (fntV t)]) :
    CallDef (simEnv B) ρ "size" args (natV t.width) := by
  refine callDef_of_tryClauses hρ findDef_size ha ?_
  cases t with
  | f32 =>
      exact tryClauses_skip_match (matchArgs_caseLit_undef (op' := "F32") (by decide))
        (tryClauses_skip_match (matchArgs_caseLit_undef (op' := "F32") (by decide))
          (tryClauses_hit matchArgs_caseLit premsHold_nil evalExp_num))
  | f64 =>
      exact tryClauses_skip_match (matchArgs_caseLit_undef (op' := "F64") (by decide))
        (tryClauses_skip_match (matchArgs_caseLit_undef (op' := "F64") (by decide))
          (tryClauses_skip_match (matchArgs_caseLit_undef (op' := "F64") (by decide))
            (tryClauses_hit matchArgs_caseLit premsHold_nil evalExp_num)))

set_option maxRecDepth 100000 in
/-- `$sizenn(Fnn)` is the width, through `$size`. -/
theorem callDef_sizenn_float (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "sizenn" = none) (ha : EvalArgs (simEnv B) ρ args [.val (fntV t)]) :
    CallDef (simEnv B) ρ "sizenn" args (natV t.width) := by
  refine callDef_of_tryClauses hρ findDef_sizenn ha ?_
  exact tryClauses_hit (ρ₀ := VarEnv.empty.bindVal "nt" (fntV t))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
    premsHold_nil
    (evalExp_callE_iff.2 (callDef_size_float t rfl
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil)))

set_option maxRecDepth 100000 in
/-- `$vsizenn(V128) = 128`, through `$vsize`. -/
theorem callDef_vsizenn {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "vsizenn" = none)
    (ha : EvalArgs (simEnv B) ρ args [.val (Equiv.Execution.caseNilV "V128")]) :
    CallDef (simEnv B) ρ "vsizenn" args (natV 128) := by
  refine callDef_of_tryClauses hρ findDef_vsizenn ha ?_
  refine tryClauses_hit (ρ₀ := VarEnv.empty.bindVal "vt" (Equiv.Execution.caseNilV "V128"))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) premsHold_nil
    (evalExp_callE_iff.2 (callDef_of_tryClauses (ws := [.val (Equiv.Execution.caseNilV "V128")])
      rfl findDef_vsize
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil) ?_))
  exact tryClauses_hit (ρ₀ := VarEnv.empty)
    (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil)
    premsHold_nil evalExp_num

set_option maxRecDepth 100000 in
/-- `$signif(N)`, at a float width. -/
theorem callDef_signif (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "signif" = none) (ha : EvalArgs (simEnv B) ρ args [.val (natV t.width)]) :
    CallDef (simEnv B) ρ "signif" args (natV (floatFractionWidth t)) := by
  refine callDef_of_tryClauses hρ findDef_signif ha ?_
  cases t with
  | f32 => exact tryClauses_hit matchArgs_numLit premsHold_nil evalExp_num
  | f64 =>
      exact tryClauses_skip_match (matchArgs_numLit_undef (by decide))
        (tryClauses_hit matchArgs_numLit premsHold_nil evalExp_num)

set_option maxRecDepth 100000 in
/-- `$expon(N)`, at a float width. -/
theorem callDef_expon (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "expon" = none) (ha : EvalArgs (simEnv B) ρ args [.val (natV t.width)]) :
    CallDef (simEnv B) ρ "expon" args (natV (floatExponentWidth t)) := by
  refine callDef_of_tryClauses hρ findDef_expon ha ?_
  cases t with
  | f32 => exact tryClauses_hit matchArgs_numLit premsHold_nil evalExp_num
  | f64 =>
      exact tryClauses_skip_match (matchArgs_numLit_undef (by decide))
        (tryClauses_hit matchArgs_numLit premsHold_nil evalExp_num)

set_option maxRecDepth 100000 in
/-- `$M(N)` in a scope binding `N` to a float width. -/
theorem evalExp_M (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} (hd : ρ.findDef? "M" = none)
    (hN : ρ.findVal? "N" = some (natV t.width)) :
    EvalExp (simEnv B) ρ (.callE "M" [.expA (.varE "N")]) (natV (floatFractionWidth t)) := by
  refine evalExp_callE_iff.2 (callDef_of_tryClauses hd findDef_M
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 hN) Equiv.evalArgs_nil) ?_)
  exact tryClauses_hit (ρ₀ := VarEnv.empty.bindVal "N" (natV t.width))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) premsHold_nil
    (evalExp_callE_iff.2 (callDef_signif t rfl
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil)))

set_option maxRecDepth 100000 in
/-- `$E(N)` in a scope binding `N` to a float width. -/
theorem evalExp_E (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} (hd : ρ.findDef? "E" = none)
    (hN : ρ.findVal? "N" = some (natV t.width)) :
    EvalExp (simEnv B) ρ (.callE "E" [.expA (.varE "N")]) (natV (floatExponentWidth t)) := by
  refine evalExp_callE_iff.2 (callDef_of_tryClauses hd findDef_E
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 hN) Equiv.evalArgs_nil) ?_)
  exact tryClauses_hit (ρ₀ := VarEnv.empty.bindVal "N" (natV t.width))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) premsHold_nil
    (evalExp_callE_iff.2 (callDef_expon t rfl
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil)))

/-! ## Arithmetic of the `fNmag` premises -/

/-- `2 ^ (E - 1)`, written as the script writes it (subtraction in `int`). -/
theorem evalExp_twoPowPredE {env : Env} {ρ : VarEnv} {e : Exp} {k : Nat} (hk : 0 < k)
    (h : EvalExp env ρ e (natV k)) :
    EvalExp env ρ (.binE .powOp (.numT .natT) (.numE (.natN 2))
      (.cvtE (.binE .subOp (.numT .intT) (.cvtE e .natT .intT)
        (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT)) (natV (2 ^ (k - 1))) := by
  have hsub : EvalExp env ρ (.binE .subOp (.numT .intT) (.cvtE e .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) (intV ((k : Int) - 1)) :=
    evalExp_binNum (Equiv.evalExp_toInt h) Equiv.evalExp_oneInt rfl
  have hnat := Equiv.evalExp_toNat (show (0 : Int) ≤ (k : Int) - 1 by omega) hsub
  rw [show ((k : Int) - 1).toNat = k - 1 by omega] at hnat
  exact evalExp_binNum evalExp_num hnat rfl

/-- The minimal normal exponent `2 - 2^(E-1)`, in `int`. -/
theorem evalExp_minExp {env : Env} {ρ : VarEnv} {e : Exp} {k : Nat} (hk : 0 < k)
    (h : EvalExp env ρ e (natV k)) :
    EvalExp env ρ (.binE .subOp (.numT .intT) (.cvtE (.numE (.natN 2)) .natT .intT)
      (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2))
        (.cvtE (.binE .subOp (.numT .intT) (.cvtE e .natT .intT)
          (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT)) .natT .intT))
      (intV (2 - ((2 ^ (k - 1) : Nat) : Int))) :=
  evalExp_binNum (Equiv.evalExp_toInt evalExp_num)
    (Equiv.evalExp_toInt (evalExp_twoPowPredE hk h)) rfl

/-- The maximal exponent `2^(E-1) - 1`, in `int`. -/
theorem evalExp_maxExp {env : Env} {ρ : VarEnv} {e : Exp} {k : Nat} (hk : 0 < k)
    (h : EvalExp env ρ e (natV k)) :
    EvalExp env ρ (.binE .subOp (.numT .intT)
      (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2))
        (.cvtE (.binE .subOp (.numT .intT) (.cvtE e .natT .intT)
          (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT)) .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT))
      (intV (((2 ^ (k - 1) : Nat) : Int) - 1)) :=
  evalExp_binNum (Equiv.evalExp_toInt (evalExp_twoPowPredE hk h)) Equiv.evalExp_oneInt rfl

/-- `m < 2 ^ $M(N)`. -/
theorem evalExp_ltSignif (t : Silmaril.Wasm.FloatType) {ρ : VarEnv} {m : Nat}
    (hd : ρ.findDef? "M" = none) (hN : ρ.findVal? "N" = some (natV t.width))
    (hm : ρ.findVal? "m" = some (.num (.natN m))) (hlt : m < 2 ^ floatFractionWidth t) :
    EvalExp (simEnv B) ρ (.cmpE .ltOp (.numT .natT) (.varE "m")
      (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.callE "M" [.expA (.varE "N")])))
      (.bool true) :=
  evalExp_cmpNum (evalExp_var hm) (evalExp_binNum evalExp_num (evalExp_M t hd hN) rfl)
    (by simp [Num.cmp, hlt])

/-! ## `fNmag(N)` and `fN(N)` -/

/-- The magnitude part of `floatV`. -/
def magV (t : Silmaril.Wasm.FloatType) (b : BitVec t.width) : Value :=
  let ew := floatExponentWidth t
  let m := floatFraction t b
  let e := floatExponent t b
  if e = 0 then .case "SUBNORM" (.tuple [.num (.natN m)])
  else if e = 2 ^ ew - 1 then
    (if m = 0 then Equiv.Execution.caseNilV "INF" else .case "NAN" (.tuple [.num (.natN m)]))
  else .case "NORM" (.tuple [.num (.natN m),
    .num (.intN ((e : Int) - ((2 ^ (ew - 1) - 1 : Nat) : Int)))])

theorem floatV_eq (t : Silmaril.Wasm.FloatType) (b : BitVec t.width) :
    floatV t b = .case (if floatSign t b = 0 then "POS" else "NEG") (magV t b) := rfl

/-- The variant case `op` of `cs` and its quantifiers and premises. -/
def findCaseQ : List TypCase → MixopS → Option (Typ × List Param × List Prem)
  | [], _ => none
  | .mk o t qs prems :: cs, op => if o = op then some (t, qs, prems) else findCaseQ cs op

/-- A case found with its quantifiers is inhabited by a payload of its type whose defined
quantifiers bind and whose premises hold. -/
theorem hasTypCase_of_findCaseQ {env : Env} {σ : VarEnv} :
    ∀ {cs : List TypCase} {op : MixopS} {t : Typ} {qs : List Param} {prems : List Prem}
      {w : Value} {ρq : VarEnv},
      findCaseQ cs op = some (t, qs, prems) → HasTyp env σ t w →
      BindQuants env (caseScope σ t w) (quantDefs qs prems) ρq → PremsOk env ρq prems →
      HasTypCase env σ cs op w
  | [], _, _, _, _, _, _, hf, _, _, _ => by simp [findCaseQ] at hf
  | .mk o t' qs' prems' :: cs, op, t, qs, prems, w, ρq, hf, ht, hb, hp => by
      by_cases ho : o = op
      · simp only [findCaseQ, ho, ite_true, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl, rfl⟩ := hf
        exact (hasTypCase_cons_hit_iffQ ho).2 ⟨ht, ρq, hb, hp⟩
      · simp only [findCaseQ, ho, ite_false] at hf
        exact (hasTypCase_cons_miss_iff ho).2 (hasTypCase_of_findCaseQ hf ht hb hp)

/-- `m` holds naturals. -/
theorem hasTyp_m {ρ : VarEnv} (hρ : ρ.findTyp? "m" = none) (n : Nat) :
    HasTyp (simEnv B) ρ (.varT "m" []) (.num (.natN n)) :=
  hasTyp_varT_of_insts (by simp [localTyp?, hρ]) findTyp_m Equiv.evalArgs_nil
    (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2
      (hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩)))

/-- `exp` holds integers. -/
theorem hasTyp_exp {ρ : VarEnv} (hρ : ρ.findTyp? "exp" = none) (j : Int) :
    HasTyp (simEnv B) ρ (.varT "exp" []) (.num (.intN j)) :=
  hasTyp_varT_of_insts (by simp [localTyp?, hρ]) findTyp_exp Equiv.evalArgs_nil
    (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2
      (hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩)))

/-- The scope `fNmag`'s instance binds. -/
abbrev magScope (t : Silmaril.Wasm.FloatType) : VarEnv := VarEnv.empty.bindVal "N" (natV t.width)

theorem floatFraction_lt (t : Silmaril.Wasm.FloatType) (b : BitVec t.width) :
    floatFraction t b < 2 ^ floatFractionWidth t :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem floatExponent_lt (t : Silmaril.Wasm.FloatType) (b : BitVec t.width) :
    floatExponent t b < 2 ^ floatExponentWidth t :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem floatExponentWidth_pos (t : Silmaril.Wasm.FloatType) : 0 < floatExponentWidth t := by
  cases t <;> decide

set_option maxRecDepth 100000 in
/-- `INF` and `NAN m` (`1 ≤ m < 2^M`). -/
theorem hasTypCase_mag_inf_nan (t : Silmaril.Wasm.FloatType) (m : Nat)
    (hm : m < 2 ^ floatFractionWidth t) :
    HasTypCase (simEnv B) (magScope t) (instCases Original.d39 0) "INF" (.tuple []) ∧
      (0 < m → HasTypCase (simEnv B) (magScope t) (instCases Original.d39 0) "NAN"
        (.tuple [.num (.natN m)])) := by
  refine ⟨IntNumeric.hasTypCase_nullary rfl, fun hpos => ?_⟩
  have htup : HasTyp (simEnv B) (magScope t) (.tupT [.mk "m" (.varT "m" [])])
      (.tuple [.num (.natN m)]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_m rfl m,
      hasTypTup_nil_iff.2 rfl⟩⟩
  refine hasTypCase_of_findCase rfl htup (premsOk_if (evalExp_and ?_ ?_))
  · exact evalExp_cmpNum (m₂ := .natN m) evalExp_num (evalExp_var (by simp [caseScope, typBinds]))
      (by simp [Num.cmp]; omega)
  · exact evalExp_ltSignif t rfl (by simp [caseScope, typBinds])
      (by simp [caseScope, typBinds]) hm

set_option maxRecDepth 100000 in
/-- `SUBNORM m` (`m < 2^M`; the quantifier `exp` is defined as `2 - 2^(E-1)`). -/
theorem hasTypCase_mag_subnorm (t : Silmaril.Wasm.FloatType) (m : Nat)
    (hm : m < 2 ^ floatFractionWidth t) :
    HasTypCase (simEnv B) (magScope t) (instCases Original.d39 0) "SUBNORM"
      (.tuple [.num (.natN m)]) := by
  have htup : HasTyp (simEnv B) (magScope t) (.tupT [.mk "m" (.varT "m" [])])
      (.tuple [.num (.natN m)]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_m rfl m,
      hasTypTup_nil_iff.2 rfl⟩⟩
  have hk := floatExponentWidth_pos t
  have hE : EvalExp (simEnv B) (caseScope (magScope t) (.tupT [.mk "m" (.varT "m" [])])
      (.tuple [.num (.natN m)])) (.callE "E" [.expA (.varE "N")])
      (natV (floatExponentWidth t)) :=
    evalExp_E t rfl (by simp [caseScope, typBinds])
  refine hasTypCase_of_findCaseQ rfl htup
    (bindQuants_cons (evalExp_minExp hk hE) (hasTyp_exp rfl _)
      (bindQuants_nil_iff.2 rfl))
    (premsOk_if (evalExp_and ?_ ?_))
  · exact evalExp_ltSignif t rfl (by simp [caseScope, typBinds])
      (by simp [caseScope, typBinds]) hm
  · refine evalExp_cmpE_iff.2 ⟨intV (2 - ((2 ^ (floatExponentWidth t - 1) : Nat) : Int)),
      intV (2 - ((2 ^ (floatExponentWidth t - 1) : Nat) : Int)),
      evalExp_minExp hk (evalExp_E t rfl (by simp [caseScope, typBinds])),
      evalExp_var (by simp [caseScope, typBinds]), ?_⟩
    simp [cmpValues]

set_option maxRecDepth 100000 in
/-- `NORM m exp` (`m < 2^M`, `2 - 2^(E-1) ≤ exp ≤ 2^(E-1) - 1`). -/
theorem hasTypCase_mag_norm (t : Silmaril.Wasm.FloatType) (m : Nat) (j : Int)
    (hm : m < 2 ^ floatFractionWidth t)
    (hlo : 2 - ((2 ^ (floatExponentWidth t - 1) : Nat) : Int) ≤ j)
    (hhi : j ≤ ((2 ^ (floatExponentWidth t - 1) : Nat) : Int) - 1) :
    HasTypCase (simEnv B) (magScope t) (instCases Original.d39 0) "NORM"
      (.tuple [.num (.natN m), .num (.intN j)]) := by
  have htup : HasTyp (simEnv B) (magScope t)
      (.tupT [.mk "m" (.varT "m" []), .mk "exp" (.varT "exp" [])])
      (.tuple [.num (.natN m), .num (.intN j)]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_m rfl m,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_exp rfl j, hasTypTup_nil_iff.2 rfl⟩⟩⟩
  have hk := floatExponentWidth_pos t
  have hE : EvalExp (simEnv B) (caseScope (magScope t)
      (.tupT [.mk "m" (.varT "m" []), .mk "exp" (.varT "exp" [])])
      (.tuple [.num (.natN m), .num (.intN j)])) (.callE "E" [.expA (.varE "N")])
      (natV (floatExponentWidth t)) :=
    evalExp_E t rfl (by simp [caseScope, typBinds])
  refine hasTypCase_of_findCase rfl htup (premsOk_if (evalExp_and ?_ (evalExp_and ?_ ?_)))
  · exact evalExp_ltSignif t rfl (by simp [caseScope, typBinds])
      (by simp [caseScope, typBinds]) hm
  · exact evalExp_cmpNum (m₂ := .intN j) (evalExp_minExp hk hE)
      (evalExp_var (by simp [caseScope, typBinds]))
      (by simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]; omega)
  · exact evalExp_cmpNum (m₁ := .intN j) (evalExp_var (by simp [caseScope, typBinds]))
      (evalExp_maxExp hk hE)
      (by simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]; omega)

/-- Every magnitude `floatV` produces is a `fNmag` case of the width. -/
theorem hasTypCase_magV (t : Silmaril.Wasm.FloatType) (b : BitVec t.width) :
    ∃ op w, magV t b = .case op w ∧
      HasTypCase (simEnv B) (magScope t) (instCases Original.d39 0) op w := by
  have hm := floatFraction_lt t b
  have he := floatExponent_lt t b
  unfold magV
  simp only
  split_ifs with h0 hmax hm0
  · exact ⟨_, _, rfl, hasTypCase_mag_subnorm t _ hm⟩
  · exact ⟨_, _, rfl, (hasTypCase_mag_inf_nan t _ hm).1⟩
  · exact ⟨_, _, rfl, (hasTypCase_mag_inf_nan t _ hm).2 (Nat.pos_of_ne_zero hm0)⟩
  · refine ⟨_, _, rfl, hasTypCase_mag_norm t _ _ hm ?_ ?_⟩
    · cases t <;> simp only [floatExponentWidth] at * <;> omega
    · cases t <;> simp only [floatExponentWidth] at * <;> omega

/-- `fNmag(N)` holds every magnitude of the width. -/
theorem hasTyp_fNmag {ρ : VarEnv} {e : Exp} (t : Silmaril.Wasm.FloatType) (b : BitVec t.width)
    (he : EvalExp (simEnv B) ρ e (natV t.width)) :
    HasTyp (simEnv B) ρ (.varT "fNmag" [.expA e]) (magV t b) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_fNmag (B := B)
  obtain ⟨op, w, hv, hc⟩ := hasTypCase_magV (B := B) t b
  rw [hv]
  exact hasTyp_varT_case (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) hc

set_option maxRecDepth 100000 in
/-- **`fN(N)` holds every float of the width**: both signs, every magnitude. -/
theorem hasTyp_fN {ρ : VarEnv} {e : Exp} (t : Silmaril.Wasm.FloatType) (b : BitVec t.width)
    (he : EvalExp (simEnv B) ρ e (natV t.width)) :
    HasTyp (simEnv B) ρ (.varT "fN" [.expA e]) (floatV t b) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_fN (B := B)
  have hmag : HasTyp (simEnv B) (magScope t) (.varT "fNmag" [.expA (.varE "N")]) (magV t b) :=
    hasTyp_fNmag t b (evalExp_var (by simp))
  rw [floatV_eq]
  refine hasTyp_varT_case (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) ?_
  split_ifs
  · exact hasTypCase_of_findCase rfl hmag premsOk_nil
  · exact hasTypCase_of_findCase rfl hmag premsOk_nil

/-- `$sizenn(Fnn)` written as `num_`'s instance writes it, `Fnn` bound to `fntV t`. -/
theorem evalExp_sizennFnn (t : Silmaril.Wasm.FloatType) {ρ : VarEnv}
    (hρ : ρ.findDef? "sizenn" = none) (hFnn : ρ.findVal? "Fnn" = some (fntV t)) :
    EvalExp (simEnv B) ρ (.callE "sizenn" [.expA fnnPat]) (natV t.width) :=
  evalExp_callE_iff.2 (callDef_sizenn_float t hρ
    (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_varE_iff.2 hFnn)) Equiv.evalArgs_nil))

/-- **`num_(Fnn)` holds every float of the width** (the finding `not_hasTyp_num_float` no
longer applies: `num_`'s `Inn` instance now fails its subtype test on `F32`/`F64`). -/
theorem hasTyp_num_float {ρ : VarEnv} {e : Exp} (t : Silmaril.Wasm.FloatType)
    (b : BitVec t.width) (he : EvalExp (simEnv B) ρ e (fntV t)) :
    HasTyp (simEnv B) ρ (.varT "num_" [.expA e]) (floatV t b) := by
  obtain ⟨ps, qs, qs', htd⟩ := findTyp_num_full (B := B)
  have hfN : HasTyp (simEnv B) (VarEnv.empty.bindVal "Fnn" (fntV t))
      (.varT "fN" [.expA (.callE "sizenn" [.expA fnnPat])]) (floatV t b) :=
    hasTyp_fN t b (evalExp_sizennFnn t rfl (by simp))
  obtain ⟨n, hn⟩ : MatchArgsUndef (simEnv B) VarEnv.empty [.expA innPat] [.val (fntV t)] :=
    matchArgs_cons_undef (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub
      (argSubOk_inn_float t rfl))
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_tail hn (hasTypInsts_head (matchArgs_cons (matchArg_expA
      (Equiv.Validation.matchExp_sub_iff.2 (matchExp_varE (by simp)))
      (argSubOk_fnn_float t rfl)) matchArgs_nil) (hasTypDef_aliasT_iff.2 hfN)))

/-- The old reading's finding, refuted: `num_(F32)` *does* hold a float. -/
theorem not_forall_not_hasTyp_num_float :
    ¬ ∀ (e : Exp) (t : Silmaril.Wasm.FloatType) (b : BitVec t.width),
      ¬ HasTyp (simEnv B) VarEnv.empty (.varT "num_" [.expA e]) (floatV t b) :=
  fun h => h (.caseE "F32" (.tupE [])) .f32 0 (hasTyp_num_float .f32 0
    (evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[], Equiv.Validation.evalExps_nil_iff.2 rfl,
      rfl⟩, rfl⟩))

/-! ## `vec_(V128)` -/

set_option maxRecDepth 100000 in
theorem findTyp_vec : ∃ ps qs, (simEnv B).findTyp? "vec_" = some (ps, [.instD qs
    [.expA (.varE "Vnn")] (.aliasT (.varT "vN" [.expA (.callE "vsizenn" [.expA (.varE "Vnn")])]))]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findTyp_vN : ∃ ps qs, (simEnv B).findTyp? "vN" = some (ps, [.instD qs
    [.expA (.varE "N")] (.aliasT (.varT "uN" [.expA (.varE "N")]))]) :=
  ⟨_, _, rfl⟩

/-- **`vec_(V128)` holds every 128-bit pattern.** -/
theorem hasTyp_vec {ρ : VarEnv} {e : Exp} (a : BitVec 128)
    (he : EvalExp (simEnv B) ρ e (Equiv.Execution.caseNilV "V128")) :
    HasTyp (simEnv B) ρ (.varT "vec_" [.expA e]) (Equiv.Execution.pctV a.toNat) := by
  obtain ⟨ps, qs, htd⟩ := findTyp_vec (B := B)
  obtain ⟨ps', qs', htd'⟩ := findTyp_vN (B := B)
  have hvN : HasTyp (simEnv B) (VarEnv.empty.bindVal "Vnn" (Equiv.Execution.caseNilV "V128"))
      (.varT "vN" [.expA (.callE "vsizenn" [.expA (.varE "Vnn")])])
      (Equiv.Execution.pctV a.toNat) :=
    hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd'
      (Equiv.evalArgs_cons (evalExp_callE_iff.2 (callDef_vsizenn rfl
        (Equiv.evalArgs_cons (evalExp_varE_iff.2 (by simp)) Equiv.evalArgs_nil)))
        Equiv.evalArgs_nil)
      (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
        (hasTypDef_aliasT_iff.2 (IntNumeric.hasTyp_uN (evalExp_var (by simp)) a.isLt)))
  exact hasTyp_varT_of_insts (localTyp?_cons _ _ _) htd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (hasTypInsts_head (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
      (hasTypDef_aliasT_iff.2 hvN))

/-! ## Numerals and `val` -/

open Silmaril.Wasm.Execution.Core (NumVal)

/-- **Every numeral has type `num_(t)`**, integers and floats alike, whichever quantifier names
its number type (family V's `FloatTyping.num`). -/
theorem typedDep_num (x : IL.Id) (n : NumVal) :
    Vec.TypedDep (simEnv B) x (Vec.numTypeV n.type) (Vec.numT x) (numV n) := by
  intro ρ _ hx
  obtain ⟨t, b⟩ := n
  cases t with
  | int t =>
      have h := IntNumeric.hasTyp_num (B := B) (ρ := ρ) (e := .varE x) b
        (evalExp_var (by cases t <;> exact hx))
      exact h
  | float t => exact hasTyp_num_float t b (evalExp_var hx)

/-- The `numtype` encoding of the runtime is `Vec.numTypeV`. -/
theorem toValue_numType (t : Silmaril.Wasm.NumType) :
    Encode.toValue t = Vec.numTypeV t := by
  cases t with
  | int t => cases t <;> rfl
  | float t => cases t <;> rfl

set_option maxRecDepth 100000 in
theorem findTyp_val : (simEnv B).findTyp? "val" =
    some ([], [.instD [] [] (.variantT (instCases Original.d269 0))]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_vectype : (simEnv B).findTyp? "vectype" =
    some ([], [.instD [] [] (.variantT (instCases Original.d90 0))]) := rfl

/-- A term-only scope stays term-only. -/
theorem valsOnly_bindVal {ρ : VarEnv} (hρ : ValsOnly ρ) (x : IL.Id) (v : Value) :
    ValsOnly (ρ.bindVal x v) := hρ

/-- `numtype` holds every number type. -/
theorem hasTyp_numtype {ρ : VarEnv} (hρ : ValsOnly ρ) (t : Silmaril.Wasm.NumType) :
    HasTyp (simEnv B) ρ (.varT "numtype" []) (Vec.numTypeV t) := by
  rcases t with t | t <;> cases t <;> exact hasTyp_closedNullary hρ findTyp_numtype rfl

/-- **Every numeric constant is a typed `val`** (floats included: every IEEE shape). -/
theorem typedV_val_num (n : NumVal) : TypedV (simEnv B) (.varT "val" []) (valV (.num n)) := by
  intro ρ hρ
  have hl : localTyp? ρ "val" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  have hnt : HasTyp (simEnv B) VarEnv.empty (.varT "numtype" []) (Encode.toValue n.type) := by
    rw [toValue_numType]; exact hasTyp_numtype ⟨rfl, rfl, rfl⟩ _
  have hn : HasTyp (simEnv B) (VarEnv.empty.bindVal "numtype" (Encode.toValue n.type))
      (.varT "num_" [.expA (.varE "numtype")]) (numV n) := by
    rw [toValue_numType]
    exact typedDep_num "numtype" n _ ⟨rfl, rfl, rfl⟩ (by simp)
  exact hasTyp_varT_case hl findTyp_val Equiv.evalArgs_nil matchArgs_nil
    (hasTypCase_of_findCase rfl (hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hnt,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, hn, hasTypTup_nil_iff.2 rfl⟩⟩⟩) premsOk_nil)

/-- **Every vector constant is a typed `val`.** -/
theorem typedV_val_vec (b : BitVec 128) :
    TypedV (simEnv B) (.varT "val" []) (valV (.vec b)) := by
  intro ρ hρ
  have hl : localTyp? ρ "val" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  have hvt : HasTyp (simEnv B) VarEnv.empty (.varT "vectype" [])
      (Equiv.Execution.caseNilV "V128") :=
    hasTyp_closedNullary ⟨rfl, rfl, rfl⟩ findTyp_vectype rfl
  have hv : HasTyp (simEnv B) (VarEnv.empty.bindVal "vectype" (Equiv.Execution.caseNilV "V128"))
      (.varT "vec_" [.expA (.varE "vectype")]) (Equiv.Execution.pctV b.toNat) :=
    hasTyp_vec b (evalExp_var (by simp))
  exact hasTyp_varT_case hl findTyp_val Equiv.evalArgs_nil matchArgs_nil
    (hasTypCase_of_findCase rfl (hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hvt,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, hv, hasTypTup_nil_iff.2 rfl⟩⟩⟩) premsOk_nil)

/-- `VecTyping.vec`: every 128-bit pattern is a `vec_(V128)`. -/
theorem typedV_vecT (a : BitVec 128) : TypedV (simEnv B) Vec.vecT (Vec.vecV a) := fun _ _ =>
  hasTyp_vec a (evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[],
    Equiv.Validation.evalExps_nil_iff.2 rfl, rfl⟩, rfl⟩)

end Silmaril.Wasm.SpecTec.Sim.Typing
