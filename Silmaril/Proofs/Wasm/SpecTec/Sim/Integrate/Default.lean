module

public import Silmaril.Wasm.SpecTec.Sim.Integrate.Defs

/-!
# Round 2 integration: `CtrlCall.default`, by evaluating `$default_`

Round 2's builtins track refuted `CtrlCall.default` for every `B` (`Prims/Default.lean`): the
evaluator did not test `SubE` argument patterns, so `$default_`'s `Inn` clause caught every value
type. After the typing track's fix (`Sem.argSubOk`) each clause of

```
def $default_(Inn) = (CONST Inn 0)
def $default_(Fnn) = (CONST Fnn $fzero($size(Fnn)))
def $default_(Vnn) = (VCONST Vnn 0)
def $default_(REF NULL ht) = REF.NULL_ADDR
def $default_(REF ht) = eps
```

matches exactly its value types, and `$default_(t)` is Core's `defaultVal?` on every value type
(`ctrlCallDefault_simEnv`, for every `B`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Integrate

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

/-- The five clauses of `$default_`. -/
abbrev defaultClauses : List Clause :=
  [(Clause.defD [(Param.expP "Inn" (Typ.varT "Inn" []))] [(Arg.expA (Exp.subE (Exp.varE "Inn")
    (Typ.varT "Inn" []) (Typ.varT "valtype" [])))] (Exp.optE (some (Exp.caseE "CONST" (Exp.tupE [(Exp.subE
    (Exp.varE "Inn") (Typ.varT "Inn" []) (Typ.varT "numtype" [])), (Exp.caseE "%" (Exp.tupE [(Exp.numE
    (Num.natN 0))]))])))) []), (Clause.defD [(Param.expP "Fnn" (Typ.varT "Fnn" []))] [(Arg.expA (Exp.subE
    (Exp.varE "Fnn") (Typ.varT "Fnn" []) (Typ.varT "valtype" [])))] (Exp.optE (some (Exp.caseE "CONST"
    (Exp.tupE [(Exp.subE (Exp.varE "Fnn") (Typ.varT "Fnn" []) (Typ.varT "numtype" [])), (Exp.callE "fzero"
    [(Arg.expA (Exp.callE "size" [(Arg.expA (Exp.subE (Exp.varE "Fnn") (Typ.varT "Fnn" []) (Typ.varT "numtype"
    [])))]))])])))) []), (Clause.defD [(Param.expP "Vnn" (Typ.varT "Vnn" []))] [(Arg.expA (Exp.subE
    (Exp.varE "Vnn") (Typ.varT "Vnn" []) (Typ.varT "valtype" [])))] (Exp.optE (some (Exp.caseE "VCONST"
    (Exp.tupE [(Exp.varE "Vnn"), (Exp.caseE "%" (Exp.tupE [(Exp.numE (Num.natN 0))]))])))) []), (Clause.defD
    [(Param.expP "ht" (Typ.varT "heaptype" []))] [(Arg.expA (Exp.caseE "REF" (Exp.tupE [(Exp.optE (some
    (Exp.caseE "NULL" (Exp.tupE [])))), (Exp.varE "ht")])))] (Exp.optE (some (Exp.caseE "REF.NULL_ADDR"
    (Exp.tupE [])))) []), (Clause.defD [(Param.expP "ht" (Typ.varT "heaptype" []))] [(Arg.expA (Exp.caseE "REF"
    (Exp.tupE [(Exp.optE none), (Exp.varE "ht")])))] (Exp.optE none) [])]

set_option maxRecDepth 100000 in
theorem findDef_default (B : Builtins) :
    ∃ ps t, (simEnv B).findDef? "default_" = some (ps, t, defaultClauses) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_fzero (B : Builtins) :
    ∃ ps t, (simEnv B).findDef? "fzero" = some (ps, t, [.defD [.expP "N" (.varT "N" [])]
      [.expA (.varE "N")] (.caseE "POS" (.caseE "SUBNORM" (.tupE [.numE (.natN 0)]))) []]) :=
  ⟨_, _, rfl⟩

variable {B : Builtins}

/-- `$default_` applies where its clauses do. -/
theorem applies_default_of {v w : Value} (h : TryClauses (simEnv B) defaultClauses [.val v] w) :
    Applies (simEnv B) "default_" [.val v] w :=
  let ⟨ps, t, hd⟩ := findDef_default B
  ⟨ps, t, _, hd, Or.inl h⟩

/-- The kind pattern `X <: valtype` of the first three clauses. -/
abbrev vkPat (X : IL.Id) : Exp := .subE (.varE X) (.varT X []) (.varT "valtype" [])

/-- The image of a reference type. -/
theorem encode_ref (b : Bool) (h : HeapType) :
    Encode.toValue (ValType.ref ⟨b, h⟩) = .case "REF" (.tuple [.opt
      (if b then some (.case "NULL" (.tuple [])) else none), Encode.toValue h]) := by
  cases b <;> rfl

set_option maxRecDepth 100000 in
/-- No kind pattern admits a reference type. -/
theorem argSubOk_vk_ref (X : IL.Id) (hX : X = "Inn" ∨ X = "Fnn" ∨ X = "Vnn") (r : RefType) :
    argSubOk (simEnv B) VarEnv.empty (vkPat X) (Encode.toValue (ValType.ref r)) = false := by
  obtain ⟨b, h⟩ := r
  rw [encode_ref, argSubOk, Aggregates.subCaseOk_case]
  rcases hX with rfl | rfl | rfl <;> rfl

/-- A kind pattern failing its subtype test fails definitely. -/
theorem skip_vk {X : IL.Id} {q : List Param} {e : Exp} {cs : List Clause} {v w : Value}
    (hs : argSubOk (simEnv B) VarEnv.empty (vkPat X) v = false)
    (h : TryClauses (simEnv B) cs [.val v] w) :
    TryClauses (simEnv B) (.defD q [.expA (vkPat X)] e [] :: cs) [.val v] w :=
  tryClauses_skip_match (matchArgs_cons_undef
    (Silmaril.SpecTec.Equiv.ExecBuiltins.matchArg_expA_undef_of_sub hs)) h

/-- A kind pattern passing its subtype test binds the variable. -/
theorem match_vk {X : IL.Id} {v : Value}
    (hs : argSubOk (simEnv B) VarEnv.empty (vkPat X) v = true) :
    MatchArgs (simEnv B) VarEnv.empty [.expA (vkPat X)] [.val v] (VarEnv.empty.bindVal X v) :=
  matchArgs_cons (matchArg_expA (Prims.matchExp_subE (matchExp_varE (by simp))) hs) matchArgs_nil

set_option maxRecDepth 100000 in
/-- `$default_` on an integer type. -/
theorem applies_default_int (t : IntType) :
    Applies (simEnv B) "default_" [.val (Encode.toValue (ValType.num (.int t)))]
      (.opt (some (.case "CONST" (.tuple [Encode.toValue (ValType.num (.int t)),
        .case "%" (.tuple [.num (.natN 0)])])))) := by
  have hs : argSubOk (simEnv B) VarEnv.empty (vkPat "Inn") (Encode.toValue (ValType.num (.int t)))
      = true := by
    cases t <;> rfl
  exact applies_default_of (tryClauses_hit (match_vk hs) premsHold_nil
    (evalExp_optE_some_iff.2 ⟨_, evalExp_case (evalExp_tup2 (evalExp_subE_iff.2
      (evalExp_var (by simp))) (evalExp_case (evalExp_tupE_iff.2
        ⟨_, evalExps_cons evalExp_num evalExps_nil, rfl⟩))), rfl⟩))

/-- The image of a float number type is its `numtype` image. -/
theorem encode_float (t : FloatType) :
    Encode.toValue (ValType.num (.float t)) = Vec.numTypeV (.float t) := by
  cases t <;> rfl

/-- `+0`, Core's default float, is `POS (SUBNORM 0)`. -/
theorem floatV_zero (t : FloatType) :
    floatV t 0 = .case "POS" (.case "SUBNORM" (.tuple [.num (.natN 0)])) := by
  cases t <;> rfl

/-- `$fzero(N) = POS (SUBNORM 0)`. -/
theorem evalExp_fzero {ρ : VarEnv} (hρ : ρ.findDef? "fzero" = none) {e : Exp} {N : Value}
    (he : EvalExp (simEnv B) ρ e N) :
    EvalExp (simEnv B) ρ (.callE "fzero" [.expA e])
      (.case "POS" (.case "SUBNORM" (.tuple [.num (.natN 0)]))) :=
  let ⟨_, _, hd⟩ := findDef_fzero B
  evalExp_callE_iff.2 (callDef_of_tryClauses hρ hd (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_varE (by simp))) matchArgs_nil)
      premsHold_nil (evalExp_case (evalExp_case (evalExp_tupE_iff.2
        ⟨_, evalExps_cons evalExp_num evalExps_nil, rfl⟩)))))

set_option maxRecDepth 100000 in
/-- `$default_` on a float type. -/
theorem applies_default_float (t : FloatType) :
    Applies (simEnv B) "default_" [.val (Encode.toValue (ValType.num (.float t)))]
      (.opt (some (.case "CONST" (.tuple [Encode.toValue (ValType.num (.float t)),
        floatV t 0])))) := by
  rw [floatV_zero]
  have h₁ : argSubOk (simEnv B) VarEnv.empty (vkPat "Inn")
      (Encode.toValue (ValType.num (.float t))) = false := by
    cases t <;> rfl
  have h₂ : argSubOk (simEnv B) VarEnv.empty (vkPat "Fnn")
      (Encode.toValue (ValType.num (.float t))) = true := by
    cases t <;> rfl
  have hv : (VarEnv.empty.bindVal "Fnn" (Encode.toValue (ValType.num (.float t)))).findVal? "Fnn" =
      some (Vec.numTypeV (.float t)) := by
    rw [encode_float]
    simp
  have hsz : EvalExp (simEnv B) (VarEnv.empty.bindVal "Fnn" (Encode.toValue (ValType.num (.float t))))
      (.callE "size" [.expA (.subE (.varE "Fnn") (.varT "Fnn" []) (.varT "numtype" []))])
      (Silmaril.SpecTec.Equiv.natV (NumType.float t).width) :=
    evalExp_callE_iff.2 (Floats.callDef_size_num (.float t) rfl
      (Equiv.evalArgs_cons (evalExp_subE_iff.2 (evalExp_var hv)) Equiv.evalArgs_nil))
  exact applies_default_of (skip_vk h₁ (tryClauses_hit (match_vk h₂) premsHold_nil
    (evalExp_optE_some_iff.2 ⟨_, evalExp_case (evalExp_tup2 (evalExp_subE_iff.2
      (evalExp_var (by simp))) (evalExp_fzero rfl hsz)), rfl⟩)))

set_option maxRecDepth 100000 in
/-- `$default_(V128) = VCONST V128 0`. -/
theorem applies_default_vec (t : VecType) :
    Applies (simEnv B) "default_" [.val (Encode.toValue (ValType.vec t))]
      (.opt (some (.case "VCONST" (.tuple [Encode.toValue (ValType.vec t),
        .case "%" (.tuple [.num (.natN 0)])])))) := by
  cases t
  have h₁ : argSubOk (simEnv B) VarEnv.empty (vkPat "Inn") (Encode.toValue (ValType.vec .v128)) =
      false := rfl
  have h₂ : argSubOk (simEnv B) VarEnv.empty (vkPat "Fnn") (Encode.toValue (ValType.vec .v128)) =
      false := rfl
  have h₃ : argSubOk (simEnv B) VarEnv.empty (vkPat "Vnn") (Encode.toValue (ValType.vec .v128)) =
      true := rfl
  exact applies_default_of (skip_vk h₁ (skip_vk h₂ (tryClauses_hit (match_vk h₃) premsHold_nil
    (evalExp_optE_some_iff.2 ⟨_, evalExp_case (evalExp_tup2 (evalExp_var (by simp))
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons evalExp_num evalExps_nil, rfl⟩))),
      rfl⟩))))

/-- The pattern `REF n? ht`. -/
abbrev refPat (n : Option Exp) : Exp := .caseE "REF" (.tupE [.optE n, .varE "ht"])

/-- `REF NULL ht` matches a nullable reference type. -/
theorem match_refNull (hv : Value) :
    MatchExp (simEnv B) VarEnv.empty (refPat (some (.caseE "NULL" (.tupE []))))
      (.case "REF" (.tuple [.opt (some (.case "NULL" (.tuple []))), hv]))
      (VarEnv.empty.bindVal "ht" hv) :=
  ⟨12, by simp [matchExp, matchExps, Res.assert, Bind.bind, Except.bind, Value.asCase?,
    Value.asTuple?]⟩

/-- `REF NULL ht` fails definitely on a non-nullable reference type. -/
theorem matchUndef_refNull (hv : Value) :
    MatchExpUndef (simEnv B) VarEnv.empty (refPat (some (.caseE "NULL" (.tupE []))))
      (.case "REF" (.tuple [.opt none, hv])) :=
  ⟨5, by simp [matchExp, matchExps, Res.assert, Bind.bind, Except.bind, Value.asCase?,
    Value.asTuple?]⟩

/-- `REF ht` matches a non-nullable reference type. -/
theorem match_ref (hv : Value) :
    MatchExp (simEnv B) VarEnv.empty (refPat none) (.case "REF" (.tuple [.opt none, hv]))
      (VarEnv.empty.bindVal "ht" hv) :=
  ⟨12, by simp [matchExp, matchExps, Res.assert, Bind.bind, Except.bind, Value.asCase?,
    Value.asTuple?]⟩

/-- `$default_(REF NULL ht) = REF.NULL_ADDR`, `$default_(REF ht) = ε`. -/
theorem applies_default_ref (b : Bool) (h : HeapType) :
    Applies (simEnv B) "default_" [.val (Encode.toValue (ValType.ref ⟨b, h⟩))]
      (.opt (if b then some (.case "REF.NULL_ADDR" (.tuple [])) else none)) := by
  have hI := argSubOk_vk_ref (B := B) "Inn" (.inl rfl) ⟨b, h⟩
  have hF := argSubOk_vk_ref (B := B) "Fnn" (.inr (.inl rfl)) ⟨b, h⟩
  have hV := argSubOk_vk_ref (B := B) "Vnn" (.inr (.inr rfl)) ⟨b, h⟩
  refine applies_default_of (skip_vk hI (skip_vk hF (skip_vk hV ?_)))
  rw [encode_ref]
  cases b with
  | true =>
    exact tryClauses_hit (matchArgs_cons (matchArg_expA (match_refNull _)) matchArgs_nil)
      premsHold_nil (evalExp_optE_some_iff.2 ⟨_, evalExp_case (evalExp_tupE_iff.2
        ⟨[], evalExps_nil, rfl⟩), rfl⟩)
  | false =>
    exact tryClauses_skip_match (matchArgs_cons_undef
      (Silmaril.SpecTec.Equiv.ExecBuiltins.matchArg_expA_undef (matchUndef_refNull _)))
      (tryClauses_hit (matchArgs_cons (matchArg_expA (match_ref _)) matchArgs_nil)
        premsHold_nil (by simpa using (evalExp_optE_none_iff (env := simEnv B)
          (ρ := VarEnv.empty.bindVal "ht" (Encode.toValue h))).2 rfl))

/-- **`CtrlCall.default` holds in every `simEnv B`**: `$default_(t)` is Core's `defaultVal?`
of the closed type, at every value type. -/
theorem ctrlCallDefault_simEnv (B : Builtins) :
    ∀ (m : ModuleInst) (t : ValType), Applies (simEnv B) "default_" [.val (Encode.toValue t)]
      (.opt ((defaultVal? ((liftVal t).substAll (m.types.map .dt))).map valV)) := by
  intro m t
  rcases t with (t | t) | t | ⟨b, h⟩
  · cases t <;> exact applies_default_int _
  · cases t <;> exact applies_default_float _
  · cases t; exact applies_default_vec _
  · obtain ⟨h', e⟩ : ∃ h', (liftVal (.ref ⟨b, h⟩)).substAll (m.types.map .dt) =
        .refv (.ref b h') := ⟨_, rfl⟩
    rw [e]
    cases b <;> exact applies_default_ref _ h

end Silmaril.Wasm.SpecTec.Sim.Integrate
