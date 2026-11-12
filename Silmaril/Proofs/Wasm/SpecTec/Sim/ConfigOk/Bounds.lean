module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.ConfigOk.Exports

/-!
# Finding: the unconditional type-typing fields of `Residue` are false

`Integrate.Residue.types : Prims.TypeTyping env` claims that the image of **every** semantic
type is typed: `TypeTyping.typeuses : ∀ us : Ty (.list .use), TypedV env typeuse* (tyV us)`.
Core's `Ty` carries free type indices `Ty.idx x` for every natural `x`, while SpecTec's
`typeuse ::= _IDX typeidx | …` takes `typeidx = idx = u32 = uN(32)`, whose one case has the
premise `i <= 2^32 - 1`. So the image of `[_IDX 2^32]` is not a `typeuse*`:

* `lt_of_hasTyp_uN32`: inversion of `uN(32)` (through its instance, the defining match `N = 32`
  and the premise, evaluated to `false` beyond the bound);
* `not_typeTyping`: `¬ Prims.TypeTyping (simEnv B)`, for every `B`;
* `not_residue`: `¬ Integrate.Residue (simEnv B) hn`, for every `B` and `hn`. So
  `Integrate.forward_concrete`, `Integrate.backward_concrete` and
  `Integrate.wholeStepBounded_of_concrete` hold **vacuously**: their bundle hypothesis is
  unsatisfiable (`not_wholeStepBounded_of_concrete_hyp`).

The same bound fails for `valtype`, `storagetype`, `deftype` (`Residue.valtypes`,
`AggTypes.storagetype`, `TypeTyping.deftype`), and every `list(X)` position of the type syntax
(`rectype`, `STRUCT`, `FUNC`) bounds its length by `2 ^ 32`, which Core's `Ty` does not. A
satisfiable restatement quantifies over closed, bounded types only (`docs/projects/spectec/README.md`,
track configok).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.ConfigOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d22)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-- Premises that hold are premises that hold with some outward scope. -/
theorem premsHold_of_premsOk {env : Env} {ρ : VarEnv} {prems : List Prem}
    (h : PremsOk env ρ prems) : ∃ ρ', PremsHold env ρ prems ρ' := by
  obtain ⟨n, h⟩ := h
  unfold premsOk Res.elimUndef at h
  split at h
  · rename_i ρ' hρ'
    exact ⟨ρ', n, hρ'⟩
  · simp at h
  · simp at h

/-- A single `if` premise that holds evaluates to `true`. -/
theorem evalExp_of_premsOk_if {env : Env} {ρ : VarEnv} {e : Exp}
    (h : PremsOk env ρ [.ifPr e]) : EvalExp env ρ e (.bool true) := by
  obtain ⟨ρ', hp⟩ := premsHold_of_premsOk h
  obtain ⟨σ, h₁, -⟩ := Equiv.Validation.premsHold_cons_iff.1 hp
  exact (Equiv.Validation.premHolds_if_iff.1 h₁).2

/-- The premise of `uN(N)`'s case: `i >= 0 /\ i <= 2^N - 1`. -/
noncomputable def uNPrem : Exp :=
  .binE .andOp .boolT (.cmpE .geOp (.numT .natT) (.varE "i") (.numE (.natN 0)))
    (.cmpE .leOp (.numT .natT) (.varE "i") (.cvtE (.binE .subOp (.numT .intT)
      (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT))

set_option maxRecDepth 100000 in
theorem uNCases : IntNumeric.instCases Original.d22 0 =
    [.mk "%" (.tupT [.mk "i" (.numT .natT)]) [] [.ifPr uNPrem]] := rfl

/-- The scope in which `uN(32)`'s premise is checked for the numeral `n`. -/
noncomputable def uNScope (n : Nat) : VarEnv :=
  caseScope (VarEnv.empty.bindVal "N" (.num (.natN 32)))
    (.tupT [.mk "i" (.numT .natT)]) (.tuple [.num (.natN n)])

theorem uNScope_N (n : Nat) : (uNScope n).findVal? "N" = some (Equiv.natV 32) := by
  simp [uNScope, caseScope, typBinds, Equiv.natV]

theorem uNScope_i (n : Nat) : (uNScope n).findVal? "i" = some (.num (.natN n)) := by
  simp [uNScope, caseScope, typBinds]

/-- `2^32 - 1`, as `uN(32)`'s premise computes it. -/
theorem evalExp_uNBound (n : Nat) : EvalExp (simEnv B) (uNScope n)
    (.cvtE (.binE .subOp (.numT .intT)
      (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT) (Equiv.natV (2 ^ 32 - 1)) := by
  have hpow : EvalExp (simEnv B) (uNScope n)
      (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) (Equiv.natV (2 ^ 32)) :=
    Equiv.evalExp_twoPow (uNScope_N n)
  have hsub : EvalExp (simEnv B) (uNScope n) (.binE .subOp (.numT .intT)
      (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) (.num (.intN ((2 ^ 32 : Nat) - 1))) :=
    evalExp_binNum (Equiv.evalExp_toInt hpow) Equiv.evalExp_oneInt rfl
  exact Equiv.evalExp_toNat (j := ((2 ^ 32 : Nat) : Int) - 1) (by omega) hsub

/-- **`uN(32)`'s premise is false beyond the bound.** -/
theorem evalExp_uNPrem_false {n : Nat} (hn : 2 ^ 32 ≤ n) :
    EvalExp (simEnv B) (uNScope n) uNPrem (.bool false) := by
  have hge : EvalExp (simEnv B) (uNScope n)
      (.cmpE .geOp (.numT .natT) (.varE "i") (.numE (.natN 0))) (.bool true) :=
    evalExp_cmpNum (evalExp_var (uNScope_i n)) evalExp_num (by simp [Num.cmp])
  have hcmp : Num.cmp .leOp (.natN n) (.natN (2 ^ 32 - 1)) = some false := by
    simp only [Num.cmp, Option.some.injEq, decide_eq_false_iff_not]
    omega
  exact IntNumeric.evalExp_and hge
    (evalExp_cmpNum (evalExp_var (uNScope_i n)) (evalExp_uNBound n) hcmp)

/-- The instance of `uN(32)`, after its argument pattern `N` matched `32`. -/
theorem hasTypDef_of_hasTyp_uN32 {σ : VarEnv} {n : Nat}
    (h : HasTyp (simEnv B) σ (.varT "uN" [.expA (.numE (.natN 32))]) (Equiv.Execution.pctV n)) :
    HasTypDef (simEnv B) (VarEnv.empty.bindVal "N" (.num (.natN 32)))
      (.variantT (IntNumeric.instCases Original.d22 0)) (Equiv.Execution.pctV n) := by
  obtain ⟨ps, qs, htd⟩ := IntNumeric.findTyp_uN (B := B)
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  obtain ⟨v, hv, rfl⟩ := evalArgs_expA_iff.1 hargs
  obtain rfl := evalExp_numE_iff.1 hv
  have hm0 : MatchArgs (simEnv B) VarEnv.empty [.expA (.varE "N")] [.val (.num (.natN 32))]
      (VarEnv.empty.bindVal "N" (.num (.natN 32))) :=
    matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil
  rcases hasTypInsts_cons_inv hi with ⟨σ', ⟨k, hk⟩, hd⟩ | hrest
  · rwa [IntNumeric.matchArgs_det hm0 hk] at hd
  · exact absurd hrest not_hasTypInsts_nil

/-- A typed `uN(32)` numeral satisfies the premise in `uNScope`. -/
theorem premsOk_of_hasTyp_uN32 {σ : VarEnv} {n : Nat}
    (h : HasTyp (simEnv B) σ (.varT "uN" [.expA (.numE (.natN 32))]) (Equiv.Execution.pctV n)) :
    PremsOk (simEnv B) (uNScope n) [.ifPr uNPrem] := by
  obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 (hasTypDef_of_hasTyp_uN32 h)
  obtain ⟨rfl, rfl⟩ : op = "%" ∧ w = .tuple [.num (.natN n)] := by
    simpa only [Equiv.Execution.pctV, Value.case.injEq] using he.symm
  have hc' : HasTypCase (simEnv B) (VarEnv.empty.bindVal "N" (.num (.natN 32)))
      [.mk "%" (.tupT [.mk "i" (.numT .natT)]) [] [.ifPr uNPrem]] "%"
      (.tuple [.num (.natN n)]) := by rwa [uNCases] at hc
  exact ((hasTypCase_cons_hit_iff rfl).1 hc').2

/-- **Inversion of `uN(32)`**: a typed numeral is below `2 ^ 32`. -/
theorem lt_of_hasTyp_uN32 {σ : VarEnv} {n : Nat}
    (h : HasTyp (simEnv B) σ (.varT "uN" [.expA (.numE (.natN 32))]) (Equiv.Execution.pctV n)) :
    n < 2 ^ 32 := by
  have htrue : EvalExp (simEnv B) (uNScope n) uNPrem (.bool true) :=
    evalExp_of_premsOk_if (premsOk_of_hasTyp_uN32 h)
  refine Nat.lt_of_not_le fun hn => ?_
  have hfalse : EvalExp (simEnv B) (uNScope n) uNPrem (.bool false) := evalExp_uNPrem_false hn
  cases htrue.unique hfalse

/-- **Inversion of a closed alias**: a value of an alias is a value of its target, in the empty
scope. -/
theorem hasTyp_of_closedAlias {x : IL.Id} {t : Typ} {ρ : VarEnv} (hρ : ValsOnly ρ)
    (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.aliasT t)])) {v : Value}
    (h : HasTyp (simEnv B) ρ (.varT x []) v) : HasTyp (simEnv B) VarEnv.empty t v := by
  have hl : localTyp? ρ x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd', -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
  · obtain rfl := IntNumeric.matchArgs_nil_scope hm
    exact hasTypDef_aliasT_iff.1 hd
  · exact absurd hrest not_hasTypInsts_nil

/-- **A `typeidx` is below `2 ^ 32`.** -/
theorem lt_of_hasTyp_typeidx {ρ : VarEnv} (hρ : ValsOnly ρ) {n : Nat}
    (h : HasTyp (simEnv B) ρ (.varT "typeidx" []) (Equiv.Execution.pctV n)) : n < 2 ^ 32 :=
  lt_of_hasTyp_uN32 (hasTyp_of_closedAlias valsOnly_empty Typing.findTyp_u32
    (hasTyp_of_closedAlias valsOnly_empty Typing.findTyp_idx
      (hasTyp_of_closedAlias hρ Typing.findTyp_typeidx h)))

set_option maxRecDepth 100000 in
/-- **`_IDX x` is a `typeuse` only for `x < 2 ^ 32`.** -/
theorem lt_of_hasTyp_typeuse_idx {n : Nat}
    (h : HasTyp (simEnv B) VarEnv.empty (.varT "typeuse" [])
      (.case "_IDX" (Equiv.Execution.pctV n))) :
    n < 2 ^ 32 :=
  lt_of_hasTyp_typeidx valsOnly_empty (IntNumeric.hasTyp_of_hasTypCase
    (Typing.hasTypCase_of_closedVariant Typing.findTyp_typeuse h) rfl)

/-- The image of the type-use list `[_IDX 2^32]`. -/
theorem tyV_bigIdx :
    Silmaril.SpecTec.Equiv.Validation.tyV
      (Ty.cons (Ty.idx (2 ^ 32)) Ty.nil : Ty (.list .use)) =
      .list [.case "_IDX" (Equiv.Execution.pctV (2 ^ 32))] := rfl

/-- **The image of `[_IDX 2^32]` is not a `typeuse*`.** -/
theorem not_typedV_typeuses_bigIdx :
    ¬ TypedV (simEnv B) (.iterT (.varT "typeuse" []) .list)
      (Silmaril.SpecTec.Equiv.Validation.tyV
        (Ty.cons (Ty.idx (2 ^ 32)) Ty.nil : Ty (.list .use))) := by
  intro h
  rw [tyV_bigIdx] at h
  obtain ⟨l, hl', hl⟩ := hasTyp_iterT_list_iff.1 (h _ valsOnly_empty)
  cases hl'
  exact absurd (lt_of_hasTyp_typeuse_idx (hasTypList_iff.1 hl _ (List.mem_singleton_self _)))
    (Nat.lt_irrefl _)

/-- **`Prims.TypeTyping` is false in every `simEnv B`.** -/
theorem not_typeTyping (B : Builtins) : ¬ Prims.TypeTyping (simEnv B) :=
  fun T => not_typedV_typeuses_bigIdx (T.typeuses _)

/-- **`Integrate.Residue` is uninhabited**, for every `B` and `hn`: the round-2 theorems that
take it (`forward_concrete`, `backward_concrete`, `wholeStepBounded_of_concrete`) are vacuous. -/
theorem not_residue {H : Type} (B : Builtins) (hn : H → String) :
    ¬ Integrate.Residue (simEnv B) hn :=
  fun O => not_typeTyping B O.types

set_option maxRecDepth 100000 in
/-- **`REF null? (_IDX x)` is a `valtype` only for `x < 2 ^ 32`.** -/
theorem lt_of_hasTyp_valtype_refIdx {b : Bool} {n : Nat}
    (h : HasTyp (simEnv B) VarEnv.empty (.varT "valtype" [])
      (.case "REF" (.tuple [Equiv.Validation.nullV b, .case "_IDX" (Equiv.Execution.pctV n)]))) :
    n < 2 ^ 32 := by
  have hp := IntNumeric.hasTyp_of_hasTypCase
    (Typing.hasTypCase_of_closedVariant Typing.findTyp_valtype h)
    (t := .tupT [.mk "null?" (.iterT (.varT "null" []) .opt), .mk "heaptype" (.varT "heaptype" [])])
    (prems := []) rfl
  have hh := IntNumeric.hasTyp_varT_nil_congr ⟨rfl, rfl, rfl⟩ valsOnly_empty
    (Typing.hasTyp_pair_inv hp).2
  exact lt_of_hasTyp_typeidx valsOnly_empty (IntNumeric.hasTyp_of_hasTypCase
    (Typing.hasTypCase_of_closedVariant Typing.findTyp_heaptype hh) (prems := []) rfl)

/-- The value type `ref (_IDX 2^32)`. -/
def bigRefType : CValType := .refv (.ref false (.use (.idx (2 ^ 32))))

/-- **The image of `[ref (_IDX 2^32)]` is not a `valtype*`.** -/
theorem not_typedV_valtypes_big :
    ¬ TypedV (simEnv B) valtypesT
      (.list ((Ty.cons bigRefType Ty.nil : Ty (.list .val)).toList.map
        Silmaril.SpecTec.Equiv.Validation.tyV)) := by
  intro h
  obtain ⟨l, hl', hl⟩ := hasTyp_iterT_list_iff.1 (h _ valsOnly_empty)
  cases hl'
  exact absurd (lt_of_hasTyp_valtype_refIdx (b := false)
    (hasTypList_iff.1 hl _ (List.mem_singleton_self _))) (Nat.lt_irrefl _)

/-- **Family C's `CtrlCall` is false in every `simEnv B`** (its `valtypes` field). -/
theorem not_ctrlCall (B : Builtins) : ¬ CtrlCall (simEnv B) :=
  fun C => not_typedV_valtypes_big (C.valtypes _)

/-- **`Whole.Assumptions` is uninhabited**, for every `B`, `hn` and host: the round-1 assembly
(`Whole.forward_covered`) and every theorem built on `Integrate.assumptions_concrete` hold
vacuously. -/
theorem not_wholeAssumptions {H : Type} (B : Builtins) (hn : H → String)
    (host : Execution.Core.HostSemantics H) : ¬ Whole.Assumptions B hn host :=
  fun A => not_ctrlCall B A.ctrlCall

open Silmaril.Wasm.Execution.Core (HostSemantics Config Step) in
open Silmaril.Wasm.Numerics (RelaxedChoice Profile) in
/-- **The hypothesis of `Integrate.wholeStepBounded_of_concrete` is false** (verbatim): already
for the empty host type, its `Residue` conjunct fails. -/
theorem not_wholeStepBounded_of_concrete_hyp :
    ¬ (∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
        Prims.HostRespects hn host ∧
        Integrate.Residue (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn ∧
        Integrate.Extra (simEnv (Prims.builtins (Profile.spec nd r) hn host)) ∧
        Integrate.BwdOpen (Prims.builtins (Profile.spec nd r) hn host) hn (Profile.spec nd r) host ∧
        (∀ c c' : Config H, ¬ Integrate.Covered c → Integrate.StoreOk c.store →
          Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c →
          Typed (simEnv (Prims.builtins (Profile.spec nd r) hn host)) hn c' →
          Step (Profile.spec nd r) host c c' →
          ∃ d', Bwd.ConfigEq c' d' ∧
            SStep (simEnv (Prims.builtins (Profile.spec nd r) hn host)) (configV hn c)
              (configV hn d'))) := by
  intro h
  have hinj : Function.Injective (fun e : Empty => e.elim : Empty → String) := fun e => e.elim
  obtain ⟨-, O, -⟩ := h Empty (fun e => e.elim) hinj Integrate.emptyHost
    Integrate.hostFinite_emptyHost false {}
  exact not_residue _ _ O

end Silmaril.Wasm.SpecTec.Sim.ConfigOk
