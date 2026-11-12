module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Exn

/-!
# Encoded source types are typed: `heaptype`, `valtype`, `blocktype`

The source type syntax (`Silmaril.Wasm.ValType`: number, vector and reference types over
abstract or index heap types) is encoded by `Encode.toValue`. `typedV_heaptype`,
`typedV_valtype`, `typedV_blocktype` show the images inhabit the IL types; with them family X's
`Exn.Typing` holds outright (`exnTyping_simEnv'`), and `Whole.Assumptions` follows from its
non-typing fields alone (`assumptions_of'`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Typing

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d87 Original.d95)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findTyp_heaptype : (simEnv B).findTyp? "heaptype" =
    some ([], [.instD [] [] (.variantT (IntNumeric.recCases Original.d95 1 0))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_valtype : (simEnv B).findTyp? "valtype" =
    some ([], [.instD [] [] (.variantT (IntNumeric.recCases Original.d95 2 0))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_null : (simEnv B).findTyp? "null" =
    some ([], [.instD [] [] (.variantT (IntNumeric.instCases Original.d87 0))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_blocktype : (simEnv B).findTyp? "blocktype" = some ([], [.instD [] []
    (.variantT [.mk "_RESULT" (.iterT (.varT "valtype" []) .opt) [] [],
      .mk "_IDX" (.varT "typeidx" []) [] []])]) := rfl

/-- A case of a closed one-instance variant, with a payload typed in the empty scope. -/
theorem typedV_closedCase {x : IL.Id} {cs : List TypCase} {op : MixopS} {t : Typ} {w : Value}
    (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.variantT cs)]))
    (hf : IntNumeric.findCase cs op = some (t, []))
    (hw : HasTyp (simEnv B) VarEnv.empty t w) : TypedV (simEnv B) (.varT x []) (.case op w) :=
  fun ρ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) htd
    Equiv.evalArgs_nil matchArgs_nil (IntNumeric.hasTypCase_of_findCase hf hw premsOk_nil
      (IntNumeric.quantFreeAt_of_findCase_nil hf))

/-- Every encoded heap type is a `heaptype`. -/
theorem typedV_heaptype (h : HeapType) :
    TypedV (simEnv B) (.varT "heaptype" []) (Encode.toValue h) := by
  rcases h with a | x
  · cases a <;> exact typedV_closedCase findTyp_heaptype rfl hasTyp_tupT_nil
  · exact typedV_closedCase findTyp_heaptype rfl
      (typedV_alias findTyp_typeidx (typedV_idx x) _ ⟨rfl, rfl, rfl⟩)

/-- Both nullabilities are a `null?`. -/
theorem hasTyp_nullOpt (b : Bool) :
    HasTyp (simEnv B) VarEnv.empty (.iterT (.varT "null" []) .opt)
      (Equiv.nullToValue b) := by
  cases b
  · exact hasTyp_iterT_opt_iff.2 (.inl rfl)
  · exact hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl,
      typedV_closedCase (op := "NULL") findTyp_null rfl hasTyp_tupT_nil _ ⟨rfl, rfl, rfl⟩⟩)

/-- Every encoded value type is a `valtype`. -/
theorem typedV_valtype (t : ValType) :
    TypedV (simEnv B) (.varT "valtype" []) (Encode.toValue t) := by
  rcases t with (t | t) | t | ⟨b, h⟩
  · cases t <;> exact typedV_closedCase findTyp_valtype rfl hasTyp_tupT_nil
  · cases t <;> exact typedV_closedCase findTyp_valtype rfl hasTyp_tupT_nil
  · cases t; exact typedV_closedCase findTyp_valtype rfl hasTyp_tupT_nil
  · exact typedV_closedCase findTyp_valtype rfl (hasTyp_tupT_iff.2 ⟨_, rfl,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_nullOpt b, hasTypTup_cons_iff.2 ⟨_, _, rfl,
        typedV_heaptype h _ ⟨rfl, rfl, rfl⟩, hasTypTup_nil_iff.2 rfl⟩⟩⟩)

/-- Every encoded block type is a `blocktype`. -/
theorem typedV_blocktype (bt : BlockType) :
    TypedV (simEnv B) Exn.blocktypeT (Encode.toValue bt) := by
  rcases bt with _ | t | x
  · exact typedV_closedCase findTyp_blocktype rfl (hasTyp_iterT_opt_iff.2 (.inl rfl))
  · exact typedV_closedCase findTyp_blocktype rfl (hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl,
      typedV_valtype t _ ⟨rfl, rfl, rfl⟩⟩))
  · exact typedV_closedCase findTyp_blocktype rfl
      (typedV_alias findTyp_typeidx (typedV_idx x) _ ⟨rfl, rfl, rfl⟩)

/-- **Family X's typing interface holds in every `simEnv B`.** -/
theorem exnTyping_simEnv' (B : Builtins) : Exn.Typing (simEnv B) :=
  exnTyping_simEnv B typedV_blocktype

end Silmaril.Wasm.SpecTec.Sim.Typing
