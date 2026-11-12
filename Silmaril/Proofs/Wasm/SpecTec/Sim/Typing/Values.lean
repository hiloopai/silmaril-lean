module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Ctrl
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Tags
public import Silmaril.Wasm.SpecTec.Sim.State.Thms

/-!
# Every value is typed; family M's `StateTyping` and `StateDecode`

`typedV_ref`: every encoded reference is a `ref` (by induction: `REF.EXTERN` carries a `ref`);
`typedV_val`: every Core `Val` is a typed `val` (numbers with `typedV_val_num`, vectors with
`typedV_val_vec`, references here). `stateTyping_simEnv`, `stateDecode_simEnv` discharge family M's
two interfaces in every `simEnv B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Typing

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d88 Original.d268)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findTyp_ref : (simEnv B).findTyp? "ref" =
    some ([], [.instD [] [] (.variantT (IntNumeric.recCases Original.d268 0 0))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_u31 : (simEnv B).findTyp? "u31" =
    some ([], [.instD [] [] (.aliasT (.varT "uN" [.expA (.numE (.natN 31))]))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_structaddr :
    (simEnv B).findTyp? "structaddr" = some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_arrayaddr :
    (simEnv B).findTyp? "arrayaddr" = some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_funcaddr :
    (simEnv B).findTyp? "funcaddr" = some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_exnaddr :
    (simEnv B).findTyp? "exnaddr" = some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_hostaddr :
    (simEnv B).findTyp? "hostaddr" = some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_addrtype : (simEnv B).findTyp? "addrtype" =
    some ([], [.instD [] [] (.variantT (IntNumeric.instCases Original.d88 0))]) := rfl

/-- An address is any of the address aliases. -/
theorem typedV_addrAlias {x : IL.Id}
    (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.aliasT (.varT "addr" []))]))
    (a : Nat) : TypedV (simEnv B) (.varT x []) (.num (.natN a)) :=
  typedV_alias htd (typedV_natAlias findTyp_addr a)

/-- A case of `ref` whose payload is typed. -/
theorem typedV_refCase {op : MixopS} {t : Typ} {w : Value}
    (hf : IntNumeric.findCase (IntNumeric.recCases Original.d268 0 0) op = some (t, []))
    (hw : HasTyp (simEnv B) VarEnv.empty t w) : TypedV (simEnv B) (.varT "ref" []) (.case op w) :=
  fun ρ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_ref
    Equiv.evalArgs_nil matchArgs_nil (IntNumeric.hasTypCase_of_findCase hf hw premsOk_nil
      (IntNumeric.quantFreeAt_of_findCase_nil hf))

/-- **Every encoded reference is a `ref`.** -/
theorem typedV_ref : ∀ r : Ref, TypedV (simEnv B) (.varT "ref" []) (refToValue r)
  | .i31 b => typedV_refCase rfl (hasTyp_varT_of_insts rfl findTyp_u31
      Equiv.evalArgs_nil (hasTypInsts_head matchArgs_nil
        (hasTypDef_aliasT_iff.2 (IntNumeric.hasTyp_uN evalExp_num b.isLt))))
  | .null => typedV_refCase rfl hasTyp_tupT_nil
  | .struct a => typedV_refCase rfl (typedV_addrAlias findTyp_structaddr a _ ⟨rfl, rfl, rfl⟩)
  | .array a => typedV_refCase rfl (typedV_addrAlias findTyp_arrayaddr a _ ⟨rfl, rfl, rfl⟩)
  | .func a => typedV_refCase rfl (typedV_addrAlias findTyp_funcaddr a _ ⟨rfl, rfl, rfl⟩)
  | .exn a => typedV_refCase rfl (typedV_addrAlias findTyp_exnaddr a _ ⟨rfl, rfl, rfl⟩)
  | .host a => typedV_refCase rfl (typedV_addrAlias findTyp_hostaddr a _ ⟨rfl, rfl, rfl⟩)
  | .extern r => typedV_refCase rfl (typedV_ref r _ ⟨rfl, rfl, rfl⟩)

/-- A case of `val` whose payload is typed. -/
theorem typedV_valCase {op : MixopS} {t : Typ} {w : Value}
    (hf : IntNumeric.findCase (IntNumeric.instCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d269 0) op = some (t, []))
    (hw : HasTyp (simEnv B) VarEnv.empty t w) : TypedV (simEnv B) (.varT "val" []) (.case op w) :=
  fun ρ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_val
    Equiv.evalArgs_nil matchArgs_nil (IntNumeric.hasTypCase_of_findCase hf hw premsOk_nil
      (IntNumeric.quantFreeAt_of_findCase_nil hf))

/-- A reference's `val` typing: `val`'s reference cases are `ref`'s. -/
theorem typedV_val_ref : ∀ r : Ref, TypedV (simEnv B) (.varT "val" []) (refToValue r)
  | .i31 b => typedV_valCase rfl (hasTyp_varT_of_insts rfl findTyp_u31
      Equiv.evalArgs_nil (hasTypInsts_head matchArgs_nil
        (hasTypDef_aliasT_iff.2 (IntNumeric.hasTyp_uN evalExp_num b.isLt))))
  | .null => typedV_valCase rfl hasTyp_tupT_nil
  | .struct a => typedV_valCase rfl (typedV_addrAlias findTyp_structaddr a _ ⟨rfl, rfl, rfl⟩)
  | .array a => typedV_valCase rfl (typedV_addrAlias findTyp_arrayaddr a _ ⟨rfl, rfl, rfl⟩)
  | .func a => typedV_valCase rfl (typedV_addrAlias findTyp_funcaddr a _ ⟨rfl, rfl, rfl⟩)
  | .exn a => typedV_valCase rfl (typedV_addrAlias findTyp_exnaddr a _ ⟨rfl, rfl, rfl⟩)
  | .host a => typedV_valCase rfl (typedV_addrAlias findTyp_hostaddr a _ ⟨rfl, rfl, rfl⟩)
  | .extern r => typedV_valCase rfl (typedV_ref r _ ⟨rfl, rfl, rfl⟩)

/-- **Every Core value is a typed `val`.** -/
theorem typedV_val : ∀ v : Val, TypedV (simEnv B) (.varT "val" []) (valV v)
  | .num n => typedV_val_num n
  | .vec b => typedV_val_vec b
  | .ref r => typedV_val_ref r

/-- Every address type is an `addrtype`. -/
theorem typedV_addrtype (a : AddrType) :
    TypedV (simEnv B) (.varT "addrtype" []) (Encode.toValue a) := fun ρ hρ => by
  cases a <;> exact IntNumeric.hasTyp_closedNullary hρ findTyp_addrtype rfl

/-- An address type's encoding is its integer type's. -/
theorem encode_addrType_ntV (a : AddrType) :
    (Encode.toValue a : Value) = IntNumeric.ntV a.intType := by
  cases a <;> rfl

/-- **Family M's typing interface holds in every `simEnv B`.** -/
theorem stateTyping_simEnv (B : Builtins) : State.StateTyping (simEnv B) where
  idx n hn := typedV_alias findTyp_idx (typedV_u32 hn)
  addr a := typedV_addrtype a
  num y a b ρ _ hy := IntNumeric.hasTyp_num b
    (evalExp_subE_iff.2 (evalExp_var (by rw [hy, encode_addrType_ntV])))
  num32 b := fun _ _ => IntNumeric.hasTyp_num (t := .i32) b (evalExp_caseE_iff.2 ⟨_,
    evalExp_tupE_iff.2 ⟨[], Equiv.Validation.evalExps_nil_iff.2 rfl, rfl⟩, rfl⟩)
  nat := typedV_natAlias findTyp_n
  ref r _ := typedV_ref r

theorem head_localTee {a : Admin} (h : adminHead a = "LOCAL.TEE") :
    ∃ x, a = .plain (.localTee x) := by
  revert h
  admin_head_inv

/-- **Family M's decoders hold in every `simEnv B`.** -/
theorem stateDecode_simEnv (B : Builtins) : State.StateDecode (simEnv B) where
  val a ρ hρ h := by
    obtain ⟨op, w, hw, hop⟩ := head_of_typed_val hρ h
    exact head_val ((adminToV_case hw) ▸ hop)
  localTee a X h := by
    obtain ⟨x, rfl⟩ := head_localTee (adminToV_case h).symm
    refine ⟨x, rfl, ?_⟩
    injection h with _ h₂
    exact h₂.symm

end Silmaril.Wasm.SpecTec.Sim.Typing
