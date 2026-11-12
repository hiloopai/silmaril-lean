module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.ConfigOk.Store

/-!
# `Memory.MemTyping` holds in every `simEnv B`; `Aggregates.AggTypes` does not

`memTyping_simEnv`: every field of the memory track's typing interface. Number types, `Inn`,
memory arguments (`ALIGN u32`, `OFFSET u64`, both bounded in Core's `MemArg`), signedness and
integer constants are typed outright; the limits and element type of a table, and the limits of a
memory, of a typed state are typed by inversion (`store → tableinst → tabletype`,
`store → meminst → memtype`).

`not_aggTypes`: the aggregates track's `AggTypes.storagetype` (every encoded storage type is a
`storagetype`) fails at `ref (_IDX 2^32)`, like `Residue.valtypes`; so `Integrate.Extra` is
uninhabited too (`not_extra`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.ConfigOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core (Store Frame TableInst MemInst)
open Silmaril.SpecTec.Equiv.RuntimeBridge (tableInstToValue memInstToValue)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-- The components of a typed triple. -/
theorem hasTyp_triple_inv {σ : VarEnv} {a b c : IL.Id} {τ₁ τ₂ τ₃ : Typ} {u v w : Value}
    (h : HasTyp (simEnv B) σ (.tupT [.mk a τ₁, .mk b τ₂, .mk c τ₃]) (.tuple [u, v, w])) :
    HasTyp (simEnv B) σ τ₁ u ∧ HasTyp (simEnv B) (σ.bindVal a u) τ₂ v ∧
      HasTyp (simEnv B) ((σ.bindVal a u).bindVal b v) τ₃ w := by
  obtain ⟨_, he, htt⟩ := hasTyp_tupT_iff.1 h
  obtain rfl := (Value.tuple.inj he).symm
  obtain ⟨_, _, he₁, h₁, ht₁⟩ := hasTypTup_cons_iff.1 htt
  obtain ⟨rfl, rfl⟩ := List.cons.inj he₁
  obtain ⟨_, _, he₂, h₂, ht₂⟩ := hasTypTup_cons_iff.1 ht₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj he₂
  obtain ⟨_, _, he₃, h₃, -⟩ := hasTypTup_cons_iff.1 ht₂
  obtain ⟨rfl, -⟩ := List.cons.inj he₃
  exact ⟨h₁, h₂, h₃⟩

set_option maxRecDepth 100000 in
theorem findTyp_tableinst : (simEnv B).findTyp? "tableinst" = some ([], [.instD [] [] (.structT
    [.mk "TYPE" (.varT "tabletype" []) [] [],
     .mk "REFS" (.iterT (.varT "ref" []) .list) [] []])]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_tabletype : (simEnv B).findTyp? "tabletype" = some ([], [.instD [] [] (.variantT
    [.mk "%%%" (.tupT [.mk "addrtype" (.varT "addrtype" []), .mk "limits" (.varT "limits" []),
      .mk "reftype" (.varT "reftype" [])]) [] []])]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_meminst : (simEnv B).findTyp? "meminst" = some ([], [.instD [] [] (.structT
    [.mk "TYPE" (.varT "memtype" []) [] [],
     .mk "BYTES" (.iterT (.varT "byte" []) .list) [] []])]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_memtype : (simEnv B).findTyp? "memtype" = some ([], [.instD [] [] (.variantT
    [.mk "%%PAGE" (.tupT [.mk "addrtype" (.varT "addrtype" []), .mk "limits" (.varT "limits" [])])
      [] []])]) := rfl

/-- The limits and element type of a typed table instance are typed. -/
theorem tableType_of_tableinst (ti : TableInst)
    (h : TypedV (simEnv B) (.varT "tableinst" []) (tableInstToValue CT ti)) :
    TypedV (simEnv B) Memory.limitsT (Encode.toValue ti.type.limits) ∧
      TypedV (simEnv B) Memory.reftypeT (Equiv.Validation.tyV ti.type.element) := by
  have hF := hasTypFields_of_closedStruct valsOnly_empty findTyp_tableinst (h _ valsOnly_empty)
  simp only [List.forall₂_cons, fieldTyp] at hF
  have hp := IntNumeric.hasTyp_of_hasTypCase
    (Typing.hasTypCase_of_closedVariant findTyp_tabletype hF.1) (prems := []) rfl
  obtain ⟨-, h₂, h₃⟩ := hasTyp_triple_inv hp
  exact ⟨Typing.typedV_of_hasTyp ⟨rfl, rfl, rfl⟩ h₂, Typing.typedV_of_hasTyp ⟨rfl, rfl, rfl⟩ h₃⟩

/-- The limits of a typed memory instance are typed. -/
theorem memType_of_meminst (mi : MemInst)
    (h : TypedV (simEnv B) (.varT "meminst" []) (memInstToValue mi)) :
    TypedV (simEnv B) Memory.limitsT (Encode.toValue mi.type.limits) := by
  have hF := hasTypFields_of_closedStruct valsOnly_empty findTyp_meminst (h _ valsOnly_empty)
  simp only [List.forall₂_cons, fieldTyp] at hF
  have hp := IntNumeric.hasTyp_of_hasTypCase
    (Typing.hasTypCase_of_closedVariant findTyp_memtype hF.1) (prems := []) rfl
  exact Typing.typedV_of_hasTyp ⟨rfl, rfl, rfl⟩ (Typing.hasTyp_pair_inv hp).2

/-- Every number type is a `numtype`. -/
theorem typedV_numtype (t : NumType) :
    TypedV (simEnv B) (.varT "numtype" []) (Encode.toValue t) := fun ρ hρ => by
  rcases t with t | t <;> cases t <;>
    exact IntNumeric.hasTyp_closedNullary hρ IntNumeric.findTyp_numtype rfl

set_option maxRecDepth 100000 in
theorem findTyp_Inn : (simEnv B).findTyp? "Inn" = some ([], [.instD [] [] (.variantT
    [.mk "I32" (.tupT []) [] [], .mk "I64" (.tupT []) [] []])]) := rfl

/-- Every integer number type is an `Inn`. -/
theorem typedV_inn (t : IntType) :
    TypedV (simEnv B) (.varT "Inn" []) (Encode.toValue (NumType.int t)) := fun ρ hρ => by
  cases t <;> exact IntNumeric.hasTyp_closedNullary hρ findTyp_Inn rfl

/-- Both signednesses are an `sx`. -/
theorem typedV_sx (s : Signedness) : TypedV (simEnv B) (.varT "sx" []) (sxV s) := fun ρ hρ => by
  cases s <;> exact IntNumeric.hasTyp_closedNullary hρ IntNumeric.findTyp_sx rfl

set_option maxRecDepth 100000 in
theorem findTyp_u64 : (simEnv B).findTyp? "u64" =
    some ([], [.instD [] [] (.aliasT (.varT "uN" [.expA (.numE (.natN 64))]))]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_memarg : (simEnv B).findTyp? "memarg" = some ([], [.instD [] [] (.structT
    [.mk "ALIGN" (.varT "u32" []) [] [], .mk "OFFSET" (.varT "u64" []) [] []])]) := rfl

/-- `u64` holds every natural below `2^64`. -/
theorem typedV_u64 {k : Nat} (hk : k < 2 ^ 64) :
    TypedV (simEnv B) (.varT "u64" []) (Equiv.Execution.pctV k) := fun ρ hρ =>
  hasTyp_varT_of_insts (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_u64
    Equiv.evalArgs_nil (hasTypInsts_head matchArgs_nil
      (hasTypDef_aliasT_iff.2 (IntNumeric.hasTyp_uN evalExp_num hk)))

/-- Every memory argument is a `memarg`. -/
theorem typedV_memarg (a : MemArg) : TypedV (simEnv B) (.varT "memarg" []) (memargV a) :=
  fun ρ hρ => hasTyp_varT_struct (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_memarg
    Equiv.evalArgs_nil matchArgs_nil
    (hasTypFields_cons_iff.2 ⟨_, _, rfl, Typing.typedV_u32 a.align.isLt _ valsOnly_empty,
      premsOk_nil, hasTypFields_cons_iff.2 ⟨_, _, rfl, typedV_u64 a.offset.isLt _ valsOnly_empty,
        premsOk_nil, hasTypFields_nil_iff.2 rfl⟩⟩)

/-- An integer number type's encoding is its `ntV`. -/
theorem encode_int_ntV (t : IntType) :
    (Encode.toValue (NumType.int t) : Value) = IntNumeric.ntV t := by
  cases t <;> rfl

/-- **`Memory.MemTyping` holds in every `simEnv B`.** -/
theorem memTyping_simEnv (B : Builtins) : Memory.MemTyping (simEnv B) where
  tableType _ _ _ ti hti h :=
    tableType_of_tableinst ti ((instTyping_simEnv B).tableinst _ _ _ ti hti h)
  memType _ _ _ mi hmi h := memType_of_meminst mi ((instTyping_simEnv B).meminst _ _ _ mi hmi h)
  numtype := typedV_numtype
  inn := typedV_inn
  memarg := typedV_memarg
  sx := typedV_sx
  numInt _ t b _ _ hy := IntNumeric.hasTyp_num b (evalExp_var (by rw [hy, encode_int_ntV]))
  numInn _ t b _ _ hy :=
    IntNumeric.hasTyp_num b (evalExp_subE_iff.2 (evalExp_var (by rw [hy, encode_int_ntV])))

/-! ## `AggTypes.storagetype` is false -/

set_option maxRecDepth 100000 in
theorem findTyp_storagetype : (simEnv B).findTyp? "storagetype" =
    some ([], [.instD [] [] (.variantT (IntNumeric.recCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d95 3 0))]) := rfl

set_option maxRecDepth 100000 in
/-- **`REF null? (_IDX x)` is a `storagetype` only for `x < 2 ^ 32`.** -/
theorem lt_of_hasTyp_storagetype_refIdx {b : Bool} {n : Nat}
    (h : HasTyp (simEnv B) VarEnv.empty (.varT "storagetype" [])
      (.case "REF" (.tuple [Equiv.Validation.nullV b, .case "_IDX" (Equiv.Execution.pctV n)]))) :
    n < 2 ^ 32 := by
  have hp := IntNumeric.hasTyp_of_hasTypCase
    (Typing.hasTypCase_of_closedVariant findTyp_storagetype h)
    (t := .tupT [.mk "null?" (.iterT (.varT "null" []) .opt), .mk "heaptype" (.varT "heaptype" [])])
    (prems := []) rfl
  have hh := IntNumeric.hasTyp_varT_nil_congr ⟨rfl, rfl, rfl⟩ valsOnly_empty
    (Typing.hasTyp_pair_inv hp).2
  exact lt_of_hasTyp_typeidx valsOnly_empty (IntNumeric.hasTyp_of_hasTypCase
    (Typing.hasTypCase_of_closedVariant Typing.findTyp_heaptype hh) (prems := []) rfl)

/-- **`Aggregates.AggTypes` is false in every `simEnv B`** (its `storagetype` field). -/
theorem not_aggTypes (B : Builtins) : ¬ Aggregates.AggTypes (simEnv B) := by
  intro A
  exact absurd (lt_of_hasTyp_storagetype_refIdx (b := false)
    (A.storagetype (.val bigRefType) _ valsOnly_empty)) (Nat.lt_irrefl _)

/-- **`Integrate.Extra` is uninhabited**, for every `B`. -/
theorem not_extra (B : Builtins) : ¬ Integrate.Extra (simEnv B) :=
  fun X => not_aggTypes B X.agg

end Silmaril.Wasm.SpecTec.Sim.ConfigOk
