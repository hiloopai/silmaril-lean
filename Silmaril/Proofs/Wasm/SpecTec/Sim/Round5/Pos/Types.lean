module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Defs

/-!
# Round 5: bounded runtime types are typed

`tyT_tyV`: the image `tyV t` of every runtime type `t : Ty k` within SpecTec's bounds
(`Round4.tyBnd t`) inhabits the IL type of its sort, in every `simEnv B`. Sorts that SpecTec's
elaborator flattens into a larger variant (`typeuse` into `heaptype`, `reftype` into `valtype`,
`valtype` into `storagetype`, `deftype` into `typeuse`) are typed at every variant they occur in
(`TyT`). The `list(X)` positions (`REC`, `STRUCT`, `FUNC`'s `resulttype`s) are typed through
`hasTyp_listT`, whose premise `|X*| < 2^32` is the bound `tyBnd` carries.

No validity is needed: under `TyOk {}` a type has no `_IDX` at all, but `tyBnd` already bounds
every `_IDX`. Consequences: `PosTypingNE.callRefType` and `returnCallRefType` hold
(`typedV_callRefType`, `typedV_returnCallRefType`), without the `TyOk {}` hypothesis.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Pos

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d94 Original.d95 Original.d96 Original.d98)

variable {B : Builtins}

/-! ## `list(X)` -/

/-- `|X*| < 2^32`, the premise of `list(X)`. -/
def listPrem : Exp := .cmpE .ltOp (.numT .natT)
  (.lenE (.iterE (.varE "X") (.mk .list [.mk "X" (.varE "X*")])))
  (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.numE (.natN 32)))

set_option maxRecDepth 100000 in
theorem findTyp_list (B : Builtins) : (simEnv B).findTyp? "list" = some ([.typP "X"],
    [.instD [.typP "X"] [.typA (.varT "X" [])] (.variantT [.mk "%"
      (.tupT [.mk "X*" (.iterT (.varT "X" []) .list)]) [] [.ifPr listPrem]])]) := rfl

set_option maxRecDepth 100000 in
/-- `X` is not a global type name. -/
theorem memTyp_X (B : Builtins) : (simEnv B).memTyp "X" = false := by rfl

/-- A closed named type, in a scope that does not bind it as a type variable. -/
theorem hasTyp_varT_global_congr {σ : VarEnv} {y : IL.Id} {u : Value}
    (hσ : σ.findTyp? y = none) (h : TypedV (simEnv B) (.varT y []) u) :
    HasTyp (simEnv B) σ (.varT y []) u := by
  have h0 := h VarEnv.empty ⟨rfl, rfl, rfl⟩
  obtain ⟨td, ws, htd, hargs, hi⟩ := (hasTyp_varT_global_iff (ρ := VarEnv.empty) rfl).1 h0
  obtain rfl := Equiv.Validation.evalArgs_nil_iff.1 hargs
  exact (hasTyp_varT_global_iff (by simpa [localTyp?] using hσ)).2
    ⟨td, [], htd, Equiv.evalArgs_nil, hi⟩

/-- `list(X)`'s premise holds below `2^32` elements. -/
theorem evalExp_listPrem {σ : VarEnv} {l : List Value} (hl : l.length < 2 ^ 32) :
    EvalExp (simEnv B) (σ.bindVal "X*" (.list l)) listPrem (.bool true) := by
  have hit : EvalExp (simEnv B) (σ.bindVal "X*" (.list l))
      (.iterE (.varE "X") (.mk .list [.mk "X" (.varE "X*")])) (.list (l.map id)) :=
    evalExp_iterMap (by simp [Equiv.Execution.findVal?_bindVal_lit])
      (fun w _ => evalExp_varE_iff.2
        (by simp [VarEnv.bindVals, VarEnv.findVal?, Map.binds, Map.bind]))
  rw [List.map_id] at hit
  refine evalExp_cmpE_iff.2 ⟨_, .num (.natN (2 ^ 32)), evalExp_lenE_iff.2 ⟨_, hit, rfl⟩,
    evalExp_twoPowE (evalExp_numE_iff.2 rfl), ?_⟩
  simpa [cmpValues, Num.cmp] using hl

/-- **`list(y)`**: fewer than `2^32` typed elements. -/
theorem hasTyp_listT {ρ : VarEnv} (hρ : ValsOnly ρ) {y : IL.Id} (hy : y ≠ "X")
    {l : List Value} (hl : l.length < 2 ^ 32) (hall : ∀ u ∈ l, TypedV (simEnv B) (.varT y []) u) :
    HasTyp (simEnv B) ρ (.varT "list" [.typA (.varT y [])]) (.case "%" (.tuple [.list l])) := by
  have hargs : EvalArgs (simEnv B) ρ [.typA (.varT y [])] [.typ (.varT y [])] :=
    ⟨2, by simp [evalArgs, evalArg, resolveTyp, VarEnv.findTyp?, hρ.1]⟩
  have hm : MatchArgs (simEnv B) VarEnv.empty [.typA (.varT "X" [])] [.typ (.varT y [])]
      (VarEnv.empty.bindTyp "X" (.varT y [])) :=
    ⟨2, by simp [matchArgs, matchArg, matchTypV, memTyp_X, VarEnv.findTyp?, VarEnv.empty,
      Map.find?, Map.empty]⟩
  refine hasTyp_varT_case rfl (findTyp_list B) hargs hm
    (IntNumeric.hasTypCase_of_findCase rfl ?_ (IntNumeric.premsOk_if (evalExp_listPrem hl)))
  refine hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    hasTyp_iterT_list_iff.2 ⟨l, rfl, hasTypList_iff.2 fun u hu => ?_⟩, hasTypTup_nil_iff.2 rfl⟩⟩
  refine (hasTyp_varT_local_iff (t := .varT y []) ?_).2 (hasTyp_varT_global_congr ?_ (hall u hu))
  · simp [localTyp?, VarEnv.findTyp?, VarEnv.bindTyp, Map.bind, VarEnv.empty]
  · simp [VarEnv.findTyp?, VarEnv.bindTyp, Map.bind, Map.find?, VarEnv.empty, Map.empty,
      Ne.symm hy]

/-! ## The type variants -/

set_option maxRecDepth 100000 in
theorem findTyp_storagetype : (simEnv B).findTyp? "storagetype" =
    some ([], [.instD [] [] (.variantT (IntNumeric.recCases Original.d95 3 0))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_resulttype : (simEnv B).findTyp? "resulttype" =
    some ([], [.instD [] [] (.aliasT (.varT "list" [.typA (.varT "valtype" [])]))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_fieldtype : (simEnv B).findTyp? "fieldtype" =
    some ([], [.instD [] [] (.variantT (IntNumeric.recCases Original.d95 5 0))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_comptype : (simEnv B).findTyp? "comptype" =
    some ([], [.instD [] [] (.variantT (IntNumeric.recCases Original.d95 6 0))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_subtype : (simEnv B).findTyp? "subtype" =
    some ([], [.instD [] [] (.variantT (IntNumeric.recCases Original.d95 7 0))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_rectype : (simEnv B).findTyp? "rectype" =
    some ([], [.instD [] [] (.variantT (IntNumeric.recCases Original.d95 8 0))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_deftype : (simEnv B).findTyp? "deftype" =
    some ([], [.instD [] [] (.variantT (IntNumeric.instCases Original.d96 0))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_reftype : (simEnv B).findTyp? "reftype" =
    some ([], [.instD [] [] (.variantT (IntNumeric.instCases Original.d98 0))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_final : (simEnv B).findTyp? "final" =
    some ([], [.instD [] [] (.variantT (IntNumeric.instCases Original.d94 0))]) := rfl

/-- A two-field tuple of typed components. -/
theorem hasTyp_tup2 {a b : IL.Id} {τ₁ τ₂ : Typ} {u v : Value} (h₁ : TypedV (simEnv B) τ₁ u)
    (h₂ : TypedV (simEnv B) τ₂ v) :
    HasTyp (simEnv B) VarEnv.empty (.tupT [.mk a τ₁, .mk b τ₂]) (.tuple [u, v]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, h₁ _ ⟨rfl, rfl, rfl⟩,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, h₂ _ ⟨rfl, rfl, rfl⟩, hasTypTup_nil_iff.2 rfl⟩⟩⟩

/-- A three-field tuple of typed components. -/
theorem hasTyp_tup3 {a b c : IL.Id} {τ₁ τ₂ τ₃ : Typ} {u v w : Value}
    (h₁ : TypedV (simEnv B) τ₁ u) (h₂ : TypedV (simEnv B) τ₂ v) (h₃ : TypedV (simEnv B) τ₃ w) :
    HasTyp (simEnv B) VarEnv.empty (.tupT [.mk a τ₁, .mk b τ₂, .mk c τ₃]) (.tuple [u, v, w]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, h₁ _ ⟨rfl, rfl, rfl⟩,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, h₂ _ ⟨rfl, rfl, rfl⟩,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, h₃ _ ⟨rfl, rfl, rfl⟩, hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩

/-- `null?`. -/
theorem typedV_nullV (b : Bool) :
    TypedV (simEnv B) (.iterT (.varT "null" []) .opt) (Equiv.Validation.nullV b) := by
  cases b
  · exact fun _ _ => hasTyp_iterT_opt_iff.2 (.inl rfl)
  · exact fun _ hρ => hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl,
      Typing.typedV_closedCase (op := "NULL") Typing.findTyp_null rfl hasTyp_tupT_nil _ hρ⟩)

/-- `final?`. -/
theorem typedV_finalV (b : Bool) :
    TypedV (simEnv B) (.iterT (.varT "final" []) .opt) (Equiv.Validation.finalV b) := by
  cases b
  · exact fun _ _ => hasTyp_iterT_opt_iff.2 (.inl rfl)
  · exact fun _ hρ => hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl,
      Typing.typedV_closedCase (op := "FINAL") findTyp_final rfl hasTyp_tupT_nil _ hρ⟩)

/-- A `typeidx` below `2^32`. -/
theorem typedV_typeidxNat {x : Nat} (hx : x < 2 ^ 32) :
    TypedV (simEnv B) (.varT "typeidx" []) (Equiv.Validation.idxV x) :=
  Typing.typedV_alias Typing.findTyp_typeidx (Typing.typedV_alias Typing.findTyp_idx
    (Typing.typedV_u32 hx))

/-- `list(y)`, as a `TypedV`. -/
theorem typedV_listT {y : IL.Id} (hy : y ≠ "X") {l : List Value} (hl : l.length < 2 ^ 32)
    (hall : ∀ u ∈ l, TypedV (simEnv B) (.varT y []) u) :
    TypedV (simEnv B) (.varT "list" [.typA (.varT y [])]) (.case "%" (.tuple [.list l])) :=
  fun _ hρ => hasTyp_listT hρ hy hl hall

/-- `resulttype`. -/
theorem typedV_resulttype {l : List Value} (hl : l.length < 2 ^ 32)
    (hall : ∀ u ∈ l, TypedV (simEnv B) (.varT "valtype" []) u) :
    TypedV (simEnv B) (.varT "resulttype" []) (.case "%" (.tuple [.list l])) := fun ρ hρ =>
  hasTyp_varT_of_insts (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_resulttype
    Equiv.evalArgs_nil (hasTypInsts_head matchArgs_nil
      (hasTypDef_aliasT_iff.2 (hasTyp_listT ⟨rfl, rfl, rfl⟩ (by decide) hl hall)))

/-! ## Every bounded runtime type -/

/-- The IL types the image of a runtime type of sort `k` inhabits: its own sort's, and the
larger variants SpecTec's elaborator flattens it into. -/
def TyT (B : Builtins) : TKind → Value → Prop
  | .use, v => TypedV (simEnv B) (.varT "typeuse" []) v ∧ TypedV (simEnv B) (.varT "heaptype" []) v
  | .heap, v => TypedV (simEnv B) (.varT "heaptype" []) v
  | .ref, v => TypedV (simEnv B) (.varT "reftype" []) v ∧
      TypedV (simEnv B) (.varT "valtype" []) v ∧ TypedV (simEnv B) (.varT "storagetype" []) v
  | .val, v => TypedV (simEnv B) (.varT "valtype" []) v ∧
      TypedV (simEnv B) (.varT "storagetype" []) v
  | .storage, v => TypedV (simEnv B) (.varT "storagetype" []) v
  | .field, v => TypedV (simEnv B) (.varT "fieldtype" []) v
  | .comp, v => TypedV (simEnv B) (.varT "comptype" []) v
  | .sub, v => TypedV (simEnv B) (.varT "subtype" []) v
  | .group, v => TypedV (simEnv B) (.varT "rectype" []) v
  | .def, v => TypedV (simEnv B) (.varT "deftype" []) v ∧
      TypedV (simEnv B) (.varT "typeuse" []) v ∧ TypedV (simEnv B) (.varT "heaptype" []) v
  | .list k, v => ∃ l, v = .list l ∧ ∀ u ∈ l, TyT B k u

/-- A sequence's elements, read off `TyT`. -/
theorem tyT_list_of {k : TKind} (t : Ty (.list k)) (h : TyT B (.list k) (tyV t)) :
    ∀ u ∈ t.toList.map tyV, TyT B k u := by
  obtain ⟨l, hl, hall⟩ := h
  rw [Equiv.Validation.tyV_list, Value.list.injEq] at hl
  subst hl
  exact hall

/-- `_DEF rectype n`, at every variant it occurs in. -/
theorem tyT_defn {v : Value} (hg : TypedV (simEnv B) (.varT "rectype" []) v) (i : Nat) :
    TyT B .def (.case "_DEF" (.tuple [v, .num (.natN i)])) := by
  have hp := hasTyp_tup2 (a := "rectype") (b := "n") hg ((Typing.stateTyping_simEnv B).nat i)
  exact ⟨Typing.typedV_closedCase findTyp_deftype rfl hp,
    Typing.typedV_closedCase Typing.findTyp_typeuse rfl hp,
    Typing.typedV_closedCase Typing.findTyp_heaptype rfl hp⟩

/-- `REF null? heaptype`, at every variant it occurs in. -/
theorem tyT_ref (n : Bool) {v : Value} (hh : TypedV (simEnv B) (.varT "heaptype" []) v) :
    TyT B .ref (.case "REF" (.tuple [Equiv.Validation.nullV n, v])) := by
  have hp := hasTyp_tup2 (a := "null?") (b := "heaptype") (typedV_nullV (B := B) n) hh
  exact ⟨Typing.typedV_closedCase findTyp_reftype rfl hp,
    Typing.typedV_closedCase Typing.findTyp_valtype rfl hp,
    Typing.typedV_closedCase findTyp_storagetype rfl hp⟩

/-- The bounds of a `cons`. -/
theorem tyBnd_cons {k : TKind} {a : Ty k} {l : Ty (.list k)} :
    Round4.tyBnd (.cons a l) = true ↔ Round4.tyBnd a = true ∧ Round4.tyBnd l = true := by
  simp [Round4.tyBnd]

/-- The bounds of a `STRUCT`. -/
theorem tyBnd_struct {fs : Ty (.list .field)} :
    Round4.tyBnd (.struct fs) = true ↔ fs.toList.length < 2 ^ 32 ∧ Round4.tyBnd fs = true := by
  simp [Round4.tyBnd, Round4.bnd32]

/-- The bounds of a `FUNC`. -/
theorem tyBnd_func {ps rs : Ty (.list .val)} :
    Round4.tyBnd (.func ps rs) = true ↔ (ps.toList.length < 2 ^ 32 ∧ rs.toList.length < 2 ^ 32) ∧
      Round4.tyBnd ps = true ∧ Round4.tyBnd rs = true := by
  simp [Round4.tyBnd, Round4.bnd32, and_assoc]

/-- The bounds of a `SUB`. -/
theorem tyBnd_sub {fin : Bool} {sups : Ty (.list .use)} {body : Ty .comp} :
    Round4.tyBnd (.sub fin sups body) = true ↔
      Round4.tyBnd sups = true ∧ Round4.tyBnd body = true := by
  simp [Round4.tyBnd]

/-- The bounds of a `REC`. -/
theorem tyBnd_group {subs : Ty (.list .sub)} :
    Round4.tyBnd (.group subs) = true ↔
      subs.toList.length < 2 ^ 32 ∧ Round4.tyBnd subs = true := by
  simp [Round4.tyBnd, Round4.bnd32]

/-- `cons`. -/
theorem tyT_cons {k : TKind} {a : Ty k} {l : Ty (.list k)} (ha : TyT B k (tyV a))
    (hl : TyT B (.list k) (tyV l)) : TyT B (.list k) (tyV (.cons a l)) := by
  obtain ⟨l', hl', hall⟩ := hl
  have hv : tyV (Ty.cons a l) = .list (tyV a :: l') := by simp [tyV, hl', Equiv.Validation.consV]
  exact ⟨_, hv, by simpa only [List.mem_cons, forall_eq_or_imp] using ⟨ha, hall⟩⟩

/-- `_IDX x`. -/
theorem tyT_idx {x : Nat} (hx : Round4.tyBnd (Ty.idx x) = true) : TyT B .use (tyV (Ty.idx x)) := by
  have hx' : x < 2 ^ 32 := by simpa [Round4.tyBnd, Round4.bnd32] using hx
  exact ⟨Typing.typedV_closedCase Typing.findTyp_typeuse rfl
      (typedV_typeidxNat hx' _ ⟨rfl, rfl, rfl⟩),
    Typing.typedV_closedCase Typing.findTyp_heaptype rfl
      (typedV_typeidxNat hx' _ ⟨rfl, rfl, rfl⟩)⟩

/-- `REC i`. -/
theorem tyT_recv (i : Nat) : TyT B .use (tyV (Ty.recv i)) :=
  ⟨Typing.typedV_closedCase Typing.findTyp_typeuse rfl
      ((Typing.stateTyping_simEnv B).nat i _ ⟨rfl, rfl, rfl⟩),
    Typing.typedV_closedCase Typing.findTyp_heaptype rfl
      ((Typing.stateTyping_simEnv B).nat i _ ⟨rfl, rfl, rfl⟩)⟩

/-- Number types. -/
theorem tyT_num (t : NumType) : TyT B .val (tyV (Ty.num t)) := by
  rcases t with t | t <;> cases t <;>
    exact ⟨Typing.typedV_closedCase Typing.findTyp_valtype rfl hasTyp_tupT_nil,
      Typing.typedV_closedCase findTyp_storagetype rfl hasTyp_tupT_nil⟩

/-- `STRUCT`. -/
theorem tyT_struct {fs : Ty (.list .field)} (hlen : fs.toList.length < 2 ^ 32)
    (h : TyT B (.list .field) (tyV fs)) : TyT B .comp (tyV (Ty.struct fs)) := by
  have hall : ∀ u ∈ fs.toList.map tyV, TyT B .field u := tyT_list_of fs h
  have hv : tyV (Ty.struct fs) = .case "STRUCT" (.case "%" (.tuple [.list (fs.toList.map tyV)])) :=
    by rw [tyV, Equiv.Validation.tyV_list fs]; rfl
  rw [hv]
  exact Typing.typedV_closedCase findTyp_comptype rfl
    (typedV_listT (by decide) (by simpa using hlen) hall _ ⟨rfl, rfl, rfl⟩)

/-- `FUNC`. -/
theorem tyT_func {ps rs : Ty (.list .val)} (hlp : ps.toList.length < 2 ^ 32)
    (hlr : rs.toList.length < 2 ^ 32) (hp : TyT B (.list .val) (tyV ps))
    (hr : TyT B (.list .val) (tyV rs)) : TyT B .comp (tyV (Ty.func ps rs)) := by
  have hp' : ∀ u ∈ ps.toList.map tyV, TyT B .val u := tyT_list_of ps hp
  have hr' : ∀ u ∈ rs.toList.map tyV, TyT B .val u := tyT_list_of rs hr
  have hv : tyV (Ty.func ps rs) = .case "FUNC%->%" (.tuple
      [.case "%" (.tuple [.list (ps.toList.map tyV)]), .case "%" (.tuple [.list (rs.toList.map tyV)])]) :=
    by rw [tyV, Equiv.Validation.tyV_list ps, Equiv.Validation.tyV_list rs]; rfl
  rw [hv]
  exact Typing.typedV_closedCase findTyp_comptype rfl (hasTyp_tup2
    (typedV_resulttype (by simpa using hlp) fun u hu => (hp' u hu).1)
    (typedV_resulttype (by simpa using hlr) fun u hu => (hr' u hu).1))

/-- `SUB`. -/
theorem tyT_sub (fin : Bool) {sups : Ty (.list .use)} {body : Ty .comp}
    (hs : TyT B (.list .use) (tyV sups)) (hb : TyT B .comp (tyV body)) :
    TyT B .sub (tyV (Ty.sub fin sups body)) := by
  have hs' : ∀ u ∈ sups.toList.map tyV, TyT B .use u := tyT_list_of sups hs
  have hv : tyV (Ty.sub fin sups body) = .case "SUB" (.tuple
      [Equiv.Validation.finalV fin, .list (sups.toList.map tyV), tyV body]) :=
    by rw [tyV, Equiv.Validation.tyV_list sups]
  rw [hv]
  exact Typing.typedV_closedCase findTyp_subtype rfl (hasTyp_tup3 (typedV_finalV fin)
    (typedV_list_iff.2 fun u hu => (hs' u hu).1) hb)

/-- `REC`. -/
theorem tyT_group {subs : Ty (.list .sub)} (hlen : subs.toList.length < 2 ^ 32)
    (h : TyT B (.list .sub) (tyV subs)) : TyT B .group (tyV (Ty.group subs)) := by
  have hall : ∀ u ∈ subs.toList.map tyV, TyT B .sub u := tyT_list_of subs h
  have hv : tyV (Ty.group subs) = .case "REC" (.case "%" (.tuple [.list (subs.toList.map tyV)])) :=
    by rw [tyV, Equiv.Validation.tyV_list subs]; rfl
  rw [hv]
  exact Typing.typedV_closedCase findTyp_rectype rfl
    (typedV_listT (by decide) (by simpa using hlen) hall _ ⟨rfl, rfl, rfl⟩)

/-- Nullary value types. -/
theorem tyT_valNullary {op : MixopS}
    (hv : IntNumeric.findCase (IntNumeric.recCases Original.d95 2 0) op = some (.tupT [], []))
    (hs : IntNumeric.findCase (IntNumeric.recCases Original.d95 3 0) op = some (.tupT [], [])) :
    TyT B .val (.case op (.tuple [])) :=
  ⟨Typing.typedV_closedCase Typing.findTyp_valtype hv hasTyp_tupT_nil,
    Typing.typedV_closedCase findTyp_storagetype hs hasTyp_tupT_nil⟩

set_option maxRecDepth 100000 in
/-- **Every bounded runtime type is typed** at its sort (`TyT`), in every `simEnv B`. -/
theorem tyT_tyV : ∀ {k : TKind} (t : Ty k), Round4.tyBnd t = true → TyT B k (tyV t) := by
  intro k t
  induction t with
  | nil => exact fun _ => ⟨[], rfl, by simp⟩
  | cons a l iha ihl => exact fun h => tyT_cons (iha (tyBnd_cons.1 h).1) (ihl (tyBnd_cons.1 h).2)
  | idx x => exact tyT_idx
  | recv i => exact fun _ => tyT_recv i
  | dt d ih => exact fun h => (ih h).2
  | defn g i ih => exact fun h => tyT_defn (ih h) i
  | abs a =>
    intro _
    cases a <;> exact Typing.typedV_closedCase Typing.findTyp_heaptype rfl hasTyp_tupT_nil
  | bot => exact fun _ => Typing.typedV_closedCase Typing.findTyp_heaptype rfl hasTyp_tupT_nil
  | use u ih => exact fun h => (ih h).2
  | ref n hp ih => exact fun h => tyT_ref n (ih h)
  | num t => exact fun _ => tyT_num t
  | vec t => exact fun _ => by cases t; exact tyT_valNullary rfl rfl
  | refv r ih => exact fun h => (ih h).2
  | botv => exact fun _ => tyT_valNullary rfl rfl
  | val t ih => exact fun h => (ih h).2
  | pack p =>
    intro _
    cases p <;> exact Typing.typedV_closedCase findTyp_storagetype rfl hasTyp_tupT_nil
  | field m s ih =>
    exact fun h => Typing.typedV_closedCase findTyp_fieldtype rfl
      (hasTyp_tup2 (ConfigOk.typedV_mut m) (ih h))
  | struct fs ih => exact fun h => tyT_struct (tyBnd_struct.1 h).1 (ih (tyBnd_struct.1 h).2)
  | array f ih =>
    exact fun h => Typing.typedV_closedCase findTyp_comptype rfl (ih h _ ⟨rfl, rfl, rfl⟩)
  | func ps rs ihp ihr =>
    exact fun h => tyT_func (tyBnd_func.1 h).1.1 (tyBnd_func.1 h).1.2 (ihp (tyBnd_func.1 h).2.1)
      (ihr (tyBnd_func.1 h).2.2)
  | sub fin sups body ihs ihb =>
    exact fun h => tyT_sub fin (ihs (tyBnd_sub.1 h).1) (ihb (tyBnd_sub.1 h).2)
  | group subs ih => exact fun h => tyT_group (tyBnd_group.1 h).1 (ih (tyBnd_group.1 h).2)

/-- **Every bounded defined type is a `deftype`.** -/
theorem typedV_deftype (d : DefType) (h : Round4.tyBnd d = true) :
    TypedV (simEnv B) (.varT "deftype" []) (tyV d) := (tyT_tyV d h).1

/-- **`PosTypingNE.callRefType`**, without validity. -/
theorem typedV_callRefType (d : DefType) (h : Round4.tyBnd d = true) :
    TypedV (simEnv B) (.varT "instr" []) (adminToV (.callRefType d)) :=
  FwdMem.typedV_instrCase rfl rfl ((tyT_tyV d h).2.1 _ ⟨rfl, rfl, rfl⟩)

set_option maxRecDepth 100000 in
/-- **`PosTypingNE.returnCallRefType`**, without validity. -/
theorem typedV_returnCallRefType (d : DefType) (h : Round4.tyBnd d = true) :
    TypedV (simEnv B) (.varT "instr" []) (adminToV (.returnCallRefType d)) :=
  FwdMem.typedV_instrCase rfl rfl ((tyT_tyV d h).2.1 _ ⟨rfl, rfl, rfl⟩)

end Silmaril.Wasm.SpecTec.Sim.Round5.Pos
