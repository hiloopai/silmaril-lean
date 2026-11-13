module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkInv

/-!
# `InvokeTy`: function types and module instances

`InvokeTy` asks for every function type of the store and every module instance to be typed in
`simEnv20`. Here both are reduced to plain conditions on the V2 values.

* **`typedV_funcType20`**: `ft` is a `functype` when it has fewer than `2 ^ 32` parameters and
  fewer than `2 ^ 32` results. `resulttype` is `list(valtype)`, and `list(X)` carries the premise
  `|X*| < 2 ^ 32`; that bound is the whole condition, since every V2 value type is a `valtype`.
* **`typedV_moduleInst20`**: a module instance is a `moduleinst` when its function types are
  bounded (`TypesSmall`) and every export name is a `name`. Addresses and extern addresses are
  typed in general.
* `typedV_name_nil20`: the empty name is a `name` (checked by evaluation).
* **`invokeTy_of`**: `InvokeTy` from `TypesSmall` of every function type and module, typed export
  names, and the erased bodies typed (`InvokeOk`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreBulk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim20.Whole (typedV_structG hasTypFields_consG hasTypFields_oneG
  typedV_aliasG)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-- Builtins that answer nothing, to name `simEnv20`'s type definitions. -/
def noBuiltins : Builtins := ⟨fun _ _ => none⟩

/-! ## Environments with the 2.0 script's types -/

/-- **An environment with the 2.0 script's type definitions**: `simEnv20 B` for every `B`, and
the `$utf8` erratum `utf8Env20 B` (`StoreBulkUtf8`), which changes only a definition. -/
def Types20 (e : Env) : Prop := e.typs = baseEnv20.typs

theorem types20_simEnv20 (B : Builtins) : Types20 (E20 B) := rfl

/-- A type definition of `simEnv20 B` is one of every `Types20` environment. -/
theorem Types20.find {e : Env} (h : Types20 e) {x : IL.Id} {r : Option TypDef}
    (hr : (E20 B).findTyp? x = r) : e.findTyp? x = r := by
  rw [← hr]
  show e.typs.find? x = (E20 B).typs.find? x
  rw [h]
  rfl

theorem Types20.memTyp {e : Env} (h : Types20 e) (x : IL.Id) :
    e.memTyp x = baseEnv20.memTyp x := by
  unfold Env.memTyp
  rw [h]

variable {e : Env}

/-! ## `list(X)` and `resulttype` -/

/-- `list(X)`'s premise, `|X*| < 2 ^ 32`. -/
def listPrem20 : Exp := .cmpE .ltOp (.numT .natT)
  (.lenE (.iterE (.varE "X") (.mk .list [.mk "X" (.varE "X*")])))
  (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.numE (.natN 32)))

theorem findTyp_list20 : (E20 B).findTyp? "list" = some ([.typP "X"],
    [.instD [.typP "X"] [.typA (.varT "X" [])] (.variantT [.mk "%"
      (.tupT [.mk "X*" (.iterT (.varT "X" []) .list)]) [] [.ifPr listPrem20]])]) := rfl

theorem memTyp_X20 : baseEnv20.memTyp "X" = false := by rfl

theorem findTyp_resulttype20 : (E20 B).findTyp? "resulttype" =
    some ([], [.instD [] [] (.aliasT (.varT "list" [.typA (.varT "valtype" [])]))]) := rfl

theorem findTyp_functype20 : (E20 B).findTyp? "functype" = some ([], [.instD [] []
    (.variantT [.mk "%->%" (.tupT [.mk "resulttype" (.varT "resulttype" []),
      .mk "resulttype" (.varT "resulttype" [])]) [] []])]) := rfl

/-- A closed named type, in a scope that does not bind it as a type variable. -/
theorem hasTyp_varT_global_congrE {σ : VarEnv} {y : IL.Id} {u : Value}
    (hσ : σ.findTyp? y = none) (h : TypedV e (.varT y []) u) :
    HasTyp e σ (.varT y []) u := by
  have h0 := h VarEnv.empty ⟨rfl, rfl, rfl⟩
  obtain ⟨td, ws, htd, hargs, hi⟩ := (hasTyp_varT_global_iff (ρ := VarEnv.empty) rfl).1 h0
  obtain rfl := Equiv.Validation.evalArgs_nil_iff.1 hargs
  exact (hasTyp_varT_global_iff (by simpa [localTyp?] using hσ)).2
    ⟨td, [], htd, Equiv.evalArgs_nil, hi⟩

/-- `list(X)`'s premise holds below `2 ^ 32` elements, in every environment. -/
theorem evalExp_listPrem20 {σ : VarEnv} {l : List Value} (hl : l.length < 2 ^ 32) :
    EvalExp e (σ.bindVal "X*" (.list l)) listPrem20 (.bool true) := by
  have hit : EvalExp e (σ.bindVal "X*" (.list l))
      (.iterE (.varE "X") (.mk .list [.mk "X" (.varE "X*")])) (.list (l.map id)) :=
    Sim.evalExp_iterMap (by simp)
      (fun w _ => evalExp_varE_iff.2
        (by simp [VarEnv.bindVals, VarEnv.findVal?, Map.binds, Map.bind]))
  rw [List.map_id] at hit
  refine evalExp_cmpE_iff.2 ⟨_, .num (.natN (2 ^ 32)), evalExp_lenE_iff.2 ⟨_, hit, rfl⟩,
    evalExp_twoPowE (evalExp_numE_iff.2 rfl), ?_⟩
  simpa [cmpValues, Num.cmp] using hl

/-- **`list(y)`**: fewer than `2 ^ 32` typed elements. -/
theorem hasTyp_listTE (hE : Types20 e) {ρ : VarEnv} (hρ : Sim.ValsOnly ρ) {y : IL.Id}
    (hy : y ≠ "X") {l : List Value} (hl : l.length < 2 ^ 32)
    (hall : ∀ u ∈ l, TypedV e (.varT y []) u) :
    HasTyp e ρ (.varT "list" [.typA (.varT y [])]) (.case "%" (.tuple [.list l])) := by
  have hargs : EvalArgs e ρ [.typA (.varT y [])] [.typ (.varT y [])] :=
    ⟨2, by simp [evalArgs, evalArg, resolveTyp, VarEnv.findTyp?, hρ.1]⟩
  have hm : MatchArgs e VarEnv.empty [.typA (.varT "X" [])] [.typ (.varT y [])]
      (VarEnv.empty.bindTyp "X" (.varT y [])) :=
    ⟨2, by simp [matchArgs, matchArg, matchTypV, hE.memTyp, memTyp_X20, VarEnv.findTyp?,
      VarEnv.empty, Map.find?, Map.empty]⟩
  refine hasTyp_varT_case rfl (hE.find (findTyp_list20 (B := noBuiltins))) hargs hm
    (Sim.IntNumeric.hasTypCase_of_findCase rfl ?_
      (Sim.IntNumeric.premsOk_if (evalExp_listPrem20 hl)))
  refine hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    hasTyp_iterT_list_iff.2 ⟨l, rfl, hasTypList_iff.2 fun u hu => ?_⟩, hasTypTup_nil_iff.2 rfl⟩⟩
  refine (hasTyp_varT_local_iff (t := .varT y []) ?_).2
    (hasTyp_varT_global_congrE ?_ (hall u hu))
  · simp [localTyp?, VarEnv.findTyp?, VarEnv.bindTyp, Map.bind, VarEnv.empty]
  · simp [VarEnv.findTyp?, VarEnv.bindTyp, Map.bind, Map.find?, VarEnv.empty, Map.empty,
      Ne.symm hy]

/-- Every 2.0 value type is a `valtype`, in every `Types20` environment. -/
theorem typedV_valTypeE (hE : Types20 e) (t : V2.ValType) :
    TypedV e (.varT "valtype" []) (valTypeV t) := by
  rcases t with ((_ | _) | (_ | _)) | ⟨⟩ | (_ | _) <;>
    exact Pure.typedV_closedCase20 (hE.find (Whole.findTyp_valtype20 (B := noBuiltins))) rfl
      hasTyp_tupT_nil

/-- **`resulttype`**: fewer than `2 ^ 32` value types. -/
theorem typedV_resultTypeE (hE : Types20 e) {ts : List V2.ValType} (hl : ts.length < 2 ^ 32) :
    TypedV e (.varT "resulttype" []) (resultTypeV ts) := fun ρ hρ =>
  hasTyp_varT_of_insts (by simp [localTyp?, VarEnv.findTyp?, hρ.1])
    (hE.find (findTyp_resulttype20 (B := noBuiltins))) Equiv.evalArgs_nil
    (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2
      (hasTyp_listTE hE ⟨rfl, rfl, rfl⟩ (by decide) (by simpa using hl) fun u hu => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.1 hu
        exact typedV_valTypeE hE t)))

/-- **A function type with fewer than `2 ^ 32` parameters and results is a `functype`**, in
every `Types20` environment. -/
theorem typedV_funcTypeE (hE : Types20 e) {ft : V2.FuncType} (hp : ft.params.length < 2 ^ 32)
    (hr : ft.results.length < 2 ^ 32) :
    TypedV e (.varT "functype" []) (funcTypeV ft) :=
  Pure.typedV_closedCase20 (hE.find (findTyp_functype20 (B := noBuiltins))) rfl
    (Whole.hasTyp_tup2G (typedV_resultTypeE hE hp) (typedV_resultTypeE hE hr))

/-- **A function type with fewer than `2 ^ 32` parameters and results is a `functype`.** -/
theorem typedV_funcType20 {ft : V2.FuncType} (hp : ft.params.length < 2 ^ 32)
    (hr : ft.results.length < 2 ^ 32) :
    TypedV (E20 B) (.varT "functype" []) (funcTypeV ft) :=
  typedV_funcTypeE (types20_simEnv20 B) hp hr

/-! ## Module instances -/

/-- **A function type within SpecTec's bound**: fewer than `2 ^ 32` parameters and results. -/
def FuncTypeSmall (ft : V2.FuncType) : Prop :=
  ft.params.length < 2 ^ 32 ∧ ft.results.length < 2 ^ 32

/-- Every function type of a module instance is within SpecTec's bound. -/
def TypesSmall (m : ModuleInst) : Prop := ∀ ft ∈ m.types, FuncTypeSmall ft

theorem findTyp_exportinst20 : (E20 B).findTyp? "exportinst" = some ([], [.instD [] []
    (.structT [.mk "NAME" (.varT "name" []) [] [], .mk "ADDR" (.varT "externaddr" []) [] []])]) :=
  rfl

theorem findTyp_externaddr20 : (E20 B).findTyp? "externaddr" = some ([], [.instD [] []
    (.variantT [.mk "FUNC" (.varT "funcaddr" []) [] [], .mk "GLOBAL" (.varT "globaladdr" []) [] [],
      .mk "TABLE" (.varT "tableaddr" []) [] [], .mk "MEM" (.varT "memaddr" []) [] []])]) := rfl

theorem findTyp_moduleinst20 : (E20 B).findTyp? "moduleinst" = some ([], [.instD [] []
    (.structT [.mk "TYPES" (.iterT (.varT "functype" []) .list) [] [],
      .mk "FUNCS" (.iterT (.varT "funcaddr" []) .list) [] [],
      .mk "GLOBALS" (.iterT (.varT "globaladdr" []) .list) [] [],
      .mk "TABLES" (.iterT (.varT "tableaddr" []) .list) [] [],
      .mk "MEMS" (.iterT (.varT "memaddr" []) .list) [] [],
      .mk "ELEMS" (.iterT (.varT "elemaddr" []) .list) [] [],
      .mk "DATAS" (.iterT (.varT "dataaddr" []) .list) [] [],
      .mk "EXPORTS" (.iterT (.varT "exportinst" []) .list) [] []])]) := rfl

theorem findTyp_globaladdr20 : (E20 B).findTyp? "globaladdr" =
    some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl
theorem findTyp_tableaddr20 : (E20 B).findTyp? "tableaddr" =
    some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl
theorem findTyp_memaddr20 : (E20 B).findTyp? "memaddr" =
    some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl
theorem findTyp_elemaddr20 : (E20 B).findTyp? "elemaddr" =
    some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl
theorem findTyp_dataaddr20 : (E20 B).findTyp? "dataaddr" =
    some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl

/-- An address at an alias of `addr`. -/
theorem typedV_addrAliasE (hE : Types20 e) {x : IL.Id}
    (htd : (E20 B).findTyp? x = some ([], [.instD [] [] (.aliasT (.varT "addr" []))])) (k : Nat) :
    TypedV e (.varT x []) (.num (.natN k)) :=
  typedV_aliasG (hE.find htd)
    (typedV_aliasG (hE.find (Whole.findTyp_addr20 (B := noBuiltins))) (Whole.hasTyp_nat _ _ k) _
      ⟨rfl, rfl, rfl⟩)

/-- A list of addresses at an alias of `addr`. -/
theorem typedV_addrsE (hE : Types20 e) {x : IL.Id}
    (htd : (E20 B).findTyp? x = some ([], [.instD [] [] (.aliasT (.varT "addr" []))]))
    (xs : List Nat) : TypedV e (.iterT (.varT x []) .list) (addrsV xs) :=
  Sim.typedV_list_iff.2 fun u hu => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hu
    exact typedV_addrAliasE hE htd k

/-- **Every extern address is an `externaddr`.** -/
theorem typedV_externAddrE (hE : Types20 e) (a : ExternAddr) :
    TypedV e (.varT "externaddr" []) (externAddrV a) := by
  have hx := hE.find (findTyp_externaddr20 (B := noBuiltins))
  cases a with
  | func k =>
    exact Pure.typedV_closedCase20 hx (op := "FUNC") rfl
      (typedV_addrAliasE hE (Whole.findTyp_funcaddr20 (B := noBuiltins)) k _ ⟨rfl, rfl, rfl⟩)
  | global k =>
    exact Pure.typedV_closedCase20 hx (op := "GLOBAL") rfl
      (typedV_addrAliasE hE (findTyp_globaladdr20 (B := noBuiltins)) k _ ⟨rfl, rfl, rfl⟩)
  | table k =>
    exact Pure.typedV_closedCase20 hx (op := "TABLE") rfl
      (typedV_addrAliasE hE (findTyp_tableaddr20 (B := noBuiltins)) k _ ⟨rfl, rfl, rfl⟩)
  | mem k =>
    exact Pure.typedV_closedCase20 hx (op := "MEM") rfl
      (typedV_addrAliasE hE (findTyp_memaddr20 (B := noBuiltins)) k _ ⟨rfl, rfl, rfl⟩)

/-- Every export name of a module instance is a `name` of `e`. -/
def NamesTypedIn (e : Env) (m : ModuleInst) : Prop :=
  ∀ x ∈ m.exports, TypedV e (.varT "name" []) (nameV x.name)

/-- Every export name of a module instance is a `name` of `simEnv20 B`. -/
abbrev NamesTyped (B : Builtins) (m : ModuleInst) : Prop := NamesTypedIn (E20 B) m

/-- **A module instance is a `moduleinst`** of every `Types20` environment when its function
types are within SpecTec's bound and its export names are `name`s there. -/
theorem typedV_moduleInstE (hE : Types20 e) {m : ModuleInst} (ht : TypesSmall m)
    (hx : NamesTypedIn e m) : TypedV e (.varT "moduleinst" []) (moduleInstV m) := by
  have hT : TypedV e (.iterT (.varT "functype" []) .list) (.list (m.types.map funcTypeV)) :=
    Sim.typedV_list_iff.2 fun u hu => by
      obtain ⟨ft, hft, rfl⟩ := List.mem_map.1 hu
      exact typedV_funcTypeE hE (ht ft hft).1 (ht ft hft).2
  have hX : TypedV e (.iterT (.varT "exportinst" []) .list) (.list (m.exports.map fun x =>
      .struct [("NAME", nameV x.name), ("ADDR", externAddrV x.addr)])) :=
    Sim.typedV_list_iff.2 fun u hu => by
      obtain ⟨x, hxm, rfl⟩ := List.mem_map.1 hu
      exact typedV_structG (hE.find (findTyp_exportinst20 (B := noBuiltins))) (hasTypFields_consG
        (hx x hxm) (hasTypFields_oneG (typedV_externAddrE hE x.addr)))
  exact typedV_structG (hE.find (findTyp_moduleinst20 (B := noBuiltins))) (hasTypFields_consG hT
    (hasTypFields_consG (typedV_addrsE hE (Whole.findTyp_funcaddr20 (B := noBuiltins)) m.funcs)
    (hasTypFields_consG (typedV_addrsE hE (findTyp_globaladdr20 (B := noBuiltins)) m.globals)
    (hasTypFields_consG (typedV_addrsE hE (findTyp_tableaddr20 (B := noBuiltins)) m.tables)
    (hasTypFields_consG (typedV_addrsE hE (findTyp_memaddr20 (B := noBuiltins)) m.mems)
    (hasTypFields_consG (typedV_addrsE hE (findTyp_elemaddr20 (B := noBuiltins)) m.elems)
    (hasTypFields_consG (typedV_addrsE hE (findTyp_dataaddr20 (B := noBuiltins)) m.datas)
      (hasTypFields_oneG hX))))))))

/-- **A module instance is a `moduleinst`** of `simEnv20 B` when its function types are within
SpecTec's bound and its export names are `name`s. -/
theorem typedV_moduleInst20 {m : ModuleInst} (ht : TypesSmall m) (hx : NamesTyped B m) :
    TypedV (E20 B) (.varT "moduleinst" []) (moduleInstV m) :=
  typedV_moduleInstE (types20_simEnv20 B) ht hx

set_option maxHeartbeats 1000000 in
/-- **The empty name is a `name`** of `simEnv20 B`: `$utf8([]) = []` (checked by evaluation). -/
theorem typedV_name_nil20 : TypedV (E20 B) (.varT "name" []) (nameV "") :=
  Whole.typedV_of_empty20 ⟨100, by with_unfolding_all rfl⟩

/-- A module instance without exports has its names typed. -/
theorem namesTyped_of_nil {m : ModuleInst} (h : m.exports = []) : NamesTypedIn e m := by
  intro x hx
  simp [h] at hx

/-- A module instance whose export names are all empty has its names typed in `simEnv20 B`. -/
theorem namesTyped_of_empty {m : ModuleInst} (h : ∀ x ∈ m.exports, x.name = "") :
    NamesTyped B m := by
  intro x hx
  rw [h x hx]
  exact typedV_name_nil20

/-! ## `InvokeTy` -/

/-- **What `InvokeTy` reduces to**: for the frame's module and every function of the store,
bounded function types and typed export names, and every function a Wasm function whose erased
body is an `instr*` of `simEnv20`. -/
structure InvokeOk (B : Builtins) (s : Store H) (f : Frame) : Prop where
  frameTypes : TypesSmall f.module
  frameNames : NamesTyped B f.module
  funcs : ∀ fi ∈ s.funcs, ∃ fn, fi.code = .wasm fn ∧ FuncTypeSmall fi.type ∧
    TypesSmall fi.module ∧ NamesTyped B fi.module ∧
    TypedV (E20 B) Pure.instrsT (.list (instrsToV (fn.body.map StoreDeep.eD)))

/-- **`InvokeTy` from `InvokeOk`.** -/
theorem invokeTy_of {s : Store H} {f : Frame} (h : InvokeOk B s f) : InvokeTy B s f where
  frame := typedV_moduleInst20 h.frameTypes h.frameNames
  funcs fi hfi := by
    obtain ⟨fn, hc, hty, hts, hns, hb⟩ := h.funcs fi hfi
    exact ⟨fn, hc, typedV_funcType20 hty.1 hty.2, typedV_moduleInst20 hts hns, hb⟩

/-- **`Good20B` at an invocation `val* (CALL_ADDR a)`**, from `InvokeOk`, a `StoreOkB` store and
`StoreSmall`. -/
theorem good20B_invoke_ok {P : Silmaril.Wasm.Numerics.Profile} {s : Store H} {f : Frame}
    {args : List Val} {a : FuncAddr} (h : InvokeOk (Whole.storeB P) s f) (hs : StoreOkB s)
    (hm : StoreSmall s) : Good20B hn P ⟨s, f, vals args ++ [.callAddr a]⟩ :=
  good20B_invoke_of (invokeTy_of h) hs hm

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
