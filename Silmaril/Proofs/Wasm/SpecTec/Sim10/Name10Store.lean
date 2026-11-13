module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Name10

/-!
# A non-empty export name makes the 1.0 state untypable

From `Name10`: a non-empty string is not a 1.0 `name`. Up the store, in every environment with
the 1.0 `moduleinst`, `exportinst`, `funcinst` and `store` (`StoreEnv10`; both `simEnv10 B` and
`simEnv10T B` are):

* `not_hasTyp_moduleInst10_ne`: a module instance with an export of a non-empty name is not a
  `moduleinst`;
* `not_hasTyp_funcInst10_ne`: nor is a defined function instance whose module instance has one;
* `not_typedV_store10_ne`: nor is a store holding such a function instance;
* **`not_typed10_export_ne`**, **`not_typed10T_export_ne`**: no configuration over such a store
  has a typed image.

`not_typed10_add`, `not_typed10T_add`: the round 6 observation. Silmaril's `addModule` (export
`"add"`) instantiated into the empty store gives a store over which no invocation is typed. The
same holds for any other non-empty export name, such as `"a"`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Name10

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Validation.Examples (addModule addType addBody addModule_valid)
open Silmaril.Wasm.V1.Execution (Store Config HostSemantics prepare? Instantiation)
open Silmaril.Wasm.Execution.Runtime (ModuleInst ExportInst FuncInst Frame)
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Valid (invokeCfg10)
open Silmaril.Wasm.SpecTec.Sim20.Whole (hasTypFields_of_closed hasTypFields_cons_nil_iff
  typedV_of_empty20)

set_option maxRecDepth 100000

/-- The 1.0 record types from `name` up to `store`. -/
structure StoreEnv10 (env : Env) : Prop where
  name : NameEnv10 env
  exportinst : env.findTyp? "exportinst" = some ([], [.instD [] []
    (.structT [.mk "NAME" (.varT "name" []) [] [], .mk "ADDR" (.varT "externaddr" []) [] []])])
  moduleinst : ∃ t₁ t₂ t₃ t₄ t₅ : Typ, env.findTyp? "moduleinst" = some ([], [.instD [] []
    (.structT [.mk "TYPES" t₁ [] [], .mk "FUNCS" t₂ [] [], .mk "GLOBALS" t₃ [] [],
      .mk "TABLES" t₄ [] [], .mk "MEMS" t₅ [] [],
      .mk "EXPORTS" (.iterT (.varT "exportinst" []) .list) [] []])])
  funcinst : ∃ t₁ t₃ : Typ, env.findTyp? "funcinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" t₁ [] [], .mk "MODULE" (.varT "moduleinst" []) [] [],
      .mk "CODE" t₃ [] []])])
  store : ∃ rest, env.findTyp? "store" = some ([], [.instD [] []
    (.structT (.mk "FUNCS" (.iterT (.varT "funcinst" []) .list) [] [] :: rest))])

set_option maxRecDepth 8000000 in
theorem storeEnv10 (B : Builtins) : StoreEnv10 (simEnv10 B) :=
  ⟨nameEnv10 B, rfl, ⟨_, _, _, _, _, rfl⟩, ⟨_, _, rfl⟩, Whole.findTyp_store10⟩

set_option maxRecDepth 8000000 in
theorem storeEnv10T (B : Builtins) : StoreEnv10 (simEnv10T B) :=
  ⟨nameEnv10T B, rfl, ⟨_, _, _, _, _, rfl⟩, ⟨_, _, rfl⟩, Whole.findTyp_store10T⟩

variable {env : Env}

/-- An element of a typed list over a closed type name is typed. -/
theorem hasTyp_mem_list {x : IL.Id} {l : List Value} {u : Value}
    (h : HasTyp env VarEnv.empty (.iterT (.varT x []) .list) (.list l)) (hu : u ∈ l) :
    HasTyp env VarEnv.empty (.varT x []) u := by
  obtain ⟨l', he, hl⟩ := hasTyp_iterT_list_iff.1 h
  obtain rfl := Value.list.inj he
  exact hasTypList_iff.1 hl u hu

/-- **A module instance with an export of a non-empty name is not a `moduleinst`.** -/
theorem not_hasTyp_moduleInst10_ne (hE : StoreEnv10 env) {m : ModuleInst} {x : ExportInst}
    (hx : x ∈ m.exports) (hne : x.name ≠ "") :
    ¬ HasTyp env VarEnv.empty (.varT "moduleinst" []) (moduleInstV m) := by
  intro h
  obtain ⟨t₁, t₂, t₃, t₄, t₅, hmod⟩ := hE.moduleinst
  have hF := hasTypFields_of_closed hmod (typedV_of_empty20 h)
  obtain ⟨-, hF⟩ := hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := hasTypFields_cons_nil_iff.1 hF
  obtain ⟨-, hF⟩ := hasTypFields_cons_nil_iff.1 hF
  obtain ⟨hX, -⟩ := hasTypFields_cons_nil_iff.1 hF
  have hx' := hasTyp_mem_list hX (List.mem_map_of_mem (f := fun e : ExportInst =>
    Value.struct [("NAME", Sim20.nameV e.name), ("ADDR", externAddrV e.value)]) hx)
  have hN := hasTypFields_of_closed hE.exportinst (typedV_of_empty20 hx')
  obtain ⟨hN, -⟩ := hasTypFields_cons_nil_iff.1 hN
  exact not_hasTyp_nameV_ne10 hE.name hne hN

/-- **A defined function instance whose module exports a non-empty name is not a
`funcinst`.** -/
theorem not_hasTyp_funcInst10_ne {H : Type} (hn : H → String) (hE : StoreEnv10 env)
    {t : V1.FuncType} {m : ModuleInst} {fn : V1.Func} {x : ExportInst}
    (hx : x ∈ m.exports) (hne : x.name ≠ "") :
    ¬ HasTyp env VarEnv.empty (.varT "funcinst" []) (funcInstV hn (.wasm t m fn)) := by
  intro h
  obtain ⟨t₁, t₃, hfi⟩ := hE.funcinst
  have hF := hasTypFields_of_closed hfi (typedV_of_empty20 h)
  obtain ⟨-, hF⟩ := hasTypFields_cons_nil_iff.1 hF
  obtain ⟨hM, -⟩ := hasTypFields_cons_nil_iff.1 hF
  exact not_hasTyp_moduleInst10_ne hE hx hne hM

/-- **A store holding such a function instance is not a `store`.** -/
theorem not_hasTyp_store10_ne {H : Type} (hn : H → String) (hE : StoreEnv10 env) {s : Store H}
    {i : Nat} {t : V1.FuncType} {m : ModuleInst} {fn : V1.Func} {x : ExportInst}
    (hs : s.funcs[i]? = some (.wasm t m fn)) (hx : x ∈ m.exports) (hne : x.name ≠ "") :
    ¬ TypedV env (.varT "store" []) (storeV hn s) := by
  intro h
  obtain ⟨rest, hst⟩ := hE.store
  have hF := hasTypFields_of_closed hst h
  obtain ⟨w, gs', he, hw, -, -⟩ := hasTypFields_cons_iff.1 hF
  obtain ⟨he', -⟩ := List.cons.inj he
  obtain rfl := (Prod.mk.inj he').2
  exact not_hasTyp_funcInst10_ne hn hE hx hne
    (hasTyp_mem_list hw (List.mem_map_of_mem (List.mem_of_getElem? hs)))

/-- **No configuration over such a store has a typed image** (`simEnv10 B`). -/
theorem not_typed10_export_ne {H : Type} (hn : H → String) (B : Builtins) {c : Config H}
    {i : Nat} {t : V1.FuncType} {m : ModuleInst} {fn : V1.Func} {x : ExportInst}
    (hs : c.store.funcs[i]? = some (.wasm t m fn)) (hx : x ∈ m.exports) (hne : x.name ≠ "") :
    ¬ Typed10 (simEnv10 B) hn c := fun h =>
  not_hasTyp_store10_ne hn (storeEnv10 B) hs hx hne
    (Whole.typedV_stV_iff10.1 (Whole.typedV_state_of_typed10 h)).1

/-- **The same in `simEnv10T B`.** -/
theorem not_typed10T_export_ne {H : Type} (hn : H → String) (B : Builtins) {c : Config H}
    {i : Nat} {t : V1.FuncType} {m : ModuleInst} {fn : V1.Func} {x : ExportInst}
    (hs : c.store.funcs[i]? = some (.wasm t m fn)) (hx : x ∈ m.exports) (hne : x.name ≠ "") :
    ¬ Typed10 (simEnv10T B) hn c := fun h =>
  not_hasTyp_store10_ne hn (storeEnv10T B) hs hx hne
    (Whole.typedV_stV_iff10T.1 (Whole.typedV_state_of_typed10T h)).1

/-! ## The observed case: `addModule`, exporting `"add"` -/

/-- The store `prepare?` allocates for `addModule` in the empty store. -/
def addStoreN : Store Empty :=
  match prepare? ({} : Store Empty) addModule [] with
  | some p => p.store
  | none => {}

/-- The module instance it allocates. -/
def addModN : ModuleInst :=
  match prepare? ({} : Store Empty) addModule [] with
  | some p => p.module
  | none => {}

theorem prep_addN : prepare? ({} : Store Empty) addModule [] = some ⟨addStoreN, addModN, []⟩ :=
  rfl

/-- **The V1 instantiation of `addModule` into the empty store**, under every host. -/
theorem inst_addN (host : HostSemantics Empty) :
    Instantiation host {} addModule [] addStoreN addModN (.values []) :=
  ⟨addModule_valid, .nil, _, prep_addN, rfl, .refl⟩

theorem addStoreN_funcs : addStoreN.funcs[0]? = some (.wasm addType addModN ⟨⟨0⟩, [], addBody⟩) :=
  rfl

theorem export_addN : (⟨"add", .func ⟨0⟩⟩ : ExportInst) ∈ addModN.exports := by
  decide

/-- **No configuration over the instantiated `addModule` has a typed image**, in particular the
invocation of `add` on `1, 2`: the export name `"add"` is not a 1.0 `name`. -/
theorem not_typed10_add (B : Builtins) (c : Config Empty) (hc : c.store = addStoreN) :
    ¬ Typed10 (simEnv10 B) Empty.elim c :=
  not_typed10_export_ne Empty.elim B (hc ▸ addStoreN_funcs) export_addN (by decide)

/-- **The same in `simEnv10T B`.** -/
theorem not_typed10T_add (B : Builtins) (c : Config Empty) (hc : c.store = addStoreN) :
    ¬ Typed10 (simEnv10T B) Empty.elim c :=
  not_typed10T_export_ne Empty.elim B (hc ▸ addStoreN_funcs) export_addN (by decide)

/-- The invocation of `add` on `1, 2`. -/
theorem not_typed10_add_invoke (B : Builtins) :
    ¬ Typed10 (simEnv10 B) Empty.elim
      (invokeCfg10 addStoreN InstWitness10.addArgs ⟨0⟩) ∧
    ¬ Typed10 (simEnv10T B) Empty.elim
      (invokeCfg10 addStoreN InstWitness10.addArgs ⟨0⟩) :=
  ⟨not_typed10_add B _ rfl, not_typed10T_add B _ rfl⟩

end Silmaril.Wasm.SpecTec.Sim10.Name10
