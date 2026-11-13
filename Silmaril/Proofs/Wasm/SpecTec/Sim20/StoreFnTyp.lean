module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreFnStore

/-!
# States whose functions hold stores, typed in `simEnv20T`

* `eraseFI`, `eraseS`: the store with every Wasm function body deeply erased (`StoreDeep.eD`:
  every scalar store becomes `nop`, at every depth).
* `StoreOkD s`: every function of `s` is a Wasm function whose body is `ctrlOkD` (round 5's
  covered code with scalar stores at every depth) in its own module.
* **`typedT_state_of_erased`**: if the erased state is typed in `simEnv20` and `StoreOkD` holds,
  the state itself is typed in `simEnv20T`. The store is taken apart field by field
  (`Whole.typedV_storeV_iff`); every field but `FUNCS` is relation-free and moves as is; each
  function instance is taken apart (`TYPE`, `MODULE`, `CODE = FUNC x local* instr*`) and its body
  is typed in `simEnv20T` 's `typedT_instrs_of_eD`.
* The converse parts, in `simEnv20T`: a typed state gives typed function instances, modules,
  codes and bodies (`typedT_funcInst_of_state`, `typedT_funcInst_parts`, `typedT_body_of_func`),
  which `call_addr` needs as quantifiers.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreFn

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly stateT storeT frameT)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.StoreDeep (eD ctrlOkD)
open Silmaril.Wasm.SpecTec.Sim20.Whole (codeV20 funcInstV_wasm hasTypFields_of_closed
  hasTypFields_cons_nil_iff typedV_of_empty20 typedV_list_of_empty20 typedV_of_valsOnly20
  typedV_list_of_valsOnly20 hasTypDef_of_closed typedV_structG hasTypFields_consG hasTypFields_oneG
  typedV_aliasG typedV_struct2 hasTyp_struct2_fst hasTyp_struct2_snd valsOnly_empty)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## Type declarations in `simEnv20T` -/

/-- **Off `instr` and `admininstr`, `simEnv20T` finds what `simEnv20` finds.** -/
theorem findTypT_off (y : IL.Id) (ha : y ≠ "admininstr") (hi : y ≠ "instr") :
    (simEnv20T B).findTyp? y = (E20 B).findTyp? y := by
  have ht := (StoreAgree.simEnv20T_tables B).1
  have h : (simEnv20T B).findTyp? y = (StepFix.simEnv20S B).findTyp? y := by
    simp only [Env.findTyp?, ht, StoreAgree.find?_map_repl]
    simp [ha, hi]
  rw [h, RelFree.simEnv20S_eq B]
  rfl

theorem findTyp_stateT : (simEnv20T B).findTyp? "state" = some ([], [.instD [] []
    (.variantT [.mk "%;%" (.tupT [.mk "store" (.varT "store" []), .mk "frame" (.varT "frame" [])])
      [] []])]) := (findTypT_off _ (by decide) (by decide)).trans Whole.findTyp_state20

theorem findTyp_storeT : (simEnv20T B).findTyp? "store" = some ([], [.instD [] []
    (.structT [.mk "FUNCS" (.iterT (.varT "funcinst" []) .list) [] [],
      .mk "GLOBALS" (.iterT (.varT "globalinst" []) .list) [] [],
      .mk "TABLES" (.iterT (.varT "tableinst" []) .list) [] [],
      .mk "MEMS" (.iterT (.varT "meminst" []) .list) [] [],
      .mk "ELEMS" (.iterT (.varT "eleminst" []) .list) [] [],
      .mk "DATAS" (.iterT (.varT "datainst" []) .list) [] []])]) :=
  (findTypT_off _ (by decide) (by decide)).trans Whole.findTyp_store20

theorem findTyp_frameT : (simEnv20T B).findTyp? "frame" = some ([], [.instD [] []
    (.structT [.mk "LOCALS" (.iterT (.varT "val" []) .list) [] [],
      .mk "MODULE" (.varT "moduleinst" []) [] []])]) :=
  (findTypT_off _ (by decide) (by decide)).trans Whole.findTyp_frame20

theorem findTyp_funcinstT : (simEnv20T B).findTyp? "funcinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "functype" []) [] [], .mk "MODULE" (.varT "moduleinst" []) [] [],
      .mk "CODE" (.varT "func" []) [] []])]) :=
  (findTypT_off _ (by decide) (by decide)).trans Whole.findTyp_funcinst20

theorem findTyp_funcT : (simEnv20T B).findTyp? "func" = some ([], [.instD [] [] (.variantT
    [.mk "FUNC" (.tupT [.mk "typeidx" (.varT "typeidx" []),
      .mk "local*" (.iterT (.varT "local" []) .list), .mk "expr" (.varT "expr" [])]) [] []])]) :=
  (findTypT_off _ (by decide) (by decide)).trans Whole.findTyp_func20

theorem findTyp_exprT : (simEnv20T B).findTyp? "expr" =
    some ([], [.instD [] [] (.aliasT (.iterT (.varT "instr" []) .list))]) :=
  (findTypT_off _ (by decide) (by decide)).trans Whole.findTyp_expr20

/-! ## States, stores, frames -/

theorem typedT_stateV_iff {s : Store H} {f : Frame} :
    TypedV (simEnv20T B) stateT (stateV hn s f) ↔
      TypedV (simEnv20T B) storeT (storeV hn s) ∧ TypedV (simEnv20T B) frameT (frameV f) :=
  ⟨Whole.typedV_pair_inv findTyp_stateT,
    fun ⟨hs, hf⟩ => Pure.typedV_closedCase20 findTyp_stateT rfl (Whole.hasTyp_tup2G hs hf)⟩

/-- **A store image is typed in `simEnv20T` field by field.** -/
structure StoreTyT (B : Builtins) (hn : H → String) (s : Store H) : Prop where
  funcs : TypedV (simEnv20T B) (.iterT (.varT "funcinst" []) .list) (.list (s.funcs.map (funcInstV hn)))
  globals : TypedV (simEnv20T B) (.iterT (.varT "globalinst" []) .list) (.list (s.globals.map globalInstV))
  tables : TypedV (simEnv20T B) (.iterT (.varT "tableinst" []) .list) (.list (s.tables.map tableInstV))
  mems : TypedV (simEnv20T B) (.iterT (.varT "meminst" []) .list) (.list (s.mems.map memInstV))
  elems : TypedV (simEnv20T B) (.iterT (.varT "eleminst" []) .list) (.list (s.elems.map elemInstV))
  datas : TypedV (simEnv20T B) (.iterT (.varT "datainst" []) .list) (.list (s.datas.map dataInstV))

theorem typedT_storeV_iff {s : Store H} :
    TypedV (simEnv20T B) storeT (storeV hn s) ↔ StoreTyT B hn s := by
  constructor
  · intro h
    have h₀ := hasTypFields_of_closed findTyp_storeT h
    obtain ⟨h₁, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₂, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₃, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₄, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₅, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₆, -⟩ := hasTypFields_cons_nil_iff.1 h₀
    exact ⟨typedV_list_of_empty20 h₁, typedV_list_of_empty20 h₂, typedV_list_of_empty20 h₃,
      typedV_list_of_empty20 h₄, typedV_list_of_empty20 h₅, typedV_list_of_empty20 h₆⟩
  · intro h
    exact typedV_structG findTyp_storeT (hasTypFields_consG h.funcs (hasTypFields_consG h.globals
      (hasTypFields_consG h.tables (hasTypFields_consG h.mems (hasTypFields_consG h.elems
        (hasTypFields_oneG h.datas))))))

/-! ## Function instances in `simEnv20T` -/

/-- A typed function instance of `simEnv20T` has a typed module and code. -/
theorem typedT_funcInst_parts {fi : FuncInst H} {fn : V2.Func} (hcode : fi.code = .wasm fn)
    (h : TypedV (simEnv20T B) (.varT "funcinst" []) (funcInstV hn fi)) :
    TypedV (simEnv20T B) (.varT "moduleinst" []) (moduleInstV fi.module) ∧
      TypedV (simEnv20T B) (.varT "func" []) (codeV20 fn) := by
  rw [funcInstV_wasm hcode] at h
  have h₀ := hasTypFields_of_closed findTyp_funcinstT h
  have h₁ := (hasTypFields_cons_nil_iff.1 h₀).2
  have h₂ := hasTypFields_cons_nil_iff.1 h₁
  exact ⟨typedV_of_empty20 h₂.1, typedV_of_empty20 (hasTypFields_cons_nil_iff.1 h₂.2).1⟩

/-- The three components of a typed `FUNC x local* instr*`, in any environment declaring `func`
and `expr` as 2.0 does. -/
theorem func_parts {env : Env} {fn : V2.Func}
    (hfd : env.findTyp? "func" = some ([], [.instD [] [] (.variantT
      [.mk "FUNC" (.tupT [.mk "typeidx" (.varT "typeidx" []),
        .mk "local*" (.iterT (.varT "local" []) .list), .mk "expr" (.varT "expr" [])]) [] []])]))
    (hed : env.findTyp? "expr" = some ([], [.instD [] [] (.aliasT (.iterT (.varT "instr" []) .list))]))
    (h : TypedV env (.varT "func" []) (codeV20 fn)) :
    TypedV env (.varT "typeidx" []) (idxV fn.type) ∧
      TypedV env (.iterT (.varT "local" []) .list)
        (.list ((fn.locals.map valTypeV).map (.case "LOCAL"))) ∧
      TypedV env Pure.instrsT (.list (instrsToV fn.body)) := by
  obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 (hasTypDef_of_closed hfd (h _ valsOnly_empty))
  obtain ⟨rfl, rfl⟩ : op = "FUNC" ∧ w = .tuple [idxV fn.type,
      .list ((fn.locals.map valTypeV).map (.case "LOCAL")), .list (instrsToV fn.body)] := by
    simpa [codeV20] using he.symm
  have ht := Sim.IntNumeric.hasTyp_of_hasTypCase hc rfl
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 ht
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y₁, ys₁, h₁, hy₁, ht₁⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, rfl⟩ := List.cons.inj h₁
  obtain ⟨y₂, ys₂, h₂, hy₂, ht₂⟩ := hasTypTup_cons_iff.1 ht₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj h₂
  obtain ⟨y₃, ys₃, h₃, hy₃, -⟩ := hasTypTup_cons_iff.1 ht₂
  obtain ⟨rfl, -⟩ := List.cons.inj h₃
  have hE : TypedV env (.varT "expr" []) (.list (instrsToV fn.body)) :=
    typedV_of_valsOnly20 ⟨rfl, rfl, rfl⟩ hy₃
  exact ⟨typedV_of_empty20 hy₁, typedV_list_of_valsOnly20 ⟨rfl, rfl, rfl⟩ hy₂,
    typedV_list_of_empty20 (hasTypDef_aliasT_iff.1 (hasTypDef_of_closed hed (hE _ valsOnly_empty)))⟩

/-- `FUNC x local* instr*` from its typed components, in any environment declaring `func` and
`expr` as 2.0 does. -/
theorem func_mk {env : Env} {fn : V2.Func}
    (hfd : env.findTyp? "func" = some ([], [.instD [] [] (.variantT
      [.mk "FUNC" (.tupT [.mk "typeidx" (.varT "typeidx" []),
        .mk "local*" (.iterT (.varT "local" []) .list), .mk "expr" (.varT "expr" [])]) [] []])]))
    (hed : env.findTyp? "expr" = some ([], [.instD [] [] (.aliasT (.iterT (.varT "instr" []) .list))]))
    (h₁ : TypedV env (.varT "typeidx" []) (idxV fn.type))
    (h₂ : TypedV env (.iterT (.varT "local" []) .list)
      (.list ((fn.locals.map valTypeV).map (.case "LOCAL"))))
    (h₃ : TypedV env Pure.instrsT (.list (instrsToV fn.body))) :
    TypedV env (.varT "func" []) (codeV20 fn) := by
  have hE : TypedV env (.varT "expr" []) (.list (instrsToV fn.body)) :=
    typedV_aliasG hed (h₃ _ valsOnly_empty)
  exact Pure.typedV_closedCase20 hfd rfl (hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2
    ⟨_, _, rfl, h₁ _ ⟨rfl, rfl, rfl⟩, hasTypTup_cons_iff.2 ⟨_, _, rfl, h₂ _ ⟨rfl, rfl, rfl⟩,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, hE _ ⟨rfl, rfl, rfl⟩, hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩)

/-- **A typed Wasm function of `simEnv20T` has a typed body.** -/
theorem typedT_body_of_func {fn : V2.Func}
    (h : TypedV (simEnv20T B) (.varT "func" []) (codeV20 fn)) :
    TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV fn.body)) :=
  (func_parts findTyp_funcT findTyp_exprT h).2.2

/-- The function instance at an address of a state typed in `simEnv20T` is typed there. -/
theorem typedT_funcInst_of_state {s : Store H} {f : Frame} {a : FuncAddr} {fi : FuncInst H}
    (hz : TypedV (simEnv20T B) stateT (stateV hn s f)) (hf : s.funcInst? a = some fi) :
    TypedV (simEnv20T B) (.varT "funcinst" []) (funcInstV hn fi) :=
  Whole.typedV_of_getElem? (typedT_storeV_iff.1 (typedT_stateV_iff.1 hz).1).funcs
    (by simpa [Store.funcInst?] using hf)

/-- A frame from values and a module typed in `simEnv20T`. -/
theorem typedT_frame_of {m : ModuleInst}
    (hm : TypedV (simEnv20T B) (.varT "moduleinst" []) (moduleInstV m)) (ls : List Val) :
    TypedV (simEnv20T B) Pure.frameT (frameV ⟨ls, m⟩) :=
  typedV_struct2 findTyp_frameT
    (StoreAgree.typedV_list_to20T (x := "val") (by decide) (Whole.typedV_vals20 ls) _ valsOnly_empty)
    (hm _ valsOnly_empty)

/-! ## The erased store -/

/-- A Wasm function with its body deeply erased; a host function unchanged. -/
def eraseFI (fi : FuncInst H) : FuncInst H :=
  { fi with code := match fi.code with
    | .wasm fn => .wasm { fn with body := fn.body.map eD }
    | .host h => .host h }

/-- The store with every function body deeply erased. -/
def eraseS (s : Store H) : Store H := { s with funcs := s.funcs.map eraseFI }

@[simp] theorem eraseFI_type (fi : FuncInst H) : (eraseFI fi).type = fi.type := rfl
@[simp] theorem eraseFI_module (fi : FuncInst H) : (eraseFI fi).module = fi.module := rfl
theorem eraseFI_code {fi : FuncInst H} {fn : V2.Func} (h : fi.code = .wasm fn) :
    (eraseFI fi).code = .wasm { fn with body := fn.body.map eD } := by
  simp [eraseFI, h]

@[simp] theorem eraseS_globals (s : Store H) : (eraseS s).globals = s.globals := rfl
@[simp] theorem eraseS_tables (s : Store H) : (eraseS s).tables = s.tables := rfl
@[simp] theorem eraseS_mems (s : Store H) : (eraseS s).mems = s.mems := rfl
@[simp] theorem eraseS_elems (s : Store H) : (eraseS s).elems = s.elems := rfl
@[simp] theorem eraseS_datas (s : Store H) : (eraseS s).datas = s.datas := rfl
@[simp] theorem eraseS_funcs (s : Store H) : (eraseS s).funcs = s.funcs.map eraseFI := rfl

theorem eraseS_funcInst {s : Store H} {a : FuncAddr} {fi : FuncInst H}
    (h : s.funcInst? a = some fi) : (eraseS s).funcInst? a = some (eraseFI fi) := by
  simp only [Store.funcInst?] at h ⊢
  simp [h]

/-- **Every function of the store is a Wasm function whose body is covered, stores at every
depth included, in its own module.** -/
def StoreOkD (s : Store H) : Prop :=
  ∀ a fi, s.funcInst? a = some fi → ∃ fn, fi.code = .wasm fn ∧ fn.body.all (ctrlOkD fi.module) = true

theorem StoreOkD.not_host {s : Store H} (hs : StoreOkD s) {a : FuncAddr} {fi : FuncInst H} {h : H}
    (hf : s.funcInst? a = some fi) (hc : fi.code = .host h) : False := by
  obtain ⟨fn, hc', -⟩ := hs a fi hf
  rw [hc] at hc'
  cases hc'

theorem storeOkD_of_funcs {s s' : Store H} (h : StoreOkD s) (e : s'.funcs = s.funcs) :
    StoreOkD s' := fun a fi hf => h a fi (by simpa [Store.funcInst?, e] using hf)

/-- `StoreOkM` is `StoreOkD` without stores. -/
theorem storeOkD_of_storeOkM {s : Store H} (h : GoodMerge.StoreOkM s) : StoreOkD s := by
  intro a fi hf
  obtain ⟨fn, hc, hb⟩ := h a fi hf
  exact ⟨fn, hc, StoreDeep.all_ctrlOkD_of_ctrlOkM hb⟩

/-- **The erased store of a `StoreOkD` store is `StoreOkM`.** -/
theorem storeOkM_eraseS {s : Store H} (h : StoreOkD s) : GoodMerge.StoreOkM (eraseS s) := by
  intro a fi hf
  simp only [Store.funcInst?, eraseS_funcs, List.getElem?_map, Option.map_eq_some_iff] at hf
  obtain ⟨fi₀, hf₀, rfl⟩ := hf
  obtain ⟨fn, hc, hb⟩ := h a fi₀ (by simpa [Store.funcInst?] using hf₀)
  exact ⟨_, eraseFI_code hc, by simpa using StoreDeep.all_ctrlOkM_eD hb⟩

/-- `StoreOkM` stores are their own erasure. -/
theorem eraseS_of_storeOkM {s : Store H} (h : GoodMerge.StoreOkM s) : eraseS s = s := by
  rcases s with ⟨funcs, g, t, m, e, d⟩
  simp only [eraseS, Store.mk.injEq, and_true]
  refine (List.map_congr_left (fun fi hfi => ?_)).trans (List.map_id funcs)
  obtain ⟨a, ha⟩ := List.getElem?_of_mem hfi
  obtain ⟨fn, hc, hb⟩ := h a fi (by simpa [Store.funcInst?] using ha)
  rcases fi with ⟨ty, mo, co⟩
  simp only at hc
  subst hc
  simp [eraseFI, StoreDeep.map_eD_of_ctrlOkM hb]

/-! ## The state, from its erasure -/

/-- **A function instance whose erasure is typed in `simEnv20`, with a covered body, is typed in
`simEnv20T`.** -/
theorem typedT_funcInst_of_erased {fi : FuncInst H} {fn : V2.Func} (hc : fi.code = .wasm fn)
    (hb : fn.body.all (ctrlOkD fi.module) = true)
    (h : TypedV (E20 B) (.varT "funcinst" []) (funcInstV hn (eraseFI fi))) :
    TypedV (simEnv20T B) (.varT "funcinst" []) (funcInstV hn fi) := by
  have hc' := eraseFI_code hc
  rw [funcInstV_wasm hc'] at h
  have h₀ := hasTypFields_of_closed Whole.findTyp_funcinst20 h
  obtain ⟨hty, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
  obtain ⟨hmo, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
  obtain ⟨hco, -⟩ := hasTypFields_cons_nil_iff.1 h₀
  obtain ⟨p₁, p₂, p₃⟩ := func_parts Whole.findTyp_func20 Whole.findTyp_expr20 (typedV_of_empty20 hco)
  have hbody : TypedV (simEnv20T B) Pure.instrsT (.list (instrsToV fn.body)) :=
    StoreDeep.typedT_instrs_of_eD hb (by simpa using p₃)
  have hfunc : TypedV (simEnv20T B) (.varT "func" []) (codeV20 fn) :=
    func_mk findTyp_funcT findTyp_exprT (StoreAgree.typedV_to20T (by decide) p₁)
      (StoreAgree.typedV_list_to20T (x := "local") (by decide) p₂) hbody
  rw [funcInstV_wasm hc]
  exact typedV_structG findTyp_funcinstT (hasTypFields_consG
    (StoreAgree.typedV_to20T (x := "functype") (by decide) (typedV_of_empty20 hty))
    (hasTypFields_consG (StoreAgree.typedV_to20T (x := "moduleinst") (by decide)
      (typedV_of_empty20 hmo)) (hasTypFields_oneG hfunc)))

/-- **A state whose erasure is typed in `simEnv20`, over a `StoreOkD` store, is typed in
`simEnv20T`.** -/
theorem typedT_state_of_erased {s : Store H} {f : Frame} (hs : StoreOkD s)
    (h : TypedV (E20 B) stateT (stateV hn (eraseS s) f)) :
    TypedV (simEnv20T B) stateT (stateV hn s f) := by
  obtain ⟨hst, hfr⟩ := Whole.typedV_stateV_iff.1 h
  have S := Whole.typedV_storeV_iff.1 hst
  refine typedT_stateV_iff.2 ⟨typedT_storeV_iff.2 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    StoreAgree.typedV_to20T (x := "frame") (by decide) hfr⟩
  · refine Sim.typedV_list_iff.2 fun u hu => ?_
    obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 hu
    obtain ⟨a, ha⟩ := List.getElem?_of_mem hfi
    obtain ⟨fn, hc, hb⟩ := hs a fi (by simpa [Store.funcInst?] using ha)
    refine typedT_funcInst_of_erased hc hb (Sim.typedV_list_iff.1 S.funcs _ ?_)
    exact List.mem_map_of_mem (List.mem_map_of_mem hfi)
  · exact StoreAgree.typedV_list_to20T (x := "globalinst") (by decide) S.globals
  · exact StoreAgree.typedV_list_to20T (x := "tableinst") (by decide) S.tables
  · exact StoreAgree.typedV_list_to20T (x := "meminst") (by decide) S.mems
  · exact StoreAgree.typedV_list_to20T (x := "eleminst") (by decide) S.elems
  · exact StoreAgree.typedV_list_to20T (x := "datainst") (by decide) S.datas

end Silmaril.Wasm.SpecTec.Sim20.StoreFn
