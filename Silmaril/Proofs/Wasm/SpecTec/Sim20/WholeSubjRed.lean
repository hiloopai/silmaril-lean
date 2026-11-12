module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeCtxAgree

/-!
# Subject reduction for the image of the top-level fragment

`Task.wholeStepCtxS20` assumes that the successor configuration of the inner step is typed. This
module proves that it is: every `TopVStep20` step from a configuration whose image is IL-typed
leads to one whose image is IL-typed (`typed20_of_topVStep20`), at every builtins. So the stronger
target **`Task.wholeStepCtxS20'`** (no successor hypothesis) is proved (`wholeStepCtxS20'`).

The typing of an image is taken apart and put back together along the 2.0 type definitions,
all record types without premises:

* `config = state; admininstr*`, `state = store; frame` (`typed20_iff`, `typedV_stateV_iff`);
* `store` has six list fields, `frame` two, `globalinst` and `eleminst` two each
  (`StoreTy20`, `typedV_storeV_iff`, `typedV_frameV_iff`, …);
* a store update `s.setXInst a x` keeps the store typed when `x` is (`storeTy20_setTable`, …),
  and `f.setLocal x v` keeps the frame typed (`typedV_frameV_setLocal`);
* the new instances are typed: every table and memory instance (`typedV_tableInst20`,
  `typedV_memInst20`), a global with a new value (`typedV_globalInstV_value`), an element with
  its references dropped, a data instance with its bytes dropped;
* the new code is `[]`, `[TRAP]` or `[i32.const k]` (`typedV_admins_nil20`, `typedV_admins_trap20`,
  `typedV_admins_const20`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.SpecTec.Equiv.Execution (caseNilV)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly stateT storeT frameT)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S adminsTy)
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d282)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Generic inversions, in the empty scope -/

/-- The empty scope binds term variables only. -/
theorem valsOnly_empty : ValsOnly VarEnv.empty := ⟨rfl, rfl, rfl⟩

/-- A value of a closed one-instance type is typed by its body. -/
theorem hasTypDef_of_closed {env : Env} {x : IL.Id} {dt : DefTyp} {v : Value}
    (htd : env.findTyp? x = some ([], [.instD [] [] dt]))
    (h : HasTyp env VarEnv.empty (.varT x []) v) : HasTypDef env VarEnv.empty dt v := by
  have hl : localTyp? VarEnv.empty x [] = none := rfl
  obtain ⟨td, ws, htd', -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
  · obtain rfl := Sim.IntNumeric.matchArgs_nil_scope hm
    exact hd
  · exact absurd hrest not_hasTypInsts_nil

/-- The fields of a typed closed record. -/
theorem hasTypFields_of_closed {env : Env} {x : IL.Id} {fs : List TypField}
    {gs : List (AtomS × Value)} (htd : env.findTyp? x = some ([], [.instD [] [] (.structT fs)]))
    (h : TypedV env (.varT x []) (.struct gs)) : HasTypFields env VarEnv.empty fs gs := by
  obtain ⟨gs', he, hf⟩ := hasTypDef_structT_iff.1 (hasTypDef_of_closed htd (h _ valsOnly_empty))
  obtain rfl := (Value.struct.inj he).symm
  exact hf

/-- A field without premises, in both directions. -/
theorem hasTypFields_cons_nil_iff {env : Env} {a : AtomS} {t : Typ} {fs : List TypField}
    {v : Value} {gs : List (AtomS × Value)} :
    HasTypFields env VarEnv.empty (.mk a t [] [] :: fs) ((a, v) :: gs) ↔
      HasTyp env VarEnv.empty t v ∧ HasTypFields env VarEnv.empty fs gs := by
  rw [hasTypFields_cons_iff]
  constructor
  · rintro ⟨w, gs', he, ht, -, hr⟩
    obtain ⟨rfl, rfl⟩ : v = w ∧ gs = gs' := by simpa using he
    exact ⟨ht, hr⟩
  · rintro ⟨ht, hr⟩
    exact ⟨v, gs, rfl, ht, premsOk_nil, hr⟩

/-- A closed type name, from the empty scope to every scope binding term variables only. -/
theorem typedV_of_empty20 {env : Env} {x : IL.Id} {v : Value}
    (h : HasTyp env VarEnv.empty (.varT x []) v) : TypedV env (.varT x []) v :=
  fun _ hρ => Sim.IntNumeric.hasTyp_varT_nil_congr valsOnly_empty hρ h

/-- A list over a closed type name, from the empty scope to every such scope. -/
theorem typedV_list_of_empty20 {env : Env} {x : IL.Id} {l : List Value}
    (h : HasTyp env VarEnv.empty (.iterT (.varT x []) .list) (.list l)) :
    TypedV env (.iterT (.varT x []) .list) (.list l) := by
  obtain ⟨l', he, hl⟩ := hasTyp_iterT_list_iff.1 h
  obtain rfl := Value.list.inj he
  exact Sim.typedV_list_iff.2 fun u hu => typedV_of_empty20 (hasTypList_iff.1 hl u hu)

/-- A typed list over a closed type name, elementwise. -/
theorem typedV_list_iff20 {env : Env} {x : IL.Id} {l : List Value} :
    TypedV env (.iterT (.varT x []) .list) (.list l) ↔ ∀ u ∈ l, TypedV env (.varT x []) u :=
  Sim.typedV_list_iff

/-- Replacing one element of a typed list by a typed value. -/
theorem typedV_list_set20 {env : Env} {t : Typ} {α : Type} {F : α → Value} {l : List α} {i : Nat}
    {a : α} (hl : TypedV env (.iterT t .list) (.list (l.map F))) (ha : TypedV env t (F a)) :
    TypedV env (.iterT t .list) (.list ((l.set i a).map F)) := by
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hu
  rcases List.mem_or_eq_of_mem_set hb with hb | rfl
  · exact Sim.typedV_list_iff.1 hl _ (List.mem_map_of_mem hb)
  · exact ha

/-! ## The 2.0 type definitions used -/

theorem findTyp_store20 : (simEnv20 B).findTyp? "store" = some ([], [.instD [] []
    (.structT [.mk "FUNCS" (.iterT (.varT "funcinst" []) .list) [] [],
      .mk "GLOBALS" (.iterT (.varT "globalinst" []) .list) [] [],
      .mk "TABLES" (.iterT (.varT "tableinst" []) .list) [] [],
      .mk "MEMS" (.iterT (.varT "meminst" []) .list) [] [],
      .mk "ELEMS" (.iterT (.varT "eleminst" []) .list) [] [],
      .mk "DATAS" (.iterT (.varT "datainst" []) .list) [] []])]) := rfl

theorem findTyp_frame20 : (simEnv20 B).findTyp? "frame" = some ([], [.instD [] []
    (.structT [.mk "LOCALS" (.iterT (.varT "val" []) .list) [] [],
      .mk "MODULE" (.varT "moduleinst" []) [] []])]) := rfl

theorem findTyp_globalinst20 : (simEnv20 B).findTyp? "globalinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "globaltype" []) [] [], .mk "VALUE" (.varT "val" []) [] []])]) :=
  rfl

theorem findTyp_eleminst20 : (simEnv20 B).findTyp? "eleminst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "elemtype" []) [] [],
      .mk "REFS" (.iterT (.varT "ref" []) .list) [] []])]) := rfl

theorem findTyp_datainst20 : (simEnv20 B).findTyp? "datainst" = some ([], [.instD [] []
    (.structT [.mk "BYTES" (.iterT (.varT "byte" []) .list) [] []])]) := rfl

theorem findTyp_admininstr20 : (simEnv20 B).findTyp? "admininstr" = some ([], [.instD [] []
    (.variantT (Sim.IntNumeric.recCases Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d295 0 0))]) :=
  rfl

/-! ## Two-field records -/

/-- The first field of a typed two-field record. -/
theorem hasTyp_struct2_fst {env : Env} {x : IL.Id} {a b : AtomS} {t₁ t₂ : Typ} {u v : Value}
    (htd : env.findTyp? x = some ([], [.instD [] [] (.structT [.mk a t₁ [] [], .mk b t₂ [] []])]))
    (h : TypedV env (.varT x []) (.struct [(a, u), (b, v)])) : HasTyp env VarEnv.empty t₁ u :=
  (hasTypFields_cons_nil_iff.1 (hasTypFields_of_closed htd h)).1

/-- The second field of a typed two-field record. -/
theorem hasTyp_struct2_snd {env : Env} {x : IL.Id} {a b : AtomS} {t₁ t₂ : Typ} {u v : Value}
    (htd : env.findTyp? x = some ([], [.instD [] [] (.structT [.mk a t₁ [] [], .mk b t₂ [] []])]))
    (h : TypedV env (.varT x []) (.struct [(a, u), (b, v)])) : HasTyp env VarEnv.empty t₂ v :=
  (hasTypFields_cons_nil_iff.1 (hasTypFields_cons_nil_iff.1 (hasTypFields_of_closed htd h)).2).1

/-- A two-field record from its fields. -/
theorem typedV_struct2 {env : Env} {x : IL.Id} {a b : AtomS} {t₁ t₂ : Typ} {u v : Value}
    (htd : env.findTyp? x = some ([], [.instD [] [] (.structT [.mk a t₁ [] [], .mk b t₂ [] []])]))
    (hu : HasTyp env VarEnv.empty t₁ u) (hv : HasTyp env VarEnv.empty t₂ v) :
    TypedV env (.varT x []) (.struct [(a, u), (b, v)]) :=
  typedV_structG htd (hasTypFields_cons_nil_iff.2 ⟨hu,
    hasTypFields_cons_nil_iff.2 ⟨hv, hasTypFields_nil_iff.2 rfl⟩⟩)

/-! ## `config`, `state`, `store`, `frame` -/

/-- A pair case `"%;%"` of a closed one-case variant, taken apart. -/
theorem hasTyp_pair_inv {env : Env} {x a b : IL.Id} {τ₁ τ₂ : Typ} {u v : Value}
    (htd : env.findTyp? x = some ([], [.instD [] []
      (.variantT [.mk "%;%" (.tupT [.mk a τ₁, .mk b τ₂]) [] []])]))
    (h : HasTyp env VarEnv.empty (.varT x []) (.case "%;%" (.tuple [u, v]))) :
    HasTyp env VarEnv.empty τ₁ u ∧ HasTyp env (VarEnv.empty.bindVal a u) τ₂ v := by
  obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 (hasTypDef_of_closed htd h)
  obtain ⟨rfl, rfl⟩ : op = "%;%" ∧ w = .tuple [u, v] := by simpa using he.symm
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 ((hasTypCase_cons_hit_iff rfl).1 hc).1
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, hy, htup'⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, rfl⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', hy', -⟩ := hasTypTup_cons_iff.1 htup'
  obtain ⟨rfl, -⟩ := List.cons.inj hys'
  exact ⟨hy, hy'⟩

/-- The two components of a typed `"%;%"` pair over closed type names. -/
theorem typedV_pair_inv {env : Env} {x a b X Y : IL.Id} {u v : Value}
    (htd : env.findTyp? x = some ([], [.instD [] []
      (.variantT [.mk "%;%" (.tupT [.mk a (.varT X []), .mk b (.varT Y [])]) [] []])]))
    (h : TypedV env (.varT x []) (.case "%;%" (.tuple [u, v]))) :
    TypedV env (.varT X []) u ∧ TypedV env (.varT Y []) v := by
  obtain ⟨hu, hv⟩ := hasTyp_pair_inv htd (h _ valsOnly_empty)
  exact ⟨typedV_of_empty20 hu,
    fun _ hρ => Sim.IntNumeric.hasTyp_varT_nil_congr ⟨rfl, rfl, rfl⟩ hρ hv⟩

theorem typed20_iff {c : Config H} :
    Typed20 (simEnv20 B) hn c ↔ TypedV (simEnv20 B) stateT (stateV hn c.store c.frame) ∧
      TypedV (simEnv20 B) adminsTy (.list (adminsToV c.code)) := by
  refine ⟨fun h => ⟨typedV_state_of_typed20 h, typedV_code_of_typed20 h⟩, fun ⟨hz, hc⟩ => ?_⟩
  exact Pure.typedV_closedCase20 findTyp_config20 rfl (hasTyp_tup2G hz hc) _ valsOnly_empty

theorem typedV_stateV_iff {s : Store H} {f : Frame} :
    TypedV (simEnv20 B) stateT (stateV hn s f) ↔
      TypedV (simEnv20 B) storeT (storeV hn s) ∧ TypedV (simEnv20 B) frameT (frameV f) :=
  ⟨typedV_pair_inv findTyp_state20,
    fun ⟨hs, hf⟩ => Pure.typedV_closedCase20 findTyp_state20 rfl (hasTyp_tup2G hs hf)⟩

/-- **A store image is typed field by field.** -/
structure StoreTy20 (B : Builtins) (hn : H → String) (s : Store H) : Prop where
  funcs : TypedV (simEnv20 B) (.iterT (.varT "funcinst" []) .list) (.list (s.funcs.map (funcInstV hn)))
  globals : TypedV (simEnv20 B) (.iterT (.varT "globalinst" []) .list) (.list (s.globals.map globalInstV))
  tables : TypedV (simEnv20 B) (.iterT (.varT "tableinst" []) .list) (.list (s.tables.map tableInstV))
  mems : TypedV (simEnv20 B) (.iterT (.varT "meminst" []) .list) (.list (s.mems.map memInstV))
  elems : TypedV (simEnv20 B) (.iterT (.varT "eleminst" []) .list) (.list (s.elems.map elemInstV))
  datas : TypedV (simEnv20 B) (.iterT (.varT "datainst" []) .list) (.list (s.datas.map dataInstV))

theorem typedV_storeV_iff {s : Store H} :
    TypedV (simEnv20 B) storeT (storeV hn s) ↔ StoreTy20 B hn s := by
  constructor
  · intro h
    have h₀ := hasTypFields_of_closed findTyp_store20 h
    obtain ⟨h₁, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₂, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₃, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₄, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₅, h₀⟩ := hasTypFields_cons_nil_iff.1 h₀
    obtain ⟨h₆, -⟩ := hasTypFields_cons_nil_iff.1 h₀
    exact ⟨typedV_list_of_empty20 h₁, typedV_list_of_empty20 h₂, typedV_list_of_empty20 h₃,
      typedV_list_of_empty20 h₄, typedV_list_of_empty20 h₅, typedV_list_of_empty20 h₆⟩
  · intro h
    exact typedV_structG findTyp_store20 (hasTypFields_consG h.funcs (hasTypFields_consG h.globals
      (hasTypFields_consG h.tables (hasTypFields_consG h.mems (hasTypFields_consG h.elems
        (hasTypFields_oneG h.datas))))))

/-! ## Updates -/

theorem storeTy20_setTable {s : Store H} (h : StoreTy20 B hn s) (a : TableAddr) (ti : TableInst) :
    StoreTy20 B hn (s.setTableInst a ti) :=
  { h with tables := typedV_list_set20 h.tables (typedV_tableInst20 ti) }

theorem storeTy20_setMem {s : Store H} (h : StoreTy20 B hn s) (a : MemAddr) (mi : MemInst) :
    StoreTy20 B hn (s.setMemInst a mi) :=
  { h with mems := typedV_list_set20 h.mems (typedV_memInst20 mi) }

theorem storeTy20_setGlobal {s : Store H} (h : StoreTy20 B hn s) (a : GlobalAddr) {gi : GlobalInst}
    (hg : TypedV (simEnv20 B) (.varT "globalinst" []) (globalInstV gi)) :
    StoreTy20 B hn (s.setGlobalInst a gi) :=
  { h with globals := typedV_list_set20 h.globals hg }

theorem storeTy20_setElem {s : Store H} (h : StoreTy20 B hn s) (a : ElemAddr) {ei : ElemInst}
    (he : TypedV (simEnv20 B) (.varT "eleminst" []) (elemInstV ei)) :
    StoreTy20 B hn (s.setElemInst a ei) :=
  { h with elems := typedV_list_set20 h.elems he }

theorem storeTy20_setData {s : Store H} (h : StoreTy20 B hn s) (a : DataAddr) {di : DataInst}
    (hd : TypedV (simEnv20 B) (.varT "datainst" []) (dataInstV di)) :
    StoreTy20 B hn (s.setDataInst a di) :=
  { h with datas := typedV_list_set20 h.datas hd }

/-- An element of a typed list over a closed type name is typed. -/
theorem typedV_of_getElem? {env : Env} {x : IL.Id} {α : Type} {F : α → Value} {l : List α}
    {i : Nat} {a : α} (hl : TypedV env (.iterT (.varT x []) .list) (.list (l.map F)))
    (ha : l[i]? = some a) : TypedV env (.varT x []) (F a) :=
  Sim.typedV_list_iff.1 hl _ (List.mem_map_of_mem (List.mem_of_getElem? ha))

/-- A global instance with a new value. -/
theorem typedV_globalInstV_value {gi : GlobalInst}
    (hg : TypedV (simEnv20 B) (.varT "globalinst" []) (globalInstV gi)) (v : Val) :
    TypedV (simEnv20 B) (.varT "globalinst" []) (globalInstV { gi with value := v }) :=
  typedV_struct2 findTyp_globalinst20 (hasTyp_struct2_fst findTyp_globalinst20 hg)
    (typedV_val20 v _ valsOnly_empty)

/-- An element instance with its references dropped. -/
theorem typedV_elemInstV_drop {ei : ElemInst}
    (he : TypedV (simEnv20 B) (.varT "eleminst" []) (elemInstV ei)) :
    TypedV (simEnv20 B) (.varT "eleminst" []) (elemInstV { ei with refs := [] }) :=
  typedV_struct2 findTyp_eleminst20 (hasTyp_struct2_fst findTyp_eleminst20 he)
    (Sim.typedV_list_iff.2 (by simp) _ valsOnly_empty)

/-- Every data instance is a `datainst`. -/
theorem typedV_dataInst20 (di : DataInst) :
    TypedV (simEnv20 B) (.varT "datainst" []) (dataInstV di) :=
  typedV_structG findTyp_datainst20 (hasTypFields_oneG (typedV_bytes20 di.bytes))

/-- A frame with a local replaced by a value. -/
theorem typedV_frameV_setLocal {f : Frame} (hf : TypedV (simEnv20 B) frameT (frameV f))
    (x : LocalIdx) (v : Val) : TypedV (simEnv20 B) frameT (frameV (f.setLocal x v)) := by
  have hl : TypedV (simEnv20 B) (.iterT (.varT "val" []) .list)
      (.list ((f.locals.set x.toNat v).map valV)) :=
    typedV_list_set20 (typedV_list_of_empty20 (hasTyp_struct2_fst findTyp_frame20 hf))
      (typedV_val20 v)
  exact typedV_struct2 findTyp_frame20 (hl _ valsOnly_empty) (hasTyp_struct2_snd findTyp_frame20 hf)

/-! ## The new code -/

theorem typedV_admins_nil20 : TypedV (simEnv20 B) adminsTy (.list (adminsToV [])) :=
  Sim.typedV_list_iff.2 (by simp [adminsToV])

theorem typedV_admins_trap20 : TypedV (simEnv20 B) adminsTy (.list (adminsToV [.trap])) :=
  Sim.typedV_list_iff.2 (by
    simpa [adminsToV, adminToV, caseNilV] using
      Pure.typedV_closedCase20 (findTyp_admininstr20 (B := B)) (op := "TRAP") rfl hasTyp_tupT_nil)

/-- `CONST t c` is an `admininstr`. -/
theorem typedV_admin_num20 (n : NumVal) :
    TypedV (simEnv20 B) (.varT "admininstr" []) (valV (.num n)) := by
  obtain ⟨t, x⟩ := n
  have hnt : HasTyp (simEnv20 B) VarEnv.empty (.varT "numtype" []) (numTypeV t) :=
    Pure.typedV_numtype20 B t _ ⟨rfl, rfl, rfl⟩
  have hn : HasTyp (simEnv20 B) (VarEnv.empty.bindVal "numtype" (numTypeV t))
      (.varT "num_" [.expA (.varE "numtype")]) (numV ⟨t, x⟩) :=
    (Pure.numTyped_simEnv20 B).num t x "numtype" _ ⟨rfl, rfl, rfl⟩ (by simp)
  exact Pure.typedV_closedCase20 findTyp_admininstr20 rfl (hasTyp_tupT_iff.2 ⟨_, rfl,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, hnt, hasTypTup_cons_iff.2 ⟨_, _, rfl, hn,
      hasTypTup_nil_iff.2 rfl⟩⟩⟩)

theorem typedV_admins_const20 (k : BitVec 32) :
    TypedV (simEnv20 B) adminsTy (.list (adminsToV [constI32 k])) :=
  Sim.typedV_list_iff.2 (by simpa [adminsToV, adminToV, instrToV] using typedV_admin_num20 (B := B) ⟨.int .i32, k⟩)

/-! ## Subject reduction -/

/-- A configuration image is typed when its store, frame and code are. -/
theorem typed20_mk {s : Store H} {f : Frame} {code : List Admin} (hS : StoreTy20 B hn s)
    (hf : TypedV (simEnv20 B) frameT (frameV f))
    (hc : TypedV (simEnv20 B) adminsTy (.list (adminsToV code))) :
    Typed20 (simEnv20 B) hn ⟨s, f, code⟩ :=
  typed20_iff.2 ⟨typedV_stateV_iff.2 ⟨typedV_storeV_iff.2 hS, hf⟩, hc⟩

/-- Subject reduction for the growth steps. -/
theorem typed20_of_growStep20 {P : Profile} {s : Store H} {f : Frame} {c' : Config H}
    {code : List Admin} (hS : StoreTy20 B hn s) (hf : TypedV (simEnv20 B) frameT (frameV f))
    (h : GrowStep20 P ⟨s, f, code⟩ c') : Typed20 (simEnv20 B) hn c' := by
  cases h with
  | tableGrowSucceed _ _ _ _ => exact typed20_mk (storeTy20_setTable hS _ _) hf (typedV_admins_const20 _)
  | tableGrowFail _ _ _ => exact typed20_mk hS hf (typedV_admins_const20 _)
  | memoryGrowSucceed _ _ _ _ => exact typed20_mk (storeTy20_setMem hS _ _) hf (typedV_admins_const20 _)
  | memoryGrowFail _ _ _ => exact typed20_mk hS hf (typedV_admins_const20 _)

/-- Subject reduction for `TopStep20`. -/
theorem typed20_of_topStep20 {P : Profile} {s : Store H} {f : Frame} {c' : Config H}
    {code : List Admin} (hS : StoreTy20 B hn s) (hf : TypedV (simEnv20 B) frameT (frameV f))
    (h : TopStep20 P ⟨s, f, code⟩ c') : Typed20 (simEnv20 B) hn c' := by
  cases h with
  | grow h => exact typed20_of_growStep20 hS hf h
  | tableSetTrap _ _ _ => exact typed20_mk hS hf typedV_admins_trap20
  | tableSetVal _ _ _ => exact typed20_mk (storeTy20_setTable hS _ _) hf typedV_admins_nil20
  | elemDrop _ he =>
    exact typed20_mk (storeTy20_setElem hS _ (typedV_elemInstV_drop (typedV_of_getElem? hS.elems he)))
      hf typedV_admins_nil20
  | dataDrop _ _ => exact typed20_mk (storeTy20_setData hS _ (typedV_dataInst20 _)) hf typedV_admins_nil20

/-- Subject reduction for `TopVarStep20`. -/
theorem typed20_of_topVarStep20 {P : Profile} {s : Store H} {f : Frame} {c' : Config H}
    {code : List Admin} (hS : StoreTy20 B hn s) (hf : TypedV (simEnv20 B) frameT (frameV f))
    (h : TopVarStep20 P ⟨s, f, code⟩ c') : Typed20 (simEnv20 B) hn c' := by
  cases h with
  | top h => exact typed20_of_topStep20 hS hf h
  | localSet _ => exact typed20_mk hS (typedV_frameV_setLocal hf _ _) typedV_admins_nil20
  | globalSet _ hg =>
    exact typed20_mk (storeTy20_setGlobal hS _
      (typedV_globalInstV_value (typedV_of_getElem? hS.globals hg) _)) hf typedV_admins_nil20

/-- **Subject reduction for the image of the top-level fragment**: a `TopVStep20` step from a
configuration whose image is typed leads to one whose image is typed, at every builtins. -/
theorem typed20_of_topVStep20 {P : Profile} {c c' : Config H} (hc : Typed20 (simEnv20 B) hn c)
    (h : TopVStep20 P c c') : Typed20 (simEnv20 B) hn c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨hs, hf⟩ := typedV_stateV_iff.1 (typed20_iff.1 hc).1
  have hS : StoreTy20 B hn s := typedV_storeV_iff.1 hs
  cases h with
  | var h => exact typed20_of_topVarStep20 hS hf h
  | vecStoreOob _ _ _ => exact typed20_mk hS hf typedV_admins_trap20
  | vecStoreLaneOob _ _ _ => exact typed20_mk hS hf typedV_admins_trap20

/-! ## The target without the successor hypothesis -/

/-- **The forward 2.0 half below the top, through the erratum, without the successor hypothesis**
(stated and proved here): `Task.wholeStepCtxS20` with the typing of the inner successor dropped. -/
def Task.wholeStepCtxS20' : Prop :=
  ∀ (H : Type) (hn : H → String) (nd : Bool) (r : RelaxedChoice)
    (s s' : Store H) (f f' : Frame) (code code' : List Admin) (vs : List Val) (rest : List Admin),
    Typed20 (simEnv20 (growB (Profile.spec nd r))) hn ⟨s, f, code⟩ →
    TypedV (simEnv20 (growB (Profile.spec nd r))) adminsTy (.list (adminsToV rest)) →
    WholePages s → TopVStep20 (Profile.spec nd r) ⟨s, f, code⟩ ⟨s', f', code'⟩ →
    Sim.Round6.Reading.SStepB (simEnv20S (growB (Profile.spec nd r)))
      (configV hn ⟨s, f, vals vs ++ code ++ rest⟩) (configV hn ⟨s', f', vals vs ++ code' ++ rest⟩)

/-- **`Task.wholeStepCtxS20'` is proved**, from `Task.wholeStepCtxS20` and subject reduction. -/
theorem wholeStepCtxS20' : Task.wholeStepCtxS20' :=
  fun H hn nd r s s' f f' code code' vs rest hc hrest hw hs =>
    wholeStepCtxS20 H hn nd r s s' f f' code code' vs rest hc (typed20_of_topVStep20 hc hs) hrest
      hw hs

end Silmaril.Wasm.SpecTec.Sim20.Whole
