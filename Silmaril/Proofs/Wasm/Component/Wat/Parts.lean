module

public import Silmaril.Proofs.Wasm.Component.Wat.Atoms

/-!
# Component WAT: every production reads back

`R.x (P.x a) = some (norm a)` for the productions below the type definitions:
sorts, names with attributes, core instances, component instances, aliases, core
types, value types and extern descriptors.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Wat

open Silmaril.Wasm.Component.Binary Sexp

theorem coreSort_rt (s : CoreSort) : R.coreSort (P.coreSort s) = some s := by cases s <;> rfl

theorem sortPre_rt (s : ItemSort) (rest : List Sexp) :
    R.sortPre (P.sort s ++ rest) = some (s, rest) := by
  cases s with
  | core c => cases c <;> rfl
  | _ => rfl

theorem sort_rt (s : ItemSort) : R.sort (P.sort s) = some s := by
  have := sortPre_rt s []
  rw [List.append_nil] at this
  simp [R.sort, this]

theorem sortIdx_rt (x : SortIdx) : R.sortIdx (P.sortIdx x) = some x := by
  simp [R.sortIdx, P.sortIdx, sortPre_rt]

theorem coreSortIdx_rt (x : CoreSortIdx) : R.coreSortIdx (P.coreSortIdx x) = some x := by
  simp [R.coreSortIdx, P.coreSortIdx, coreSort_rt]

theorem attr_rt (a : Attribute) : R.attr (P.attr a) = some a := by
  cases a <;> simp [R.attr, P.attr]

theorem attrs_rt (rest : List Sexp) (h : ∀ s r, rest = s :: r → R.attr s = none) :
    ∀ as : List Attribute, R.attrs (as.map P.attr ++ rest) = (as, rest)
  | [] => by
    cases rest with
    | nil => rfl
    | cons s r => simp [R.attrs, h s r rfl]
  | a :: as => by simp [R.attrs, attr_rt, attrs_rt rest h as]

theorem name_rt (n : ExternName) (rest : List Sexp)
    (h : ∀ s r, rest = s :: r → R.attr s = none) :
    R.name (P.name n ++ rest) = some (normName n, rest) := by
  obtain ⟨s, f⟩ := n
  have h0 := attrs_rt rest h []
  rw [List.map_nil, List.nil_append] at h0
  cases f with
  | plain0 => simp [P.name, R.name, h0, normName]
  | plain1 => simp [P.name, R.name, h0, normName]
  | attrs as =>
    cases as with
    | nil => simp [P.name, R.name, h0, normName]
    | cons a as =>
      have h1 := attrs_rt rest h (a :: as)
      rw [List.map_cons, List.cons_append] at h1
      simp [P.name, R.name, h1, normName]

theorem attr_externDesc (d : ExternDesc) : R.attr (P.externDesc d) = none := by
  cases d with
  | value b => cases b with
    | eq => rfl
    | type t => cases t <;> rfl
  | type b => cases b <;> rfl
  | _ => rfl

theorem attr_sortIdx (x : SortIdx) : R.attr (P.sortIdx x) = none := by
  obtain ⟨s, i⟩ := x
  cases s with
  | core c => cases c <;> rfl
  | _ => rfl

theorem name_desc_rt (n : ExternName) (d : ExternDesc) :
    R.name (P.name n ++ [P.externDesc d]) = some (normName n, [P.externDesc d]) :=
  name_rt n _ (by rintro s r ⟨rfl, rfl⟩; exact attr_externDesc d)

/-! ## Instances and aliases -/

theorem coreInstance_rt (x : CoreInstanceExpr) :
    R.coreInstance (match P.coreInstance x with
      | .list (_ :: _ :: ss) => ss
      | _ => []) = some x := by
  cases x with
  | instantiate m args =>
    simp only [P.coreInstance, R.coreInstance, mapO, R.coreExport, num?_num, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
    rw [mapO_map_id _ _ args (fun a _ => by simp [R.coreWith])]
    rfl
  | exports es =>
    simp only [P.coreInstance, R.coreInstance]
    rw [mapO_map_id _ _ es (fun e _ => by simp [R.coreExport, coreSortIdx_rt])]

theorem item_coreInstance (x : CoreInstanceExpr) :
    R.item (P.coreInstance x) = some (.coreInstances [x]) := by
  have := coreInstance_rt x
  cases x with
  | instantiate m args =>
    exact (show R.item (P.coreInstance (.instantiate m args)) =
      (R.coreInstance [_]).map fun x => .coreInstances [x] from rfl).trans
      (by simp only [P.coreInstance] at this; rw [this]; rfl)
  | exports es =>
    exact (show R.item (P.coreInstance (.exports es)) =
      (R.coreInstance _).map fun x => .coreInstances [x] from rfl).trans
      (by simp only [P.coreInstance] at this; rw [this]; rfl)

theorem inst_rt (x : InstanceExpr) :
    R.inst (match P.inst x with
      | .list (_ :: ss) => ss
      | _ => []) = some (normInstance x) := by
  cases x with
  | instantiate c args =>
    simp only [P.inst, R.inst, mapO, R.inlineExport, num?_num, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
    rw [mapO_map_id _ _ args (fun a _ => by simp [R.with_, sortIdx_rt])]
    rfl
  | exports es =>
    simp only [P.inst, R.inst]
    rw [mapO_map _ _ (fun e => (normName e.1, e.2)) es (fun e _ => by
      simp [R.inlineExport, name_rt e.1 [P.sortIdx e.2]
        (by rintro s r ⟨rfl, rfl⟩; exact attr_sortIdx _), sortIdx_rt])]
    rfl

theorem item_inst (x : InstanceExpr) :
    R.item (P.inst x) = some (.instances [normInstance x]) := by
  have := inst_rt x
  cases x with
  | instantiate c args =>
    exact (show R.item (P.inst (.instantiate c args)) =
      (R.inst [_]).map fun x => .instances [x] from rfl).trans
      (by simp only [P.inst] at this; rw [this]; rfl)
  | exports es =>
    exact (show R.item (P.inst (.exports es)) =
      (R.inst _).map fun x => .instances [x] from rfl).trans
      (by simp only [P.inst] at this; rw [this]; rfl)

theorem alias_rt (a : Alias) :
    R.alias_ (match P.alias_ a with
      | .list (_ :: ss) => ss
      | _ => []) = some a := by
  obtain ⟨s, t⟩ := a
  cases t <;> simp [P.alias_, R.alias_, sort_rt]

theorem alias_list (a : Alias) : ∃ ss, P.alias_ a = .list (kw "alias" :: ss) := by
  obtain ⟨s, t⟩ := a
  cases t <;> exact ⟨_, rfl⟩

theorem item_alias (a : Alias) : R.item (P.alias_ a) = some (.aliases [a]) := by
  have h := alias_rt a
  obtain ⟨ss, hs⟩ := alias_list a
  rw [hs] at h ⊢
  exact (show R.item (.list (kw "alias" :: ss)) = (R.alias_ ss).map fun x => .aliases [x]
    from rfl).trans (by simp only at h; rw [h]; rfl)

/-! ## Core types -/

theorem coreValType_rt (t : CoreValType) : R.coreValType (P.coreValType t) = some t := by
  cases t <;> rfl

theorem coreImportDesc_rt (d : CoreImportDesc) :
    R.coreImportDesc (P.coreImportDesc d) = some d := by
  cases d with
  | func t => simp [P.coreImportDesc, R.coreImportDesc, R.typeUse]
  | table t l =>
    obtain ⟨m, n⟩ := l
    cases n <;> simp [P.coreImportDesc, P.limits, R.coreImportDesc, coreValType_rt]
  | memory l =>
    obtain ⟨m, n⟩ := l
    cases n <;> simp [P.coreImportDesc, P.limits, R.coreImportDesc]
  | global t m => cases m <;> cases t <;> rfl
  | tag t => simp [P.coreImportDesc, R.coreImportDesc, R.typeUse]

theorem coreFuncType_rt (t : CoreFuncType) :
    R.coreFuncType (match P.coreFuncType t with
      | .list (_ :: ss) => ss
      | _ => []) = some t := by
  obtain ⟨ps, rs⟩ := t
  have hp := mapO_map_id R.coreValType P.coreValType ps (fun x _ => coreValType_rt x)
  have hr := mapO_map_id R.coreValType P.coreValType rs (fun x _ => coreValType_rt x)
  rcases ps with _ | ⟨p, ps⟩ <;> rcases rs with _ | ⟨r, rs⟩ <;>
    simp_all [P.coreFuncType, R.coreFuncType]

theorem moduleDecl_rt (d : ModuleDecl) : R.moduleDecl (P.moduleDecl d) = some d := by
  cases d
  case type t =>
    have := coreFuncType_rt t
    simp only [P.moduleDecl, P.coreFuncType] at this ⊢
    simp [R.moduleDecl, this]
  all_goals simp [P.moduleDecl, R.moduleDecl, coreImportDesc_rt]

theorem coreType_rt (t : CoreType) : R.coreType (P.coreType t) = some t := by
  cases t with
  | func f =>
    have := coreFuncType_rt f
    simp only [P.coreType, P.coreFuncType] at this ⊢
    simp [R.coreType, this]
  | module ds =>
    simp [P.coreType, R.coreType, mapO_map_id _ _ ds (fun d _ => moduleDecl_rt d)]

/-! ## Value types and descriptors -/

theorem prim_rt (p : PrimValType) : R.prim (P.prim p) = some p := by cases p <;> rfl

theorem valType_rt (t : Silmaril.Wasm.Component.Binary.ValType) : R.valType (P.valType t) = some t := by
  cases t with
  | prim p => cases p <;> rfl
  | idx i => simp [R.valType, P.valType]

theorem optValType_rt (t : Option Silmaril.Wasm.Component.Binary.ValType) :
    R.optValType (t.map P.valType).toList = some t := by
  cases t <;> simp [R.optValType, valType_rt]

theorem externDesc_rt (d : ExternDesc) : R.externDesc (P.externDesc d) = some (normDesc d) := by
  cases d with
  | value b => cases b with
    | eq => simp [P.externDesc, R.externDesc, normDesc]
    | type t => cases t with
      | idx i => simp [P.externDesc, R.externDesc, normDesc]
      | prim p => cases p <;> rfl
  | type b => cases b <;> simp [P.externDesc, R.externDesc, normDesc]
  | _ => simp [P.externDesc, R.externDesc, R.typeUse, normDesc]

theorem nameDesc_rt (n : ExternName) (d : ExternDesc) :
    R.nameDesc (P.name n ++ [P.externDesc d]) = some (normName n, d) := by
  simp [R.nameDesc, name_desc_rt, externDesc_rt, normDesc]

end Silmaril.Wasm.Component.Wat
