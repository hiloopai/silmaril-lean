module

public import Silmaril.Proofs.Wasm.Component.Wat.Atoms

/-!
# Component WAT: the printer's atoms are well formed

Every atom the printer writes is a keyword (a literal run of `idchar`s) or a
decimal number, so `Sexp.WF (toSexp c)` for every component `c`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Wat

open Silmaril.Wasm.Component.Binary Sexp

/-- The simp set of well-formedness: structure, numbers, names and keywords. -/
syntax "wf_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| wf_simp) => `(tactic| simp (config := { decide := true }) [kw, wf_atom, wf_list,
      wfl_cons, wfl_append, wfl_map, wf_num, wf_nm, wf_bytesS])
  | `(tactic| wf_simp [$args,*]) => `(tactic| simp (config := { decide := true }) [kw, wf_atom,
      wf_list, wfl_cons, wfl_append, wfl_map, wf_num, wf_nm, wf_bytesS, $args,*])

theorem wf_coreSort (s : CoreSort) : WF (P.coreSort s) := by cases s <;> wf_simp [P.coreSort]
theorem wfl_sort (s : ItemSort) : WFL (P.sort s) := by
  cases s with
  | core c => cases c <;> wf_simp [P.sort, P.coreSort]
  | _ => wf_simp [P.sort]
theorem wf_sortIdx (x : SortIdx) : WF (P.sortIdx x) := by
  simp [P.sortIdx, wfl_sort]
theorem wf_coreSortIdx (x : CoreSortIdx) : WF (P.coreSortIdx x) := by
  wf_simp [P.coreSortIdx, wf_coreSort]
theorem wf_attr (a : Attribute) : WF (P.attr a) := by cases a <;> wf_simp [P.attr]
theorem wfl_name (n : ExternName) : WFL (P.name n) := by
  obtain ⟨s, f⟩ := n
  cases f <;> simp [P.name, wf_attr]
theorem wf_coreInstance (x : CoreInstanceExpr) : WF (P.coreInstance x) := by
  cases x <;> wf_simp [P.coreInstance, wf_coreSortIdx]
theorem wf_inst (x : InstanceExpr) : WF (P.inst x) := by
  cases x <;> wf_simp [P.inst, wf_sortIdx, wfl_name]
theorem wf_alias (a : Alias) : WF (P.alias_ a) := by
  obtain ⟨s, t⟩ := a
  cases t <;> wf_simp [P.alias_, wfl_sort]
theorem wf_coreValType (t : CoreValType) : WF (P.coreValType t) := by
  cases t <;> wf_simp [P.coreValType]
theorem wf_coreImportDesc (d : CoreImportDesc) : WF (P.coreImportDesc d) := by
  cases d with
  | table t l =>
    obtain ⟨m, n⟩ := l
    cases n <;> wf_simp [P.coreImportDesc, P.limits, wf_coreValType]
  | memory l =>
    obtain ⟨m, n⟩ := l
    cases n <;> wf_simp [P.coreImportDesc, P.limits]
  | global t m => cases m <;> wf_simp [P.coreImportDesc, wf_coreValType]
  | _ => wf_simp [P.coreImportDesc]
theorem wf_coreFuncType (t : CoreFuncType) : WF (P.coreFuncType t) := by
  obtain ⟨ps, rs⟩ := t
  simp only [P.coreFuncType]
  split <;> split <;> wf_simp [wf_coreValType]
theorem wf_moduleDecl (d : ModuleDecl) : WF (P.moduleDecl d) := by
  cases d <;> wf_simp [P.moduleDecl, wf_coreImportDesc, wf_coreFuncType]
theorem wf_coreType (t : CoreType) : WF (P.coreType t) := by
  cases t <;> wf_simp [P.coreType, wf_coreFuncType, wf_moduleDecl]
theorem wf_prim (p : PrimValType) : WF (P.prim p) := by cases p <;> wf_simp [P.prim]
theorem wf_valType (t : Silmaril.Wasm.Component.Binary.ValType) : WF (P.valType t) := by
  cases t <;> simp [P.valType, wf_prim]
theorem wf_defValType (d : DefValType) : WF (P.defValType d) := by
  cases d with
  | variant cs =>
    wf_simp [P.defValType]
    intro n t _
    cases t <;> simp [wf_valType]
  | result ok err => cases ok <;> cases err <;> wf_simp [P.defValType, wf_valType]
  | stream t => cases t <;> wf_simp [P.defValType, wf_valType]
  | future t => cases t <;> wf_simp [P.defValType, wf_valType]
  | _ => wf_simp [P.defValType, wf_valType, wf_prim]
theorem wf_funcType (f : Silmaril.Wasm.Component.Binary.FuncType) : WF (P.funcType f) := by
  obtain ⟨ps, r, a⟩ := f
  cases a <;> cases r <;> wf_simp [P.funcType, wf_valType]
theorem wf_externDesc (d : ExternDesc) : WF (P.externDesc d) := by
  cases d with
  | value b => cases b with
    | eq => wf_simp [P.externDesc]
    | type t => cases t <;> wf_simp [P.externDesc, wf_prim]
  | type b => cases b <;> wf_simp [P.externDesc]
  | _ => wf_simp [P.externDesc]

mutual
theorem wf_defType : ∀ t : DefType, WF (P.defType t)
  | .val d => wf_defValType d
  | .func f => wf_funcType f
  | .component ds => by
    have := wfl_componentDecls ds
    wf_simp [P.defType, this]
  | .instance ds => by
    have := wfl_instanceDecls ds
    wf_simp [P.defType, this]
  | .resource r d => by cases d <;> wf_simp [P.defType, wf_coreValType]

theorem wf_instanceDecl : ∀ d : InstanceDecl, WF (P.instanceDecl d)
  | .coreType t => by wf_simp [P.instanceDecl, wf_coreType]
  | .type t => by
    have := wf_defType t
    wf_simp [P.instanceDecl, this]
  | .alias a => wf_alias a
  | .export n d => by wf_simp [P.instanceDecl, wfl_name, wf_externDesc]

theorem wf_componentDecl : ∀ d : ComponentDecl, WF (P.componentDecl d)
  | .import n d => by wf_simp [P.componentDecl, wfl_name, wf_externDesc]
  | .inst d => wf_instanceDecl d

theorem wfl_instanceDecls : ∀ ds : List InstanceDecl, WFL (P.instanceDecls ds)
  | [] => wfl_nil
  | d :: ds => (wfl_cons _ _).2 ⟨wf_instanceDecl d, wfl_instanceDecls ds⟩

theorem wfl_componentDecls : ∀ ds : List ComponentDecl, WFL (P.componentDecls ds)
  | [] => wfl_nil
  | d :: ds => (wfl_cons _ _).2 ⟨wf_componentDecl d, wfl_componentDecls ds⟩
end

theorem wf_canonOpt (o : CanonOpt) : WF (P.canonOpt o) := by cases o <;> wf_simp [P.canonOpt]
theorem wf_canon (c : Canon) : WF (P.canon c) := by cases c <;> wf_simp [P.canon, wf_canonOpt]
theorem wf_start (s : Start) : WF (P.start s) := by
  obtain ⟨f, a, r⟩ := s
  wf_simp [P.start]
  induction r with
  | zero => exact wfl_nil
  | succ r ih => rw [List.replicate_succ]; wf_simp [ih]
theorem wf_import (i : Silmaril.Wasm.Component.Binary.Import) : WF (P.import_ i) := by
  wf_simp [P.import_, wfl_name, wf_externDesc]
theorem wf_export (e : Export) : WF (P.export_ e) := by
  cases h : e.desc <;> wf_simp [P.export_, wfl_name, wf_sortIdx, wf_externDesc, h]
theorem wf_value (v : Value) : WF (P.value v) := by wf_simp [P.value, wf_valType]

mutual
theorem wfl_section : ∀ s : Section, WFL (P.section_ s)
  | .component (.mk ss) => by
    have := wfl_sections ss
    wf_simp [P.section_, P.ast, this]
  | .custom n d => by wf_simp [P.section_]
  | .coreModule b => by wf_simp [P.section_]
  | .coreInstances xs => by wf_simp [P.section_, wf_coreInstance]
  | .coreTypes xs => by wf_simp [P.section_, wf_coreType]
  | .instances xs => by wf_simp [P.section_, wf_inst]
  | .aliases xs => by wf_simp [P.section_, wf_alias]
  | .types xs => by wf_simp [P.section_, wf_defType]
  | .canons xs => by wf_simp [P.section_, wf_canon]
  | .start s => by wf_simp [P.section_, wf_start]
  | .imports xs => by wf_simp [P.section_, wf_import]
  | .exports xs => by wf_simp [P.section_, wf_export]
  | .values xs => by wf_simp [P.section_, wf_value]

theorem wfl_sections : ∀ ss : List Section, WFL (P.sections ss)
  | [] => wfl_nil
  | s :: ss => (wfl_append _ _).2 ⟨wfl_section s, wfl_sections ss⟩
end

theorem wf_toSexp (c : Ast) : WF (toSexp c) := by
  obtain ⟨ss⟩ := c
  have := wfl_sections ss
  wf_simp [toSexp, P.ast, this]

end Silmaril.Wasm.Component.Wat
