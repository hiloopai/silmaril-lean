module

public import Silmaril.Wasm.Tools.Component.Unbundle.Defs

/-!
# Specification of `wasm-tools component unbundle`

* `mapAst_id`, `mapAst_comp`: the index rewrite is functorial in the index map, so
  `unshift_shift`: shifting the top-level core-type and core-module indices past the new
  definitions and shifting them back gives the component back. The rewrite changes nothing but
  the core-type and core-module positions of the top level (`mapAst_id`: a map that is the
  identity on both leaves every section unchanged).
* `unbundle_not_component`: a non-component input is written back unchanged, with no module.
* `unbundle_modules`: the modules written are the component's modules (`modulesOf`, parser
  order) larger than the threshold, in order.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Unbundle

open Silmaril.Wasm.Component.Binary (CoreType ModuleDecl ExternDesc Alias DefType ComponentDecl
  InstanceDecl CoreInstanceExpr InstanceExpr Import Export SortIdx)
open Silmaril.Wasm.Component.BinaryP3 (Section Ast Canon)

/-! ## Leaves -/

theorem tyAt_id (d i : Nat) : tyAt IxMap.id d i = i := by unfold tyAt; split <;> rfl
theorem outerTyAt_id (d c i : Nat) : outerTyAt IxMap.id d c i = i := by
  unfold outerTyAt; split <;> rfl
theorem modAt_id (d i : Nat) : modAt IxMap.id d i = i := by unfold modAt; split <;> rfl
theorem outerModAt_id (d c i : Nat) : outerModAt IxMap.id d c i = i := by
  unfold outerModAt; split <;> rfl

theorem tyAt_comp (f g : IxMap) (d i : Nat) : tyAt f d (tyAt g d i) = tyAt (f.comp g) d i := by
  unfold tyAt IxMap.comp; split <;> rfl
theorem outerTyAt_comp (f g : IxMap) (d c i : Nat) :
    outerTyAt f d c (outerTyAt g d c i) = outerTyAt (f.comp g) d c i := by
  unfold outerTyAt IxMap.comp; split <;> rfl
theorem modAt_comp (f g : IxMap) (d i : Nat) : modAt f d (modAt g d i) = modAt (f.comp g) d i := by
  unfold modAt IxMap.comp; split <;> rfl
theorem outerModAt_comp (f g : IxMap) (d c i : Nat) :
    outerModAt f d c (outerModAt g d c i) = outerModAt (f.comp g) d c i := by
  unfold outerModAt IxMap.comp; split <;> rfl

theorem mapModuleDecl_id (d : Nat) (x : ModuleDecl) : mapModuleDecl IxMap.id d x = x := by
  cases x <;> simp [mapModuleDecl, outerTyAt_id]

theorem mapModuleDecl_comp (f g : IxMap) (d : Nat) (x : ModuleDecl) :
    mapModuleDecl f d (mapModuleDecl g d x) = mapModuleDecl (f.comp g) d x := by
  cases x <;> simp [mapModuleDecl, outerTyAt_comp]

/-- A pointwise identity is an identity on lists. -/
theorem map_id_of {α : Type} {f : α → α} (h : ∀ x, f x = x) (l : List α) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, h, ih]

/-- A pointwise composition is a composition on lists. -/
theorem map_comp_of {α : Type} {f g k : α → α} (h : ∀ x, f (g x) = k x) (l : List α) :
    (l.map g).map f = l.map k := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, h, ih]

theorem mapCoreType_id (d : Nat) (x : CoreType) : mapCoreType IxMap.id d x = x := by
  cases x with
  | func _ => rfl
  | module ds => simp only [mapCoreType, map_id_of (mapModuleDecl_id (d + 1))]

theorem mapCoreType_comp (f g : IxMap) (d : Nat) (x : CoreType) :
    mapCoreType f d (mapCoreType g d x) = mapCoreType (f.comp g) d x := by
  cases x with
  | func _ => rfl
  | module ds => simp only [mapCoreType, map_comp_of (mapModuleDecl_comp f g (d + 1))]

theorem mapExternDesc_id (d : Nat) (x : ExternDesc) : mapExternDesc IxMap.id d x = x := by
  cases x <;> simp [mapExternDesc, tyAt_id]

theorem mapExternDesc_comp (f g : IxMap) (d : Nat) (x : ExternDesc) :
    mapExternDesc f d (mapExternDesc g d x) = mapExternDesc (f.comp g) d x := by
  cases x <;> simp [mapExternDesc, tyAt_comp]

theorem mapAlias_id (d : Nat) (a : Alias) : mapAlias IxMap.id d a = a := by
  obtain ⟨s, t⟩ := a
  rcases s with ⟨cs⟩ | _ | _ | _ | _ | _ <;> (try cases cs) <;> cases t <;>
    first | rfl | simp [mapAlias, outerModAt_id, outerTyAt_id]

theorem mapAlias_comp (f g : IxMap) (d : Nat) (a : Alias) :
    mapAlias f d (mapAlias g d a) = mapAlias (f.comp g) d a := by
  obtain ⟨s, t⟩ := a
  rcases s with ⟨cs⟩ | _ | _ | _ | _ | _ <;> (try cases cs) <;> cases t <;>
    first | rfl | simp [mapAlias, outerModAt_comp, outerTyAt_comp]

theorem mapSortIdx_id (d : Nat) (s : SortIdx) : mapSortIdx IxMap.id d s = s := by
  obtain ⟨so, i⟩ := s
  rcases so with ⟨cs⟩ | _ | _ | _ | _ | _ <;> (try cases cs) <;>
    first | rfl | simp [mapSortIdx, modAt_id]

theorem mapSortIdx_comp (f g : IxMap) (d : Nat) (s : SortIdx) :
    mapSortIdx f d (mapSortIdx g d s) = mapSortIdx (f.comp g) d s := by
  obtain ⟨so, i⟩ := s
  rcases so with ⟨cs⟩ | _ | _ | _ | _ | _ <;> (try cases cs) <;>
    first | rfl | simp [mapSortIdx, modAt_comp]

/-! ## Type definitions -/

mutual
theorem mapDefType_id (d : Nat) : ∀ t : DefType, mapDefType IxMap.id d t = t
  | .component ds => by simp only [mapDefType, mapCDecls_id]
  | .instance ds => by simp only [mapDefType, mapIDecls_id]
  | .val _ => rfl
  | .func _ => rfl
  | .resource _ _ => rfl

theorem mapCDecls_id (d : Nat) : ∀ ds : List ComponentDecl, mapCDecls IxMap.id d ds = ds
  | [] => rfl
  | x :: xs => by simp only [mapCDecls, mapCDecl_id, mapCDecls_id]

theorem mapCDecl_id (d : Nat) : ∀ x : ComponentDecl, mapCDecl IxMap.id d x = x
  | .import n desc => by simp only [mapCDecl, mapExternDesc_id]
  | .inst i => by simp only [mapCDecl, mapIDecl_id]

theorem mapIDecls_id (d : Nat) : ∀ ds : List InstanceDecl, mapIDecls IxMap.id d ds = ds
  | [] => rfl
  | x :: xs => by simp only [mapIDecls, mapIDecl_id, mapIDecls_id]

theorem mapIDecl_id (d : Nat) : ∀ x : InstanceDecl, mapIDecl IxMap.id d x = x
  | .coreType t => by simp only [mapIDecl, mapCoreType_id]
  | .type t => by simp only [mapIDecl, mapDefType_id]
  | .alias a => by simp only [mapIDecl, mapAlias_id]
  | .export n desc => by simp only [mapIDecl, mapExternDesc_id]
end

mutual
theorem mapDefType_comp (f g : IxMap) (d : Nat) :
    ∀ t : DefType, mapDefType f d (mapDefType g d t) = mapDefType (f.comp g) d t
  | .component ds => by simp only [mapDefType, mapCDecls_comp]
  | .instance ds => by simp only [mapDefType, mapIDecls_comp]
  | .val _ => rfl
  | .func _ => rfl
  | .resource _ _ => rfl

theorem mapCDecls_comp (f g : IxMap) (d : Nat) :
    ∀ ds : List ComponentDecl, mapCDecls f d (mapCDecls g d ds) = mapCDecls (f.comp g) d ds
  | [] => rfl
  | x :: xs => by simp only [mapCDecls, mapCDecl_comp, mapCDecls_comp]

theorem mapCDecl_comp (f g : IxMap) (d : Nat) :
    ∀ x : ComponentDecl, mapCDecl f d (mapCDecl g d x) = mapCDecl (f.comp g) d x
  | .import n desc => by simp only [mapCDecl, mapExternDesc_comp]
  | .inst i => by simp only [mapCDecl, mapIDecl_comp]

theorem mapIDecls_comp (f g : IxMap) (d : Nat) :
    ∀ ds : List InstanceDecl, mapIDecls f d (mapIDecls g d ds) = mapIDecls (f.comp g) d ds
  | [] => rfl
  | x :: xs => by simp only [mapIDecls, mapIDecl_comp, mapIDecls_comp]

theorem mapIDecl_comp (f g : IxMap) (d : Nat) :
    ∀ x : InstanceDecl, mapIDecl f d (mapIDecl g d x) = mapIDecl (f.comp g) d x
  | .coreType t => by simp only [mapIDecl, mapCoreType_comp]
  | .type t => by simp only [mapIDecl, mapDefType_comp]
  | .alias a => by simp only [mapIDecl, mapAlias_comp]
  | .export n desc => by simp only [mapIDecl, mapExternDesc_comp]
end

/-! ## Sections -/

theorem mapCanon_id (d : Nat) (c : Canon) : mapCanon IxMap.id d c = c := by
  cases c <;> simp [mapCanon, tyAt_id]

theorem mapCanon_comp (f g : IxMap) (d : Nat) (c : Canon) :
    mapCanon f d (mapCanon g d c) = mapCanon (f.comp g) d c := by
  cases c <;> simp [mapCanon, tyAt_comp]

theorem mapCoreInstance_id (d : Nat) (x : CoreInstanceExpr) : mapCoreInstance IxMap.id d x = x := by
  cases x <;> simp [mapCoreInstance, modAt_id]

theorem mapCoreInstance_comp (f g : IxMap) (d : Nat) (x : CoreInstanceExpr) :
    mapCoreInstance f d (mapCoreInstance g d x) = mapCoreInstance (f.comp g) d x := by
  cases x <;> simp [mapCoreInstance, modAt_comp]

theorem mapInstance_id (d : Nat) (x : InstanceExpr) : mapInstance IxMap.id d x = x := by
  cases x <;> simp [mapInstance, mapSortIdx_id]

theorem mapInstance_comp (f g : IxMap) (d : Nat) (x : InstanceExpr) :
    mapInstance f d (mapInstance g d x) = mapInstance (f.comp g) d x := by
  cases x <;> simp [mapInstance, mapSortIdx_comp, Function.comp_def]

theorem mapImport_id (d : Nat) (x : Import) : mapImport IxMap.id d x = x := by
  simp [mapImport, mapExternDesc_id]

theorem mapImport_comp (f g : IxMap) (d : Nat) (x : Import) :
    mapImport f d (mapImport g d x) = mapImport (f.comp g) d x := by
  simp [mapImport, mapExternDesc_comp]

theorem mapExport_id (d : Nat) (x : Export) : mapExport IxMap.id d x = x := by
  obtain ⟨n, s, desc⟩ := x
  cases desc <;> simp [mapExport, mapSortIdx_id, mapExternDesc_id]

theorem mapExport_comp (f g : IxMap) (d : Nat) (x : Export) :
    mapExport f d (mapExport g d x) = mapExport (f.comp g) d x := by
  obtain ⟨n, s, desc⟩ := x
  cases desc <;> simp [mapExport, mapSortIdx_comp, mapExternDesc_comp]

mutual
/-- **Identity**: the identity map leaves a component unchanged. -/
theorem mapAst_id (d : Nat) : ∀ c : Ast, mapAst IxMap.id d c = c
  | .mk ss => by simp only [mapAst, mapSections_id]

theorem mapSections_id (d : Nat) : ∀ ss : List Section, mapSections IxMap.id d ss = ss
  | [] => rfl
  | s :: ss => by simp only [mapSections, mapSection_id, mapSections_id]

theorem mapSection_id (d : Nat) : ∀ s : Section, mapSection IxMap.id d s = s
  | .component c => by simp only [mapSection, mapAst_id]
  | .coreInstances xs => by simp only [mapSection, map_id_of (mapCoreInstance_id d)]
  | .coreTypes xs => by simp only [mapSection, map_id_of (mapCoreType_id d)]
  | .instances xs => by simp only [mapSection, map_id_of (mapInstance_id d)]
  | .aliases xs => by simp only [mapSection, map_id_of (mapAlias_id d)]
  | .types xs => by simp only [mapSection, map_id_of (mapDefType_id d)]
  | .canons xs => by simp only [mapSection, map_id_of (mapCanon_id d)]
  | .imports xs => by simp only [mapSection, map_id_of (mapImport_id d)]
  | .exports xs => by simp only [mapSection, map_id_of (mapExport_id d)]
  | .custom _ _ => rfl
  | .coreModule _ => rfl
  | .start _ => rfl
  | .values _ => rfl
end

mutual
/-- **Composition**: rewriting by `g`, then by `f`, is rewriting by `f ∘ g`. -/
theorem mapAst_comp (f g : IxMap) (d : Nat) :
    ∀ c : Ast, mapAst f d (mapAst g d c) = mapAst (f.comp g) d c
  | .mk ss => by simp only [mapAst, mapSections_comp]

theorem mapSections_comp (f g : IxMap) (d : Nat) :
    ∀ ss : List Section, mapSections f d (mapSections g d ss) = mapSections (f.comp g) d ss
  | [] => rfl
  | s :: ss => by simp only [mapSections, mapSection_comp, mapSections_comp]

theorem mapSection_comp (f g : IxMap) (d : Nat) :
    ∀ s : Section, mapSection f d (mapSection g d s) = mapSection (f.comp g) d s
  | .component c => by simp only [mapSection, mapAst_comp]
  | .coreInstances xs => by simp only [mapSection, map_comp_of (mapCoreInstance_comp f g d)]
  | .coreTypes xs => by simp only [mapSection, map_comp_of (mapCoreType_comp f g d)]
  | .instances xs => by simp only [mapSection, map_comp_of (mapInstance_comp f g d)]
  | .aliases xs => by simp only [mapSection, map_comp_of (mapAlias_comp f g d)]
  | .types xs => by simp only [mapSection, map_comp_of (mapDefType_comp f g d)]
  | .canons xs => by simp only [mapSection, map_comp_of (mapCanon_comp f g d)]
  | .imports xs => by simp only [mapSection, map_comp_of (mapImport_comp f g d)]
  | .exports xs => by simp only [mapSection, map_comp_of (mapExport_comp f g d)]
  | .custom _ _ => rfl
  | .coreModule _ => rfl
  | .start _ => rfl
  | .values _ => rfl
end

theorem unshift_comp_shift (t m : Nat) : (IxMap.unshift t m).comp (IxMap.shift t m) = IxMap.id := by
  simp only [IxMap.comp, IxMap.unshift, IxMap.shift, IxMap.id]
  congr 1 <;> funext i <;> simp

/-- **Nothing is lost**: shifting the top-level core types and modules by `t` and `m` and
shifting back gives the component back. -/
theorem unshift_shift (t m d : Nat) (c : Ast) :
    mapAst (IxMap.unshift t m) d (mapAst (IxMap.shift t m) d c) = c := by
  rw [mapAst_comp, unshift_comp_shift, mapAst_id]

/-! ## The subcommand -/

/-- A non-component input is written back unchanged. -/
theorem unbundle_not_component {b : ByteArray} (h : isComponent b = false) (t : Nat) :
    unbundle b t = .ok (b, []) := by
  simp [unbundle, h]
  rfl

end Silmaril.Wasm.Tools.Component.Unbundle
