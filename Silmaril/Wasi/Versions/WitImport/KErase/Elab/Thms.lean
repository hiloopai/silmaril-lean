module

public import Silmaril.Wasi.Versions.WitImport.KErase.Univ.Thms

@[expose] public section

/-!
# Doc comments do not reach the elaboration of interfaces

In the context of the erased universe (`Ctx.ofUniverse U.erase`), types elaborate as in the
context of `U` (`elabTy_erase`), and a type definition, a function and an interface body
elaborate to the erased results (`elabTypeDef_erase`, `elabFunc_erase`, `elabBody_erase`). The
step that compares items with their docs, `toposort` (`List.erase` of the chosen entry, with the
`DecidableEq` of type definitions), commutes with erasing the entries (`toposort_map`): the
chosen entry is the first ready one, and erasure changes neither readiness nor which entry comes
first. Hence `elabEnv_erase`: the environment of the erased universe is the erased environment.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Wit

/-! ## Generic facts -/

/-- `List.erase` of the first element satisfying `p`, along a map that keeps `p`. -/
theorem erase_map_of_find {α : Type} [BEq α] [LawfulBEq α] {p : α → Bool} {g : α → α}
    (hp : ∀ x, p (g x) = p x) :
    ∀ (es : List α) (e : α), es.find? p = some e → (es.map g).erase (g e) = (es.erase e).map g
  | [], _, h => by simp at h
  | x :: xs, e, h => by
    by_cases hx : p x = true
    · have hxe : x = e := by simpa [List.find?_cons, hx] using h
      rw [← hxe]
      simp
    · have hxs : xs.find? p = some e := by simpa [List.find?_cons, hx] using h
      have he : p e = true := List.find?_some hxs
      have hne : g x ≠ g e := fun hg => hx (by rw [← hp x, hg, hp e]; exact he)
      have hne' : x ≠ e := fun hxe => hx (hxe ▸ he)
      have ih := erase_map_of_find hp xs e hxs
      simp [beq_iff_eq, hne, hne', ih]

/-- A `mapM` in `Except` along a pointwise map of the results. -/
theorem mapM_except_map {α β γ ε : Type} {f : α → Except ε β} {f' : α → Except ε γ} {g : β → γ}
    (h : ∀ x, f' x = (f x).map g) : ∀ l : List α, l.mapM f' = (l.mapM f).map (List.map g)
  | [] => rfl
  | x :: l => by
    rw [List.mapM_cons, List.mapM_cons, h x, mapM_except_map h l]
    cases f x <;> cases l.mapM f <;> rfl

namespace Elab

/-! ## Contexts and types -/

theorem ofUniverse_erase (U : Universe) :
    Ctx.ofUniverse U.erase = ⟨U.erase, U.ifaceIds.length, U.typeIds.length⟩ := by
  simp [Ctx.ofUniverse, Universe.ifaceIds_erase, Universe.typeIds_erase]

theorem isRes_ofUniverse_erase (U : Universe) :
    (Ctx.ofUniverse U.erase).isRes = (Ctx.ofUniverse U).isRes := by
  funext o x
  simp [Ctx.isRes, Ctx.ofUniverse, bind_erase, isRes_erase, Universe.ifaceIds_erase,
    Universe.typeIds_erase]

mutual
theorem elabTy_congr {c c' : Ctx} (h : c.isRes = c'.isRes) (o : Owner) :
    (t : Ty) → elabTy c o t = elabTy c' o t
  | .named n => by simp only [elabTy, h]
  | .list t => by simp only [elabTy, elabTy_congr h o t]
  | .fixedList t n => by simp only [elabTy, elabTy_congr h o t]
  | .map k v => by simp only [elabTy, elabTy_congr h o k, elabTy_congr h o v]
  | .tuple ts => by simp only [elabTy, elabTys_congr h o ts]
  | .option t => by simp only [elabTy, elabTy_congr h o t]
  | .result a b => by simp only [elabTy, elabTyOpt_congr h o a, elabTyOpt_congr h o b]
  | .future t => by simp only [elabTy, elabTyOpt_congr h o t]
  | .stream t => by simp only [elabTy, elabTyOpt_congr h o t]
  | .bool | .s8 | .s16 | .s32 | .s64 | .u8 | .u16 | .u32 | .u64 | .f32 | .f64 | .char
  | .string | .errorContext | .own _ | .borrow _ => by simp only [elabTy]
theorem elabTyOpt_congr {c c' : Ctx} (h : c.isRes = c'.isRes) (o : Owner) :
    (t : Option Ty) → elabTyOpt c o t = elabTyOpt c' o t
  | none => rfl
  | some t => by simp only [elabTyOpt, elabTy_congr h o t]
theorem elabTys_congr {c c' : Ctx} (h : c.isRes = c'.isRes) (o : Owner) :
    (ts : List Ty) → elabTys c o ts = elabTys c' o ts
  | [] => rfl
  | t :: ts => by simp only [elabTys, elabTy_congr h o t, elabTys_congr h o ts]
end

theorem elabTy_erase (U : Universe) (o : Owner) (t : Ty) :
    elabTy (Ctx.ofUniverse U.erase) o t = elabTy (Ctx.ofUniverse U) o t :=
  elabTy_congr (isRes_ofUniverse_erase U) o t

theorem elabTyOpt_erase (U : Universe) (o : Owner) (t : Option Ty) :
    elabTyOpt (Ctx.ofUniverse U.erase) o t = elabTyOpt (Ctx.ofUniverse U) o t :=
  elabTyOpt_congr (isRes_ofUniverse_erase U) o t

theorem elabParams_erase (U : Universe) (o : Owner) (ps : List (Name × Ty)) :
    elabParams (Ctx.ofUniverse U.erase) o ps = elabParams (Ctx.ofUniverse U) o ps := by
  simp [elabParams, elabTy_erase]

/-! ## Type definitions -/

theorem elabKind_erase (U : Universe) (o : Owner) (k : TypeDefKind) :
    elabKind (Ctx.ofUniverse U.erase) o k.erase = (elabKind (Ctx.ofUniverse U) o k).erase := by
  cases k with
  | «alias» t => cases t <;> simp [elabKind, TypeDefKind.erase, Binary.TyDefKind.erase, elabTy_erase]
  | _ => simp [elabKind, TypeDefKind.erase, Binary.TyDefKind.erase, Field.erase, Case.erase,
      Label.erase, Binary.Labeled.erase, elabTy_erase, elabTyOpt_erase]

theorem elabTypeDef_erase (U : Universe) (o : Owner) (d : TypeDef) :
    elabTypeDef (Ctx.ofUniverse U.erase) o d.erase = (elabTypeDef (Ctx.ofUniverse U) o d).erase := by
  simp [elabTypeDef, TypeDef.erase, Binary.TypeDef.erase, elabKind_erase]

theorem elabUse_erase (U : Universe) (o : Owner) (u : Use) :
    elabUse (Ctx.ofUniverse U.erase) o u = elabUse (Ctx.ofUniverse U) o u := by
  simp [elabUse, Ctx.ofUniverse, resolve_erase]

theorem elabUse_map_erase (c : Ctx) (o : Owner) (u : Use) :
    (elabUse c o u).map Binary.TypeDef.erase = elabUse c o u := by
  simp [elabUse, Binary.TypeDef.erase, Binary.TyDefKind.erase]

/-! ## Topological order -/

/-- An entry with its type definition erased. -/
def eraseEntry (e : Entry) : Entry := (e.1, e.2.1, e.2.2.map Binary.TypeDef.erase)

theorem toposort_map : ∀ (f : Nat) (placed : List Name) (es : List Entry),
    toposort f placed (es.map eraseEntry) = (toposort f placed es).map (List.map eraseEntry)
  | _, _, [] => by simp [toposort]
  | 0, _, _ :: _ => by simp [toposort]
  | f + 1, placed, e :: es => by
    have hp : ∀ x : Entry, (fun e : Entry => e.2.1.all (· ∈ placed)) (eraseEntry x) =
        (fun e : Entry => e.2.1.all (· ∈ placed)) x := fun _ => rfl
    have hf : ((e :: es).map eraseEntry).find? (fun e => e.2.1.all (· ∈ placed)) =
        ((e :: es).find? (fun e => e.2.1.all (· ∈ placed))).map eraseEntry := by
      rw [List.find?_map]
      rfl
    rw [List.map_cons, toposort, ← List.map_cons, hf, toposort]
    cases hx : (e :: es).find? (fun e => e.2.1.all (· ∈ placed)) with
    | none => rfl
    | some x =>
      simp only [Option.map_some]
      rw [erase_map_of_find hp (e :: es) x hx, show (eraseEntry x).1 = x.1 from rfl, toposort_map f]
      cases toposort f (x.1 :: placed) ((e :: es).erase x) <;> rfl

theorem scopeEntries_erase (U : Universe) (o : Owner) : ∀ items : List ScopeItem,
    scopeEntries (Ctx.ofUniverse U.erase) o (items.map ScopeItem.erase) =
      (scopeEntries (Ctx.ofUniverse U) o items).map eraseEntry
  | [] => rfl
  | .type d :: rest => by
    simp [ScopeItem.erase, scopeEntries, eraseEntry, TypeDef.refs_erase, elabTypeDef_erase,
      scopeEntries_erase U o rest]
  | .use u :: rest => by
    simp [ScopeItem.erase, scopeEntries, eraseEntry, Function.comp_def, scopeEntries_erase U o rest]

theorem filterMap_eraseEntry (l : List Entry) :
    (l.map eraseEntry).filterMap (·.2.2) = (l.filterMap (·.2.2)).map Binary.TypeDef.erase := by
  simp [List.filterMap_map, List.map_filterMap, Function.comp_def, eraseEntry]

theorem elabTypes_erase (U : Universe) (o : Owner) (items : List ScopeItem) :
    elabTypes (Ctx.ofUniverse U.erase) o (items.map ScopeItem.erase) =
      (elabTypes (Ctx.ofUniverse U) o items).map (List.map Binary.TypeDef.erase) := by
  simp only [elabTypes, scopeEntries_erase, List.length_map, toposort_map]
  cases toposort (scopeEntries (Ctx.ofUniverse U) o items).length []
    (scopeEntries (Ctx.ofUniverse U) o items) with
  | none => rfl
  | some order =>
    show some _ = some _
    rw [List.map_append, filterMap_eraseEntry]
    congr 2
    simp only [List.flatMap_map, List.map_flatMap]
    congr 1
    funext s
    cases s <;> simp [ScopeItem.erase, elabUse_erase, elabUse_map_erase]

/-! ## Functions and bodies -/

theorem elabFunc_erase (U : Universe) (o : Owner) (n : Name) (f : Func) (d : Docs) (gs : List Gate) :
    elabFunc (Ctx.ofUniverse U.erase) o n f {} gs = (elabFunc (Ctx.ofUniverse U) o n f d gs).erase := by
  simp [elabFunc, Binary.Func.erase, elabParams_erase, elabTyOpt_erase]

theorem elabResFunc_erase (U : Universe) (o : Owner) (r : Name) (rf : ResourceFunc) :
    elabResFunc (Ctx.ofUniverse U.erase) o r rf.erase =
      (elabResFunc (Ctx.ofUniverse U) o r rf).erase := by
  rcases rf with ⟨k, f, ds, gs⟩
  cases k <;> simp [elabResFunc, ResourceFunc.erase, Binary.Func.erase, elabParams_erase,
    elabTyOpt_erase]

theorem resFuncs_erase (U : Universe) (o : Owner) (d : TypeDef) :
    resFuncs (Ctx.ofUniverse U.erase) o d.erase = (resFuncs (Ctx.ofUniverse U) o d).map Binary.Func.erase := by
  rcases d with ⟨n, k, ds, gs⟩
  cases k <;> simp [resFuncs, TypeDef.erase, TypeDefKind.erase, elabResFunc_erase]

theorem itemFuncs_erase (U : Universe) (o : Owner) (it : IfaceItem) :
    itemFuncs (Ctx.ofUniverse U.erase) o it.erase = (itemFuncs (Ctx.ofUniverse U) o it).map Binary.Func.erase := by
  cases it with
  | type d => exact resFuncs_erase U o d
  | use u => rfl
  | func f => simp [itemFuncs, IfaceItem.erase, FuncDef.erase, elabFunc_erase U o f.name f.func f.docs]

theorem elabBody_erase (U : Universe) (o : Owner) (items : List IfaceItem) (d : Docs) (gs : List Gate) :
    elabBody (Ctx.ofUniverse U.erase) o (items.map IfaceItem.erase) {} gs =
      (elabBody (Ctx.ofUniverse U) o items d gs).map Binary.Interface.erase := by
  have hf : (items.map IfaceItem.erase).flatMap (itemFuncs (Ctx.ofUniverse U.erase) o) =
      (items.flatMap (itemFuncs (Ctx.ofUniverse U) o)).map Binary.Func.erase := by
    simp [List.flatMap_map, List.map_flatMap, itemFuncs_erase]
  unfold elabBody
  rw [filterMap_scope_erase, elabTypes_erase, hf]
  cases elabTypes (Ctx.ofUniverse U) o (items.filterMap IfaceItem.scope) <;> rfl

/-! ## The environment -/

theorem envItems_erase (U : Universe) :
    Silmaril.Wasi.Versions.WitImport.envItems U.erase = (Silmaril.Wasi.Versions.WitImport.envItems U).map (fun x => (x.1, x.2.erase)) := by
  simp only [Silmaril.Wasi.Versions.WitImport.envItems, Universe.erase, List.flatMap_map, List.map_flatMap,
    Package.erase_items, List.filterMap_map, List.map_filterMap, Package.erase_name]
  congr 1
  funext P
  congr 1
  funext it
  cases it <;> rfl

theorem envStep_erase (U : Universe) (x : PackageName × Interface) :
    Silmaril.Wasi.Versions.WitImport.envStep (Ctx.ofUniverse U.erase) (x.1, x.2.erase) =
      (Silmaril.Wasi.Versions.WitImport.envStep (Ctx.ofUniverse U) x).map (fun y => (y.1, y.2.erase)) := by
  have hb := elabBody_erase U (.iface ⟨x.1, x.2.name⟩) x.2.items x.2.docs x.2.gates
  unfold Silmaril.Wasi.Versions.WitImport.envStep
  simp only [Interface.erase_items, Interface.erase_docs, Interface.erase_gates, Interface.erase_name,
    hb]
  cases elabBody (Ctx.ofUniverse U) (.iface ⟨x.1, x.2.name⟩) x.2.items x.2.docs x.2.gates <;> rfl

theorem elabEnv_erase (U : Universe) :
    elabEnv (Ctx.ofUniverse U.erase) = (elabEnv (Ctx.ofUniverse U)).map Binary.Env.erase := by
  have h1 : elabEnv (Ctx.ofUniverse U.erase) =
      (Silmaril.Wasi.Versions.WitImport.envItems U.erase).mapM (Silmaril.Wasi.Versions.WitImport.envStep (Ctx.ofUniverse U.erase)) := rfl
  have h2 : elabEnv (Ctx.ofUniverse U) =
      (Silmaril.Wasi.Versions.WitImport.envItems U).mapM (Silmaril.Wasi.Versions.WitImport.envStep (Ctx.ofUniverse U)) := rfl
  rw [h1, h2, envItems_erase, List.mapM_map]
  exact mapM_except_map (fun x => envStep_erase U x) _

end Elab

end Silmaril.Wasm.Wit
