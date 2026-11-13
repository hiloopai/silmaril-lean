module

public import Silmaril.Wasi.Versions.WitImport.KErase.World.Thms
public import Silmaril.Wasi.Versions.WitImport.KErase.Valid.Thms

@[expose] public section

/-!
# Doc comments do not reach a world, a package or `Elab.elaborate`

`elabWorld_erase`: a world of the erased universe elaborates to the erased world;
`elabPackage_erase`, and the binary checks read no docs (`validB_erase`, `namesUniqueB_erase`);
hence `elaborate_erase : Elab.elaborate U.erase p fs = (Elab.elaborate U p fs).map …`, the
elaboration of the erased universe is the erased elaboration.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Wit

namespace Elab

local notation "E" => Binary.WorldItem.erase

/-- Both lists of a pair, erased. -/
def pairErase (p : List Binary.WorldItem × List Binary.WorldItem) :
    List Binary.WorldItem × List Binary.WorldItem := (p.1.map E, p.2.map E)

theorem foldlM_bind_comm0 {ε α β γ ζ η : Type} {F : α → β → Except ε α} {F' : γ → β → Except ε γ}
    {S : α → γ} {k : α → Except ε ζ} {k' : γ → Except ε η} {h : ζ → η}
    (hs : ∀ a x, F' (S a) x = (F a x).map S) (hk : ∀ b, k' (S b) = (k b).map h)
    (l : List β) (a : α) : (l.foldlM F' (S a) >>= k') = ((l.foldlM F a) >>= k).map h := by
  have hl := foldlM_except_comm (T := id) (fun a x => hs a x) l a
  rw [List.map_id] at hl
  rw [hl]
  exact except_bind_map _ _ _ _ _ hk

theorem includeInto_erase (ext : Bool) (ns : List IncludeName) (W : Binary.World)
    (imps exps : List Binary.WorldItem) :
    includeInto ext ns W.erase (imps.map E) (exps.map E) =
      (includeInto ext ns W imps exps).map pairErase := by
  have h1 : W.erase.imports.map (renameItem (renameBy ns)) =
      (W.imports.map (renameItem (renameBy ns))).map E := by
    simp [Binary.World.erase, List.map_map, Function.comp_def, renameItem_erase]
  have h2 : W.erase.exports.map (renameItem (renameBy ns)) =
      (W.exports.map (renameItem (renameBy ns))).map E := by
    simp [Binary.World.erase, List.map_map, Function.comp_def, renameItem_erase]
  unfold includeInto
  simp only [h1, h2]
  refine foldlM_bind_comm (S := List.map E) (T := E) (fun a x => includeItem_erase ext a x)
    (fun b => ?_) _ _
  exact foldlM_bind_comm (S := List.map E) (T := E) (fun a x => includeItem_erase ext a x)
    (fun b' => rfl) _ _

theorem includesOf_erase (U : Universe) (w : ItemId) (W : World) :
    includesOf (Ctx.ofUniverse U.erase) w W.erase = includesOf (Ctx.ofUniverse U) w W := by
  have hU : (Ctx.ofUniverse U.erase).U = U.erase := rfl
  unfold includesOf
  rw [hU, resolve_erase, World.erase_items, List.filterMap_map]
  congr 1
  funext it
  cases it <;> rfl

theorem except_map_pure {ε α β : Type} (f : α → β) (a : α) :
    (pure a : Except ε α).map f = pure (f a) := rfl

theorem elabFunc_erase_rev (U : Universe) (o : Owner) (n : Name) (f : Func) (d : Docs) (gs : List Gate) :
    (elabFunc (Ctx.ofUniverse U) o n f d gs).erase = elabFunc (Ctx.ofUniverse U.erase) o n f {} gs :=
  (elabFunc_erase U o n f d gs).symm

theorem preItems_erase (U : Universe) (w : ItemId) (W : World) :
    preItems (Ctx.ofUniverse U.erase) w W.erase = (preItems (Ctx.ofUniverse U) w W).map pairErase := by
  have hU : (Ctx.ofUniverse U.erase).U = U.erase := rfl
  have hU0 : (Ctx.ofUniverse U).U = U := rfl
  unfold preItems
  simp only [World.erase_items, filterMap_wscope_erase, elabTypes_erase, hU, resolve_erase]
  rcases elabTypes (Ctx.ofUniverse U) (.world w) (W.items.filterMap WorldItem.scope) with _ | types
  · rfl
  have ht : (types.map Binary.TypeDef.erase).map Binary.WorldItem.type =
      (types.map Binary.WorldItem.type).map E := by simp [Binary.WorldItem.erase]
  simp only [Option.map_some, ht]
  refine foldlM_bind_comm (S := List.map E) (T := WorldItem.erase) (fun a x => ?_)
    (fun imps => ?_) _ _
  · rcases x with ⟨⟨n, f⟩ | ⟨n, items⟩ | ⟨p⟩, ds, gs⟩ | e | u | d | inc
    all_goals try rfl
    all_goals try (simp [WorldItem.erase, WorldExtern.erase, Extern.erase, elabFunc_erase_rev,
      except_map_pure, Binary.WorldItem.erase, resFuncs_erase, Function.comp_def, hU0]; done)
    simp only [WorldItem.erase, WorldExtern.erase, Extern.erase, elabBody_erase U _ items ds gs]
    cases elabBody (Ctx.ofUniverse U) (.inline w false n) items ds gs <;>
      first | rfl | simp [except_map_pure, Binary.WorldItem.erase]
  have hinl : ∀ (n : Name) (items : List IfaceItem) (ds : Docs) (gs : List Gate),
      elabBody (Ctx.ofUniverse U.erase) (.inline w true n) (items.map IfaceItem.erase) {} gs =
        (elabBody (Ctx.ofUniverse U) (.inline w true n) items ds gs).map Binary.Interface.erase :=
    fun n items ds gs => elabBody_erase U _ items ds gs
  refine foldlM_bind_comm (S := List.map E) (T := WorldItem.erase) (fun a x => ?_)
    (fun exps => rfl) _ []
  rcases x with e | ⟨⟨n, f⟩ | ⟨n, items⟩ | ⟨p⟩, ds, gs⟩ | u | d | inc
  all_goals try rfl
  all_goals try (simp [WorldItem.erase, WorldExtern.erase, Extern.erase, elabFunc_erase_rev,
    except_map_pure, Binary.WorldItem.erase, hU0]; done)
  simp only [WorldItem.erase, WorldExtern.erase, Extern.erase, hinl n items ds gs]
  cases elabBody (Ctx.ofUniverse U) (.inline w true n) items ds gs <;>
    first | rfl | simp [except_map_pure, Binary.WorldItem.erase]

theorem elabWorld_erase (U : Universe) (env : Binary.Env) : ∀ (f : Nat) (w : ItemId),
    elabWorld (Ctx.ofUniverse U.erase) env.erase f w =
      (elabWorld (Ctx.ofUniverse U) env f w).map Binary.World.erase
  | 0, _ => rfl
  | f + 1, w => by
    have hU : (Ctx.ofUniverse U.erase).U = U.erase := rfl
    have hU0 : (Ctx.ofUniverse U).U = U := rfl
    unfold elabWorld
    simp only [hU, hU0, Universe.world?_erase]
    cases U.world? w with
    | none => rfl
    | some W =>
      simp only [Option.map_some, preItems_erase, includesOf_erase]
      refine except_bind_map _ _ _ _ _ (fun p => ?_)
      refine foldlM_bind_comm0 (S := pairErase) (fun acc inc => ?_) (fun q => ?_) _ (p.1, p.2)
      · rw [elabWorld_erase U env f inc.1]
        exact except_bind_map _ _ _ _ _ (fun W' => includeInto_erase _ _ W' acc.1 acc.2)
      · simp only [pairErase, elabWorldItems_erase]
        exact except_bind_map _ _ _ _ _ (fun r => rfl)

/-! ## Packages -/

end Elab

theorem Package.ifaces_erase (P : Package) : P.erase.ifaces = P.ifaces.map Interface.erase := by
  simp only [Package.ifaces, Package.erase_items, List.filterMap_map, List.map_filterMap]
  congr 1
  funext it
  cases it <;> rfl

theorem Package.worlds_erase (P : Package) : P.erase.worlds = P.worlds.map World.erase := by
  simp only [Package.worlds, Package.erase_items, List.filterMap_map, List.map_filterMap]
  congr 1
  funext it
  cases it <;> rfl

namespace Elab

theorem worldIds_ofUniverse_erase (U : Universe) :
    (Ctx.ofUniverse U.erase).U.worldIds = (Ctx.ofUniverse U).U.worldIds :=
  Universe.worldIds_erase U

theorem bind_mapM_comm {ε α α' β β' ζ η : Type} {f : α → Except ε β} {f' : α' → Except ε β'}
    {e : α → α'} {g : β → β'} {k : List β → Except ε ζ} {k' : List β' → Except ε η} {h : ζ → η}
    (hf : ∀ x, f' (e x) = (f x).map g) (hk : ∀ b, k' (b.map g) = (k b).map h) (l : List α) :
    ((l.map e).mapM f' >>= k') = ((l.mapM f) >>= k).map h := by
  rw [List.mapM_map, mapM_except_map (f := f) (f' := f' ∘ e) (g := g) (fun x => hf x) l]
  exact except_bind_map _ _ _ _ _ hk

theorem elabPackage_erase (U : Universe) (env : Binary.Env) (P : Package) :
    elabPackage (Ctx.ofUniverse U.erase) env.erase P.erase =
      (elabPackage (Ctx.ofUniverse U) env P).map Binary.Package.erase := by
  unfold elabPackage
  rw [Package.ifaces_erase, Package.worlds_erase, worldIds_ofUniverse_erase]
  refine bind_mapM_comm (e := Interface.erase) (g := fun x => (x.1, x.2.erase)) (fun I => ?_)
    (fun ifs => ?_) P.ifaces
  · simp only [Interface.erase_items, Interface.erase_docs, Interface.erase_gates, Interface.erase_name,
      Package.erase_name, elabBody_erase U _ I.items I.docs I.gates]
    cases elabBody (Ctx.ofUniverse U) (.iface ⟨P.name, I.name⟩) I.items I.docs I.gates <;> rfl
  · refine bind_mapM_comm (e := World.erase) (g := fun x => (x.1, x.2.erase)) (fun W => ?_)
      (fun ws => rfl) P.worlds
    simp only [World.erase_name, Package.erase_name, elabWorld_erase]
    exact except_bind_map _ _ _ _ _ (fun w => rfl)

/-! ## Binary checks -/

local notation "E" => Binary.WorldItem.erase

theorem all_map_erase {p : Binary.WorldItem → Bool} (hp : ∀ x, p (E x) = p x) (l : List Binary.WorldItem) :
    (l.map E).all p = l.all p := by
  simp [List.all_map, Function.comp_def, hp]

theorem Interface.validB_erase (b : Binary.Interface) : Interface.validB b.erase = Interface.validB b := by
  have hf : ∀ f : Binary.Func, Func.validB f.erase = Func.validB f := fun _ => rfl
  simp [Interface.validB, Binary.Interface.erase, Function.comp_def, hf]

theorem WorldItem.validB_erase (it : Binary.WorldItem) : WorldItem.validB (E it) = WorldItem.validB it := by
  cases it with
  | ifaceInline n b => simp [WorldItem.validB, Binary.WorldItem.erase, Interface.validB_erase]
  | _ => rfl

theorem Package.validB_erase (p : Binary.Package) (deps : Binary.Env) :
    Package.validB p.erase deps.erase = Package.validB p deps := by
  simp [Package.validB, Binary.Package.erase, Binary.Env.erase, Binary.Package.env, Binary.World.erase,
    Interface.validB_erase, WorldItem.validB_erase, Function.comp_def]

theorem labelsUniqueB_erase (k : Binary.TyDefKind) : labelsUniqueB k.erase = labelsUniqueB k := by
  cases k <;> simp [labelsUniqueB, Binary.TyDefKind.erase, Binary.Labeled.erase, Function.comp_def]

theorem Interface.namesUniqueB_erase (b : Binary.Interface) :
    Interface.namesUniqueB b.erase = Interface.namesUniqueB b := by
  simp [Interface.namesUniqueB, Binary.Interface.erase, Binary.TypeDef.erase, Function.comp_def,
    labelsUniqueB_erase]

theorem World.namesUniqueB_erase (w : Binary.World) : World.namesUniqueB w.erase = World.namesUniqueB w := by
  have hi : (w.erase.imports ++ w.erase.exports) = (w.imports ++ w.exports).map E := by
    simp [Binary.World.erase]
  have he : w.erase.exports = w.exports.map E := rfl
  have hm : w.erase.imports = w.imports.map E := rfl
  unfold World.namesUniqueB
  rw [hi, he, hm, map_key_erase, map_key_erase, all_map_erase ?h1, all_map_erase ?h2]
  case h1 => intro x; cases x <;> rfl
  case h2 =>
    intro x
    cases x <;> simp [Binary.WorldItem.erase, Interface.namesUniqueB_erase, Binary.TypeDef.erase,
      labelsUniqueB_erase]

theorem Package.namesUniqueB_erase (p : Binary.Package) :
    Package.namesUniqueB p.erase = Package.namesUniqueB p := by
  simp [Package.namesUniqueB, Binary.Package.erase, Function.comp_def, Interface.namesUniqueB_erase,
    World.namesUniqueB_erase]

end Elab

end Silmaril.Wasm.Wit
