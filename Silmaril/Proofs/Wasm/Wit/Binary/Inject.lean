module

public import Silmaril.Wasm.Wit.Binary.Docs.Defs
public import Silmaril.Proofs.Wasm.Wit.Binary.Canon

/-!
# Docs injection inverts docs extraction

`inject_docsJson`: putting the `package-docs` metadata of a
package with distinct names into its normal form gives the package back, its
functions in wit-component's order. The metadata objects are looked up by
distinct keys (`lookupKey_metaMap`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

/-! ## Looking up keys -/

/-- The value of key `k` among object members. -/
def lookupKey (k : String) (fs : List (String × JVal)) : Option JVal := (fs.find? (·.1 = k)).map (·.2)

theorem getObj_jobj (k : String) (fs : List (String × JVal)) : getObj k (jobj fs) = lookupKey k fs := by
  cases fs <;> rfl

theorem get_obj (k : String) (fs : List (String × JVal)) : (JVal.obj fs).get k = lookupKey k fs := rfl

theorem lookupKey_append (k : String) (a b : List (String × JVal)) :
    lookupKey k (a ++ b) = (lookupKey k a).or (lookupKey k b) := by
  simp only [lookupKey, List.find?_append]
  cases a.find? (·.1 = k) <;> rfl

theorem lookupKey_jopt (k k' : String) (a : Option JVal) :
    lookupKey k (jopt k' a) = if k' = k then a else none := by
  cases a <;> by_cases h : k' = k <;> simp [lookupKey, jopt, h]

theorem lookupKey_jmap (k k' : String) (fs : List (String × JVal)) :
    lookupKey k (jmap k' fs) = if k' = k then jobj fs else none := by
  cases fs <;> by_cases h : k' = k <;> simp [lookupKey, jmap, jobj, h]

theorem getStr?_of (k : String) (v : Option JVal) :
    getStr? k v = match v.bind (·.get k) with | some (.str s) => some s | _ => none := by
  cases v <;> rfl

/-- A key-value list with distinct keys, built from `xs`: the value of `x`'s
key is `x`'s value. -/
theorem lookupKey_filterMap {α : Type} (key : α → String) (g : α → Option JVal) :
    ∀ {xs : List α}, (xs.map key).Nodup → ∀ {x : α}, x ∈ xs →
      lookupKey (key x) (xs.filterMap fun y => (g y).map (key y, ·)) = g x
  | [], _, _, hx => absurd hx (List.not_mem_nil)
  | y :: ys, hn, x, hx => by
    have hn' : key y ∉ ys.map key ∧ (ys.map key).Nodup := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hx with rfl | hx'
    · cases hg : g x with
      | none =>
        have hnot : ∀ z ∈ ys, key z ≠ key x := fun z hz e => hn'.1 (e ▸ List.mem_map_of_mem hz)
        simp only [List.filterMap_cons, hg, Option.map_none]
        simp only [lookupKey, Option.map_eq_none_iff, List.find?_eq_none, List.mem_filterMap,
          decide_eq_true_eq]
        rintro ⟨k, v⟩ ⟨z, hz, hzv⟩
        cases hgz : g z with
        | none => rw [hgz] at hzv; cases hzv
        | some w => rw [hgz] at hzv; cases hzv; exact hnot z hz
      | some v => simp [hg, lookupKey]
    · have hne : key y ≠ key x := fun e => hn'.1 (e ▸ List.mem_map_of_mem hx')
      have ih := lookupKey_filterMap key g hn'.2 hx'
      cases hg : g y with
      | none => simpa [List.filterMap_cons, hg] using ih
      | some v => simpa [List.filterMap_cons, hg, lookupKey, hne] using ih

theorem metaMap_eq {α : Type} (name : α → String) (m : α → Option JVal) (xs : List α) :
    metaMap name m xs = xs.filterMap fun y => (m y).map (name y, ·) := rfl

/-! ## Stability -/

theorem Stability.ofJson_json (st : Stability) : Stability.ofJson st.json = st := by
  cases st with
  | unknown => rfl
  | stable v d => cases d <;> rfl
  | unstable f d => cases d <;> rfl

/-- The string of a JSON string. -/
def strOf : Option JVal → Option String
  | some (.str s) => some s
  | _ => none

theorem getStr?_eq (k : String) (v : Option JVal) : getStr? k v = strOf (getObj k v) := by
  cases v with
  | none => rfl
  | some j => simp only [getStr?, getObj, Option.bind_some, JVal.getStr, strOf]; split <;> simp_all

theorem strOf_jstr (d : Option String) : strOf (jstr d) = d := by cases d <;> rfl

/-- The head of a metadata object read back. -/
theorem head_lookup (d : Option String) (st : Stability) (rest : List (String × JVal))
    (hd : lookupKey "docs" rest = none) (hs : lookupKey "stability" rest = none) :
    getStr? "docs" (jobj (headJson d st ++ rest)) = d ∧
      Stability.ofJson (getObj "stability" (jobj (headJson d st ++ rest))) = st := by
  simp only [getStr?_eq, getObj_jobj, headJson, lookupKey_append, lookupKey_jopt, hd, hs]
  constructor
  · cases d <;> simp [jstr, strOf]
  · cases d <;> simp [Stability.ofJson_json]

/-! ## Labels, types, functions -/

theorem labelDocs_eq {α : Type} (ls : List (Labeled α)) :
    labelDocs ls = ls.filterMap fun l => (jstr l.docs).map (l.name, ·) := by
  simp only [labelDocs, jstr, Option.map_map]; rfl

theorem label_inject {α : Type} {ls : List (Labeled α)} (hn : (ls.map (·.name)).Nodup) :
    (ls.map Labeled.strip).map (Labeled.inject (jobj (labelDocs ls))) = ls := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ls]
  refine List.map_congr_left fun l hl => ?_
  have hk : lookupKey l.name (labelDocs ls) = jstr l.docs := by
    rw [labelDocs_eq]; exact lookupKey_filterMap (·.name) (fun l => jstr l.docs) hn hl
  simp only [Function.comp_apply, Labeled.inject, Labeled.strip, getStr?_eq, getObj_jobj, hk,
    strOf_jstr, id]

theorem kind_inject {k : TyDefKind} (hk : k.LabelsUnique) : k.strip.inject (jobj k.items) = k := by
  cases k with
  | record fs => simp only [TyDefKind.strip, TyDefKind.inject, TyDefKind.items, label_inject hk]
  | variant cs => simp only [TyDefKind.strip, TyDefKind.inject, TyDefKind.items, label_inject hk]
  | enum cs => simp only [TyDefKind.strip, TyDefKind.inject, TyDefKind.items, label_inject hk]
  | flags fs => simp only [TyDefKind.strip, TyDefKind.inject, TyDefKind.items, label_inject hk]
  | resource => rfl
  | type t => rfl

/-- **A type's metadata put back.** -/
theorem typeDef_inject {td : TypeDef} (hk : td.kind.LabelsUnique) {m : Option JVal}
    (hm : getObj td.name m = td.meta) : td.strip.inject m = td := by
  obtain ⟨n, k, d, st⟩ := td
  have hmeta : getObj n m = jobj (headJson d st ++ jmap "items" k.items) := hm
  have hh := head_lookup d st (jmap "items" k.items) (by simp [lookupKey_jmap]) (by simp [lookupKey_jmap])
  have hi : getObj "items" (jobj (headJson d st ++ jmap "items" k.items)) = jobj k.items := by
    simp [getObj_jobj, headJson, lookupKey_append, lookupKey_jopt, lookupKey_jmap]
  simp only [TypeDef.inject, TypeDef.strip, hmeta, hh.1, hh.2, hi, kind_inject hk]

/-- **A function's metadata put back.** -/
theorem func_inject {f : Func} {m : Option JVal} (hm : getObj f.mangled m = f.meta) : f.strip.inject m = f := by
  have hs : f.strip.mangled = f.mangled := rfl
  have hmeta : getObj f.mangled m = jobj (headJson f.docs f.stability ++ []) := by
    rw [List.append_nil]; exact hm
  have hh := head_lookup f.docs f.stability [] rfl rfl
  simp only [Func.inject, hs, hmeta, hh.1, hh.2]
  rfl

theorem mem_types_inject {b : Interface} (hn : (b.types.map (·.name)).Nodup) {td : TypeDef} (htd : td ∈ b.types) :
    getObj td.name (jobj (metaMap TypeDef.name TypeDef.meta b.types)) = td.meta := by
  rw [getObj_jobj, metaMap_eq]; exact lookupKey_filterMap TypeDef.name TypeDef.meta hn htd

theorem mem_funcs_inject {fs : List Func} (hn : (fs.map Func.mangled).Nodup) {f : Func} (hf : f ∈ fs) :
    getObj f.mangled (jobj (metaMap Func.mangled Func.meta fs)) = f.meta := by
  rw [getObj_jobj, metaMap_eq]; exact lookupKey_filterMap Func.mangled Func.meta hn hf

/-- **An interface's metadata put back**, functions in wit-component's order. -/
theorem iface_inject {b : Interface} (hu : b.NamesUnique) {m : Option JVal} (hm : m = b.meta) :
    b.normalize.inject m = b.canon := by
  obtain ⟨htn, hfn, hlab⟩ := hu
  have hmeta : m = jobj (headJson b.docs b.stability ++ (jmap "funcs" (metaMap Func.mangled Func.meta b.funcs) ++
      jmap "types" (metaMap TypeDef.name TypeDef.meta b.types))) := by
    rw [hm, Interface.meta, List.append_assoc]
  have hh := head_lookup b.docs b.stability (jmap "funcs" (metaMap Func.mangled Func.meta b.funcs) ++
      jmap "types" (metaMap TypeDef.name TypeDef.meta b.types))
    (by simp [lookupKey_append, lookupKey_jmap]) (by simp [lookupKey_append, lookupKey_jmap])
  have hty : getObj "types" m = jobj (metaMap TypeDef.name TypeDef.meta b.types) := by
    rw [hmeta]; simp [getObj_jobj, headJson, lookupKey_append, lookupKey_jopt, lookupKey_jmap]
  have hfu : getObj "funcs" m = jobj (metaMap Func.mangled Func.meta b.funcs) := by
    rw [hmeta]; simp [getObj_jobj, headJson, lookupKey_append, lookupKey_jopt, lookupKey_jmap]
  have htypes : (b.types.map TypeDef.strip).map (TypeDef.inject (getObj "types" m)) = b.types := by
    rw [List.map_map, hty]
    conv_rhs => rw [← List.map_id b.types]
    exact List.map_congr_left fun td htd => typeDef_inject (hlab td htd) (mem_types_inject htn htd)
  have hfuncs : ((sortFuncs b.types b.funcs).map Func.strip).map (Func.inject (getObj "funcs" m)) =
      sortFuncs b.types b.funcs := by
    rw [List.map_map, hfu]
    conv_rhs => rw [← List.map_id (sortFuncs b.types b.funcs)]
    exact List.map_congr_left fun f hf => func_inject (mem_funcs_inject hfn (mem_sortFuncs hf))
  rw [← hmeta] at hh
  simp only [Interface.inject, Interface.normalize, htypes, hfuncs, hh.1, hh.2, Interface.canon]

/-! ## Worlds -/

def gInline : WorldItem → Option JVal | .ifaceInline _ b => b.meta | _ => none
def gType : WorldItem → Option JVal | .type td => td.meta | _ => none
def gFunc : WorldItem → Option JVal | .func f => f.meta | _ => none
def gRefSt : WorldItem → Option JVal | .ifaceRef _ _ st => st.json | _ => none
def gRefDocs : WorldItem → Option JVal | .ifaceRef _ d _ => jstr d | _ => none

/-- The map of world items keyed by their keys. -/
def wmap (g : WorldItem → Option JVal) (its : List WorldItem) : List (String × JVal) :=
  its.filterMap fun y => (g y).map (y.key, ·)

theorem inlineMeta_eq (its : List WorldItem) : its.filterMap inlineMeta = wmap gInline its := by
  simp only [wmap]; congr 1; funext y; cases y <;> rfl
theorem typeMeta_eq (its : List WorldItem) : its.filterMap typeMeta = wmap gType its := by
  simp only [wmap]; congr 1; funext y; cases y <;> rfl
theorem funcMeta_eq (its : List WorldItem) : its.filterMap funcMeta = wmap gFunc its := by
  simp only [wmap]; congr 1; funext y; cases y <;> rfl
theorem refStability_eq (its : List WorldItem) : its.filterMap refStability = wmap gRefSt its := by
  simp only [wmap]; congr 1; funext y; cases y <;> rfl
theorem refDocs_eq (its : List WorldItem) : its.filterMap refDocs = wmap gRefDocs its := by
  simp only [wmap]; congr 1; funext y
  cases y with
  | ifaceRef i d st => cases d <;> rfl
  | _ => rfl

theorem lookup_wmap {g : WorldItem → Option JVal} {its : List WorldItem} (hn : (its.map WorldItem.key).Nodup)
    {it : WorldItem} (hit : it ∈ its) : getObj it.key (jobj (wmap g its)) = g it := by
  rw [getObj_jobj]; exact lookupKey_filterMap WorldItem.key g hn hit

/-- The metadata object of a world, by keys. -/
theorem world_meta (w : World) : w.meta = jobj (headJson w.docs w.stability ++
    (jmap "interfaces" (wmap gInline w.imports) ++ jmap "types" (wmap gType w.imports) ++
    jmap "funcs" (wmap gFunc w.imports) ++ jmap "interface_exports" (wmap gInline w.exports) ++
    jmap "func_exports" (wmap gFunc w.exports) ++
    jmap "interface_import_stability" (wmap gRefSt w.imports) ++
    jmap "interface_export_stability" (wmap gRefSt w.exports) ++
    jmap "interface_import_docs" (wmap gRefDocs w.imports) ++
    jmap "interface_export_docs" (wmap gRefDocs w.exports))) := by
  simp only [World.meta, inlineMeta_eq, typeMeta_eq, funcMeta_eq, refStability_eq, refDocs_eq,
    List.append_assoc]

/-- The world's maps, looked up. -/
structure WorldMaps (w : World) (m : Option JVal) : Prop where
  docs : getStr? "docs" m = w.docs
  stability : Stability.ofJson (getObj "stability" m) = w.stability
  inl : getObj "interfaces" m = jobj (wmap gInline w.imports)
  types : getObj "types" m = jobj (wmap gType w.imports)
  funcs : getObj "funcs" m = jobj (wmap gFunc w.imports)
  inlE : getObj "interface_exports" m = jobj (wmap gInline w.exports)
  funcsE : getObj "func_exports" m = jobj (wmap gFunc w.exports)
  stI : getObj "interface_import_stability" m = jobj (wmap gRefSt w.imports)
  stE : getObj "interface_export_stability" m = jobj (wmap gRefSt w.exports)
  docI : getObj "interface_import_docs" m = jobj (wmap gRefDocs w.imports)
  docE : getObj "interface_export_docs" m = jobj (wmap gRefDocs w.exports)

theorem worldMaps (w : World) : WorldMaps w w.meta := by
  have hh := head_lookup w.docs w.stability (jmap "interfaces" (wmap gInline w.imports) ++ jmap "types" (wmap gType w.imports) ++
    jmap "funcs" (wmap gFunc w.imports) ++ jmap "interface_exports" (wmap gInline w.exports) ++
    jmap "func_exports" (wmap gFunc w.exports) ++
    jmap "interface_import_stability" (wmap gRefSt w.imports) ++
    jmap "interface_export_stability" (wmap gRefSt w.exports) ++
    jmap "interface_import_docs" (wmap gRefDocs w.imports) ++
    jmap "interface_export_docs" (wmap gRefDocs w.exports))
    (by simp [lookupKey_append, lookupKey_jmap]) (by simp [lookupKey_append, lookupKey_jmap])
  rw [← world_meta] at hh
  refine ⟨hh.1, hh.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [world_meta, getObj_jobj, headJson, lookupKey_append, lookupKey_jopt, lookupKey_jmap]

/-- What an item needs for its metadata to be put back. -/
def ItemInjOK (imp : Bool) : WorldItem → Prop
  | .ifaceInline _ b => b.NamesUnique
  | .type td => td.kind.LabelsUnique ∧ imp = true
  | _ => True

/-- The items of one direction of a world. -/
def dir (w : World) (imp : Bool) : List WorldItem := if imp then w.imports else w.exports

theorem refItem_inject {w : World} {m : Option JVal} (hm : WorldMaps w m) (imp : Bool)
    (hn : ((dir w imp).map WorldItem.key).Nodup) {i : IfaceName} {d : Option String} {st : Stability}
    (hit : .ifaceRef i d st ∈ dir w imp) :
    (WorldItem.ifaceRef i d st).normalize.inject m imp = (WorldItem.ifaceRef i d st).canon := by
  have hd : getObj i.id (jobj (wmap gRefDocs (dir w imp))) = jstr d := by
    simpa [WorldItem.key, gRefDocs] using lookup_wmap (g := gRefDocs) hn hit
  have hs : getObj i.id (jobj (wmap gRefSt (dir w imp))) = st.json := by
    simpa [WorldItem.key, gRefSt] using lookup_wmap (g := gRefSt) hn hit
  cases imp <;> simp only [dir, Bool.false_eq_true, ↓reduceIte] at hd hs <;>
    simp [WorldItem.normalize, WorldItem.inject, WorldItem.canon, hm.docI, hm.docE, hm.stI, hm.stE,
      getStr?_eq, hd, hs, strOf_jstr, Stability.ofJson_json]

theorem inlineItem_inject {w : World} {m : Option JVal} (hm : WorldMaps w m) (imp : Bool)
    (hn : ((dir w imp).map WorldItem.key).Nodup) {n : String} {b : Interface}
    (hit : .ifaceInline n b ∈ dir w imp) (hb : b.NamesUnique) :
    (WorldItem.ifaceInline n b).normalize.inject m imp = (WorldItem.ifaceInline n b).canon := by
  have hl : getObj n (jobj (wmap gInline (dir w imp))) = b.meta := by
    simpa [WorldItem.key, gInline] using lookup_wmap (g := gInline) hn hit
  have hk : getObj n (getObj (if imp then "interfaces" else "interface_exports") m) = b.meta := by
    cases imp <;> simpa [dir, hm.inl, hm.inlE] using hl
  have he : (WorldItem.ifaceInline n b).normalize.inject m imp =
      .ifaceInline n (b.normalize.inject (getObj n (getObj (if imp then "interfaces" else "interface_exports") m))) := rfl
  rw [he, iface_inject hb hk]; rfl

theorem funcItem_inject {w : World} {m : Option JVal} (hm : WorldMaps w m) (imp : Bool)
    (hn : ((dir w imp).map WorldItem.key).Nodup) {f : Func} (hit : .func f ∈ dir w imp) :
    (WorldItem.func f).normalize.inject m imp = (WorldItem.func f).canon := by
  have hl : getObj f.mangled (jobj (wmap gFunc (dir w imp))) = f.meta := by
    simpa [WorldItem.key, gFunc] using lookup_wmap (g := gFunc) hn hit
  have hk : getObj f.mangled (getObj (if imp then "funcs" else "func_exports") m) = f.meta := by
    cases imp <;> simpa [dir, hm.funcs, hm.funcsE] using hl
  have he : (WorldItem.func f).normalize.inject m imp =
      .func (f.strip.inject (getObj (if imp then "funcs" else "func_exports") m)) := rfl
  rw [he, func_inject hk]; rfl

theorem typeItem_inject {w : World} {m : Option JVal} (hm : WorldMaps w m)
    (hn : ((dir w true).map WorldItem.key).Nodup) {td : TypeDef} (hit : .type td ∈ dir w true)
    (hlab : td.kind.LabelsUnique) :
    (WorldItem.type td).normalize.inject m true = (WorldItem.type td).canon := by
  have hl : getObj td.name (jobj (wmap gType (dir w true))) = td.meta := by
    simpa [WorldItem.key, gType] using lookup_wmap (g := gType) hn hit
  have hk : getObj td.name (getObj "types" m) = td.meta := by simpa [dir, hm.types] using hl
  have he : (WorldItem.type td).normalize.inject m true = .type (td.strip.inject (getObj "types" m)) := rfl
  rw [he, typeDef_inject hlab hk]; rfl

/-- One import or export of a world, its metadata put back. -/
theorem worldItem_inject {w : World} {m : Option JVal} (hm : WorldMaps w m) (imp : Bool)
    (hn : ((dir w imp).map WorldItem.key).Nodup) {it : WorldItem} (hit : it ∈ dir w imp)
    (hok : ItemInjOK imp it) : it.normalize.inject m imp = it.canon := by
  match it, hok with
  | .ifaceRef i d st, _ => exact refItem_inject hm imp hn hit
  | .ifaceInline n b, hb => exact inlineItem_inject hm imp hn hit hb
  | .func f, _ => exact funcItem_inject hm imp hn hit
  | .type td, ⟨hlab, himp⟩ => subst himp; exact typeItem_inject hm hn hit hlab

theorem itemOK_of {imp : Bool} {it : WorldItem}
    (hok : match it with | .ifaceInline _ b => b.NamesUnique | .type td => td.kind.LabelsUnique | _ => True)
    (ht : imp = false → it.isType = false) : ItemInjOK imp it := by
  cases it with
  | ifaceRef => trivial
  | ifaceInline n b => exact hok
  | func f => trivial
  | type td => cases imp with
    | false => exact absurd (ht rfl) (by simp [WorldItem.isType])
    | true => exact ⟨hok, rfl⟩

/-- **A world's metadata put back.** -/
theorem world_inject {w : World} (hu : w.NamesUnique) {m : Option JVal} (hm : m = w.meta) :
    w.normalize.inject m = w.canon := by
  obtain ⟨hni, hne, hnt, hok⟩ := hu
  have hM : WorldMaps w m := hm ▸ worldMaps w
  have himp : (w.imports.map WorldItem.normalize).map (WorldItem.inject m true) = w.imports.map WorldItem.canon := by
    rw [List.map_map]
    exact List.map_congr_left fun it hit => worldItem_inject hM true hni hit
      (itemOK_of (hok it (List.mem_append_left _ hit)) (fun h => by cases h))
  have hexp : (w.exports.map WorldItem.normalize).map (WorldItem.inject m false) = w.exports.map WorldItem.canon := by
    rw [List.map_map]
    exact List.map_congr_left fun it hit => worldItem_inject hM false hne hit
      (itemOK_of (hok it (List.mem_append_right _ hit)) (fun _ => hnt it hit))
  simp only [World.inject, World.normalize, himp, hexp, hM.docs, hM.stability, World.canon]

/-- The package's maps, looked up. -/
theorem package_maps (p : Package) :
    p.docsJson.getStr "docs" = p.docs ∧
    p.docsJson.get "interfaces" = jobj (metaMap Prod.fst (fun nb => nb.2.meta) p.interfaces) ∧
    p.docsJson.get "worlds" = jobj (metaMap Prod.fst (fun nw => nw.2.meta) p.worlds) := by
  refine ⟨?_, ?_, ?_⟩
  · have h : p.docsJson.getStr "docs" = strOf (lookupKey "docs" (jopt "docs" (jstr p.docs) ++
        jmap "worlds" (metaMap Prod.fst (fun nw => nw.2.meta) p.worlds) ++
        jmap "interfaces" (metaMap Prod.fst (fun nb => nb.2.meta) p.interfaces))) := by
      simp only [Package.docsJson, JVal.getStr, get_obj, strOf]; split <;> simp_all
    rw [h]; cases hd : p.docs <;> simp [lookupKey_append, lookupKey_jopt, lookupKey_jmap, jstr] <;> rfl
  · simp [Package.docsJson, get_obj, lookupKey_append, lookupKey_jopt, lookupKey_jmap]
  · simp [Package.docsJson, get_obj, lookupKey_append, lookupKey_jopt, lookupKey_jmap]

/-- **Docs injection inverts docs extraction**: the `package-docs` metadata of
a package with distinct names, put into its normal form, gives the package
back with its functions in wit-component's order. -/
theorem inject_docsJson {p : Package} (hu : p.NamesUnique) : p.normalize.inject p.docsJson = p.canon := by
  obtain ⟨hin, hwn, hib, hwb⟩ := hu
  obtain ⟨hd, hI, hW⟩ := package_maps p
  have hifs : (p.interfaces.map fun nb => (nb.1, nb.2.normalize)).map
      (fun nb => (nb.1, nb.2.inject (getObj nb.1 (p.docsJson.get "interfaces")))) =
      p.interfaces.map fun nb => (nb.1, nb.2.canon) := by
    rw [List.map_map]
    refine List.map_congr_left fun nb hnb => ?_
    have hl : getObj nb.1 (p.docsJson.get "interfaces") = nb.2.meta := by
      rw [hI, getObj_jobj, metaMap_eq]; exact lookupKey_filterMap Prod.fst (fun nb => nb.2.meta) hin hnb
    simp only [Function.comp_apply, iface_inject (hib nb hnb) hl]
  have hws : (p.worlds.map fun nw => (nw.1, nw.2.normalize)).map
      (fun nw => (nw.1, nw.2.inject (getObj nw.1 (p.docsJson.get "worlds")))) =
      p.worlds.map fun nw => (nw.1, nw.2.canon) := by
    rw [List.map_map]
    refine List.map_congr_left fun nw hnw => ?_
    have hl : getObj nw.1 (p.docsJson.get "worlds") = nw.2.meta := by
      rw [hW, getObj_jobj, metaMap_eq]; exact lookupKey_filterMap Prod.fst (fun nw => nw.2.meta) hwn hnw
    simp only [Function.comp_apply, world_inject (hwb nw hnw) hl]
  simp only [Package.inject, Package.normalize, Package.canon, hd]
  rw [hifs, hws]

end Silmaril.Wasm.Wit.Binary
