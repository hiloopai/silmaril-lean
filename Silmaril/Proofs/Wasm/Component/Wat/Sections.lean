module

public import Silmaril.Proofs.Wasm.Component.Wat.Types

/-!
# Component WAT: sections and components read back

Every item reads back as a section of one element (`item_*`), the items of a
section list read back as its split normal form (`sections_rt`), and grouping
gives `ofSexp (toSexp c) = some (norm c)`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Wat

open Silmaril.Wasm.Component.Binary Sexp

theorem canonOpt_rt (o : CanonOpt) : R.canonOpt (P.canonOpt o) = some o := by
  cases o <;> simp [P.canonOpt, R.canonOpt]

theorem canonOpts_rt (os : List CanonOpt) : mapO R.canonOpt (os.map P.canonOpt) = some os :=
  mapO_map_id _ _ os (fun o _ => canonOpt_rt o)

theorem item_kw (k : String) (ss : List Sexp) (h : k ≠ "component") :
    R.item (.list (.atom k :: ss)) = R.itemKw k ss := by
  rw [R.item.eq_def]
  split <;> simp_all

theorem itemKw_func (ss : List Sexp) : R.itemKw "func" ss = R.liftItem ss := rfl
theorem itemKw_core (ss : List Sexp) : R.itemKw "core" ss = R.coreItem ss := rfl
theorem itemKw_start (ss : List Sexp) : R.itemKw "start" ss = R.startItem ss := rfl
theorem itemKw_import (ss : List Sexp) :
    R.itemKw "import" ss = (R.nameDesc ss).map fun p => .imports [⟨p.1, p.2⟩] := rfl
theorem itemKw_export (ss : List Sexp) :
    R.itemKw "export" ss = (R.export_ ss).map fun e => .exports [e] := rfl
theorem itemKw_value (ss : List Sexp) : R.itemKw "value" ss = R.valueItem ss := rfl
theorem itemKw_type (ss : List Sexp) : R.itemKw "type" ss = R.typeItem ss := rfl
theorem itemKw_custom (ss : List Sexp) : R.itemKw "@custom" ss = R.customItem ss := rfl

theorem item_canon (c : Canon) : R.item (P.canon c) = some (.canons [c]) := by
  cases c with
  | lift f opts t =>
    rw [P.canon, item_kw _ _ (by decide), itemKw_func]
    simp [R.liftItem, R.typeUse, canonOpts_rt]
  | lower f opts =>
    rw [P.canon, item_kw _ _ (by decide), itemKw_core]
    simp [R.coreItem, R.coreCanon, canonOpts_rt]
  | _ =>
    rw [P.canon, item_kw _ _ (by decide), itemKw_core]
    simp [R.coreItem, R.coreCanon]

theorem startResults_rt (r : Nat) :
    R.startResults (List.replicate r (.list [kw "result", .list [kw "value"]])) = some r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [List.replicate_succ, R.startResults, ih]

theorem startArgs_rt (r : Nat) : ∀ args : List Nat,
    R.startArgs (args.map (fun a => .list [kw "value", num a]) ++
      List.replicate r (.list [kw "result", .list [kw "value"]])) =
      some (args, List.replicate r (.list [kw "result", .list [kw "value"]]))
  | [] => by cases r <;> rfl
  | a :: args => by simp [R.startArgs, startArgs_rt r args]

theorem item_start (s : Start) : R.item (P.start s) = some (.start s) := by
  obtain ⟨f, args, r⟩ := s
  simp only [P.start, List.cons_append]
  rw [item_kw _ _ (by decide), itemKw_start]
  simp [R.startItem, startArgs_rt, startResults_rt]

theorem item_import (i : Import) :
    R.item (P.import_ i) = some (.imports [⟨normName i.name, i.desc⟩]) := by
  simp only [P.import_, List.cons_append]
  rw [item_kw _ _ (by decide), itemKw_import, nameDesc_rt]; rfl

theorem export_rt (e : Export) :
    R.export_ (P.name e.name ++ P.sortIdx e.item :: (e.desc.map P.externDesc).toList) =
      some ⟨normName e.name, e.item, e.desc⟩ := by
  rw [R.export_, name_rt _ _ (by rintro s r ⟨rfl, rfl⟩; exact attr_sortIdx _)]
  cases e.desc <;> simp [sortIdx_rt, externDesc_rt, normDesc]

theorem item_export (e : Export) :
    R.item (P.export_ e) = some (.exports [⟨normName e.name, e.item, e.desc⟩]) := by
  simp only [P.export_, List.cons_append]
  rw [item_kw _ _ (by decide), itemKw_export, export_rt]; rfl

theorem item_value (v : Value) : R.item (P.value v) = some (.values [v]) := by
  rw [P.value, item_kw _ _ (by decide), itemKw_value]
  simp [R.valueItem, valType_rt]

theorem item_coreType (t : CoreType) :
    R.item (.list [kw "core", kw "type", P.coreType t]) = some (.coreTypes [t]) := by
  rw [item_kw _ _ (by decide), itemKw_core]
  simp [R.coreItem, coreType_rt]

theorem item_type (t : DefType) :
    R.item (.list [kw "type", P.defType t]) = some (.types [normDefType t]) := by
  rw [item_kw _ _ (by decide), itemKw_type]
  simp [R.typeItem, defType_rt]

theorem item_custom (n : String) (d : ByteArray) :
    R.item (.list [kw "@custom", nm n, bytesS d]) = some (.custom n d) := by
  rw [item_kw _ _ (by decide), itemKw_custom]
  simp [R.customItem]

theorem item_coreModule (b : ByteArray) :
    R.item (.list [kw "core", kw "module", kw "binary", bytesS b]) = some (.coreModule b) := by
  rw [item_kw _ _ (by decide), itemKw_core]
  simp [R.coreItem]

theorem item_component (ss : List Sexp) :
    R.item (.list (kw "component" :: ss)) =
      (R.items ss).map fun xs => .component (.mk (R.group xs)) := by
  rw [R.item.eq_def]
  rfl

/-! ## Item lists -/

theorem items_cons (s : Sexp) (ss : List Sexp) :
    R.items (s :: ss) = (R.item s).bind fun x => (R.items ss).map (x :: ·) := by
  show (do
    let x ← R.item s
    let xs ← R.items ss
    pure (x :: xs)) = _
  cases R.item s <;> cases R.items ss <;> rfl

theorem items_append : ∀ (a b : List Sexp),
    R.items (a ++ b) = (R.items a).bind fun xs => (R.items b).map (xs ++ ·)
  | [], b => by
    rw [List.nil_append]
    show R.items b = Option.bind (some []) _
    cases R.items b <;> rfl
  | s :: a, b => by
    rw [List.cons_append, items_cons, items_cons, items_append a b]
    cases R.item s <;> cases R.items a <;> cases R.items b <;> rfl

theorem items_map {α : Type} (f : α → Sexp) (g : α → Section) (h : ∀ x, R.item (f x) = some (g x)) :
    ∀ xs : List α, R.items (xs.map f) = some (xs.map g)
  | [] => rfl
  | x :: xs => by rw [List.map_cons, items_cons, h x, items_map f g h xs]; rfl

mutual
theorem section_rt : ∀ s : Section, R.items (P.section_ s) = some (normSection s)
  | .custom n d => by
    show R.items [_] = _
    rw [items_cons, item_custom]; rfl
  | .coreModule b => by
    show R.items [_] = _
    rw [items_cons, item_coreModule]; rfl
  | .coreInstances xs => items_map _ _ item_coreInstance xs
  | .coreTypes xs => items_map _ _ item_coreType xs
  | .component (.mk ss) => by
    show R.items [_] = _
    rw [items_cons, item_component]
    show (((R.items (P.sections ss)).map _).bind _) = _
    rw [sections_rt ss]; rfl
  | .instances xs => items_map _ _ item_inst xs
  | .aliases xs => items_map _ _ item_alias xs
  | .types xs => items_map _ _ item_type xs
  | .canons xs => items_map _ _ item_canon xs
  | .start s => by
    show R.items [_] = _
    rw [items_cons, item_start]; rfl
  | .imports xs => items_map _ _ item_import xs
  | .exports xs => items_map _ _ item_export xs
  | .values xs => items_map _ _ item_value xs

theorem sections_rt : ∀ ss : List Section, R.items (P.sections ss) = some (normSections ss)
  | [] => rfl
  | s :: ss => by
    show R.items (P.section_ s ++ P.sections ss) = _
    rw [items_append, section_rt s, sections_rt ss]; rfl
end

/-- The reader inverts the printer up to the normal form, at the level of
S-expressions. -/
theorem ofSexp_toSexp (c : Ast) : ofSexp (toSexp c) = some (norm c) := by
  obtain ⟨ss⟩ := c
  show (R.items (P.sections ss)).map _ = _
  rw [sections_rt]; rfl

end Silmaril.Wasm.Component.Wat
