module

public import Silmaril.Wasm.Wit.Bridge.Defs
public import Silmaril.Wasm.Wit.Binary.Thms
public import Silmaril.Wasm.Wit.Project.Thms
public import Silmaril.Proofs.Wasm.Wit.Bridge.Plain

/-!
# The binary encoder and the projection: proofs

* `allItemSections_eq`: the encoder's item layout is `Project.itemSecs`;
* `packageSections_itemsPackage`: the sections of a package's binary are an
  `itemsPackage` of its encoded items followed by custom sections;
* `project_encodePackage`: the bytes of a package parse to a component whose
  projection lists exactly the encoded items (in WAT normal form);
* `world_project_encodePackage`: for each world of a valid package, that list
  contains the world's wrapper, whose world (`wrappedWorld`) is exactly the
  component type the encoder writes for the world (it is in WAT normal form,
  `normComponentDecls_of_decWorld`), which decodes back to the world's normal
  form.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat
open Silmaril.Wasm.Wit.Binary
open Silmaril.Wasm.Wit.Project

theorem except_bind_ok' {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem mapM_ok_mem {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → ∀ a ∈ l, ∃ b ∈ l', f a = .ok b
  | [], _, _, a, ha => absurd ha List.not_mem_nil
  | x :: xs, l', h, a, ha => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := except_bind_ok' h
    obtain ⟨bs, hbs, h⟩ := except_bind_ok' h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨c, hc, hfc⟩ := mapM_ok_mem hbs a ha
      exact ⟨c, List.mem_cons_of_mem _ hc, hfc⟩

/-- The encoder's item layout is the projection's `itemSecs`. -/
theorem allItemSections_eq : ∀ (items : List (String × List ComponentDecl)) (k : Nat),
    allItemSections items k = itemSecs k (asDefTypes items)
  | [], _ => rfl
  | x :: xs, k => by
    have ih := allItemSections_eq xs (k + 1)
    simp only [allItemSections, List.zipIdx_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    rfl

theorem encodeItems_eq {deps : Env} {P : Package} {ss : List Section} (h : encodeItems deps P = .ok ss) :
    ∃ items, encodedItems deps P = .ok items ∧ ss = itemSecs 0 (asDefTypes items) := by
  unfold encodeItems at h
  obtain ⟨ifs, hi, h⟩ := except_bind_ok' h
  obtain ⟨ws, hw, h⟩ := except_bind_ok' h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  refine ⟨ifs ++ ws, ?_, ?_⟩
  · simp only [encodedItems, hi, hw]; rfl
  · rw [← h, allItemSections]
    exact allItemSections_eq _ 0

/-- The sections of a package's binary: its encoded items, then custom sections. -/
theorem packageSections_itemsPackage {deps : Env} {P : Package} {ss : List Section}
    (h : packageSections deps P = .ok ss) :
    ∃ items cs, encodedItems deps P = .ok items ∧ Ast.mk ss = itemsPackage (asDefTypes items) cs ∧
      ∀ c ∈ cs, isCode c = true := by
  obtain ⟨its, x, hi, rfl⟩ := packageSections_eq h
  obtain ⟨items, he, rfl⟩ := encodeItems_eq hi
  refine ⟨items, _, he, rfl, ?_⟩
  intro c hc
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> rfl

/-- **The projection of a package's binary**: the bytes wit-component writes
for a package parse to a component that projects to exactly the encoded items
(interfaces as their component types, worlds as wrappers), in WAT normal form. -/
theorem project_encodePackage {deps : Env} {P : Package} {b : ByteArray}
    (h : encodePackage deps P = .ok b) :
    ∃ c items, parse b = .ok c ∧ encodedItems deps P = .ok items ∧
      (project c).bind (packageItems 0) = some ((asDefTypes items).map fun x => (x.1, normDefType x.2)) := by
  unfold encodePackage at h
  obtain ⟨ss, hs, h⟩ := except_bind_ok' h
  obtain ⟨items, cs, he, hm, hc⟩ := packageSections_itemsPackage hs
  cases hb : encode (.mk ss) with
  | none => rw [hb] at h; cases h
  | some b' =>
    rw [hb] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨.mk ss, items, parse_encode hb, he, ?_⟩
    rw [hm]
    refine packageItems_project_itemsPackage _ cs (fun q hq => ?_) hc
    simp only [asDefTypes, List.mem_map] at hq
    obtain ⟨x, _, rfl⟩ := hq
    rfl

/-- The wrapper of a world, normalised, still wraps the world (normalised). -/
theorem wrappedWorld_normDefType (p : PackageName) (n : String) (ds : List ComponentDecl) :
    wrappedWorld (normDefType (.component (worldWrapper p n ds))) = some (normComponentDecls ds) := rfl

theorem encodeWorldItem_ok {env : Env} {p : PackageName} {nw : String × World}
    {x : String × List ComponentDecl} (h : encodeWorldItem env p nw = .ok x) :
    ∃ ds, encodeWorld env nw.2 = .ok ds ∧ x = (nw.1, worldWrapper p nw.1 ds) := by
  unfold encodeWorldItem at h
  obtain ⟨ds, hd, h⟩ := except_bind_ok' h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨ds, hd, h.symm⟩

/-- **The WIT-encoded component of a world projects back to that world**: the
bytes of a valid package parse to a component whose projection has, under the
name of each world, the world's wrapper; the world it wraps is the component
type `ds` the encoder writes for the world, and `ds` decodes back to the
world's normal form. -/
theorem world_project_encodePackage {deps : Env} {P : Package} (hv : P.Valid deps) {b : ByteArray}
    (h : encodePackage deps P = .ok b) :
    ∃ c its, parse b = .ok c ∧ (project c).bind (packageItems 0) = some its ∧
      ∀ nw ∈ P.worlds, ∃ ds d, encodeWorld (P.env deps) nw.2 = .ok ds ∧ (nw.1, d) ∈ its ∧
        wrappedWorld d = some ds ∧ decWorld ds = .ok nw.2.normalize := by
  obtain ⟨c, items, hp, he, hproj⟩ := project_encodePackage h
  refine ⟨c, _, hp, hproj, fun nw hnw => ?_⟩
  unfold encodedItems at he
  obtain ⟨ifs, _, he⟩ := except_bind_ok' he
  obtain ⟨ws, hw, he⟩ := except_bind_ok' he
  simp only [pure, Except.pure, Except.ok.injEq] at he
  subst he
  obtain ⟨x, hx, hxe⟩ := mapM_ok_mem hw nw hnw
  obtain ⟨ds, hds, rfl⟩ := encodeWorldItem_ok hxe
  have hdec : decWorld ds = .ok nw.2.normalize := decWorld_encodeWorld hv.2.2.2.1 (hv.2.2.2.2 nw hnw) hds
  have hww : wrappedWorld (normDefType (.component (worldWrapper P.name nw.1 ds))) = some ds := by
    rw [wrappedWorld_normDefType, normComponentDecls_of_decWorld hdec]
  refine ⟨ds, _, hds, ?_, hww, hdec⟩
  simp only [asDefTypes, List.map_map, List.mem_map]
  exact ⟨_, List.mem_append_right _ hx, rfl⟩

end Silmaril.Wasm.Wit.Bridge
