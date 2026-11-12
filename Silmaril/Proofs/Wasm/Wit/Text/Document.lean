module

public import Silmaril.Proofs.Wasm.Wit.Text.Items

/-!
# WIT text: packages and documents read back

`document (toks (prDocument d)) = some (Document.norm d)` for a printable document
(`document_prDocument`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

open Parse

theorem packageItem_iface (f : Interface) (hx : packageItemOk (.iface f) = true) (n : Nat) (r : List Tok)
    (h : (prPackageItem (.iface f)).length ≤ n) :
    packageItem n (toks (prPackageItem (.iface f)) ++ r) = some (PackageItem.norm (.iface f), r) := by
  obtain ⟨nm, is, dd, gs⟩ := f
  simp only [packageItemOk, Bool.and_eq_true] at hx
  obtain ⟨⟨-, hg⟩, hi⟩ := hx
  simp only [prPackageItem, prInterface, prIfaceItems] at h ⊢
  unfold_toks
  simp only [packageItem, docs_gates_kw hg, gates_kw hg, braced]
  rw [many_flatMap is (readsMany_ifaceItem is hi) n _ (by omega) (by simp)]
  simp [andThen, expect, PackageItem.norm]

theorem packageItem_world (w : World) (hx : packageItemOk (.world w) = true) (n : Nat) (r : List Tok)
    (h : (prPackageItem (.world w)).length ≤ n) :
    packageItem n (toks (prPackageItem (.world w)) ++ r) = some (PackageItem.norm (.world w), r) := by
  obtain ⟨nm, is, dd, gs⟩ := w
  simp only [packageItemOk, Bool.and_eq_true] at hx
  obtain ⟨⟨-, hg⟩, hi⟩ := hx
  simp only [prPackageItem, prWorld] at h ⊢
  unfold_toks
  simp only [packageItem, docs_gates_kw hg, gates_kw hg, braced]
  rw [many_flatMap is (readsMany_worldItem is hi) n _ (by omega) (by simp)]
  simp [andThen, expect, PackageItem.norm]

theorem packageItem_use (u : TopUse) (hx : packageItemOk (.use u) = true) (n : Nat) (r : List Tok)
    (h : (prPackageItem (.use u)).length ≤ n) :
    packageItem n (toks (prPackageItem (.use u)) ++ r) = some (PackageItem.norm (.use u), r) := by
  obtain ⟨p, a, gs⟩ := u
  simp only [packageItemOk, Bool.and_eq_true] at hx
  obtain ⟨⟨hg, hp⟩, -⟩ := hx
  have h1 := docs_gates_kw hg {}
  simp only [prDocs, toks_nil, List.nil_append] at h1
  cases a with
  | none =>
    simp only [prPackageItem, prTopUse, toks_append, toks_cons, toks_nil, List.append_assoc,
      List.cons_append, List.nil_append]
    simp only [packageItem, h1, gates_kw hg, topUseBody]
    rw [path_pr p hp (by simp) (by simp)]
    rfl
  | some a =>
    simp only [prPackageItem, prTopUse, toks_append, toks_cons, toks_nil, List.append_assoc,
      List.cons_append, List.nil_append]
    simp only [packageItem, h1, gates_kw hg, topUseBody]
    rw [path_pr p hp (by simp) (by simp)]
    rfl

theorem packageItem_pr (x : PackageItem) (hx : packageItemOk x = true) : ∀ n r,
    (prPackageItem x).length ≤ n → packageItem n (toks (prPackageItem x) ++ r) =
      some (PackageItem.norm x, r) := by
  intro n r h
  cases x with
  | iface f => exact packageItem_iface f hx n r h
  | world w => exact packageItem_world w hx n r h
  | use u => exact packageItem_use u hx n r h

theorem head_prGates (gs : List Gate) (t : Tok) (r : List Tok) :
    (toks (prGates gs) ++ t :: r).head? = some (.sym '@') ∨
      (toks (prGates gs) ++ t :: r).head? = some t := by
  cases gs with
  | nil => simp [prGates]
  | cons g gs => cases g <;> simp [prGates, prGate]

theorem docs_head_kw (d : Docs) (gs : List Gate) (w0 : Kw) (r : List Tok) (w : Kw)
    (h : (docs (toks (prDocs d) ++ (toks (prGates gs) ++ .kw w0 :: r))).2.head? =
      some (.kw w)) : w = w0 := by
  rw [docs_prDocs d (noDoc_prGates gs (fun s h => by simp at h))] at h
  rcases head_prGates gs (.kw w0) r with e | e <;> rw [e] at h <;> simp_all

theorem prPackageItem_head_iface (f : Interface) (r : List Tok) :
    0 < (prPackageItem (.iface f)).length ∧ (toks (prPackageItem (.iface f)) ++ r).head? ≠ some (.sym '}') ∧
      ∀ w, (docs (toks (prPackageItem (.iface f)) ++ r)).2.head? = some (.kw w) →
        w = .interface ∨ w = .world ∨ w = .use := by
  refine ⟨by simp [prPackageItem, prInterface]; omega, ?_, ?_⟩
  · simp only [prPackageItem, prInterface, toks_append, toks_cons, List.append_assoc,
      List.cons_append]
    exact head_docs_gates_ne f.docs f.gates _ _ (by simp)
  · intro w hw
    simp only [prPackageItem, prInterface, toks_append, toks_cons, List.append_assoc,
      List.cons_append] at hw
    exact .inl (docs_head_kw _ _ _ _ _ hw)

theorem prPackageItem_head_world (f : World) (r : List Tok) :
    0 < (prPackageItem (.world f)).length ∧ (toks (prPackageItem (.world f)) ++ r).head? ≠ some (.sym '}') ∧
      ∀ w, (docs (toks (prPackageItem (.world f)) ++ r)).2.head? = some (.kw w) →
        w = .interface ∨ w = .world ∨ w = .use := by
  refine ⟨by simp [prPackageItem, prWorld]; omega, ?_, ?_⟩
  · simp only [prPackageItem, prWorld, toks_append, toks_cons, List.append_assoc,
      List.cons_append]
    exact head_docs_gates_ne f.docs f.gates _ _ (by simp)
  · intro w hw
    simp only [prPackageItem, prWorld, toks_append, toks_cons, List.append_assoc,
      List.cons_append] at hw
    exact .inr (.inl (docs_head_kw _ _ _ _ _ hw))

theorem prPackageItem_head_use (u : TopUse) (r : List Tok) :
    0 < (prPackageItem (.use u)).length ∧ (toks (prPackageItem (.use u)) ++ r).head? ≠ some (.sym '}') ∧
      ∀ w, (docs (toks (prPackageItem (.use u)) ++ r)).2.head? = some (.kw w) →
        w = .interface ∨ w = .world ∨ w = .use := by
  obtain ⟨p, a, gs⟩ := u
  have hl : 0 < (prPackageItem (.use ⟨p, a, gs⟩)).length := by
    cases a <;> simp [prPackageItem, prTopUse] <;> omega
  obtain ⟨rest, ht⟩ : ∃ rest, toks (prPackageItem (.use ⟨p, a, gs⟩)) ++ r =
      toks (prDocs {}) ++ (toks (prGates gs) ++ .kw .use :: rest) := by
    cases a with
    | none => exact ⟨toks (prPath p) ++ .sym ';' :: r, by simp [prPackageItem, prTopUse, prDocs]⟩
    | some a => exact ⟨toks (prPath p) ++ .kw .as :: .id a :: .sym ';' :: r,
        by simp [prPackageItem, prTopUse, prDocs]⟩
  refine ⟨hl, ?_, ?_⟩
  · rw [ht]; exact head_docs_gates_ne {} gs _ _ (by simp)
  · intro w hw
    rw [ht] at hw
    exact .inr (.inr (docs_head_kw _ _ _ _ _ hw))

theorem prPackageItem_head (x : PackageItem) (r : List Tok) :
    0 < (prPackageItem x).length ∧ (toks (prPackageItem x) ++ r).head? ≠ some (.sym '}') ∧
      ∀ w, (docs (toks (prPackageItem x) ++ r)).2.head? = some (.kw w) →
        w = .interface ∨ w = .world ∨ w = .use := by
  cases x with
  | iface f => exact prPackageItem_head_iface f r
  | world f => exact prPackageItem_head_world f r
  | use u => exact prPackageItem_head_use u r

theorem readsMany_packageItem (is : List PackageItem) (hi : is.all packageItemOk = true) :
    ReadsMany packageItem prPackageItem PackageItem.norm is := fun x hx =>
  ⟨(prPackageItem_head x []).1, fun r => (prPackageItem_head x r).2.1,
   fun n r h => packageItem_pr x (List.all_eq_true.mp hi x hx) n r h⟩

/-- The printing of a top-level item or a nested package. -/
def prTop : PackageItem ⊕ Package → List PTok
  | .inl x => prPackageItem x
  | .inr p => prNested p

/-- The normal form of a top-level item or a nested package. -/
def normTop : PackageItem ⊕ Package → PackageItem ⊕ Package
  | .inl x => .inl (PackageItem.norm x)
  | .inr p => .inr (Package.norm p)

theorem topItem_inl (x : PackageItem) (hx : packageItemOk x = true) (n : Nat) (r : List Tok)
    (h : (prTop (.inl x)).length ≤ n) :
    topItem n (toks (prTop (.inl x)) ++ r) = some (normTop (.inl x), r) := by
  have hne : (docs (toks (prPackageItem x) ++ r)).2.head? ≠ some (.kw .package) := by
    intro e
    rcases (prPackageItem_head x r).2.2 _ e with e | e | e <;> cases e
  simp only [prTop] at h ⊢
  simp only [topItem, hne, ite_false]
  rw [packageItem_pr x hx n r h]
  rfl

theorem topItem_inr (p : Package) (hx : packageOk p = true) (n : Nat) (r : List Tok)
    (h : (prTop (.inr p)).length ≤ n) :
    topItem n (toks (prTop (.inr p)) ++ r) = some (normTop (.inr p), r) := by
  obtain ⟨nm, is, dd⟩ := p
  simp only [packageOk, Bool.and_eq_true] at hx
  simp only [prTop, prNested] at h ⊢
  unfold_toks
  simp only [topItem, docs_prDocs_kw, List.head?_cons, ite_true, List.tail_cons]
  rw [pkgName_pr nm hx.1 (by simp)]
  simp only [braced]
  rw [many_flatMap is (readsMany_packageItem is hx.2) n _ (by omega) (by simp)]
  simp [andThen, expect, normTop, Package.norm]

theorem topItem_pr (x : PackageItem ⊕ Package)
    (hx : (match x with
      | .inl x => packageItemOk x
      | .inr p => packageOk p) = true) : ∀ n r,
    (prTop x).length ≤ n → topItem n (toks (prTop x) ++ r) = some (normTop x, r) := by
  intro n r h
  cases x with
  | inl x => exact topItem_inl x hx n r h
  | inr p => exact topItem_inr p hx n r h

theorem prTop_head (x : PackageItem ⊕ Package) (r : List Tok) :
    0 < (prTop x).length ∧ (toks (prTop x) ++ r).head? ≠ some (.sym '}') := by
  cases x with
  | inl x => exact ⟨(prPackageItem_head x r).1, (prPackageItem_head x r).2.1⟩
  | inr p =>
    refine ⟨by simp [prTop, prNested]; omega, ?_⟩
    simp only [prTop, prNested, toks_append, toks_cons, List.append_assoc, List.cons_append]
    exact head_docs_ne p.docs (.kw .package) _ (by simp) '}'

theorem lefts_map (is : List PackageItem) (ps : List Package) :
    lefts ((is.map Sum.inl ++ ps.map Sum.inr).map normTop) = is.map PackageItem.norm := by
  induction is with
  | nil =>
    induction ps with
    | nil => rfl
    | cons p ps ih => simpa [lefts, normTop] using ih
  | cons x is ih => simpa [lefts, normTop] using ih

theorem rights_map (is : List PackageItem) (ps : List Package) :
    rights ((is.map Sum.inl ++ ps.map Sum.inr).map normTop) = ps.map Package.norm := by
  induction is with
  | nil =>
    induction ps with
    | nil => rfl
    | cons p ps ih => simpa [rights, normTop] using ih
  | cons x is ih => simpa [rights, normTop] using ih

theorem flatMap_prTop (is : List PackageItem) (ps : List Package) :
    (is.map Sum.inl ++ ps.map Sum.inr).flatMap prTop =
      is.flatMap prPackageItem ++ ps.flatMap prNested := by
  simp [List.flatMap_append, List.flatMap_map, prTop]

theorem readsMany_top (is : List PackageItem) (ps : List Package)
    (hi : is.all packageItemOk = true) (hp : ps.all packageOk = true) :
    ReadsMany topItem prTop normTop (is.map Sum.inl ++ ps.map Sum.inr) := by
  intro x hx
  refine ⟨(prTop_head x []).1, fun r => (prTop_head x r).2, fun n r h => topItem_pr x ?_ n r h⟩
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · exact List.all_eq_true.mp hi y hy
  · exact List.all_eq_true.mp hp y hy

/-- A printable document reads back to its normal form. -/
theorem document_prDocument (d : Document) (hd : printable d = true) :
    document (toks (prDocument d)) = some (Document.norm d) := by
  obtain ⟨⟨nm, is, dd⟩, ps⟩ := d
  simp only [printable, packageOk, Bool.and_eq_true] at hd
  obtain ⟨⟨hn, hi⟩, hp⟩ := hd
  have hr := readsMany_top is ps hi hp
  simp only [prDocument]
  unfold_toks
  simp only [document, docs_prDocs_kw]
  rw [← List.cons_append, pkgName_pr nm hn (by simp)]
  simp only [List.cons_append]
  rw [show toks (List.flatMap prPackageItem is) ++ toks (List.flatMap prNested ps) =
    toks ((is.map Sum.inl ++ ps.map Sum.inr).flatMap prTop) ++ [] by rw [flatMap_prTop]; simp]
  rw [many_flatMap _ hr _ [] (by rw [flatMap_prTop]; simp; omega) (by simp)]
  simp only [lefts_map, rights_map]
  rfl

end Silmaril.Wasm.Wit.Text
