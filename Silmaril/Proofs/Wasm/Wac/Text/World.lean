module

public import Silmaril.Proofs.Wasm.Wac.Text.Items

/-!
# WAC text: world items and type statements read back
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

open Parse

theorem includeItem_pr (i : IncludeItem) (rest : Toks) :
    Parse.includeItem (Pr.includeItem i ++ rest) = some (i, rest) := by
  simp [Pr.includeItem, Parse.includeItem]

theorem includeItems_pr (n : Nat) (ws : List IncludeItem) (rest : Toks)
    (hl : (commaList Pr.includeItem ws).length < n) :
    delim Parse.includeItem '}' true n (commaList Pr.includeItem ws ++ sy '}' :: rest) =
      some (ws, sy '}' :: rest) :=
  delim_commaList Parse.includeItem Pr.includeItem '}' (by decide) ws n rest
    (fun i _ r _ => includeItem_pr i r) (fun i _ => by simp [Pr.includeItem])
    (by have := length_le_commaList' Pr.includeItem (fun i => by simp [Pr.includeItem]) ws
        omega)

theorem include_pr (n : Nat) (ds : Docs) (w : WorldRef) (ws : List IncludeItem) (rest : Toks)
    (hw : Wf.worldItem (.include ds w ws) = true) (hl : (Pr.worldItem (.include ds w ws)).length < n) :
    Parse.worldItem n (Pr.worldItem (.include ds w ws) ++ rest) = some (.include ds w ws, rest) := by
  have hd : ws ≠ [] → delim Parse.includeItem '}' true n
      (commaList Pr.includeItem ws ++ sy '}' :: sy ';' :: rest) = some (ws, sy '}' :: sy ';' :: rest) := by
    intro hne
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
    apply includeItems_pr
    cases w <;> simp only [Pr.worldItem, Pr.first, List.length_cons, List.length_append] at hl <;>
      omega
  have hp : ∀ p, w = .package p → pkgPathOk p = true := by
    intro p hpw; subst hpw; simp [Wf.worldItem] at hw; exact hw.1.2
  cases w <;> cases ws <;>
    simp_all [Pr.worldItem, Parse.worldItem, Pr.first, Pr.pkgPath, pkgPath_pr]

theorem worldItem_pr (n : Nat) (i : WorldItem) (rest : Toks) (hw : Wf.worldItem i = true)
    (hl : (Pr.worldItem i).length < n) :
    Parse.worldItem n (Pr.worldItem i ++ rest) = some (i, rest) := by
  cases i with
  | use u =>
    have h := use_pr n u rest hw hl
    have he : Pr.use u = ⟨u.docs, .kw .use⟩ :: (Pr.use u).tail := rfl
    show Parse.worldItem n (Pr.use u ++ rest) = _
    rw [he, List.cons_append]; simp only [Parse.worldItem]; rw [← List.cons_append, ← he, h]
    rfl
  | type d =>
    have h := itemTypeDecl_pr n d rest hw hl
    obtain ⟨ds, k, l, he, h1, h2, h3, h4, -⟩ := Pr.itemTypeDecl_head d
    simp only [Pr.worldItem] at h ⊢
    rw [he] at h ⊢
    cases k <;> simp_all [Parse.worldItem]
  | import_ ds p | export_ ds p =>
    have h := worldItemPath_pr n p rest (by simp [Wf.worldItem] at hw; exact hw.2)
      (by simp [Pr.worldItem] at hl; omega)
    simp [Pr.worldItem, Parse.worldItem, Pr.first, h]
  | «include» ds w ws => exact include_pr n ds w ws rest hw hl

theorem Pr.worldItem_ne (i : WorldItem) :
    Pr.worldItem i ≠ [] ∧ hd? (Pr.worldItem i) ≠ some (.sym '}') := by
  cases i with
  | type d => obtain ⟨ds, k, l, he, -⟩ := Pr.itemTypeDecl_head d; simp [Pr.worldItem, he]
  | _ => simp [Pr.worldItem, Pr.use, Pr.first]

theorem world_pr (n : Nat) (ds : Docs) (id : String) (items : List WorldItem) (rest : Toks)
    (hw : ∀ x ∈ items, Wf.worldItem x = true)
    (hl : (Pr.typeStatement (.world ds id items)).length < n) :
    Parse.typeStatement n (Pr.typeStatement (.world ds id items) ++ rest) =
      some (.world ds id items, rest) := by
  have hl' : (items.flatMap Pr.worldItem).length + 4 ≤ n := by
    simp only [Pr.typeStatement, Pr.first, List.length_cons, List.length_append] at hl; omega
  have hd := delim_flatMap (Parse.worldItem n) Pr.worldItem '}' items n rest
    (fun x hx r => worldItem_pr n x r (hw x hx)
      (by have := length_le_flatMap_of_mem Pr.worldItem hx; omega))
    (fun x _ => Pr.worldItem_ne x)
    (by have := length_le_flatMap Pr.worldItem (fun x => (Pr.worldItem_ne x).1) items; omega)
  simp only [Pr.typeStatement, Pr.first, List.cons_append, List.append_assoc] at hd ⊢
  simp [Parse.typeStatement, hd]

theorem typeStatement_pr (n : Nat) (s : TypeStatement) (rest : Toks)
    (hw : Wf.typeStatement s = true) (hl : (Pr.typeStatement s).length < n) :
    Parse.typeStatement n (Pr.typeStatement s ++ rest) = some (s, rest) := by
  cases s with
  | interface ds id items =>
    have h := interfaceBody_pr n items rest (by simp [Wf.typeStatement] at hw; simpa using hw.2)
      (by simp only [Pr.typeStatement, Pr.first, List.length_cons, List.length_append] at hl
          omega)
    simp only [Pr.typeStatement, Pr.first, List.cons_append, List.append_assoc] at h ⊢
    simp [Parse.typeStatement, h]
  | world ds id items =>
    exact world_pr n ds id items rest (by simp [Wf.typeStatement] at hw; exact hw.2) hl
  | type d =>
    have h := typeDecl_pr n d rest hw hl
    cases d <;> simp_all [Pr.typeStatement, Parse.typeStatement, Pr.typeDecl, Pr.first]

end Silmaril.Wasm.Wac.Text
