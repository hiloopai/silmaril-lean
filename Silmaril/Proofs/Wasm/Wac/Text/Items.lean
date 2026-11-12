module

public import Silmaril.Proofs.Wasm.Wac.Text.Decl

/-!
# WAC text: interface and world items read back
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

open Parse

theorem resourceMethod_pr (n : Nat) (m : ResourceMethod) (rest : Toks)
    (hw : Wf.resourceMethod m = true) (hl : (Pr.resourceMethod m).length < n) :
    Parse.resourceMethod n (Pr.resourceMethod m ++ rest) = some (m, rest) := by
  cases m with
  | ctor ds ps =>
    have hp : ∀ a ∈ ps, Wf.namedType a = true := by simp [Wf.resourceMethod] at hw; exact hw.2
    have h := namedTypes_pr n ps (sy ';' :: rest) hp (by simp [Pr.resourceMethod] at hl; omega)
    simp [Pr.resourceMethod, Parse.resourceMethod, Pr.first, docsOf, h]
  | method ds id st f =>
    have hf : Wf.funcType f = true := by simp [Wf.resourceMethod] at hw; exact hw.2
    have h := funcType_pr n f (sy ';' :: rest) hf
      (by simp [Pr.resourceMethod] at hl; cases st <;> simp at hl <;> omega) (by simp) (by simp)
    obtain ⟨a, ps, r⟩ := f
    cases st <;> cases a <;>
      simp_all [Pr.resourceMethod, Parse.resourceMethod, Pr.first, docsOf, Pr.funcType]

theorem Pr.resourceMethod_ne (m : ResourceMethod) :
    Pr.resourceMethod m ≠ [] ∧ hd? (Pr.resourceMethod m) ≠ some (.sym '}') := by
  cases m <;> simp [Pr.resourceMethod, Pr.first]

theorem resource_pr (n : Nat) (ds : Docs) (id : String) (m : ResourceMethod)
    (ms : List ResourceMethod) (rest : Toks)
    (hw : Wf.itemTypeDecl (.resource ds id (m :: ms)) = true)
    (hl : (Pr.itemTypeDecl (.resource ds id (m :: ms))).length < n) :
    Parse.itemTypeDecl n (Pr.itemTypeDecl (.resource ds id (m :: ms)) ++ rest) =
      some (.resource ds id (m :: ms), rest) := by
  have hm : ∀ x ∈ m :: ms, Wf.resourceMethod x = true := by
    simp [Wf.itemTypeDecl] at hw; simpa using hw.2
  have hl' : (List.flatMap Pr.resourceMethod (m :: ms)).length + 3 < n + 1 := by
    simp only [Pr.itemTypeDecl, List.length_cons, List.length_append] at hl; omega
  have hd := delim_flatMap (Parse.resourceMethod n) Pr.resourceMethod '}' (m :: ms) n rest
    (fun x hx r => resourceMethod_pr n x r (hm x hx)
      (by have := length_le_flatMap_of_mem Pr.resourceMethod hx; omega))
    (fun x _ => Pr.resourceMethod_ne x)
    (by have := length_le_flatMap Pr.resourceMethod (fun x => (Pr.resourceMethod_ne x).1) (m :: ms)
        omega)
  simp only [Pr.itemTypeDecl, Pr.first, List.cons_append, List.append_assoc,
    List.flatMap_cons] at hd ⊢
  simp [Parse.itemTypeDecl, hd]

theorem itemTypeDecl_pr (n : Nat) (d : ItemTypeDecl) (rest : Toks)
    (hw : Wf.itemTypeDecl d = true) (hl : (Pr.itemTypeDecl d).length < n) :
    Parse.itemTypeDecl n (Pr.itemTypeDecl d ++ rest) = some (d, rest) := by
  cases d with
  | resource ds id ms =>
    cases ms with
    | nil => simp [Pr.itemTypeDecl, Parse.itemTypeDecl, Pr.first]
    | cons m ms => exact resource_pr n ds id m ms rest hw hl
  | decl d =>
    have h := typeDecl_pr n d rest (by simpa [Wf.itemTypeDecl] using hw)
      (by simpa [Pr.itemTypeDecl] using hl)
    cases d <;> simp_all [Pr.itemTypeDecl, Parse.itemTypeDecl, Pr.typeDecl, Pr.first]

theorem ver?_ok {v : Option String} (h : verOk v = true) : ver? v = some v := by
  cases v <;> simp_all [ver?, verOk]

theorem pkgPath_pr (p : PkgPath) (rest : Toks) (h : pkgPathOk p = true) :
    Parse.pkgPath (tk (.ppath p.name p.segments p.version) :: rest) = some (p, rest) := by
  have hv : verOk p.version = true := by simp [pkgPathOk] at h; exact h.2
  simp [Parse.pkgPath, ver?_ok hv]

theorem pkgName_pr (p : PkgName) (rest : Toks) (h : pkgNameOk p = true) :
    Parse.pkgName (tk (.pname p.name p.version) :: rest) = some (p, rest) := by
  have hv : verOk p.version = true := by simp [pkgNameOk] at h; exact h.2
  simp [Parse.pkgName, ver?_ok hv]

theorem useItem_pr (i : UseItem) (rest : Toks) (hr : CommaOr '}' rest) :
    Parse.useItem (Pr.useItem i ++ rest) = some (i, rest) := by
  obtain ⟨id, a⟩ := i
  cases a with
  | none => simp [Pr.useItem, Parse.useItem, isTok_of_ne (hr.ne' (t := .kw .as) (by simp) (by simp))]
  | some a => simp [Pr.useItem, Parse.useItem]

theorem use_pr (n : Nat) (u : Use) (rest : Toks) (hw : Wf.use u = true)
    (hl : (Pr.use u).length < n) : Parse.use n (Pr.use u ++ rest) = some (u, rest) := by
  obtain ⟨ds, path, items⟩ := u
  have hd := delim_commaList Parse.useItem Pr.useItem '}' (by decide) items n (sy ';' :: rest)
    (fun i _ r hr => useItem_pr i r hr) (fun i _ => by simp [Pr.useItem])
    (by have := length_le_commaList' Pr.useItem (fun i => by simp [Pr.useItem]) items
        simp [Pr.use] at hl; omega)
  cases path with
  | package p =>
    have hp : pkgPathOk p = true := by simp [Wf.use] at hw; exact hw.1.2
    simp [Pr.use, Parse.use, Pr.first, docsOf, Parse.usePath, Pr.pkgPath, pkgPath_pr p _ hp, hd]
  | ident id => simp [Pr.use, Parse.use, Pr.first, docsOf, Parse.usePath, hd]

theorem funcTypeRef_pr (n : Nat) (f : FuncTypeRef) (rest : Toks) (hw : Wf.funcTypeRef f = true)
    (hl : (Pr.funcTypeRef f).length < n) :
    Parse.funcTypeRef n (Pr.funcTypeRef f ++ sy ';' :: rest) = some (f, sy ';' :: rest) := by
  cases f with
  | ident id => simp [Pr.funcTypeRef, Parse.funcTypeRef]
  | func f =>
    have h := funcType_pr n f (sy ';' :: rest) hw hl (by simp) (by simp)
    obtain ⟨a, ps, r⟩ := f
    cases a <;> simp_all [Pr.funcTypeRef, Parse.funcTypeRef, Pr.funcType]

theorem Pr.itemTypeDecl_head (d : ItemTypeDecl) : ∃ ds k l, Pr.itemTypeDecl d = ⟨ds, .kw k⟩ :: l ∧
    k ≠ .use ∧ k ≠ .import ∧ k ≠ .export ∧ k ≠ .include ∧ k ≠ .interface ∧ k ≠ .world ∧
    k ≠ .let := by
  cases d with
  | resource ds id ms => cases ms <;> exact ⟨_, _, _, rfl, by decide⟩
  | decl d => cases d <;> exact ⟨_, _, _, rfl, by decide⟩

theorem interfaceItem_pr (n : Nat) (i : InterfaceItem) (rest : Toks)
    (hw : Wf.interfaceItem i = true) (hl : (Pr.interfaceItem i).length < n) :
    Parse.interfaceItem n (Pr.interfaceItem i ++ rest) = some (i, rest) := by
  cases i with
  | use u =>
    have h := use_pr n u rest hw hl
    have he : Pr.use u = ⟨u.docs, .kw .use⟩ :: (Pr.use u).tail := rfl
    show Parse.interfaceItem n (Pr.use u ++ rest) = _
    rw [he, List.cons_append]; simp only [Parse.interfaceItem]; rw [← List.cons_append, ← he, h]
    rfl
  | type d =>
    have h := itemTypeDecl_pr n d rest hw hl
    obtain ⟨ds, k, l, he, h1, -⟩ := Pr.itemTypeDecl_head d
    simp only [Pr.interfaceItem] at h ⊢
    rw [he] at h ⊢
    cases k <;> simp_all [Parse.interfaceItem]
  | export_ ds id f =>
    have h := funcTypeRef_pr n f rest (by simp [Wf.interfaceItem] at hw; exact hw.2)
      (by simp [Pr.interfaceItem] at hl; omega)
    simp [Pr.interfaceItem, Parse.interfaceItem, Pr.first, h]

theorem Pr.interfaceItem_ne (i : InterfaceItem) :
    Pr.interfaceItem i ≠ [] ∧ hd? (Pr.interfaceItem i) ≠ some (.sym '}') := by
  cases i with
  | type d => obtain ⟨ds, k, l, he, -⟩ := Pr.itemTypeDecl_head d; simp [Pr.interfaceItem, he]
  | _ => simp [Pr.interfaceItem, Pr.use, Pr.first]

theorem interfaceBody_pr (n : Nat) (items : List InterfaceItem) (rest : Toks)
    (hw : ∀ i ∈ items, Wf.interfaceItem i = true)
    (hl : (items.flatMap Pr.interfaceItem).length + 1 < n) :
    Parse.interfaceBody n (sy '{' :: (items.flatMap Pr.interfaceItem ++ sy '}' :: rest)) =
      some (items, rest) := by
  have hd := delim_flatMap (Parse.interfaceItem n) Pr.interfaceItem '}' items n rest
    (fun x hx r => interfaceItem_pr n x r (hw x hx)
      (by have := length_le_flatMap_of_mem Pr.interfaceItem hx; omega))
    (fun x _ => Pr.interfaceItem_ne x)
    (by have := length_le_flatMap Pr.interfaceItem (fun x => (Pr.interfaceItem_ne x).1) items
        omega)
  simp [Parse.interfaceBody, hd]

theorem inlineInterface_pr (n : Nat) (items : List InterfaceItem) (rest : Toks)
    (hw : ∀ i ∈ items, Wf.interfaceItem i = true) (hl : (Pr.inlineInterface items).length < n) :
    Parse.inlineInterface n (Pr.inlineInterface items ++ rest) = some (items, rest) := by
  have h := interfaceBody_pr n items rest hw
    (by simp only [Pr.inlineInterface, List.length_cons, List.length_append] at hl; omega)
  simp [Pr.inlineInterface, Parse.inlineInterface, h]

theorem externType_pr (n : Nat) (t : ExternType) (rest : Toks) (hw : Wf.externType t = true)
    (hl : (Pr.externType t).length < n) :
    Parse.externType n (Pr.externType t ++ sy ';' :: rest) = some (t, sy ';' :: rest) := by
  cases t with
  | ident id => simp [Pr.externType, Parse.externType]
  | func f =>
    have h := funcType_pr n f (sy ';' :: rest) hw hl (by simp) (by simp)
    obtain ⟨a, ps, r⟩ := f
    cases a <;> simp_all [Pr.externType, Parse.externType, Pr.funcType]
  | interface items =>
    have h := inlineInterface_pr n items (sy ';' :: rest)
      (by simpa [Wf.externType] using hw) hl
    simp only [Pr.externType, Pr.inlineInterface, List.cons_append, List.append_assoc,
      List.nil_append] at h ⊢
    simp [Parse.externType, h]

theorem worldItemPath_pr (n : Nat) (p : WorldItemPath) (rest : Toks)
    (hw : Wf.worldItemPath p = true) (hl : (Pr.worldItemPath p).length < n) :
    Parse.worldItemPath n (Pr.worldItemPath p ++ sy ';' :: rest) = some (p, sy ';' :: rest) := by
  cases p with
  | named id t =>
    have h := externType_pr n t rest (by simp [Wf.worldItemPath] at hw; exact hw.2)
      (by simp [Pr.worldItemPath] at hl; omega)
    simp [Pr.worldItemPath, Parse.worldItemPath, h]
  | package p =>
    simp [Pr.worldItemPath, Parse.worldItemPath, Pr.pkgPath,
      pkgPath_pr p _ (by simpa [Wf.worldItemPath] using hw)]
  | ident id => simp [Pr.worldItemPath, Parse.worldItemPath]

end Silmaril.Wasm.Wac.Text
