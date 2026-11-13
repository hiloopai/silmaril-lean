module

public import Silmaril.Proofs.Wasm.Wit.Text.Basic

/-!
# WIT text: the printer writes lexable tokens

Every token the printer writes for a `printable` document is `Tok.ok`
(`okL_prDocument`), so the lexer reads the printed text back to the printer's tokens.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

open Silmaril.Wasm.Component.Wat (natChars)

/-- Every token of a layout is printable. -/
def okL (ps : List PTok) : Bool := ps.all fun p => p.1.ok

@[simp] theorem okL_nil : okL [] = true := rfl

@[simp] theorem okL_cons (p : PTok) (ps : List PTok) : okL (p :: ps) = (p.1.ok && okL ps) := rfl

@[simp] theorem okL_append (ps qs : List PTok) : okL (ps ++ qs) = (okL ps && okL qs) := by
  simp [okL, List.all_append]

theorem okL_flatMap {α : Type} (f : α → List PTok) (xs : List α) (h : ∀ x ∈ xs, okL (f x) = true) :
    okL (xs.flatMap f) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, okL_append, Bool.and_eq_true]
    exact ⟨h x (by simp), ih (fun y hy => h y (by simp [hy]))⟩

@[simp] theorem ok_kw (w : Kw) : (Tok.kw w).ok = true := rfl
@[simp] theorem ok_arrow : Tok.arrow.ok = true := rfl
@[simp] theorem ok_id (s : String) : (Tok.id s).ok = idOk s := rfl

theorem ok_sym_all : ∀ c ∈ symChars, (Tok.sym c).ok = true := by decide

@[simp] theorem ok_sym_eq : (Tok.sym '=').ok = true := by decide
@[simp] theorem ok_sym_comma : (Tok.sym ',').ok = true := by decide
@[simp] theorem ok_sym_colon : (Tok.sym ':').ok = true := by decide
@[simp] theorem ok_sym_dot : (Tok.sym '.').ok = true := by decide
@[simp] theorem ok_sym_semi : (Tok.sym ';').ok = true := by decide
@[simp] theorem ok_sym_lp : (Tok.sym '(').ok = true := by decide
@[simp] theorem ok_sym_rp : (Tok.sym ')').ok = true := by decide
@[simp] theorem ok_sym_lb : (Tok.sym '{').ok = true := by decide
@[simp] theorem ok_sym_rb : (Tok.sym '}').ok = true := by decide
@[simp] theorem ok_sym_lt : (Tok.sym '<').ok = true := by decide
@[simp] theorem ok_sym_gt : (Tok.sym '>').ok = true := by decide
@[simp] theorem ok_sym_at : (Tok.sym '@').ok = true := by decide
@[simp] theorem ok_sym_slash : (Tok.sym '/').ok = true := by decide

@[simp] theorem idOk_since : idOk "since" = true := by decide
@[simp] theorem idOk_version : idOk "version" = true := by decide
@[simp] theorem idOk_unstable : idOk "unstable" = true := by decide
@[simp] theorem idOk_feature : idOk "feature" = true := by decide
@[simp] theorem idOk_deprecated : idOk "deprecated" = true := by decide

theorem ok_verTok (v : Version) (h : verOk v = true) : (verTok v).ok = true := by
  simp [verTok, Tok.ok, numOk_verChars v h]

theorem numOk_natChars (n : Nat) : numOk (String.ofList (natChars n)) = true := by
  unfold numOk
  rw [String.toList_ofList]
  cases hn : natChars n with
  | nil => exact absurd hn (natChars_ne_nil' n)
  | cons d l =>
    simp only [Bool.and_eq_true, List.isEmpty_iff]
    refine ⟨natChars_digits n d (by simp [hn]), takeNum_of_numTail (numTail_all fun x hx => ?_)⟩
    exact (digit_ne (natChars_digits n x (by simp [hn, hx]))).2.2.2

theorem splitOn_not_mem_cons (c d : Char) (ds : List Char)
    (ih : ∀ w ∈ splitOn c ds, c ∉ w) : ∀ w ∈ splitOn c (d :: ds), c ∉ w := by
  intro w hw
  rw [splitOn] at hw
  split at hw
  · simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · simp
    · exact ih w hw
  · rename_i hd
    split at hw
    · rename_i w' ws hs
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · simp only [List.mem_cons, not_or]
        exact ⟨fun e => hd e.symm, ih w' (by simp [hs])⟩
      · exact ih w (by simp [hs, hw])
    · simp at hw; subst hw; simp; exact fun e => hd e.symm

theorem splitOn_not_mem (c : Char) : ∀ (l : List Char), ∀ w ∈ splitOn c l, c ∉ w := by
  intro l
  induction l with
  | nil => simp [splitOn]
  | cons d ds ih => exact splitOn_not_mem_cons c d ds ih

theorem okL_prDocs (d : Docs) : okL (prDocs d) = true := by
  obtain ⟨c⟩ := d
  cases c with
  | none => rfl
  | some s =>
    simp only [prDocs]
    apply List.all_eq_true.mpr
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨l, hl, rfl⟩ := hp
    have := splitOn_not_mem '\n' s.toList l hl
    simp [Tok.ok, String.toList_ofList, this]

theorem okL_prGates (gs : List Gate) (h : gs.all gateOk = true) : okL (prGates gs) = true := by
  apply okL_flatMap
  intro g hg
  have := List.all_eq_true.mp h g hg
  cases g with
  | since v => simp [prGate, ok_verTok v this]
  | unstable f => simp_all [prGate, gateOk]
  | deprecated v => simp [prGate, ok_verTok v this]

mutual
theorem okL_prTy : (t : Ty) → tyOk t = true → okL (prTy t) = true
  | .named _, h | .own _, h | .borrow _, h => by simp_all [prTy, tyOk]
  | .list t, h | .option t, h => by simp only [tyOk] at h; simp [prTy, okL_prTy t h]
  | .fixedList t n, h => by
    simp only [tyOk] at h
    have : (Tok.num (String.ofList (natChars n))).ok = true := numOk_natChars n
    simp [prTy, okL_prTy t h, this]
  | .map a b, h => by
    simp only [tyOk, Bool.and_eq_true] at h; simp [prTy, okL_prTy a h.1, okL_prTy b h.2]
  | .tuple ts, h => by simp only [tyOk] at h; simp [prTy, okL_prTys ts h]
  | .result a b, h => by
    simp only [tyOk, Bool.and_eq_true] at h
    have ha := okL_prOpt a h.1
    have hb := okL_prOpt b h.2
    cases a <;> cases b <;> simp_all [prTy, prOpt]
  | .future t, h | .stream t, h => by
    simp only [tyOk] at h
    have := okL_prOpt t h
    cases t <;> simp_all [prTy, prArg, prOpt]
  | .bool, _ | .s8, _ | .s16, _ | .s32, _ | .s64, _ | .u8, _ | .u16, _ | .u32, _ | .u64, _
  | .f32, _ | .f64, _ | .char, _ | .string, _ | .errorContext, _ => by simp [prTy]
theorem okL_prOpt : (t : Option Ty) → optOk t = true → okL (prOpt t) = true
  | none, _ => rfl
  | some t, h => okL_prTy t h
theorem okL_prTys : (ts : List Ty) → tysOk ts = true → okL (prTys ts) = true
  | [], _ => rfl
  | [t], h => by simp only [tysOk, Bool.and_eq_true] at h; simp [prTys, okL_prTy t h.1]
  | t :: t' :: ts, h => by
    simp only [tysOk, Bool.and_eq_true] at h
    have := okL_prTys (t' :: ts) (by simp only [tysOk, Bool.and_eq_true]; exact h.2)
    simp only [prTys, okL_append, okL_prTy t h.1, this]
    rfl
end

theorem okL_prSep {α : Type} (pr : α → List PTok) : ∀ (xs : List α),
    (∀ x ∈ xs, okL (pr x) = true) → okL (prSep pr xs) = true
  | [], _ => rfl
  | [x], h => by simp [prSep, h x (by simp)]
  | x :: x' :: xs, h => by
    have := okL_prSep pr (x' :: xs) (fun y hy => h y (by simp_all))
    simp only [prSep, okL_append, h x (by simp), this]
    rfl

theorem okL_prTerm {α : Type} (pr : α → List PTok) : ∀ (xs : List α),
    (∀ x ∈ xs, okL (pr x) = true) → okL (prTerm pr xs) = true
  | [], _ => rfl
  | x :: xs, h => by
    have := okL_prTerm pr xs (fun y hy => h y (by simp_all))
    simp only [prTerm, okL_append, h x (by simp), this]
    rfl

theorem okL_prSig (ps : List (Name × Ty)) (res : Option Ty)
    (hp : ps.all (fun p => idOk p.1 && tyOk p.2) = true) (hr : optOk res = true) :
    okL (prSig ps res) = true := by
  have h1 := okL_prSep prParam ps (fun x hx => by
    have := List.all_eq_true.mp hp x hx
    simp only [Bool.and_eq_true] at this
    simp [prParam, this.1, okL_prTy x.2 this.2])
  cases res with
  | none => simp [prSig, h1]
  | some t => simp only [optOk] at hr; simp [prSig, h1, okL_prTy t hr]

theorem okL_prFunc (f : Func) (h : funcOk f = true) : okL (prFunc f) = true := by
  simp only [funcOk, Bool.and_eq_true] at h
  have := okL_prSig f.params f.result h.1 h.2
  obtain ⟨ps, res, a⟩ := f
  cases a <;> simp_all [prFunc]

theorem okL_prResFunc (f : ResourceFunc) (h : resFuncOk f = true) : okL (prResFunc f) = true := by
  obtain ⟨kind, fn, d, gs⟩ := f
  simp only [resFuncOk, Bool.and_eq_true] at h
  obtain ⟨⟨hg, hf⟩, hk⟩ := h
  simp only [funcOk, Bool.and_eq_true] at hf
  have hs := okL_prSig fn.params fn.result hf.1 hf.2
  have hfn := okL_prFunc fn (by simp [funcOk, hf.1, hf.2])
  cases kind <;> simp_all [prResFunc, okL_prDocs, okL_prGates]

theorem okL_record (fs : List Field) (hk : (fs.all fun f => idOk f.name && tyOk f.ty) = true) :
    okL (prTerm prField fs) = true :=
  okL_prTerm prField fs (fun x hx => by
    have h1 : (idOk x.name && tyOk x.ty) = true := List.all_eq_true.mp hk x hx
    simp only [Bool.and_eq_true] at h1
    simp [prField, okL_prDocs, h1.1, okL_prTy x.ty h1.2])

theorem okL_variant (cs : List Case) (hk : (cs.all fun c => idOk c.name && optOk c.ty) = true) :
    okL (prTerm prCase cs) = true :=
  okL_prTerm prCase cs (fun x hx => by
    have h1 : (idOk x.name && optOk x.ty) = true := List.all_eq_true.mp hk x hx
    simp only [Bool.and_eq_true] at h1
    have h2 := okL_prOpt x.ty h1.2
    obtain ⟨s, t, d⟩ := x
    cases t <;> simp_all [prCase, okL_prDocs, prOpt])

theorem okL_labels (ls : List Label) (hk : (ls.all fun l => idOk l.name) = true) :
    okL (prTerm prLabel ls) = true :=
  okL_prTerm prLabel ls (fun x hx => by
    have h1 : idOk x.name = true := List.all_eq_true.mp hk x hx
    simp [prLabel, okL_prDocs, h1])

theorem okL_prTypeDefBody (nm : Name) (k : TypeDefKind) (hn : idOk nm = true)
    (hk : typeDefKindOk k = true) : okL (prTypeDefBody nm k) = true := by
  cases k with
  | «alias» t => simp only [typeDefKindOk] at hk; simp [prTypeDefBody, hn, okL_prTy t hk]
  | record fs => simp [prTypeDefBody, hn, okL_record fs (by simpa [typeDefKindOk] using hk)]
  | variant cs => simp [prTypeDefBody, hn, okL_variant cs (by simpa [typeDefKindOk] using hk)]
  | enum ls => simp [prTypeDefBody, hn, okL_labels ls (by simpa [typeDefKindOk] using hk)]
  | flags ls => simp [prTypeDefBody, hn, okL_labels ls (by simpa [typeDefKindOk] using hk)]
  | resource fs =>
    have h1 := okL_flatMap prResFunc fs (fun x hx =>
      okL_prResFunc x (List.all_eq_true.mp (by simpa [typeDefKindOk] using hk) x hx))
    cases fs <;> simp_all [prTypeDefBody]

theorem okL_prTypeDef (d : TypeDef) (h : typeDefOk d = true) : okL (prTypeDef d) = true := by
  simp only [typeDefOk, Bool.and_eq_true] at h
  simp [prTypeDef, okL_prDocs, okL_prGates d.gates h.1.2,
    okL_prTypeDefBody d.name d.kind h.1.1 h.2]

theorem okL_prPkgName (p : PackageName) (h : pkgNameOk p = true) : okL (prPkgName p) = true := by
  obtain ⟨ns, nm, v⟩ := p
  simp only [pkgNameOk, Bool.and_eq_true] at h
  cases v with
  | none => simp_all [prPkgName]
  | some v => simp_all [prPkgName, ok_verTok]

theorem okL_prPath (u : UsePath) (h : pathOk u = true) : okL (prPath u) = true := by
  cases u with
  | «local» a => simp_all [prPath, pathOk]
  | foreign p c =>
    obtain ⟨ns, nm, v⟩ := p
    simp only [pathOk, pkgNameOk, Bool.and_eq_true] at h
    cases v with
    | none => simp_all [prPath]
    | some v => simp_all [prPath, ok_verTok]

theorem okL_prUse (u : Use) (h : useOk u = true) : okL (prUse u) = true := by
  simp only [useOk, Bool.and_eq_true] at h
  have := okL_prSep prUseName u.names (fun x hx => by
    have := List.all_eq_true.mp h.2 x hx
    simp only [Bool.and_eq_true] at this
    obtain ⟨a, b⟩ := x
    cases b <;> simp_all [prUseName])
  simp [prUse, okL_prGates u.gates h.1.1, okL_prPath u.path h.1.2, this]

theorem okL_prIfaceItem (x : IfaceItem) (h : ifaceItemOk x = true) :
    okL (prIfaceItem x) = true := by
  cases x with
  | type d => exact okL_prTypeDef d h
  | use u => exact okL_prUse u h
  | func f =>
    simp only [ifaceItemOk, Bool.and_eq_true] at h
    simp [prIfaceItem, prFuncDef, okL_prDocs, okL_prGates f.gates h.1.2, h.1.1,
      okL_prFunc f.func h.2]

theorem okL_prIfaceItems (is : List IfaceItem) (h : is.all ifaceItemOk = true) :
    okL (prIfaceItems is) = true :=
  okL_flatMap _ is fun x hx => okL_prIfaceItem x (List.all_eq_true.mp h x hx)

theorem okL_prExtern (e : Extern) (h : externOk e = true) : okL (prExtern e) = true := by
  cases e with
  | func n f =>
    simp only [externOk, Bool.and_eq_true] at h
    simp [prExtern, h.1, okL_prFunc f h.2]
  | iface n is =>
    simp only [externOk, Bool.and_eq_true] at h
    simp [prExtern, h.1, okL_prIfaceItems is h.2]
  | path p => simp only [externOk] at h; simp [prExtern, okL_prPath p h]

theorem okL_prInclude (n : Include) (h : includeOk n = true) : okL (prInclude n) = true := by
  obtain ⟨p, names, gs⟩ := n
  simp only [includeOk, Bool.and_eq_true] at h
  have hs := okL_prSep prIncludeName names (fun x hx => by
    have := List.all_eq_true.mp h.2 x hx
    simp only [Bool.and_eq_true] at this
    simp [prIncludeName, this.1, this.2])
  cases names <;> simp_all [prInclude, okL_prGates, okL_prPath]

theorem okL_prWorldItem (x : WorldItem) (h : worldItemOk x = true) :
    okL (prWorldItem x) = true := by
  cases x with
  | «import» e =>
    simp only [worldItemOk, Bool.and_eq_true] at h
    simp [prWorldItem, okL_prDocs, okL_prGates e.gates h.1, okL_prExtern e.ext h.2]
  | «export» e =>
    simp only [worldItemOk, Bool.and_eq_true] at h
    simp [prWorldItem, okL_prDocs, okL_prGates e.gates h.1, okL_prExtern e.ext h.2]
  | use u => exact okL_prUse u h
  | type d => exact okL_prTypeDef d h
  | «include» n => exact okL_prInclude n h

theorem okL_prPackageItem (x : PackageItem) (h : packageItemOk x = true) :
    okL (prPackageItem x) = true := by
  cases x with
  | iface n =>
    simp only [packageItemOk, Bool.and_eq_true] at h
    simp [prPackageItem, prInterface, okL_prDocs, okL_prGates n.gates h.1.2, h.1.1,
      okL_prIfaceItems n.items h.2]
  | world w =>
    simp only [packageItemOk, Bool.and_eq_true] at h
    have := okL_flatMap prWorldItem w.items fun x hx =>
      okL_prWorldItem x (List.all_eq_true.mp h.2 x hx)
    simp [prPackageItem, prWorld, okL_prDocs, okL_prGates w.gates h.1.2, h.1.1, this]
  | use u =>
    obtain ⟨p, a, gs⟩ := u
    simp only [packageItemOk, Bool.and_eq_true] at h
    cases a <;> simp_all [prPackageItem, prTopUse, okL_prGates, okL_prPath]

theorem okL_prDocument (d : Document) (h : printable d = true) : okL (prDocument d) = true := by
  obtain ⟨⟨nm, is, dd⟩, ps⟩ := d
  simp only [printable, packageOk, Bool.and_eq_true] at h
  obtain ⟨⟨hn, hi⟩, hp⟩ := h
  have h1 := okL_flatMap prPackageItem is fun x hx =>
    okL_prPackageItem x (List.all_eq_true.mp hi x hx)
  have h2 := okL_flatMap prNested ps fun p hx => by
    have := List.all_eq_true.mp hp p hx
    simp only [packageOk, Bool.and_eq_true] at this
    have := okL_flatMap prPackageItem p.items fun x hx =>
      okL_prPackageItem x (List.all_eq_true.mp this.2 x hx)
    simp_all [prNested, okL_prDocs, okL_prPkgName]
  simp [prDocument, okL_prDocs, okL_prPkgName nm hn, h1, h2]

end Silmaril.Wasm.Wit.Text
