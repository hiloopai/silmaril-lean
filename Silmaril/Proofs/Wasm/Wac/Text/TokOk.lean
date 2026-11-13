module

public import Silmaril.Proofs.Wasm.Wac.Text.Document
public import Silmaril.Proofs.Wasm.Wac.Text.Chars

/-!
# WAC text: the printer writes lexable tokens

`document_tokOk`: every token of a printed well-formed document is `Tok.ok` and its doc
comments are `docsOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

/-- Every token is spellable and every doc comment is well formed. -/
def TokOk (ts : Toks) : Prop := ∀ a ∈ ts, a.tok.ok = true ∧ docsOk a.docs = true

@[simp] theorem tokOk_nil : TokOk [] := by simp [TokOk]

@[simp] theorem tokOk_cons (a : ATok) (l : Toks) :
    TokOk (a :: l) ↔ (a.tok.ok = true ∧ docsOk a.docs = true) ∧ TokOk l := by
  simp [TokOk]

@[simp] theorem tokOk_append (l m : Toks) : TokOk (l ++ m) ↔ TokOk l ∧ TokOk m := by
  simp only [TokOk, List.mem_append]
  exact ⟨fun h => ⟨fun a ha => h a (.inl ha), fun a ha => h a (.inr ha)⟩,
    fun h a ha => ha.elim (h.1 a) (h.2 a)⟩

@[simp] theorem tokOk_flatMap {α : Type} (f : α → Toks) (as : List α) :
    TokOk (as.flatMap f) ↔ ∀ a ∈ as, TokOk (f a) := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih]

@[simp] theorem ok_kw (k : Kw) : (Tok.kw k).ok = true := rfl
@[simp] theorem ok_id (s : String) : (Tok.id s).ok = idOk s := rfl
@[simp] theorem ok_str (s : String) : (Tok.str s).ok = strOk s := rfl
@[simp] theorem ok_sym (c : Char) : (Tok.sym c).ok = symChars.contains c := rfl
@[simp] theorem ok_arrow : Tok.arrow.ok = true := rfl
@[simp] theorem ok_ellipsis : Tok.ellipsis.ok = true := rfl

theorem tokOk_commaList {α : Type} (f : α → Toks) :
    ∀ as : List α, (∀ a ∈ as, TokOk (f a)) → TokOk (commaList f as)
  | [], _ => by simp [commaList]
  | [a], h => by simpa [commaList] using h a (by simp)
  | a :: b :: r, h => by
    rw [commaList_cons_cons]
    simp only [tokOk_append, tokOk_cons]
    exact ⟨h a (by simp), ⟨by simp [symChars], by decide⟩,
      tokOk_commaList f (b :: r) (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

@[simp] theorem docsOk_nil : docsOk [] = true := rfl

theorem ty_tokOk : ∀ t : Ty, Wf.ty t = true → TokOk (Pr.ty t)
  | .tuple ts, h => by
    have hall := (Wf.tys_iff ts).mp (by simp [Wf.ty] at h; exact h.2)
    have := tokOk_commaList Pr.ty ts (fun t ht =>
      have := List.sizeOf_lt_of_mem ht
      ty_tokOk t (hall t ht))
    simp [Pr.ty, Pr.tys_eq, this, symChars]
  | .list t, h | .option t, h => by
    have := ty_tokOk t (by simpa [Wf.ty] using h)
    simp [Pr.ty, this, symChars]
  | .result none none, _ => by simp [Pr.ty]
  | .result (some o) none, h => by
    have := ty_tokOk o (by simpa [Wf.ty] using h)
    simp [Pr.ty, this, symChars]
  | .result none (some e), h => by
    have := ty_tokOk e (by simpa [Wf.ty] using h)
    simp [Pr.ty, this, symChars]
  | .result (some o) (some e), h => by
    have h' : Wf.ty o = true ∧ Wf.ty e = true := by simpa [Wf.ty] using h
    have h1 := ty_tokOk o h'.1
    have h2 := ty_tokOk e h'.2
    simp [Pr.ty, h1, h2, symChars]
  | .stream none, _ | .future none, _ => by simp [Pr.ty]
  | .stream (some t), h | .future (some t), h => by
    have := ty_tokOk t (by simpa [Wf.ty] using h)
    simp [Pr.ty, this, symChars]
  | .borrow id, h | .ident id, h => by simp_all [Wf.ty, Pr.ty, symChars]
  | .u8, _ | .s8, _ | .u16, _ | .s16, _ | .u32, _ | .s32, _ | .u64, _ | .s64, _ | .f32, _
  | .f64, _ | .char, _ | .bool, _ | .string, _ | .errorContext, _ => by simp [Pr.ty]


theorem pkgPath_ok {p : PkgPath} (h : pkgPathOk p = true) : (Pr.pkgPath p).ok = true := by
  obtain ⟨n, sg, v⟩ := p
  cases v <;> simp_all [pkgPathOk, verOk, Pr.pkgPath, Tok.ok]

theorem pkgName_ok {p : PkgName} (h : pkgNameOk p = true) : (Tok.pname p.name p.version).ok = true := by
  obtain ⟨n, v⟩ := p
  cases v <;> simp_all [pkgNameOk, verOk, Tok.ok]

theorem namedType_tokOk (a : NamedType) (h : Wf.namedType a = true) : TokOk (Pr.namedType a) := by
  simp only [Wf.namedType, Bool.and_eq_true] at h
  simp [Pr.namedType, symChars, h.1, ty_tokOk _ h.2]

theorem funcType_tokOk (f : FuncType) (h : Wf.funcType f = true) : TokOk (Pr.funcType f) := by
  obtain ⟨a, ps, r⟩ := f
  simp only [Wf.funcType, Bool.and_eq_true, List.all_eq_true] at h
  have hp := tokOk_commaList Pr.namedType ps (fun x hx => namedType_tokOk x (h.1 x hx))
  cases a <;> cases r <;> simp_all [Pr.funcType, symChars, ty_tokOk]

theorem variantCase_tokOk (c : VariantCase)
    (h : (docsOk c.docs = true ∧ idOk c.id = true) ∧
      (match c.ty with | some t => Wf.ty t | none => true) = true) :
    TokOk (Pr.variantCase c) := by
  obtain ⟨cd, cid, ct⟩ := c
  cases ct <;> simp_all [Pr.variantCase, symChars, ty_tokOk]

theorem typeDecl_tokOk (d : TypeDecl) (h : Wf.typeDecl d = true) : TokOk (Pr.typeDecl d) := by
  cases d with
  | variant ds id cs =>
    simp only [Wf.typeDecl, Bool.and_eq_true, List.all_eq_true] at h
    have := tokOk_commaList Pr.variantCase cs (fun c hc => variantCase_tokOk c (h.2 c hc))
    simp_all [Pr.typeDecl, Pr.first, symChars]
  | record ds id fs =>
    simp only [Wf.typeDecl, Bool.and_eq_true, List.all_eq_true] at h
    have := tokOk_commaList Pr.field fs (fun f hf => by
      have := h.2 f hf; simp_all [Pr.field, symChars, ty_tokOk])
    simp_all [Pr.typeDecl, Pr.first, symChars]
  | flags ds id cs | enum ds id cs =>
    simp only [Wf.typeDecl, Bool.and_eq_true, List.all_eq_true] at h
    have := tokOk_commaList Pr.case cs (fun c hc => by
      have := h.2 c hc; simp_all [Pr.case])
    simp_all [Pr.typeDecl, Pr.first, symChars]
  | alias ds id k =>
    simp only [Wf.typeDecl, Bool.and_eq_true] at h
    cases k <;> simp_all [Pr.typeDecl, Pr.first, symChars, ty_tokOk, funcType_tokOk]

theorem itemTypeDecl_tokOk (d : ItemTypeDecl) (h : Wf.itemTypeDecl d = true) :
    TokOk (Pr.itemTypeDecl d) := by
  cases d with
  | resource ds id ms =>
    simp only [Wf.itemTypeDecl, Bool.and_eq_true, List.all_eq_true] at h
    have hm : ∀ m ∈ ms, TokOk (Pr.resourceMethod m) := fun m hm => by
      have := h.2 m hm
      cases m with
      | ctor ds' ps =>
        simp only [Wf.resourceMethod, Bool.and_eq_true, List.all_eq_true] at this
        have := tokOk_commaList Pr.namedType ps (fun x hx => namedType_tokOk x (this.2 x hx))
        simp_all [Pr.resourceMethod, Pr.first, symChars]
      | method ds' id' st f =>
        simp only [Wf.resourceMethod, Bool.and_eq_true] at this
        cases st <;> simp_all [Pr.resourceMethod, Pr.first, symChars, funcType_tokOk]
    cases ms <;> simp_all [Pr.itemTypeDecl, Pr.first, symChars]
  | decl d => exact typeDecl_tokOk d h

theorem use_tokOk (u : Use) (h : Wf.use u = true) : TokOk (Pr.use u) := by
  obtain ⟨ds, path, items⟩ := u
  simp only [Wf.use, Bool.and_eq_true, List.all_eq_true] at h
  have hi := tokOk_commaList Pr.useItem items (fun i hi => by
    have := h.2 i hi
    obtain ⟨id, a⟩ := i
    cases a <;> simp_all [Pr.useItem])
  cases path <;> simp_all [Pr.use, Pr.first, symChars, pkgPath_ok]

theorem interfaceItem_tokOk (i : InterfaceItem) (h : Wf.interfaceItem i = true) :
    TokOk (Pr.interfaceItem i) := by
  cases i with
  | use u => exact use_tokOk u h
  | type d => exact itemTypeDecl_tokOk d h
  | export_ ds id f =>
    simp only [Wf.interfaceItem, Bool.and_eq_true] at h
    cases f <;> simp_all [Wf.funcTypeRef, Pr.interfaceItem, Pr.funcTypeRef, Pr.first,
      symChars, funcType_tokOk]

theorem items_tokOk (items : List InterfaceItem) (h : ∀ i ∈ items, Wf.interfaceItem i = true) :
    TokOk (Pr.inlineInterface items) := by
  simpa [Pr.inlineInterface, symChars] using fun i hi => interfaceItem_tokOk i (h i hi)

theorem worldItemPath_tokOk (p : WorldItemPath) (h : Wf.worldItemPath p = true) :
    TokOk (Pr.worldItemPath p) := by
  cases p with
  | named id t =>
    simp only [Wf.worldItemPath, Bool.and_eq_true] at h
    cases t with
    | interface items =>
      have := items_tokOk items (by simpa [Wf.externType] using h.2)
      simp_all [Pr.worldItemPath, Pr.externType, symChars]
    | _ => simp_all [Wf.externType, Pr.worldItemPath, Pr.externType, symChars, funcType_tokOk]
  | _ => simp_all [Wf.worldItemPath, Pr.worldItemPath, pkgPath_ok]

theorem worldItem_tokOk (i : WorldItem) (h : Wf.worldItem i = true) : TokOk (Pr.worldItem i) := by
  cases i with
  | use u => exact use_tokOk u h
  | type d => exact itemTypeDecl_tokOk d h
  | import_ ds p | export_ ds p =>
    simp only [Wf.worldItem, Bool.and_eq_true] at h
    simp [Pr.worldItem, Pr.first, symChars, h.1, worldItemPath_tokOk p h.2]
  | «include» ds w ws =>
    simp only [Wf.worldItem, Bool.and_eq_true, List.all_eq_true] at h
    have hi := tokOk_commaList Pr.includeItem ws (fun i hi => by
      have := h.2 i hi; simp_all [Pr.includeItem])
    cases w <;> cases ws <;> simp_all [Pr.worldItem, Pr.first, symChars, pkgPath_ok]

theorem typeStatement_tokOk (s : TypeStatement) (h : Wf.typeStatement s = true) :
    TokOk (Pr.typeStatement s) := by
  cases s with
  | interface ds id items =>
    simp only [Wf.typeStatement, Bool.and_eq_true, List.all_eq_true] at h
    simp_all [Pr.typeStatement, Pr.first, symChars,
      fun i hi => interfaceItem_tokOk i (h.2 i hi)]
  | world ds id items =>
    simp only [Wf.typeStatement, Bool.and_eq_true, List.all_eq_true] at h
    simp_all [Pr.typeStatement, Pr.first, symChars,
      fun i hi => worldItem_tokOk i (h.2 i hi)]
  | type d => exact typeDecl_tokOk d h

theorem externName_ok (n : ExternName) (h : Wf.externName n = true) : (Pr.externName n).tok.ok = true := by
  cases n <;> simpa [Wf.externName, Pr.externName] using h

@[simp] theorem externName_docs (n : ExternName) : (Pr.externName n).docs = [] := by
  cases n <;> rfl

theorem postfix_tokOk (p : Postfix) (h : Wf.postfixOk p = true) : TokOk (Pr.postfixT p) := by
  cases p <;> simp_all [Wf.postfixOk, Pr.postfixT, symChars]

mutual
theorem expr_tokOk : ∀ e : Expr, Wf.expr e = true → TokOk (Pr.expr e)
  | .mk p post, h => by
    simp only [Wf.expr, Bool.and_eq_true, List.all_eq_true] at h
    simp only [Pr.expr, tokOk_append, tokOk_flatMap]
    exact ⟨primary_tokOk p h.1, fun x hx => postfix_tokOk x (h.2 x hx)⟩
theorem primary_tokOk : ∀ p : Primary, Wf.primary p = true → TokOk (Pr.primary p)
  | .new pkg as, h => by
    simp only [Wf.primary, Bool.and_eq_true] at h
    have := args_tokOk as h.2
    simp [Pr.primary, this, pkgName_ok h.1, symChars]
  | .nested e, h => by
    have := expr_tokOk e h
    simp [Pr.primary, this, symChars]
  | .ident id, h => by simpa [Pr.primary, Wf.primary] using h
theorem args_tokOk : ∀ as : List Arg, Wf.args as = true → TokOk (Pr.args as)
  | [], _ => by simp [Pr.args]
  | [a], h => by
    simp only [Wf.args, Bool.and_eq_true] at h
    simpa [Pr.args] using arg_tokOk a h.1
  | a :: b :: r, h => by
    simp only [Wf.args, Bool.and_eq_true] at h
    have h1 := arg_tokOk a h.1
    have h2 := args_tokOk (b :: r) (by simp only [Wf.args, Bool.and_eq_true]; exact h.2)
    simp [Pr.args, h1, h2, symChars]
theorem arg_tokOk : ∀ a : Arg, Wf.arg a = true → TokOk (Pr.arg a)
  | .inferred id, h | .spread id, h => by simpa [Pr.arg, Wf.arg] using h
  | .named n e, h => by
    simp only [Wf.arg, Bool.and_eq_true] at h
    have := expr_tokOk e h.2
    simp [Pr.arg, this, externName_ok n h.1, symChars]
  | .fill, _ => by simp [Pr.arg]
end

theorem statement_tokOk (s : Statement) (h : Wf.statement s = true) : TokOk (Pr.statement s) := by
  cases s with
  | import_ ds id n t =>
    simp only [Wf.statement, Bool.and_eq_true] at h
    have ht : TokOk (Pr.importType t) := by
      cases t with
      | interface items => exact items_tokOk items (by simpa [Wf.importType] using h.2)
      | func f => exact funcType_tokOk f h.2
      | package p => simp [Pr.importType, pkgPath_ok h.2]
      | ident id => simpa [Pr.importType, Wf.importType] using h.2
    cases n <;> simp_all [Pr.statement, Pr.first, symChars, externName_ok]
  | type s => exact typeStatement_tokOk s h
  | let_ ds id e =>
    simp only [Wf.statement, Bool.and_eq_true] at h
    simp [Pr.statement, Pr.first, symChars, h.1.1, h.1.2, expr_tokOk e h.2]
  | export_ ds e o =>
    simp only [Wf.statement, Bool.and_eq_true] at h
    have := expr_tokOk e h.1.2
    cases o <;> simp_all [Pr.statement, Pr.first, symChars, externName_ok]

theorem document_tokOk (d : Document) (h : wf d = true) : TokOk (Pr.document d) := by
  obtain ⟨ds, pkg, tg, ss⟩ := d
  simp only [wf, Bool.and_eq_true, List.all_eq_true] at h
  have hs : ∀ s ∈ ss, TokOk (Pr.statement s) := fun s hs => statement_tokOk s (h.2 s hs)
  cases tg <;> simp_all [Pr.document, Pr.first, symChars, pkgName_ok, pkgPath_ok]

end Silmaril.Wasm.Wac.Text
