module

public import Silmaril.Wasm.Wac.Valid.Defs
public import Silmaril.Wasm.Wac.ElabSpec.Defs
public import Silmaril.Wasm.Wac.Alias.Thms

/-!
# WAC validation: the checkers are sound

Every checker of `Silmaril.Wasm.Wac.Valid` that succeeds establishes its relation:

* `checkDecls_sound`: `DeclsOk` (unique labels);
* `checkStmts_sound`: `StmtsOk` (names in types);
* `externB_sound`, `specialB_complete`, `checkNames_sound`: `NamesOk`;
* `checkBorrows_sound`: `NoBorrowRes`;
* `eqIH`, `subIH`: the structural checkers `tyEqS`, …, `subS` decide their relations
  soundly at every fuel; `checkArgsS_sound`: `ArgsOk`; `checkTargetsS_sound`:
  `TargetsOk`;
* `elabDocV_sound`: elaboration with validation yields a graph `ElabDoc` relates to
  the document, and the document and the graph satisfy `DocOk` and `GraphOk`.

Only soundness is proved: the structural checkers use fuel, so they may reject a pair
of very large kinds that is related. The other checkers decide their relations, but
the converse directions are not stated.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Wit.Binary (Ty Sig TyRef Owner)

namespace Valid

/-! ## Sequencing -/

theorem andThen_ok {x y : Except VError Unit} (h : andThen x y = .ok ()) :
    x = .ok () ∧ y = .ok () := by
  cases x with
  | error e => exact absurd h (by simp [andThen])
  | ok u => exact ⟨rfl, by simpa [andThen] using h⟩

theorem allOk_ok {α : Type} {f : α → Except VError Unit} :
    ∀ {l : List α}, allOk f l = .ok () → ∀ a ∈ l, f a = .ok ()
  | [], _, _, ha => absurd ha List.not_mem_nil
  | b :: l, h, a, ha => by
    have hb : f b = .ok () ∧ allOk f l = .ok () := andThen_ok h
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact hb.1
    · exact allOk_ok hb.2 a ha'

theorem ite_ok {b : Bool} {e : VError}
    (h : (if b = true then (.ok () : Except VError Unit) else .error e) = .ok ()) : b = true := by
  cases b
  · exact absurd h (by simp)
  · rfl

theorem ite_err_ok {b : Bool} {e : VError}
    (h : (if b = true then (.error e : Except VError Unit) else .ok ()) = .ok ()) : b = false := by
  cases b
  · rfl
  · exact absurd h (by simp)

theorem firstDup_none : ∀ {l : List String}, firstDup l = none → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    by_cases ha : a ∈ l
    · exact absurd h (by simp [firstDup, ha])
    · have h' : firstDup l = none := by simpa [firstDup, ha] using h
      exact List.nodup_cons.2 ⟨ha, firstDup_none h'⟩

theorem noDup_ok {mk : String → VError} {l : List String} (h : noDup mk l = .ok ()) : l.Nodup := by
  cases hd : firstDup l with
  | none => exact firstDup_none hd
  | some n => exact absurd h (by simp [noDup, hd])

/-! ## 1. Declarations -/

theorem checkResource_sound {r : String} {fns : List Wit.ResourceFunc}
    (h : checkResource r fns = .ok ()) : DefOk (.resource fns) := by
  by_cases hc : 1 < (fns.filter isCtor).length
  · exact absurd h (by simp [checkResource, hc])
  · have h' : andThen (noDup (.duplicateMethod r) (fns.filterMap (rfName ·.kind)))
        (allOk (fun f => noDup (.duplicateParam r) (f.func.params.map (·.1))) fns) = .ok () := by
      simpa [checkResource, hc] using h
    have hp := andThen_ok h'
    exact ⟨by omega, noDup_ok hp.1, fun f hf => noDup_ok (allOk_ok hp.2 f hf)⟩

/-- **A checked type definition has unique labels.** -/
theorem checkDef_sound {t : Wit.TypeDef} (h : checkDef t = .ok ()) : DefOk t.kind := by
  cases hk : t.kind with
  | «alias» _ => trivial
  | record fs => exact noDup_ok (by simpa [checkDef, hk] using h)
  | variant cs => exact noDup_ok (by simpa [checkDef, hk] using h)
  | enum ls => exact noDup_ok (by simpa [checkDef, hk] using h)
  | flags ls => exact noDup_ok (by simpa [checkDef, hk] using h)
  | resource fns => exact checkResource_sound (by simpa [checkDef, hk] using h)

/-- **Checked declarations have unique labels.** -/
theorem checkDecls_sound {d : Syntax.Document} (h : checkDecls d = .ok ()) : DeclsOk d :=
  fun t ht => checkDef_sound (allOk_ok h t ht)

/-! ## 2. Names in types -/

theorem checkRef_sound {sc : CScope} {r : Bool × String} (h : checkRef sc r = .ok ()) :
    RefOk sc r := by
  obtain ⟨b, n⟩ := r
  cases hl : sc.lookup n with
  | none => exact absurd h (by simp [checkRef, hl])
  | some c =>
    refine ⟨c, hl, ?_⟩
    cases c <;> cases b <;> simp [CatOk, checkRef, hl] at h ⊢

theorem checkTy_sound {sc : CScope} {t : Wit.Ty} (h : checkTy sc t = .ok ()) : TyOk sc t :=
  fun r hr => checkRef_sound (allOk_ok h r hr)

theorem checkFunc_sound {sc : CScope} {f : Wit.Func} (h : checkFunc sc f = .ok ()) : FuncOk sc f := by
  have hp := andThen_ok h
  exact ⟨fun p hp' => checkTy_sound (allOk_ok hp.1 p hp'),
    fun t ht => checkTy_sound (allOk_ok hp.2 t (Option.mem_toList.2 ht))⟩

theorem checkTypeDef_sound {sc : CScope} {d : Wit.TypeDef} (h : checkTypeDef sc d = .ok ()) :
    TypeDefOk sc d :=
  fun t ht => checkTy_sound (allOk_ok h t ht)

/-- **Checked interface items are well scoped.** -/
theorem checkIfaceItems_sound {sc : CScope} {items : List Wit.IfaceItem}
    (h : checkIfaceItems sc items = .ok ()) : IfaceItemsOk sc items := by
  induction items generalizing sc with
  | nil => trivial
  | cons it rest ih =>
    cases it with
    | type _ => exact ⟨checkTypeDef_sound (andThen_ok h).1, ih (andThen_ok h).2⟩
    | func _ => exact ⟨checkFunc_sound (andThen_ok h).1, ih (andThen_ok h).2⟩
    | use _ => exact ih h

theorem checkExtern_sound {sc : CScope} : ∀ {e : Wit.Extern}, checkExtern sc e = .ok () → ExternOk sc e
  | .func _ _, h => checkFunc_sound h
  | .iface _ _, h => checkIfaceItems_sound h
  | .path _, _ => trivial

/-- **Checked world items are well scoped.** -/
theorem checkWorldItems_sound {sc : CScope} {items : List Wit.WorldItem}
    (h : checkWorldItems sc items = .ok ()) : WorldItemsOk sc items := by
  induction items generalizing sc with
  | nil => trivial
  | cons it rest ih =>
    cases it with
    | type _ => exact ⟨checkTypeDef_sound (andThen_ok h).1, ih (andThen_ok h).2⟩
    | use _ => exact ih h
    | «import» _ => exact ⟨checkExtern_sound (andThen_ok h).1, ih (andThen_ok h).2⟩
    | «export» _ => exact ⟨checkExtern_sound (andThen_ok h).1, ih (andThen_ok h).2⟩
    | «include» _ => exact ih h

theorem checkImportTy_sound {sc : CScope} :
    ∀ {t : Syntax.ImportType}, checkImportTy sc t = .ok () → ImportTyOk sc t
  | .func _, h => checkFunc_sound h
  | .iface _, h => checkIfaceItems_sound h
  | .path _, _ | .ident _, _ => trivial

/-- **Checked statements are well scoped.** -/
theorem checkStmts_sound {sc : CScope} {ss : List Syntax.Stmt}
    (h : checkStmts sc ss = .ok ()) : StmtsOk sc ss := by
  induction ss generalizing sc with
  | nil => trivial
  | cons st rest ih =>
    cases st with
    | type t =>
      cases t with
      | iface _ => exact ⟨checkIfaceItems_sound (andThen_ok h).1, ih (andThen_ok h).2⟩
      | world _ => exact ⟨checkWorldItems_sound (andThen_ok h).1, ih (andThen_ok h).2⟩
      | type _ => exact ⟨checkTypeDef_sound (andThen_ok h).1, ih (andThen_ok h).2⟩
    | «import» _ => exact ⟨checkImportTy_sound (andThen_ok h).1, ih (andThen_ok h).2⟩
    | «let» _ _ => exact ih h
    | «export» _ _ => exact ih h

/-! ## 3. Extern names -/

open Silmaril.Wasm.Wit.Binary (dropPrefix? splitAt?)

theorem dropPrefix?_eq : ∀ {p l r : List Char}, dropPrefix? p l = some r → l = p ++ r
  | [], l, r, h => by
    have e : l = r := by simpa [dropPrefix?] using h
    rw [e]; rfl
  | _ :: _, [], _, h => absurd h (by simp [dropPrefix?])
  | a :: p, b :: l, r, h => by
    by_cases hab : a = b
    · have h' : dropPrefix? p l = some r := by simpa [dropPrefix?, hab] using h
      rw [dropPrefix?_eq h', hab]; rfl
    · exact absurd h (by simp [dropPrefix?, hab])

theorem dropPrefix?_app : ∀ (p r : List Char), dropPrefix? p (p ++ r) = some r
  | [], _ => rfl
  | a :: p, r => by simpa [dropPrefix?] using dropPrefix?_app p r

theorem splitAt?_eq {c : Char} : ∀ {l x y : List Char}, splitAt? c l = some (x, y) → l = x ++ c :: y
  | [], _, _, h => absurd h (by simp [splitAt?])
  | a :: l, x, y, h => by
    by_cases hac : a = c
    · have e : [] = x ∧ l = y := by simpa [splitAt?, hac] using h
      rw [← e.1, ← e.2, hac]; rfl
    · cases hs : splitAt? c l with
      | none => exact absurd h (by simp [splitAt?, hac, hs])
      | some q =>
        have e : a :: q.1 = x ∧ q.2 = y := by simpa [splitAt?, hac, hs] using h
        have e2 : l = q.1 ++ c :: q.2 := splitAt?_eq (show splitAt? c l = some (q.1, q.2) from hs)
        rw [← e.1, ← e.2, e2]; rfl

theorem labelB_sound {cs : List Char} (h : labelB cs = true) : Label cs := by
  simpa [labelB, Label, List.all_eq_true] using h

theorem verB_sound {v : List Char} (h : verB v = true) : VerOk v := by
  have h' : v.isEmpty = false ∧ ∀ c ∈ v, verChar c = true := by simpa [verB, List.all_eq_true] using h
  exact ⟨fun e => by simp [e] at h', h'.2⟩

theorem afterB_sound {p : List Char} {k : List Char → Bool} {cs : List Char}
    (h : afterB p k cs = true) : ∃ r, cs = p ++ r ∧ k r = true := by
  cases hd : dropPrefix? p cs with
  | none => exact absurd h (by simp [afterB, hd])
  | some r => exact ⟨r, dropPrefix?_eq hd, by simpa [afterB, hd] using h⟩

theorem dotB_sound {r : List Char} (h : dotB r = true) :
    ∃ a b, r = a ++ '.' :: b ∧ Label a ∧ Label b := by
  cases hs : splitAt? '.' r with
  | none => exact absurd h (by simp [dotB, hs])
  | some q =>
    have hb : labelB q.1 = true ∧ labelB q.2 = true := by simpa [dotB, hs] using h
    exact ⟨q.1, q.2, splitAt?_eq (by rw [hs]), labelB_sound hb.1, labelB_sound hb.2⟩

theorem after_label {p cs : List Char} (h : afterB p labelB cs = true) :
    ∃ r, cs = p ++ r ∧ Label r := by
  obtain ⟨r, e, hr⟩ := afterB_sound h
  exact ⟨r, e, labelB_sound hr⟩

theorem after_dot {p cs : List Char} (h : afterB p dotB cs = true) :
    ∃ r m, cs = p ++ r ++ '.' :: m ∧ Label r ∧ Label m := by
  obtain ⟨r, e, hr⟩ := afterB_sound h
  obtain ⟨a, b, e', ha, hb⟩ := dotB_sound hr
  exact ⟨a, b, by rw [e, e', List.append_assoc], ha, hb⟩

/-- The parts of an interface name. -/
def IfaceParts (cs : List Char) : Prop :=
  ∃ ns pkg i v, cs = ns ++ ':' :: (pkg ++ '/' :: (i ++ verSuffix v)) ∧ Label ns ∧ Label pkg ∧
    Label i ∧ ∀ s ∈ v, VerOk s

/-- The parts of an interface name `ifaceB` accepts. -/
theorem ifaceB_parts {cs : List Char} (h : ifaceB cs = true) : IfaceParts cs := by
  cases h1 : splitAt? ':' cs with
  | none => exact absurd h (by simp [ifaceB, h1])
  | some q =>
    show IfaceParts cs
    cases h2 : splitAt? '/' q.2 with
    | none => exact absurd h (by simp [ifaceB, h1, h2])
    | some q2 =>
      show IfaceParts cs
      have e1 : cs = q.1 ++ ':' :: q.2 := splitAt?_eq (by rw [h1])
      have e2 : q.2 = q2.1 ++ '/' :: q2.2 := splitAt?_eq (by rw [h2])
      cases h3 : splitAt? '@' q2.2 with
      | none =>
        have hb : (labelB q.1 = true ∧ labelB q2.1 = true) ∧ labelB q2.2 = true := by
          simpa [ifaceB, h1, h2, h3] using h
        refine ⟨q.1, q2.1, q2.2, none, ?_, labelB_sound hb.1.1, labelB_sound hb.1.2,
          labelB_sound hb.2, by simp⟩
        rw [e1, e2]; simp [verSuffix]
      | some q3 =>
        have e3 : q2.2 = q3.1 ++ '@' :: q3.2 := splitAt?_eq (by rw [h3])
        have hb : (labelB q.1 = true ∧ labelB q2.1 = true) ∧ labelB q3.1 = true ∧ verB q3.2 = true := by
          simpa [ifaceB, h1, h2, h3] using h
        refine ⟨q.1, q2.1, q3.1, some q3.2, ?_, labelB_sound hb.1.1, labelB_sound hb.1.2,
          labelB_sound hb.2.1, fun s hs => ?_⟩
        · rw [e1, e2, e3]; rfl
        · exact (Option.some.inj hs) ▸ verB_sound hb.2.2

theorem eq_dropLast {l : List Char} {a : Char} (h : l.getLast? = some a) : l = l.dropLast ++ [a] := by
  have hne : l ≠ [] := by rintro rfl; exact absurd h (by simp)
  have hl : l.getLast hne = a := by
    rw [List.getLast?_eq_some_getLast hne] at h; exact Option.some.inj h
  rw [← hl]; exact (List.dropLast_append_getLast hne).symm

theorem specialB_sound {cs : List Char} (h : specialB cs = true) : Special cs := by
  obtain ⟨p, hp, hs⟩ := List.any_eq_true.1 h
  obtain ⟨r, e, hr⟩ := afterB_sound hs
  have hl : r.getLast? = some '>' := by simpa using hr
  exact ⟨p, hp, r.dropLast, by rw [e, List.append_assoc, ← eq_dropLast hl]⟩

/-- **A special name is recognised as one.** -/
theorem specialB_complete {cs : List Char} (h : Special cs) : specialB cs = true := by
  obtain ⟨p, hp, body, e⟩ := h
  refine List.any_eq_true.2 ⟨p, hp, ?_⟩
  rw [e, List.append_assoc]
  simp [afterB, dropPrefix?_app]

/-- **`externB` accepts only extern names.** -/
theorem externB_sound {cs : List Char} (h : externB cs = true) : ExternName cs := by
  simp only [externB, Bool.or_eq_true] at h
  rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · exact .label (labelB_sound h)
  · obtain ⟨r, rfl, hr⟩ := after_label h; exact .ctor hr
  · obtain ⟨r, rfl, hr⟩ := after_label h; exact .async hr
  · obtain ⟨r, m, rfl, hr, hm⟩ := after_dot h; exact .method hr hm
  · obtain ⟨r, m, rfl, hr, hm⟩ := after_dot h; exact .static hr hm
  · obtain ⟨r, m, rfl, hr, hm⟩ := after_dot h; exact .asyncMethod hr hm
  · obtain ⟨r, m, rfl, hr, hm⟩ := after_dot h; exact .asyncStatic hr hm
  · obtain ⟨ns, pkg, i, v, rfl, h1, h2, h3, h4⟩ := ifaceB_parts h; exact .iface h1 h2 h3 h4
  · obtain ⟨p, hp, body, rfl⟩ := specialB_sound h; exact .special hp

/-- **Checked names are valid.** -/
theorem checkNames_sound {g : CGraph} (h : checkNames g = .ok ()) : NamesOk g := by
  have hp := andThen_ok h
  refine ⟨fun p hp' => externB_sound (ite_ok (allOk_ok hp.1 p hp')), fun p hp' => ?_⟩
  have hb : (externB p.1.toList && !specialB p.1.toList) = true := ite_ok (allOk_ok hp.2 p hp')
  have hb' : externB p.1.toList = true ∧ specialB p.1.toList = false := by simpa using hb
  exact ⟨externB_sound hb'.1, fun hs => by rw [specialB_complete hs] at hb'; exact absurd hb'.2 (by simp)⟩

/-! ## 4. Borrows in results -/

theorem hasBorrowList_of_mem {t : Silmaril.Wasm.Wit.Binary.Ty} : ∀ {ts : List Silmaril.Wasm.Wit.Binary.Ty}, t ∈ ts → hasBorrow t = true →
    hasBorrowList ts = true
  | _ :: _, .head _, h => by simp [hasBorrowList, h]
  | _ :: _, .tail _ hm, h => by simp [hasBorrowList, hasBorrowList_of_mem hm h]

/-- **`hasBorrow` finds every borrow.** -/
theorem hasBorrow_of_borrowIn {t : Silmaril.Wasm.Wit.Binary.Ty} (h : BorrowIn t) : hasBorrow t = true := by
  induction h with
  | borrow r => rfl
  | tuple hm _ ih => simpa [hasBorrow] using hasBorrowList_of_mem hm ih
  | list _ ih | fixedList _ ih | option _ ih => simpa [hasBorrow] using ih
  | mapK _ ih | mapV _ ih => simp [hasBorrow, ih]
  | resultOk _ ih | resultErr _ ih => simp [hasBorrow, hasBorrowOpt, ih]
  | future _ ih | stream _ ih => simpa [hasBorrow, hasBorrowOpt] using ih

theorem badEx_mem {n : String} {k : Kind} : ∀ {es : Externs}, badEx es = false → (n, k) ∈ es →
    badKind k = false
  | _ :: _, h, .head _ => by simp only [badEx, Bool.or_eq_false_iff] at h; exact h.1
  | _ :: _, h, .tail _ hm => by simp only [badEx, Bool.or_eq_false_iff] at h; exact badEx_mem h.2 hm

theorem sigIn_ok {k : Kind} {s : Sig} (hs : SigIn k s) (h : badKind k = false) :
    hasBorrowOpt s.result = false := by
  induction hs with
  | func s => simpa [badKind] using h
  | type _ ih => exact ih (by simpa [badKind] using h)
  | inst hm _ ih => exact ih (badEx_mem (by simpa [badKind] using h) hm)
  | compI hm _ ih => exact ih (badEx_mem (by simp only [badKind, Bool.or_eq_false_iff] at h; exact h.1) hm)
  | compE hm _ ih => exact ih (badEx_mem (by simp only [badKind, Bool.or_eq_false_iff] at h; exact h.2) hm)

/-- **Checked kinds return no borrow.** -/
theorem checkBorrows_sound {g : CGraph} (h : checkBorrows g = .ok ()) : NoBorrowRes g := by
  intro nd hnd s hs t ht hb
  have hk : badKind nd.kind = false := ite_err_ok (allOk_ok h nd hnd)
  have h0 : hasBorrowOpt s.result = false := sigIn_ok hs hk
  have e : s.result = some t := ht
  rw [e] at h0
  exact absurd (hasBorrow_of_borrowIn hb) (by simpa [hasBorrowOpt] using h0)

/-! ## 5. Structural comparison -/

/-- The structural equality checkers at fuel `n` are sound. -/
structure EqIH (n : Nat) : Prop where
  ty : ∀ {A B t u}, tyEqS n A B t u = true → TyEqS A B t u
  opt : ∀ {A B a b}, optEqS n A B a b = true → OptEqS A B a b
  tys : ∀ {A B ts us}, tysEqS n A B ts us = true → TysEqS A B ts us
  fields : ∀ {A B fs gs}, fieldsEqS n A B fs gs = true → FieldsEqS A B fs gs
  cases : ∀ {A B cs ds}, casesEqS n A B cs ds = true → CasesEqS A B cs ds
  nom : ∀ {A B a b}, nomEqS n A B a b = true → NomEqS A B a b

theorem eqIH_zero : EqIH 0 where
  ty h := by simp [tyEqS] at h
  opt h := by simp [optEqS] at h
  tys h := by simp [tysEqS] at h
  fields h := by simp [fieldsEqS] at h
  cases h := by simp [casesEqS] at h
  nom h := by simp [nomEqS] at h

theorem tyEqS_ref {n : Nat} (ih : EqIH n) {A B : Bridge.NomTable} {r r' : TyRef}
    (h : tyEqS (n + 1) A B (.ref r) (.ref r') = true) : TyEqS A B (.ref r) (.ref r') := by
  cases ha : nomOf A r with
  | some a =>
    cases hb : nomOf B r' with
    | some b => exact .refNom ha hb (ih.nom (by simpa [tyEqS, ha, hb] using h))
    | none =>
      have e : r = r' := by simpa [tyEqS, ha, hb] using h
      exact e ▸ .refOpaque (Or.inr (e ▸ hb))
  | none =>
    have e : r = r' := by cases hb : nomOf B r' <;> simpa [tyEqS, ha, hb] using h
    exact e ▸ .refOpaque (Or.inl ha)

theorem tyEqS_succ {n : Nat} (ih : EqIH n) {A B : Bridge.NomTable} {t u : Silmaril.Wasm.Wit.Binary.Ty}
    (h : tyEqS (n + 1) A B t u = true) : TyEqS A B t u := by
  cases t <;> cases u <;> simp only [tyEqS, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  case prim.prim p q => exact h ▸ .prim p
  case ref.ref r r' => exact tyEqS_ref ih (by simpa [tyEqS] using h)
  case list.list => exact .list (ih.ty h)
  case fixedList.fixedList t k u k' => exact h.1 ▸ .fixedList k (ih.ty h.2)
  case map.map => exact .map (ih.ty h.1) (ih.ty h.2)
  case option.option => exact .option (ih.ty h)
  case result.result => exact .result (ih.opt h.1) (ih.opt h.2)
  case tuple.tuple => exact .tuple (ih.tys h)
  case own.own r r' => exact h ▸ .own r
  case borrow.borrow r r' => exact h ▸ .borrow r
  case future.future => exact .future (ih.opt h)
  case stream.stream => exact .stream (ih.opt h)

theorem optEqS_succ {n : Nat} (ih : EqIH n) {A B : Bridge.NomTable} :
    ∀ {a b : Option Silmaril.Wasm.Wit.Binary.Ty}, optEqS (n + 1) A B a b = true → OptEqS A B a b
  | none, none, _ => .none
  | some _, some _, h => .some (ih.ty h)
  | none, some _, h | some _, none, h => absurd h (by simp [optEqS])

theorem tysEqS_succ {n : Nat} (ih : EqIH n) {A B : Bridge.NomTable} :
    ∀ {ts us : List Silmaril.Wasm.Wit.Binary.Ty}, tysEqS (n + 1) A B ts us = true → TysEqS A B ts us
  | [], [], _ => .nil
  | _ :: _, _ :: _, h => by
    have h' := Bool.and_eq_true _ _ ▸ h
    exact .cons (ih.ty h'.1) (ih.tys h'.2)
  | [], _ :: _, h | _ :: _, [], h => absurd h (by simp [tysEqS])

theorem fieldsEqS_succ {n : Nat} (ih : EqIH n) {A B : Bridge.NomTable} :
    ∀ {fs gs : List (String × Silmaril.Wasm.Wit.Binary.Ty)}, fieldsEqS (n + 1) A B fs gs = true → FieldsEqS A B fs gs
  | [], [], _ => .nil
  | (k, t) :: fs, (k', u) :: gs, h => by
    have h' : (k = k' ∧ tyEqS n A B t u = true) ∧ fieldsEqS n A B fs gs = true := by
      simpa [fieldsEqS] using h
    exact h'.1.1 ▸ .cons (ih.ty h'.1.2) (ih.fields h'.2)
  | [], _ :: _, h | _ :: _, [], h => absurd h (by simp [fieldsEqS])

theorem casesEqS_succ {n : Nat} (ih : EqIH n) {A B : Bridge.NomTable} :
    ∀ {cs ds : List (String × Option Silmaril.Wasm.Wit.Binary.Ty)}, casesEqS (n + 1) A B cs ds = true → CasesEqS A B cs ds
  | [], [], _ => .nil
  | (k, t) :: cs, (k', u) :: ds, h => by
    have h' : (k = k' ∧ optEqS n A B t u = true) ∧ casesEqS n A B cs ds = true := by
      simpa [casesEqS] using h
    exact h'.1.1 ▸ .cons (ih.opt h'.1.2) (ih.cases h'.2)
  | [], _ :: _, h | _ :: _, [], h => absurd h (by simp [casesEqS])

theorem nomEqS_succ {n : Nat} (ih : EqIH n) {A B : Bridge.NomTable} {a b : Bridge.Nominal}
    (h : nomEqS (n + 1) A B a b = true) : NomEqS A B a b := by
  cases a <;> cases b <;> simp only [nomEqS, Bool.false_eq_true, beq_iff_eq] at h
  case record.record => exact .record (ih.fields h)
  case variant.variant => exact .variant (ih.cases h)
  case enum.enum ls ls' => exact h ▸ .enum ls
  case flags.flags ls ls' => exact h ▸ .flags ls

/-- **The structural equality checkers are sound**, at every fuel. -/
theorem eqIH : ∀ n, EqIH n
  | 0 => eqIH_zero
  | n + 1 =>
    have ih := eqIH n
    ⟨tyEqS_succ ih, optEqS_succ ih, tysEqS_succ ih, fieldsEqS_succ ih, casesEqS_succ ih,
      nomEqS_succ ih⟩

theorem sigEqS_sound {n : Nat} {A B : Bridge.NomTable} {s s' : Sig}
    (h : sigEqS n A B s s' = true) : SigEqS A B s s' := by
  have h' : (s.async = s'.async ∧ fieldsEqS n A B s.params s'.params = true) ∧
      optEqS n A B s.result s'.result = true := by simpa [sigEqS] using h
  exact ⟨h'.1.1, (eqIH n).fields h'.1.2, (eqIH n).opt h'.2⟩

/-- The structural subtype checkers at fuel `n` are sound. -/
structure SubIH (n : Nat) : Prop where
  sub : ∀ {A B a b}, subS n A B a b = true → SubS A B a b
  ex : ∀ {A B as bs}, subExS n A B as bs = true → SubExS A B as bs
  any : ∀ {A B as k b}, anyMatchS n A B as k b = true → ∃ a, (k, a) ∈ as ∧ SubS A B a b

theorem subIH_zero : SubIH 0 where
  sub h := by simp [subS] at h
  ex h := by simp [subExS] at h
  any h := by simp [anyMatchS] at h

theorem subS_succ {n : Nat} (ih : SubIH n) {A B : Bridge.NomTable} {a b : Kind}
    (h : subS (n + 1) A B a b = true) : SubS A B a b := by
  cases a <;> cases b <;> simp only [subS, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  case func.func => exact .func (sigEqS_sound h)
  case value.value => exact .value ((eqIH n).ty h)
  case resource.resource r r' => exact h ▸ .resource r
  case type.type => exact .type (ih.sub h)
  case inst.inst => exact .inst (ih.ex h)
  case comp.comp => exact .comp (ih.ex h.1) (ih.ex h.2)

theorem subExS_succ {n : Nat} (ih : SubIH n) {A B : Bridge.NomTable} {as : Externs} :
    ∀ {bs : Externs}, subExS (n + 1) A B as bs = true → SubExS A B as bs
  | [], _ => .nil as
  | (k, b) :: bs, h => by
    have h' : anyMatchS n A B as k b = true ∧ subExS n A B as bs = true := by simpa [subExS] using h
    obtain ⟨a, ha, hs⟩ := ih.any h'.1
    exact .cons ha hs (ih.ex h'.2)

theorem anyMatchS_succ {n : Nat} (ih : SubIH n) {A B : Bridge.NomTable} {k : String} {b : Kind} :
    ∀ {as : Externs}, anyMatchS (n + 1) A B as k b = true → ∃ a, (k, a) ∈ as ∧ SubS A B a b
  | [], h => absurd h (by simp [anyMatchS])
  | (k', a) :: as, h => by
    have h' : (k' = k ∧ subS n A B a b = true) ∨ anyMatchS n A B as k b = true := by
      simpa [anyMatchS] using h
    rcases h' with h1 | h2
    · exact ⟨a, h1.1 ▸ List.mem_cons_self, ih.sub h1.2⟩
    · obtain ⟨a', ha', hs⟩ := ih.any h2
      exact ⟨a', List.mem_cons_of_mem _ ha', hs⟩

/-- **The structural subtype checker is sound**, at every fuel. -/
theorem subIH : ∀ n, SubIH n
  | 0 => subIH_zero
  | n + 1 =>
    have ih := subIH n
    ⟨subS_succ ih, subExS_succ ih, anyMatchS_succ ih⟩

theorem subS_sound {n : Nat} {A B : Bridge.NomTable} {a b : Kind} (h : subS n A B a b = true) :
    SubS A B a b := (subIH n).sub h

theorem checkNodeArgs_sound {T : Tables} {env : PkgEnv} {doc : String} {g : CGraph} {nd : CNode}
    (h : checkNodeArgs T env doc g nd = .ok ()) {p : String} {imps : Externs} {args : List (String × Nat)}
    (hop : nd.op = .inst p imps args) {a : String × Nat} (ha : a ∈ args) {k : Kind}
    (hk : Externs.find imps a.1 = some k) :
    SubS (T.of (origin env doc g a.2)) (T.of (.pkg p)) (g.kindOf a.2) k := by
  unfold checkNodeArgs at h
  rw [hop] at h
  have h' := allOk_ok h a ha
  beta_reduce at h'
  rw [hk] at h'
  exact subS_sound (ite_ok h')

/-- **Checked instantiation arguments match structurally.** -/
theorem checkArgsS_sound {T : Tables} {env : PkgEnv} {doc : String} {g : CGraph}
    (h : checkArgsS T env doc g = .ok ()) : ArgsOk T env doc g :=
  fun nd hnd _ _ _ hop _ ha _ hk => checkNodeArgs_sound (allOk_ok h nd hnd) hop ha hk

/-- **A checked `targets` world is satisfied structurally.** -/
theorem checkTargetsS_sound {T : Tables} {env : PkgEnv} {d : Syntax.Document} {g : CGraph}
    (h : checkTargetsS T env d g = .ok ()) : TargetsOk T env d g := by
  intro i wi we o ht
  unfold checkTargetsS at h
  rw [ht] at h
  have hp := andThen_ok h
  refine ⟨fun q hq k' hk => ?_, fun q hq j hj => ?_⟩
  · have h1 := allOk_ok hp.1 q hq
    beta_reduce at h1
    rw [hk] at h1
    exact subS_sound (ite_ok h1)
  · have h2 := allOk_ok hp.2 q hq
    beta_reduce at h2
    rw [hj] at h2
    exact subS_sound (ite_ok h2)

/-! ## Everything together -/

theorem checkDoc_sound {d : Syntax.Document} (h : checkDoc d = .ok ()) : DocOk d :=
  ⟨checkDecls_sound (andThen_ok h).1, checkStmts_sound (andThen_ok h).2⟩

theorem checkGraph_sound {T : Tables} {env : PkgEnv} {d : Syntax.Document} {g : CGraph}
    (h : checkGraph T env d g = .ok ()) : GraphOk T env d g := by
  have h1 := andThen_ok h
  have h2 := andThen_ok h1.2
  have h3 := andThen_ok h2.2
  exact ⟨checkNames_sound h1.1, checkBorrows_sound h2.1, checkArgsS_sound h3.1, checkTargetsS_sound h3.2⟩

/-- **Elaboration with validation is sound**: its graph is the one `ElabDoc` relates to
the document (against the registry with aliases expanded), and the document and the
graph pass every validation relation. -/
theorem elabDocV_sound {T : Tables} {env : PkgEnv} {d : Syntax.Document} {g : CGraph}
    (h : elabDocV T env d = .ok g) :
    ElabDoc env.expand d g ∧ DocOk d ∧ GraphOk T env.expand d g := by
  cases hd : checkDoc d with
  | error e => exact absurd h (by simp [elabDocV, hd])
  | ok u =>
    cases he : elabDocA env d with
    | error e => exact absurd h (by simp [elabDocV, hd, he])
    | ok g' =>
      cases hg : checkGraph T env.expand d g' with
      | error e => exact absurd h (by simp [elabDocV, hd, he, hg])
      | ok v =>
        have e : g' = g := by simpa [elabDocV, hd, he, hg] using h
        rw [← e]
        exact ⟨elabDocA_iff.1 he, checkDoc_sound hd, checkGraph_sound hg⟩

end Valid

end Silmaril.Wasm.Wac
