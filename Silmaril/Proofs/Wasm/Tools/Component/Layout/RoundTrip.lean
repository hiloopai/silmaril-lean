module

public import Silmaril.Wasm.Tools.Component.Layout.Defs
public import Silmaril.Wasm.Component.Wat.Sexp.Thms
public import Silmaril.Wasm.Tools.Component.Wat.Thms

/-!
# wasmprinter's layout keeps the tokens; the fast renderer is the renderer

* `tk_lay`: without names, the tokens of `lay E m s` are the tokens of `s`, for every mode
  (comments carry no token);
* `wf_lay`: the layout keeps the atoms;
* `lex_render`: the lexer reads `render d l` as the tokens of `l`, whatever the line breaks
  and comments;
* `renderF_eq`: `renderF d acc l = (acc ++ render d l, render d l contains a new line)`;
* `read_printW`: `Wat.read (printW c) = some (Wat.norm c)`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Layout

open Silmaril.Wasm.Component.Wat (Sexp Tok)
open Silmaril.Wasm.Component.Wat.Sexp (lex toks WF WFL AtomOk Stop spaces quote escByte)

/-! ## Tokens -/

mutual
/-- The tokens of a laid-out tree (comments have none). -/
def tk : L → List Tok
  | .atom a => [.atom a]
  | .str b => [.str b]
  | .cmt _ => []
  | .list xs => .lp :: (tkL xs ++ [.rp])

/-- The tokens of items. -/
def tkL : List (Bool × L) → List Tok
  | [] => []
  | (_, x) :: xs => tk x ++ tkL xs
end

theorem tkL_append (a b : List (Bool × L)) : tkL (a ++ b) = tkL a ++ tkL b := by
  induction a with
  | nil => rfl
  | cons p a ih => obtain ⟨_, x⟩ := p; simp [tkL, ih]

theorem ref_off {E : Ctx} (h : E.on = false) (up : Nat) (k a : String) : E.ref up k a = a := by
  simp [Ctx.ref, h]

theorem binder_off {E : Ctx} (h : E.on = false) (k : String) (n : Nat) : E.binder k n = [] := by
  simp [Ctx.binder, h]

theorem skipItem_off {E : Ctx} (h : E.on = false) (x : Sexp) : skipItem E x = false := by
  simp [skipItem, h]

theorem prodItem_off {E : Ctx} (h : E.on = false) (x : Sexp) : prodItem E x = none := by
  simp [prodItem, h]

theorem enter_on (E : Ctx) (n : Names) : (E.enter n).on = E.on := rfl

theorem cmtAt_off {E : Ctx} (h : E.on = false) (c : Option (Nat × String × Nat)) (i : Nat) :
    cmtAt E c i = match c with
      | some (p, _, n) => if p = i then [(false, .cmt n)] else []
      | none => [] := by
  unfold cmtAt
  split
  · simp [binder_off h]
  · rfl

theorem tkL_cmtAt {E : Ctx} (h : E.on = false) (c : Option (Nat × String × Nat)) (i : Nat) :
    tkL (cmtAt E c i) = [] := by
  rw [cmtAt_off h]
  split
  · split <;> simp [tkL, tk]
  · rfl

mutual
theorem tk_lay {E : Ctx} (h : E.on = false) : ∀ (m : Mode) (s : Sexp), tk (lay E m s) = toks s
  | m, .atom _ => by cases m <;> simp [lay, tk, toks, ref_off h, h]
  | m, .str _ => by cases m <;> simp [lay, tk, toks]
  | .plain, .list xs | .ref _ _, .list xs | .outer, .list xs => by
    simp only [lay, tk, toks, tkL_layIdx h]
  | .vt, .list xs => by simp only [lay, tk, toks, tkL_layIdx h]
  | .item c b cs, .list xs => by simp only [lay, tk, toks, tkL_layIdx h]
  | .scope k hd, .list xs => by
    simp only [lay, tk, toks, tkL_layHead (show (E.enter {}).on = false from h)]
  | .compDef n, .list xs => by simp only [lay, tk, toks, tkL_layHeadC h]
  | .recG hd n, .list xs => by simp only [lay, tk, toks, tkL_layRec h]

theorem tkL_layIdx {E : Ctx} (h : E.on = false) (c : Option (Nat × String × Nat)) (b : Nat)
    (cs : List (Nat × Mode)) :
    ∀ (i : Nat) (xs : List Sexp), tkL (layIdx E c b cs i xs) = toks.toksL xs
  | i, [] => by simp only [layIdx, tkL_cmtAt h, toks.toksL]
  | i, x :: xs => by
    simp only [layIdx, tkL_append, tkL_cmtAt h, tkL, tk_lay h, tkL_layIdx h c b cs (i + 1) xs,
      toks.toksL, List.nil_append]

theorem tkL_layHead {E : Ctx} (h : E.on = false) (k : Scope) : ∀ (hd : Nat) (xs : List Sexp),
    tkL (layHead E k hd xs) = toks.toksL xs
  | _, [] => by simp only [layHead, tkL, toks.toksL]
  | 0, x :: xs => by simp only [layHead, tkL, tk_lay h, tkL_layScope h, toks.toksL]
  | hd + 1, x :: xs => by simp only [layHead, tkL, tk_lay h, tkL_layHead h k hd xs, toks.toksL]

theorem tkL_layScope {E : Ctx} (h : E.on = false) (k : Scope) : ∀ (st : St) (xs : List Sexp),
    tkL (layScope E k st xs) = toks.toksL xs
  | _, [] => by simp only [layScope, tkL, toks.toksL]
  | st, x :: xs => by
    simp only [layScope, skipItem_off h, prodItem_off h, Bool.false_eq_true, ite_false, tkL,
      tk_lay h, tkL_layScope h k _ xs, toks.toksL]

theorem tkL_layHeadC {E : Ctx} (h : E.on = false) (n : Nat) :
    ∀ (xs : List Sexp), tkL (layHeadC E n xs) = toks.toksL xs
  | [] => by simp only [layHeadC, tkL, toks.toksL]
  | x :: xs => by
    simp only [layHeadC, binder_off h, List.nil_append, tkL, tk, tk_lay h,
      tkL_layScope (show (E.enter (namesIn xs)).on = false from h), toks.toksL]

theorem tkL_layRec {E : Ctx} (h : E.on = false) (hd n : Nat) : ∀ (i : Nat) (xs : List Sexp),
    tkL (layRec E hd n i xs) = toks.toksL xs
  | _, [] => by simp only [layRec, tkL, toks.toksL]
  | i, x :: xs => by
    simp only [layRec]
    split <;> simp only [tkL, tk_lay h, tkL_layRec h hd n (i + 1) xs, toks.toksL]
end

/-! ## Well-formedness -/

mutual
/-- Every atom is printable. -/
def WFl : L → Prop
  | .atom a => AtomOk a
  | .str _ => True
  | .cmt _ => True
  | .list xs => WFls xs

/-- `WFl` of every item. -/
def WFls : List (Bool × L) → Prop
  | [] => True
  | (_, x) :: xs => WFl x ∧ WFls xs
end

theorem wfls_append {a b : List (Bool × L)} (ha : WFls a) (hb : WFls b) : WFls (a ++ b) := by
  induction a with
  | nil => simpa using hb
  | cons p a ih => obtain ⟨_, x⟩ := p; exact ⟨ha.1, ih ha.2⟩

theorem wfls_cmtAt {E : Ctx} (h : E.on = false) (c : Option (Nat × String × Nat)) (i : Nat) :
    WFls (cmtAt E c i) := by
  rw [cmtAt_off h]
  split
  · split
    · exact ⟨trivial, trivial⟩
    · trivial
  · trivial

mutual
theorem wf_lay {E : Ctx} (h : E.on = false) : ∀ (m : Mode) (s : Sexp), WF s → WFl (lay E m s)
  | m, .atom a, ha => by cases m <;> simpa [lay, WFl, ref_off h, h] using ha
  | m, .str _, _ => by cases m <;> simp [lay, WFl]
  | .plain, .list xs, hx | .ref _ _, .list xs, hx | .outer, .list xs, hx =>
    wfls_layIdx h none never [] 0 xs hx
  | .vt, .list xs, hx => wfls_layIdx h none never _ 0 xs hx
  | .item c b cs, .list xs, hx => wfls_layIdx h c b cs 0 xs hx
  | .scope k hd, .list xs, hx => wfls_layHead (show (E.enter {}).on = false from h) k hd xs hx
  | .compDef n, .list xs, hx => wfls_layHeadC h n xs hx
  | .recG hd n, .list xs, hx => wfls_layRec h hd n 0 xs hx

theorem wfls_layIdx {E : Ctx} (h : E.on = false) (c : Option (Nat × String × Nat)) (b : Nat)
    (cs : List (Nat × Mode)) :
    ∀ (i : Nat) (xs : List Sexp), WFL xs → WFls (layIdx E c b cs i xs)
  | i, [], _ => by simp only [layIdx]; exact wfls_cmtAt h c i
  | i, x :: xs, hx => by
    simp only [layIdx]
    exact wfls_append (wfls_cmtAt h c i) ⟨wf_lay h _ x hx.1, wfls_layIdx h c b cs (i + 1) xs hx.2⟩

theorem wfls_layHead {E : Ctx} (h : E.on = false) (k : Scope) : ∀ (hd : Nat) (xs : List Sexp),
    WFL xs → WFls (layHead E k hd xs)
  | _, [], _ => trivial
  | 0, x :: xs, hx => ⟨wf_lay h _ x hx.1, wfls_layScope h k _ xs hx.2⟩
  | hd + 1, x :: xs, hx => ⟨wf_lay h _ x hx.1, wfls_layHead h k hd xs hx.2⟩

theorem wfls_layScope {E : Ctx} (h : E.on = false) (k : Scope) : ∀ (st : St) (xs : List Sexp),
    WFL xs → WFls (layScope E k st xs)
  | _, [], _ => trivial
  | _, x :: xs, hx => by
    simp only [layScope, skipItem_off h, prodItem_off h, Bool.false_eq_true, ite_false]
    exact ⟨wf_lay h _ x hx.1, wfls_layScope h k _ xs hx.2⟩

theorem wfls_layHeadC {E : Ctx} (h : E.on = false) (n : Nat) :
    ∀ (xs : List Sexp), WFL xs → WFls (layHeadC E n xs)
  | [], _ => trivial
  | x :: xs, hx => by
    simp only [layHeadC, binder_off h, List.nil_append]
    exact ⟨wf_lay h _ x hx.1, trivial,
      wfls_layScope (show (E.enter (namesIn xs)).on = false from h) .comp [] xs hx.2⟩

theorem wfls_layRec {E : Ctx} (h : E.on = false) (hd n : Nat) : ∀ (i : Nat) (xs : List Sexp),
    WFL xs → WFls (layRec E hd n i xs)
  | _, [], _ => trivial
  | i, x :: xs, hx => by
    simp only [layRec]
    split
    · exact ⟨wf_lay h _ x hx.1, wfls_layRec h hd n (i + 1) xs hx.2⟩
    · exact ⟨wf_lay h _ x hx.1, wfls_layRec h hd n (i + 1) xs hx.2⟩
end

/-! ## The lexer on the rendered text -/

theorem digit_ne : ∀ j < 10, Char.ofNat (48 + j) ≠ ';' ∧ Char.ofNat (48 + j) ≠ '(' ∧
    Char.ofNat (48 + j) ≠ '\n' := by decide

theorem digits_ne (n : Nat) : ∀ c ∈ digits n, c ≠ ';' ∧ c ≠ '(' ∧ c ≠ '\n' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [digits]
    split
    · next h => simpa using digit_ne n h
    · next h =>
      intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact ih (n / 10) (by omega) c hc
      · exact digit_ne (n % 10) (Nat.mod_lt _ (by omega))

theorem skipBlock_digits (cs : List Char) : ∀ ds : List Char, (∀ c ∈ ds, c ≠ ';' ∧ c ≠ '(') →
    Sexp.skipBlock 0 (ds ++ ';' :: ')' :: cs) = some cs
  | [], _ => by simp [Sexp.skipBlock]
  | c :: ds, h => by
    have hc := h c (by simp)
    have ih := skipBlock_digits cs ds (fun c hc => h c (by simp [hc]))
    rw [List.cons_append, Sexp.skipBlock.eq_def]
    split <;> simp_all

theorem lex_cmt (n : Nat) (cs : List Char) :
    lex ('(' :: ';' :: (digits n ++ [';', ')']) ++ cs) = lex cs := by
  have hs := skipBlock_digits cs (digits n) (fun c hc => ⟨(digits_ne n c hc).1, (digits_ne n c hc).2.1⟩)
  simp only [List.cons_append, List.append_assoc, List.cons_append, List.nil_append] at hs ⊢
  rw [lex.eq_def]
  split
  all_goals (try subst_vars)
  all_goals (try simp_all)
  all_goals (try (split <;> simp_all))
  case h_4 => rename_i hx heq; exact absurd heq.symm (hx _)
  case h_7 => rename_i hx2 _ _ heq; exact absurd heq.1.symm hx2

theorem nl_sep (d : Nat) : nl d = [' '] ∨ ∃ k, nl d = '\n' :: spaces k := .inr ⟨_, rfl⟩

theorem render_head (d : Nat) (x : L) (h : WFl x) (r : List Char) :
    (render d x ++ r).head? ≠ some ';' := by
  cases x with
  | atom a =>
    obtain ⟨hne, hall⟩ := h
    simp only [render]
    cases hl : a.toList with
    | nil => exact absurd hl hne
    | cons c t =>
      have := (Sexp.idChar_ne (hall c (by simp [hl]))).1
      simpa using this
  | str b => simp [render, quote]
  | cmt n => simp [render]
  | list xs => simp [render]

theorem renderItems_head (d : Nat) (xs : List (Bool × L)) (h : WFls xs) (r : List Char)
    (hr : r.head? ≠ some ';') : (renderItems d true xs ++ r).head? ≠ some ';' := by
  match xs, h with
  | [], _ => simpa [renderItems] using hr
  | (b, x) :: xs, h =>
    simp only [renderItems, ite_true, List.nil_append, List.append_assoc]
    exact render_head d x h.1 _

theorem stop_renderItems (d : Nat) (xs : List (Bool × L)) (cs : List Char) (hs : Stop cs) :
    Stop (renderItems d false xs ++ cs) := by
  match xs with
  | [] => simpa [renderItems] using hs
  | (b, x) :: xs =>
    simp only [renderItems, Bool.false_eq_true, ite_false, List.append_assoc]
    split
    · simp [nl, Stop]
    · simp [Stop]

mutual
theorem lex_render (d : Nat) : ∀ (x : L) (cs : List Char), WFl x → Stop cs →
    lex (render d x ++ cs) = (lex cs).map (tk x ++ ·)
  | .atom a, cs, h, hs => by
    simp only [render, tk]
    rw [Sexp.lex_atom h hs]; rfl
  | .str b, cs, _, _ => by
    simp only [render, tk]
    rw [Sexp.lex_str]; rfl
  | .cmt n, cs, _, _ => by
    rw [render, lex_cmt]
    cases lex cs <;> simp [tk]
  | .list xs, cs, h, _ => by
    simp only [render, List.cons_append, List.append_assoc]
    have hclose : ∀ r : List Char, Stop r →
        lex ((if (renderItems (d + 1) true xs).contains '\n' then nl d else []) ++ r) = lex r ∧
        Stop ((if (renderItems (d + 1) true xs).contains '\n' then nl d else []) ++ r) := by
      intro r hr
      split
      · exact ⟨Sexp.lex_sep (nl_sep d), Sexp.stop_sep (nl_sep d)⟩
      · exact ⟨rfl, hr⟩
    have hst : Stop (')' :: cs) := by simp [Stop]
    simp only [List.nil_append]
    rw [Sexp.lex_lp (renderItems_head (d + 1) xs h _ (by split <;> simp [nl])),
      lex_renderItems (d + 1) true xs _ h (hclose _ hst).2, (hclose _ hst).1, Sexp.lex_rp]
    cases lex cs <;> simp [tk]

theorem lex_renderItems (d : Nat) : ∀ (first : Bool) (xs : List (Bool × L)) (cs : List Char),
    WFls xs → Stop cs → lex (renderItems d first xs ++ cs) = (lex cs).map (tkL xs ++ ·)
  | _, [], cs, _, _ => by simp [renderItems, tkL]
  | first, (b, x) :: xs, cs, h, hs => by
    simp only [renderItems, List.append_assoc]
    have hx := lex_render d x (renderItems d false xs ++ cs) h.1 (stop_renderItems d xs cs hs)
    have hxs := lex_renderItems d false xs cs h.2 hs
    have hsep : ∀ r : List Char,
        lex ((if first = true then [] else if b = true then nl d else [' ']) ++ r) = lex r := by
      intro r
      split
      · rfl
      · split
        · exact Sexp.lex_sep (nl_sep d)
        · exact Sexp.lex_sep (.inl rfl)
    rw [hsep, hx, hxs]
    cases lex cs <;> simp [tkL]
end

/-! ## The fast renderer -/

theorem push_eq (s : String) (c : Char) : s.push c = s ++ String.ofList [c] := by
  rw [String.push_eq_append, String.singleton_eq_ofList]

theorem spacesF_eq (acc : String) (n : Nat) : spacesF acc n = acc ++ String.ofList (spaces n) := by
  induction n generalizing acc with
  | zero => simp [spacesF, spaces]
  | succ n ih =>
    rw [spacesF, ih, push_eq, String.append_assoc, ← String.ofList_append]
    simp only [spaces, List.replicate_succ, List.singleton_append]

theorem nlF_eq (acc : String) (d : Nat) : nlF acc d = acc ++ String.ofList (nl d) := by
  rw [nlF, spacesF_eq, push_eq, String.append_assoc, ← String.ofList_append]
  rfl

theorem escF_eq (acc : String) (b : UInt8) : escF acc b = acc ++ String.ofList (escByte b) := by
  unfold escF escByte
  split
  · rw [push_eq]
  · simp only [push_eq, String.append_assoc, ← String.ofList_append]
    rfl

theorem foldl_escF (bs : List UInt8) : ∀ acc : String,
    bs.foldl escF acc = acc ++ String.ofList (bs.flatMap escByte) := by
  induction bs with
  | nil => intro acc; simp
  | cons b bs ih =>
    intro acc
    rw [List.foldl_cons, ih, escF_eq, String.append_assoc, ← String.ofList_append]
    simp [List.flatMap_cons]

theorem quoteF_eq (acc : String) (bs : List UInt8) :
    quoteF acc bs = acc ++ String.ofList (quote bs) := by
  rw [quoteF, foldl_escF, push_eq, push_eq]
  simp only [quote, String.append_assoc, ← String.ofList_append]
  simp

theorem escByte_no_nl (b : UInt8) : '\n' ∉ escByte b := by
  have h16 : b.toNat / 16 < 16 := by have := b.toNat_lt; omega
  have hhex : ∀ k < 16, Sexp.hexDigit k ≠ '\n' := by decide
  unfold escByte
  split
  · next h =>
    simp only [List.mem_singleton]
    intro heq
    have : (Char.ofNat b.toNat).toNat = b.toNat := by
      simp [Char.ofNat, Char.ofNatAux, Char.toNat,
        show b.toNat.isValidChar from Or.inl (by have := b.toNat_lt; omega)]
    rw [← heq] at this
    simp at this
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by decide, fun e => hhex _ h16 e.symm, fun e => hhex _ (Nat.mod_lt _ (by omega)) e.symm⟩

theorem quote_no_nl (bs : List UInt8) : '\n' ∉ quote bs := by
  simp only [quote, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.not_mem_nil, or_false, not_or, not_exists, not_and]
  exact ⟨by decide, fun b _ => escByte_no_nl b, by decide⟩

theorem digits_no_nl (n : Nat) : '\n' ∉ digits n := fun h => (digits_ne n _ h).2.2 rfl

theorem atom_no_nl {a : String} (h : AtomOk a) : '\n' ∉ a.toList := by
  intro hc
  have := (Sexp.idChar_ne (h.2 _ hc)).2.2.2.2
  revert this
  decide

mutual
theorem renderF_eq (d : Nat) : ∀ (acc : String) (x : L), WFl x →
    renderF d acc x = (acc ++ String.ofList (render d x), (render d x).contains '\n')
  | acc, .atom a, h => by simp [renderF, render, atom_no_nl h]
  | acc, .str b, _ => by simp [renderF, render, quoteF_eq, quote_no_nl]
  | acc, .cmt n, _ => by
    simp only [renderF, render, push_eq, String.append_assoc, ← String.ofList_append]
    simp [digits_no_nl]
  | acc, .list xs, h => by
    simp only [renderF]
    rw [renderItemsF_eq (d + 1) true (acc.push '(') xs h]
    simp only [render]
    split
    · next hc =>
      simp only [hc, nlF_eq, push_eq, String.append_assoc, ← String.ofList_append]
      simp only [List.contains_iff_mem] at hc
      simp [hc]
    · next hc =>
      simp only [Bool.not_eq_true] at hc
      simp only [hc, push_eq, String.append_assoc, ← String.ofList_append]
      have hc' : '\n' ∉ renderItems (d + 1) true xs := by simpa using hc
      simp [hc']

theorem renderItemsF_eq (d : Nat) : ∀ (first : Bool) (acc : String) (xs : List (Bool × L)),
    WFls xs → renderItemsF d first acc xs =
      (acc ++ String.ofList (renderItems d first xs), (renderItems d first xs).contains '\n')
  | _, acc, [], _ => by simp [renderItemsF, renderItems]
  | first, acc, (b, x) :: xs, h => by
    have hsep : (if first = true then acc else if b = true then nlF acc d else acc.push ' ') =
        acc ++ String.ofList (if first = true then [] else if b = true then nl d else [' ']) := by
      split
      · simp
      · split
        · exact nlF_eq acc d
        · exact push_eq acc ' '
    simp only [renderItemsF, hsep, renderF_eq d _ x h.1, renderItemsF_eq d false _ xs h.2,
      renderItems, String.append_assoc, ← String.ofList_append, List.contains_append]
    refine Prod.ext (by simp) ?_
    simp only
    cases first <;> cases b <;> simp [nl]
end

/-! ## Entry points -/

theorem printW_eq (c : Silmaril.Wasm.Component.BinaryP3.Ast) : printW c = printWSpec c := by
  have hw : WFl (layComponent c) := wf_lay rfl _ _ (Wat.wf_toSexp c)
  rw [printW, renderF_eq 0 "" _ hw, printWSpec, push_eq, String.ofList_append]
  simp

theorem read_printWSpec (c : Silmaril.Wasm.Component.BinaryP3.Ast) :
    Sexp.read (printWSpec c) = some [Wat.toSexp c] := by
  have hw : WFl (layComponent c) := wf_lay rfl _ _ (Wat.wf_toSexp c)
  unfold Sexp.read printWSpec
  rw [String.toList_ofList, lex_render 0 _ ['\n'] hw (by simp [Stop])]
  have h1 : lex ['\n'] = some [] := by
    rw [Sexp.lex_space_cons [] (by decide)]
    rw [lex.eq_def]
  rw [h1]
  simp only [Option.map_some, List.append_nil, Option.bind_eq_bind, Option.bind_some]
  rw [layComponent, tk_lay rfl, ← Sexp.toksL_singleton, Sexp.parseTop_toksL]

/-- **Round trip**: the reader reads the text in wasmprinter's layout back to the normal form. -/
theorem read_printW (c : Silmaril.Wasm.Component.BinaryP3.Ast) :
    Wat.read (printW c) = some (Wat.norm c) := by
  rw [printW_eq, Wat.read, read_printWSpec]
  exact Wat.ofSexp_toSexp c

end Silmaril.Wasm.Tools.Component.Layout
