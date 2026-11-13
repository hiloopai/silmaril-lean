module

public import Silmaril.Proofs.Wasm.Wac.Text.Scan

/-!
# WAC text: the lexer reads every layout back

`lexAux_renderWith`: laying out well-formed tokens with doc comments and any nonempty
whitespace after each token lexes back to the tokens.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

theorem lexAux_ws (ds : Docs) {c : Char} (hc : isWs c = true) (r : List Char) :
    lexAux ds (c :: r) = lexAux ds r := by
  simp only [isWs, Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with (((h | h) | h) | h) | h <;> subst h <;> rw [lexAux.eq_def] <;> simp [isWs]

theorem lexAux_wsList (ds : Docs) : ∀ (ws : List Char) (r : List Char), ws.all isWs = true →
    lexAux ds (ws ++ r) = lexAux ds r
  | [], _, _ => rfl
  | c :: ws, r, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, lexAux_ws ds h.1, lexAux_wsList ds ws r h.2]

theorem word_start {c : Char} (hc : c = '%' ∨ isLetter c = true) :
    c ≠ '/' ∧ c ≠ '.' ∧ c ≠ '-' ∧ c ≠ '"' ∧ isWs c = false := by
  rcases hc with rfl | h
  · decide
  · have hw : isWs c = false := by
      cases hw : isWs c
      · rfl
      · exact absurd h (by simp [(ws_not hw).1])
    refine ⟨?_, ?_, ?_, ?_, hw⟩ <;> intro he <;> subst he <;> revert h <;> decide

theorem lexAux_word (ds : Docs) {c : Char} {r w r1 : List Char} (hc : c = '%' ∨ isLetter c = true)
    (hid : idRaw (c :: r) = some (w, r1)) :
    lexAux ds (c :: r) =
      if (sepIds ':' r1).1 = [] then (⟨ds, wordTok w⟩ :: ·) <$> lexAux [] r1
      else (⟨ds, nameTok w (sepIds ':' r1).1 (sepIds '/' (sepIds ':' r1).2).1
          (atVer (sepIds '/' (sepIds ':' r1).2).2).1⟩ :: ·) <$>
        lexAux [] (atVer (sepIds '/' (sepIds ':' r1).2).2).2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := word_start hc
  have h6 : (c = '%' ∨ isLetter c = true) = True := eq_true hc
  rw [lexAux.eq_def]
  split
  all_goals first | (simp_all; done) | skip
  rename_i c' r' _ _ _ _ _ heq
  obtain ⟨rfl, rfl⟩ := List.cons.inj heq
  simp only [h5, Bool.false_eq_true, ↓reduceIte, h6]
  split
  · simp_all
  · rename_i w' r1' hid'
    rw [hid] at hid'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hid')
    rfl

theorem takeLine_nl {l : List Char} (h : '\n' ∉ l) (r : List Char) :
    takeLine (l ++ '\n' :: r) = (l, r) := by
  induction l with
  | nil => simp [takeLine]
  | cons x l ih =>
    have hx : x ≠ '\n' := fun e => h (by simp [e])
    have ih' := ih (fun e => h (by simp [e]))
    rw [List.cons_append, takeLine.eq_def]
    split <;> simp_all

theorem trimU_cons_ws {c : Char} (hc : isWsU c = true) (l : List Char) :
    trimU (c :: l) = trimU l := by
  simp [trimU, hc]

theorem lexAux_doc (ds : Docs) {d : String} (hd : docOk d = true) (r : List Char) :
    lexAux ds (docStr d ++ r) = lexAux (ds ++ [d]) r := by
  have hn : '\n' ∉ d.toList := by simp [docOk] at hd; exact hd.1.1
  have ht : trimU d.toList = d.toList := by simp [docOk] at hd; exact hd.1.2
  have hl := takeLine_nl (l := '/' :: ' ' :: d.toList) (by simp [hn]) r
  have hdoc : lineDoc ('/' :: ' ' :: d.toList) = some d := by
    simp [lineDoc, trimU_cons_ws (c := ' ') (by decide), ht]
  simp only [docStr, List.cons_append, List.append_assoc]
  rw [lexAux.eq_def]
  simp only [List.cons_append] at hl
  simp [hl, hdoc]

theorem spanL_all (p : Char → Bool) : ∀ l : List Char, (∀ x ∈ l, p x = true) → spanL p l = (l, [])
  | [], _ => rfl
  | x :: l, h => by
    simp [spanL, h x (by simp), spanL_all p l (fun y hy => h y (by simp [hy]))]

/-- A word followed by whitespace: `w` is one identifier (`idRaw w = some (w, [])`). -/
theorem lexAux_word_ws (ds : Docs) {w : List Char} {c : Char} (r : List Char)
    (hc : isWs c = true) (hw : idRaw w = some (w, [])) (hne : w ≠ [])
    (h0 : ∀ x l, w = x :: l → x = '%' ∨ isLetter x = true) :
    lexAux ds (w ++ c :: r) = (⟨ds, wordTok w⟩ :: ·) <$> lexAux [] (c :: r) := by
  obtain ⟨x, l, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hid : idRaw (x :: (l ++ c :: r)) = some (x :: l, c :: r) := by
    have := idRaw_append_ws (IdStop.of_ws hc) r (x :: l); rw [hw] at this; simpa using this
  have hs : sepIds ':' (c :: r) = ([], c :: r) := sepIds_cons_ne (ws_not hc).2.2.2.2.2.2.1 r
  rw [List.cons_append, lexAux_word ds (h0 x l rfl) hid, hs]
  rfl

theorem lexAux_sym (ds : Docs) {c0 c : Char} (h0 : symChars.contains c0 = true)
    (hc : isWs c = true) (r : List Char) :
    lexAux ds (c0 :: c :: r) = (⟨ds, .sym c0⟩ :: ·) <$> lexAux [] (c :: r) := by
  have hcs : c ≠ '/' ∧ c ≠ '*' ∧ c ≠ '.' := by
    obtain ⟨-, -, -, -, -, -, -, h1, -, h2, -, -, h3⟩ := ws_not hc; exact ⟨h1, h3, h2⟩
  simp only [symChars, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
    beq_iff_eq] at h0
  rcases h0 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    rw [lexAux.eq_def] <;> split <;> (try simp only [List.cons.injEq] at *) <;>
    (try obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›) <;> simp_all [isWs, isLetter, isLower, isUpper, symChars]

theorem idOk_spec {s : String} (h : idOk s = true) :
    ∃ x l, s.toList = x :: l ∧ isLetter x = true ∧ idRaw s.toList = some (s.toList, []) ∧
      idBody s.toList = some (s.toList, []) := by
  unfold idOk at h
  split at h
  · rename_i w hb
    have hs := idBody_split hb
    simp only [List.append_nil] at hs
    match hl : s.toList, hb with
    | [], hb => simp [idBody] at hb
    | x :: l, hb =>
      have hx : isLetter x = true := by
        cases hx : isLetter x
        · simp [idBody, hx] at hb
        · rfl
      have hr : idRaw (x :: l) = idBody (x :: l) := by
        rw [idRaw.eq_def]; split <;> simp_all [isLetter, isLower, isUpper]
      refine ⟨x, l, rfl, hx, ?_, ?_⟩
      · rw [hr, hb, hs, hl]
      · rw [hb, hs, hl]
  · simp at h

theorem kw_spec (k : Kw) : idOk k.name = true ∧ kwOf? k.name = some k := by
  cases k <;> exact ⟨by decide +kernel, by decide +kernel⟩

theorem wordTok_plain {s : String} (h : idOk s = true) (hk : kwOf? s = none) :
    wordTok s.toList = .id s := by
  obtain ⟨x, l, hl, hx, -, -⟩ := idOk_spec h
  have hx' : x ≠ '%' := by intro e; subst e; revert hx; decide
  rw [hl, wordTok.eq_def]
  split
  · simp_all
  · rw [← hl]; simp [hk]

theorem lexAux_id (ds : Docs) {s : String} (h : idOk s = true) {c : Char} (hc : isWs c = true)
    (r : List Char) :
    lexAux ds ((Tok.id s).chars ++ c :: r) = (⟨ds, .id s⟩ :: ·) <$> lexAux [] (c :: r) := by
  obtain ⟨x, l, hl, hx, hid, hb⟩ := idOk_spec h
  cases hk : kwOf? s with
  | none =>
    have := lexAux_word_ws ds r hc hid (by simp [hl]) (fun y m e => by
      rw [hl] at e; obtain ⟨rfl, rfl⟩ := List.cons.inj e; exact .inr hx)
    simp [Tok.chars, hk, this, wordTok_plain h hk]
  | some k =>
    have hid' : idRaw ('%' :: s.toList) = some ('%' :: s.toList, []) := by simp [idRaw, hb]
    have := lexAux_word_ws ds r hc hid' (by simp) (fun y m e => by
      obtain ⟨rfl, rfl⟩ := List.cons.inj e; exact .inl rfl)
    rw [List.cons_append] at this
    simp [Tok.chars, hk, this, wordTok]

theorem lexAux_kw (ds : Docs) (k : Kw) {c : Char} (hc : isWs c = true) (r : List Char) :
    lexAux ds ((Tok.kw k).chars ++ c :: r) = (⟨ds, .kw k⟩ :: ·) <$> lexAux [] (c :: r) := by
  obtain ⟨hok, hkw⟩ := kw_spec k
  obtain ⟨x, l, hl, hx, hid, -⟩ := idOk_spec hok
  have := lexAux_word_ws ds r hc hid (by simp [hl]) (fun y m e => by
      rw [hl] at e; obtain ⟨rfl, rfl⟩ := List.cons.inj e; exact .inr hx)
  have hw : wordTok k.name.toList = .kw k := by
    have hx' : x ≠ '%' := by intro e; subst e; revert hx; decide
    rw [hl, wordTok.eq_def]
    split
    · simp_all
    · rw [← hl]; simp [hkw]
  simp [Tok.chars, this, hw]

theorem lexAux_arrow (ds : Docs) (r : List Char) :
    lexAux ds (Tok.arrow.chars ++ r) = (⟨ds, .arrow⟩ :: ·) <$> lexAux [] r := by
  rw [Tok.chars, lexAux.eq_def]; simp

theorem lexAux_ellipsis (ds : Docs) (r : List Char) :
    lexAux ds (Tok.ellipsis.chars ++ r) = (⟨ds, .ellipsis⟩ :: ·) <$> lexAux [] r := by
  rw [Tok.chars, lexAux.eq_def]; simp

theorem lexAux_str (ds : Docs) {s : String} (h : strOk s = true) (r : List Char) :
    lexAux ds ((Tok.str s).chars ++ r) = (⟨ds, .str s⟩ :: ·) <$> lexAux [] r := by
  have hq : ∀ x ∈ s.toList, (x != '"') = true := by
    simp [strOk] at h; intro x hx; simp only [bne_iff_ne, ne_eq]; intro e; exact h.1 (e ▸ hx)
  have hs : spanL (· != '"') (s.toList ++ '"' :: r) = (s.toList, '"' :: r) := by
    rw [spanL_append_stop _ (by decide) r, spanL_all _ _ hq]; rfl
  simp only [Tok.chars, List.cons_append, List.append_assoc]
  rw [lexAux.eq_def]
  simp only [List.nil_append]
  split
  · rename_i r' heq
    rw [hs] at heq
    obtain rfl := (List.cons.inj heq).2
    simp [hs]
  · rename_i hne
    rw [hs] at hne
    exact absurd rfl (hne r)

/-- `sepIds` takes everything of a list that starts with `sep` and has a nonempty scan. -/
theorem sepIds_head {sep : Char} {r1 : List Char} (hne : (sepIds sep r1).1 ≠ []) :
    ∃ r1', r1 = sep :: r1' := by
  cases r1 with
  | nil => simp [sepIds] at hne
  | cons y r1' =>
    by_cases hy : y = sep
    · exact ⟨r1', by rw [hy]⟩
    · rw [sepIds_cons_ne hy] at hne; exact absurd rfl hne

/-- The identifier before a `:` is one identifier on its own. -/
theorem idRaw_before_colon {w r1' : List Char}
    (hid : idRaw (w ++ ':' :: r1') = some (w, ':' :: r1')) : idRaw w = some (w, []) := by
  have := idRaw_append_ws idStop_colon r1' w
  rw [hid] at this
  cases hw : idRaw w with
  | none => simp [hw] at this
  | some p =>
    rw [hw] at this
    obtain ⟨p1, p2⟩ := p
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
    have h2 : p2 = [] := by simpa using this.2
    rw [← this.1, h2]

/-- An identifier starts with `%` or a letter. -/
theorem idRaw_start {x : Char} {wl : List Char} (hw : idRaw (x :: wl) = some (x :: wl, [])) :
    x = '%' ∨ isLetter x = true := by
  cases hx' : isLetter x
  · by_cases e : x = '%'
    · exact .inl e
    · exfalso
      have : idRaw (x :: wl) = idBody (x :: wl) := by rw [idRaw.eq_def]; split <;> simp_all
      rw [this] at hw; simp [idBody, hx'] at hw
  · exact .inr rfl

theorem name_scan_of {n : String} {w r1 : List Char} (hid : idRaw n.toList = some (w, r1))
    (hne : (sepIds ':' r1).1 ≠ []) (hnil : (sepIds ':' r1).2 = []) :
    ∃ x w r1, n.toList = x :: (w ++ r1).tail ∧
    w ++ r1 = n.toList ∧ r1 ≠ [] ∧ (x = '%' ∨ isLetter x = true) ∧
    ∀ (d : Char) (X : List Char), IdStop d → d ≠ ':' →
      idRaw (n.toList ++ d :: X) = some (w, r1 ++ d :: X) ∧
      sepIds ':' (r1 ++ d :: X) = (r1, d :: X) := by
  have hsplit : w ++ r1 = n.toList := idRaw_split hid
  have hs : (sepIds ':' r1).1 = r1 := by
    have := sepIds_split ':' (r1.length + 1) r1 (by omega); rwa [hnil, List.append_nil] at this
  obtain ⟨r1', rfl⟩ := sepIds_head hne
  have hw : idRaw w = some (w, []) := idRaw_before_colon (hsplit ▸ hid)
  obtain ⟨x, wl, rfl⟩ : ∃ x wl, w = x :: wl := by
    cases w with
    | nil => simp [idRaw, idBody] at hw
    | cons x wl => exact ⟨x, wl, rfl⟩
  refine ⟨x, x :: wl, ':' :: r1', by rw [← hsplit]; rfl, hsplit, by simp, idRaw_start hw, ?_⟩
  intro d X hd hdc
  have e := idRaw_append_ws idStop_colon (r1' ++ d :: X) (x :: wl)
  rw [hw] at e
  exact ⟨by rw [← hsplit]; simpa using e,
    by rw [sepIds_append_ws hd X ':' hdc _ _ (Nat.lt_succ_self _), hnil]; simp [hs]⟩

/-- A package name scans as its first identifier `w` and the rest `r1 = (:id)+`, whatever
stop character follows. -/
theorem name_scan {n : String} (h : nameOk n = true) : ∃ x w r1, n.toList = x :: (w ++ r1).tail ∧
    w ++ r1 = n.toList ∧ r1 ≠ [] ∧ (x = '%' ∨ isLetter x = true) ∧
    ∀ (d : Char) (X : List Char), IdStop d → d ≠ ':' →
      idRaw (n.toList ++ d :: X) = some (w, r1 ++ d :: X) ∧
      sepIds ':' (r1 ++ d :: X) = (r1, d :: X) := by
  unfold nameOk at h
  split at h
  · rename_i w r1 hid
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.isEmpty_iff] at h
    exact name_scan_of hid h.1 h.2
  · simp at h

theorem atVer_none_of {c : Char} (hc : c ≠ '@') (r : List Char) : atVer (c :: r) = (none, c :: r) := by
  rw [atVer.eq_def]; split <;> simp_all

theorem atVer_ver {v : String} (h : verLexOk v = true) {c : Char} (hc : isWs c = true)
    (r : List Char) : atVer ('@' :: v.toList ++ c :: r) = (some v.toList, c :: r) := by
  have h' : atVer ('@' :: v.toList) = (some v.toList, []) := by simpa [verLexOk] using h
  rw [atVer_append_ws hc, h']; rfl

/-- The lexer at a package name or path: `n`, then a stop character `d` other than `:`. -/
theorem lexAux_name (ds : Docs) {n : String} (h : nameOk n = true) (d : Char) (X : List Char)
    (hd : IdStop d) (hdc : d ≠ ':') :
    lexAux ds (n.toList ++ d :: X) =
      (⟨ds, if (sepIds '/' (d :: X)).1 = [] then
          .pname n ((atVer (sepIds '/' (d :: X)).2).1.map String.ofList)
        else .ppath n (String.ofList (sepIds '/' (d :: X)).1.tail)
          ((atVer (sepIds '/' (d :: X)).2).1.map String.ofList)⟩ :: ·) <$>
        lexAux [] (atVer (sepIds '/' (d :: X)).2).2 := by
  obtain ⟨x, w, r1, hx, hsplit, hne, hx0, hscan⟩ := name_scan h
  obtain ⟨hid, hsep⟩ := hscan d X hd hdc
  have hid' : idRaw (x :: ((w ++ r1).tail ++ d :: X)) = some (w, r1 ++ d :: X) := by
    rw [← List.cons_append, ← hx]; exact hid
  rw [hx, List.cons_append, lexAux_word ds hx0 hid', hsep]
  simp only [nameTok, hne, ↓reduceIte, hsplit, String.ofList_toList]

theorem lexAux_pname (ds : Docs) {n : String} {v : Option String}
    (h : (Tok.pname n v).ok = true) {c : Char} (hc : isWs c = true) (r : List Char) :
    lexAux ds ((Tok.pname n v).chars ++ c :: r) = (⟨ds, .pname n v⟩ :: ·) <$> lexAux [] (c :: r) := by
  simp only [Tok.ok, Bool.and_eq_true] at h
  obtain ⟨hn, hv⟩ := h
  have hcs := ws_not hc
  cases v with
  | none =>
    have := lexAux_name ds hn c r (IdStop.of_ws hc) hcs.2.2.2.2.2.2.1
    rw [sepIds_cons_ne hcs.2.2.2.2.2.2.2.1, atVer_none_of hcs.2.2.2.2.2.2.2.2.1] at this
    simpa [Tok.chars] using this
  | some v =>
    have := lexAux_name ds hn '@' (v.toList ++ c :: r) idStop_at (by decide)
    rw [sepIds_cons_ne (by decide), ← List.cons_append, atVer_ver hv hc] at this
    simpa [Tok.chars] using this

theorem segs_scan {sg : String} (hsg : segsOk sg = true) (d : Char) (X : List Char)
    (hd : IdStop d) (hdd : d ≠ '/') :
    sepIds '/' ('/' :: sg.toList ++ d :: X) = ('/' :: sg.toList, d :: X) := by
  simp only [segsOk, Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true',
    List.isEmpty_eq_false_iff] at hsg
  have hsplit := sepIds_split '/' (sg.toList.length + 2) ('/' :: sg.toList) (by simp)
  rw [hsg.1, List.append_nil] at hsplit
  rw [sepIds_append_ws hd X '/' hdd _ _ (Nat.lt_succ_self _), hsg.1, hsplit]; rfl

theorem lexAux_ppath (ds : Docs) {n sg : String} {v : Option String}
    (h : (Tok.ppath n sg v).ok = true) {c : Char} (hc : isWs c = true) (r : List Char) :
    lexAux ds ((Tok.ppath n sg v).chars ++ c :: r) =
      (⟨ds, .ppath n sg v⟩ :: ·) <$> lexAux [] (c :: r) := by
  simp only [Tok.ok, Bool.and_eq_true] at h
  obtain ⟨⟨hn, hsg⟩, hv⟩ := h
  have hcs := ws_not hc
  cases v with
  | none =>
    have := lexAux_name ds hn '/' (sg.toList ++ c :: r) idStop_slash (by decide)
    rw [← List.cons_append, segs_scan hsg c r (IdStop.of_ws hc) hcs.2.2.2.2.2.2.2.1,
      atVer_none_of hcs.2.2.2.2.2.2.2.2.1] at this
    simpa [Tok.chars] using this
  | some v =>
    have := lexAux_name ds hn '/' (sg.toList ++ '@' :: (v.toList ++ c :: r)) idStop_slash (by decide)
    rw [← List.cons_append, segs_scan hsg '@' _ idStop_at (by decide), ← List.cons_append,
      atVer_ver hv hc] at this
    simpa [Tok.chars] using this

theorem lexAux_tok (ds : Docs) {t : Tok} (ht : t.ok = true) {c : Char} (hc : isWs c = true)
    (r : List Char) : lexAux ds (t.chars ++ c :: r) = (⟨ds, t⟩ :: ·) <$> lexAux [] (c :: r) := by
  cases t with
  | id s => exact lexAux_id ds ht hc r
  | kw k => exact lexAux_kw ds k hc r
  | str s => exact lexAux_str ds ht _
  | pname n v => exact lexAux_pname ds ht hc r
  | ppath n sg v => exact lexAux_ppath ds ht hc r
  | sym c0 => exact lexAux_sym ds ht hc r
  | arrow => exact lexAux_arrow ds _
  | ellipsis => exact lexAux_ellipsis ds _

theorem lexAux_docs (w : List Char) (hw : w.all isWs = true) :
    ∀ (ds docs : Docs) (R : List Char), docsOk docs = true →
      lexAux ds (docs.flatMap (fun d => docStr d ++ w) ++ R) = lexAux (ds ++ docs) R
  | ds, [], R, _ => by simp
  | ds, d :: docs, R, h => by
    simp only [docsOk, List.all_cons, Bool.and_eq_true] at h
    simp only [List.flatMap_cons, List.append_assoc]
    rw [lexAux_doc ds h.1, lexAux_wsList _ w _ hw, lexAux_docs w hw (ds ++ [d]) docs R h.2]
    simp

/-- Every layout of well-formed tokens with docs lexes back to them: each token is
followed by nonempty whitespace (`sep`), doc lines by any whitespace (`ind`). -/
theorem lexAux_renderWith (sep ind : Nat → List Char)
    (hsep : ∀ i, ∃ c s, sep i = c :: s ∧ isWs c = true ∧ s.all isWs = true)
    (hind : ∀ i, (ind i).all isWs = true) :
    ∀ (ts : List ATok) (i : Nat), (∀ a ∈ ts, a.tok.ok = true ∧ docsOk a.docs = true) →
      lexAux [] (renderWith sep ind i ts) = some ts
  | [], _, _ => by simp [renderWith, lexAux]
  | a :: ts, i, h => by
    obtain ⟨c, s, hs, hc, hss⟩ := hsep i
    have ha := h a (by simp)
    have ih := lexAux_renderWith sep ind hsep hind ts (i + 1) (fun x hx => h x (by simp [hx]))
    rw [renderWith, List.append_assoc, List.append_assoc, lexAux_docs _ (hind i) [] _ _ ha.2,
      hs, List.cons_append, lexAux_tok _ ha.1 hc, lexAux_ws _ hc, lexAux_wsList _ _ _ hss, ih]
    rfl

end Silmaril.Wasm.Wac.Text
