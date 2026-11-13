module

public import Silmaril.Net.Http1.Message.Defs

/-!
# HTTP/1.1 message heads: round trips and validity

* `*_G` (introduction): the serializer's output for a valid element is in the grammar;
* `*_valid` (elimination): what the grammar relates is valid;
* `fieldLine_G_iff`: the field-line grammar is RFC 9112 §5's
  `field-name ":" OWS field-value OWS CRLF`, with the value the octets between the colon and
  the line end without surrounding whitespace;
* `fields_G_iff`: the depth-indexed field-section grammar is the depth-free `FieldSection`,
  for sections of fewer than `k` lines;
* `parseRequestHead_encode`, `parseResponseHead_encode` (round trips) and
  `parseRequestHead_sound`, `parseResponseHead_sound`.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse
open Silmaril.Parse.ByteParse.Grammar (lit then_ lit_G then_G bind_G map_G expect_G)

/-! ## The head grammars are lawful -/

namespace Grammar

instance lawful_digit : digit.Lawful := by unfold digit; grammar_lawful
instance lawful_version : version.Lawful := by unfold version; grammar_lawful
instance lawful_code : code.Lawful := by unfold code; grammar_lawful
instance lawful_requestLine : requestLine.Lawful := by unfold requestLine; grammar_lawful
instance lawful_statusLine : statusLine.Lawful := by unfold statusLine; grammar_lawful
instance lawful_fieldLine : fieldLine.Lawful := by unfold fieldLine; grammar_lawful
instance lawful_endFields : endFields.Lawful := by unfold endFields; grammar_lawful

instance lawful_fields : ∀ k, (fields k).Lawful
  | 0 => inferInstanceAs (Silmaril.Parse.ByteParse.Grammar.fail : Grammar (List FieldLine)).Lawful
  | k + 1 => by
    have := lawful_fields k
    unfold fields
    grammar_lawful

instance lawful_requestHead (k : Nat) : (requestHead k).Lawful := by
  unfold requestHead; grammar_lawful

instance lawful_responseHead (k : Nat) : (responseHead k).Lawful := by
  unfold responseHead; grammar_lawful

end Grammar

/-! ## Octet facts -/

theorem digitByte_ok : ∀ d < 10, isDigit (digitByte d) = true ∧ digitVal (digitByte d) = d := by
  decide

theorem digitVal_lt : ∀ c : UInt8, isDigit c = true → digitVal c < 10 := by decide

theorem isTchar_SP : isTchar SP = false := rfl
theorem isTchar_COLON : isTchar COLON = false := rfl
theorem isVchar_SP : isVchar SP = false := rfl
theorem isFieldByte_CR : isFieldByte CR = false := rfl
theorem isFieldByte_SP : isFieldByte SP = true := rfl
theorem isWS_SP : isWS SP = true := rfl

theorem isFieldByte_of_tchar : ∀ c : UInt8, isTchar c = true → isFieldByte c = true := by decide

/-! ## Trimming optional whitespace -/

theorem dropWhile_of_head {p : UInt8 → Bool} {l : Bytes} (h : ∀ b ∈ l.head?, p b = false) :
    l.dropWhile p = l := by
  cases l with
  | nil => rfl
  | cons x xs => simp [h x rfl]

/-- A field value with one leading `SP` trims back to itself. -/
theorem trimOWS_SP {v : Bytes} (hv : IsFieldValue v) : trimOWS (SP :: v) = v := by
  have h1 : (SP :: v).dropWhile isWS = v := by
    rw [List.dropWhile_cons_of_pos isWS_SP]; exact dropWhile_of_head hv.2.1
  have h2 : v.reverse.dropWhile isWS = v.reverse := by
    apply dropWhile_of_head
    rw [List.head?_reverse]; exact hv.2.2
  simp only [trimOWS, h1, h2, List.reverse_reverse]

theorem head?_dropWhile_not {p : UInt8 → Bool} :
    ∀ (l : Bytes), ∀ b ∈ (l.dropWhile p).head?, p b = false
  | [], _, h => by simp at h
  | x :: xs, b, h => by
    by_cases hx : p x = true
    · rw [List.dropWhile_cons_of_pos hx] at h; exact head?_dropWhile_not xs b h
    · have hx' : p x = false := by simpa using hx
      rw [List.dropWhile_cons_of_neg (by simp [hx'])] at h
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at h
      exact h ▸ hx'

/-- Trimming field octets gives a field value (RFC 9110 §5.5). -/
theorem trimOWS_valid {raw : Bytes} (h : ∀ b ∈ raw, isFieldByte b = true) :
    IsFieldValue (trimOWS raw) := by
  have hsuf1 : (raw.dropWhile isWS).IsSuffix raw := List.dropWhile_suffix isWS
  have hsuf2 : ((raw.dropWhile isWS).reverse.dropWhile isWS).IsSuffix
      (raw.dropWhile isWS).reverse := List.dropWhile_suffix isWS
  have hpre : (trimOWS raw).IsPrefix (raw.dropWhile isWS) := by
    simpa [trimOWS] using List.reverse_prefix.2 hsuf2
  refine ⟨fun b hb => h b (hsuf1.subset (hpre.subset hb)), ?_, ?_⟩
  · intro b hb
    obtain ⟨t, ht⟩ := hpre
    have hb' : b ∈ (raw.dropWhile isWS).head? := by
      rw [← ht]; cases htr : trimOWS raw with
      | nil => rw [htr] at hb; simp at hb
      | cons x xs => rw [htr] at hb; simpa using hb
    exact head?_dropWhile_not raw b hb'
  · intro b hb
    have hb' : b ∈ ((raw.dropWhile isWS).reverse.dropWhile isWS).head? := by
      simpa [trimOWS, List.getLast?_reverse] using hb
    exact head?_dropWhile_not _ b hb'

/-! ## Introduction: serializer output is in the grammar -/

namespace Grammar

theorem digit_G {d : Nat} (hd : d < 10) : digit.G [digitByte d] d :=
  ⟨digitByte d, rfl, by simp [(digitByte_ok d hd).1, (digitByte_ok d hd).2]⟩

theorem version_G {v : Version} (hv : v.Valid) : version.G (encVersion v) v := by
  obtain ⟨ma, mi⟩ := v
  have e : encVersion ⟨ma, mi⟩ = httpSlash ++ ([digitByte ma] ++ ([0x2E] ++ [digitByte mi])) := rfl
  rw [e]; unfold version
  exact then_G (lit_G httpSlash) (bind_G (digit_G hv.1) (then_G (expect_G "." 0x2E)
    (map_G (digit_G hv.2))))

theorem code_G {c : Nat} (hc : c < 1000) : code.G (encCode c) c := by
  have e : 100 * (c / 100) + 10 * (c / 10 % 10) + c % 10 = c := by omega
  have e' : encCode c = [digitByte (c / 100)] ++ ([digitByte (c / 10 % 10)] ++ [digitByte (c % 10)]) :=
    rfl
  rw [e']; unfold code
  conv => rhs; rw [← e]
  exact bind_G (digit_G (by omega)) (bind_G (digit_G (by omega)) (map_G (digit_G (by omega))))

theorem requestLine_G {r : RequestLine} (hr : r.Valid) : requestLine.G (encRequestLine r) r := by
  obtain ⟨m, t, v⟩ := r
  obtain ⟨⟨hm, hmt⟩, ht, htv, hv⟩ := hr
  have e : encRequestLine ⟨m, t, v⟩ = (m ++ [SP]) ++ ((t ++ [SP]) ++ (encVersion v ++ CRLF)) := by
    simp [encRequestLine]
  rw [e]; unfold requestLine
  exact bind_G (delim_G hmt isTchar_SP fun _ => hm) (bind_G (delim_G htv isVchar_SP fun _ => ht)
    (bind_G (version_G hv) (map_G (lit_G CRLF))))

theorem statusLine_G {s : StatusLine} (hs : s.Valid) : statusLine.G (encStatusLine s) s := by
  obtain ⟨v, c, r⟩ := s
  obtain ⟨hv, hc, hr⟩ := hs
  have e : encStatusLine ⟨v, c, r⟩ = encVersion v ++ ([SP] ++ (encCode c ++ ([SP] ++
      ((r ++ [CR]) ++ [LF])))) := by
    simp [encStatusLine]
  rw [e]; unfold statusLine
  exact bind_G (version_G hv) (then_G (expect_G "SP" SP) (bind_G (code_G hc)
    (then_G (expect_G "SP" SP) (bind_G (delim_G hr isFieldByte_CR (by simp))
      (map_G (expect_G "LF" LF))))))

theorem fieldLine_G {f : FieldLine} (hf : f.Valid) : fieldLine.G (encField f) f := by
  obtain ⟨n, v⟩ := f
  obtain ⟨⟨hn, hnt⟩, hv⟩ := hf
  have hraw : ∀ b ∈ SP :: v, isFieldByte b = true := by
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · rfl
    · exact hv.1 b hb
  have e : encField ⟨n, v⟩ = (n ++ [COLON]) ++ ((SP :: v ++ [CR]) ++ [LF]) := by
    simp [encField]
  have hv' : (⟨n, v⟩ : FieldLine) = ⟨n, trimOWS (SP :: v)⟩ := by rw [trimOWS_SP hv]
  rw [e, hv']; unfold fieldLine
  exact bind_G (delim_G hnt isTchar_COLON fun _ => hn) (bind_G
    (delim_G hraw isFieldByte_CR (by simp)) (map_G (expect_G "LF" LF)))

theorem endFields_G : endFields.G CRLF [] := map_G (lit_G CRLF)

theorem fields_G : ∀ {fs : List FieldLine} {k : Nat}, (∀ f ∈ fs, f.Valid) → fs.length < k →
    (fields k).G (encFields fs) fs
  | [], k + 1, _, _ => .inl endFields_G
  | f :: fs, k + 1, hv, hk =>
    .inr (bind_G (fieldLine_G (hv f (by simp)))
      (map_G (fields_G (fun g hg => hv g (by simp [hg])) (by simp at hk; omega))))

theorem requestHead_G {h : RequestHead} {k : Nat} (hv : h.Valid) (hk : h.fields.length < k) :
    (requestHead k).G (encRequestHead h) h :=
  bind_G (requestLine_G hv.1) (map_G (f := fun fs => (⟨h.line, fs⟩ : RequestHead)) (fields_G hv.2 hk))

theorem responseHead_G {h : ResponseHead} {k : Nat} (hv : h.Valid) (hk : h.fields.length < k) :
    (responseHead k).G (encResponseHead h) h :=
  bind_G (statusLine_G hv.1) (map_G (f := fun fs => (⟨h.line, fs⟩ : ResponseHead)) (fields_G hv.2 hk))

end Grammar

/-! ## Elimination: what the grammars relate is valid -/

namespace Grammar

theorem digit_lt {l : Bytes} {d : Nat} (h : digit.G l d) : d < 10 := by
  obtain ⟨c, -, hc⟩ := h
  have hc' : (if isDigit c then some (digitVal c) else none) = some d := hc
  split at hc'
  · next hd => cases hc'; exact digitVal_lt c hd
  · cases hc'

theorem version_valid {l : Bytes} {v : Version} (h : version.G l v) : v.Valid := by
  obtain ⟨_, _, _, -, -, _, _, ma, -, hma, _, _, _, -, -, mi, hmi, rfl⟩ := h
  exact ⟨digit_lt hma, digit_lt hmi⟩

theorem code_lt {l : Bytes} {c : Nat} (h : code.G l c) : c < 1000 := by
  obtain ⟨_, _, a, -, ha, _, _, b, -, hb, c', hc, rfl⟩ := h
  have := digit_lt ha; have := digit_lt hb; have := digit_lt hc
  show 100 * a + 10 * b + c' < 1000
  omega

theorem requestLine_valid {l : Bytes} {r : RequestLine} (h : requestLine.G l r) : r.Valid := by
  obtain ⟨_, _, m, -, hm, _, _, t, -, ht, _, _, v, -, hv, _, -, rfl⟩ := h
  obtain ⟨-, hm1, -, hm2⟩ := delim_G_iff.1 hm
  obtain ⟨-, ht1, -, ht2⟩ := delim_G_iff.1 ht
  exact ⟨⟨hm2 rfl, hm1⟩, ht2 rfl, ht1, version_valid hv⟩

theorem statusLine_valid {l : Bytes} {s : StatusLine} (h : statusLine.G l s) : s.Valid := by
  obtain ⟨_, _, v, -, hv, _, _, _, -, -, _, _, c, -, hc, _, _, _, -, -, _, _, r, -, hr, _, -, rfl⟩
    := h
  exact ⟨version_valid hv, code_lt hc, (delim_G_iff.1 hr).2.1⟩

/-- The field-line grammar is RFC 9112 §5's `field-name ":" OWS field-value OWS` followed by
`CRLF`: a token, a colon, field octets, `CRLF`; the value is the octets without surrounding
whitespace. -/
theorem fieldLine_G_iff {l : Bytes} {f : FieldLine} : fieldLine.G l f ↔
    ∃ raw, l = f.name ++ [COLON] ++ raw ++ CRLF ∧ IsToken f.name ∧
      (∀ b ∈ raw, isFieldByte b = true) ∧ f.value = trimOWS raw := by
  constructor
  · rintro ⟨_, _, n, rfl, hn, _, l₄, raw, rfl, hraw, _, hl₄, rfl⟩
    obtain ⟨rfl, hn1, -, hn2⟩ := delim_G_iff.1 hn
    obtain ⟨rfl, hr1, -, -⟩ := delim_G_iff.1 hraw
    have hl₄' : l₄ = [LF] := hl₄
    subst hl₄'
    exact ⟨raw, by simp, ⟨hn2 rfl, hn1⟩, hr1, rfl⟩
  · rintro ⟨raw, rfl, ⟨hn, hnt⟩, hraw, hv⟩
    obtain ⟨n, v⟩ := f
    have e : n ++ [COLON] ++ raw ++ CRLF = (n ++ [COLON]) ++ ((raw ++ [CR]) ++ [LF]) := by simp
    have hf : (⟨n, v⟩ : FieldLine) = ⟨n, trimOWS raw⟩ := by rw [← hv]
    rw [e, hf]
    exact bind_G (delim_G hnt isTchar_COLON fun _ => hn) (bind_G
      (delim_G hraw isFieldByte_CR (by simp)) (map_G (expect_G "LF" LF)))

theorem fieldLine_valid {l : Bytes} {f : FieldLine} (h : fieldLine.G l f) : f.Valid := by
  obtain ⟨raw, -, hn, hraw, hv⟩ := fieldLine_G_iff.1 h
  exact ⟨hn, hv ▸ trimOWS_valid hraw⟩

/-- The depth bound of the field-section grammar only bounds the number of lines. -/
theorem fields_G_iff : ∀ {k : Nat} {l : Bytes} {fs : List FieldLine},
    (fields k).G l fs ↔ FieldSection l fs ∧ fs.length < k
  | 0, _, _ => ⟨fun h => h.elim, fun h => absurd h.2 (Nat.not_lt_zero _)⟩
  | k + 1, l, fs => by
    constructor
    · rintro (⟨u, hl, rfl⟩ | ⟨l₁, l₂, f, rfl, hf, fs', hfs, rfl⟩)
      · exact ⟨lit_G_eq hl, by simp⟩
      · obtain ⟨h1, h2⟩ := fields_G_iff.1 hfs
        exact ⟨⟨l₁, l₂, rfl, hf, h1⟩, by simp; omega⟩
    · rintro ⟨hs, hk⟩
      cases fs with
      | nil => exact .inl ⟨(), by rw [show l = CRLF from hs]; exact lit_G CRLF, rfl⟩
      | cons f fs =>
        obtain ⟨l₁, l₂, rfl, hf, hs'⟩ := hs
        exact .inr (bind_G hf (map_G (fields_G_iff.2 ⟨hs', by simp at hk; omega⟩)))

theorem fieldSection_valid : ∀ {l : Bytes} {fs : List FieldLine}, FieldSection l fs →
    ∀ f ∈ fs, f.Valid
  | _, [], _ => by simp
  | _, _ :: _, ⟨_, _, _, hf, hs⟩ => by
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact fieldLine_valid hf
    · exact fieldSection_valid hs g hg

theorem requestHead_valid {k : Nat} {l : Bytes} {h : RequestHead} (hg : (requestHead k).G l h) :
    h.Valid := by
  obtain ⟨_, _, r, -, hr, fs, hfs, rfl⟩ := hg
  exact ⟨requestLine_valid hr, fieldSection_valid (fields_G_iff.1 hfs).1⟩

theorem responseHead_valid {k : Nat} {l : Bytes} {h : ResponseHead}
    (hg : (responseHead k).G l h) : h.Valid := by
  obtain ⟨_, _, s, -, hs, fs, hfs, rfl⟩ := hg
  exact ⟨statusLine_valid hs, fieldSection_valid (fields_G_iff.1 hfs).1⟩

end Grammar

/-! ## The parsers -/

theorem length_encFields_gt : ∀ fs : List FieldLine, fs.length < (encFields fs).length
  | [] => by simp [encFields]
  | f :: fs => by
    have := length_encFields_gt fs
    simp [encFields, encField]; omega

/-- Round trip: a valid request head is read back from its serialization, whatever follows
it (the body), and the parser stops exactly at its end. -/
theorem parseRequestHead_encode {h : RequestHead} (hv : h.Valid) (rest : Bytes) :
    parseRequestHead ⟨(encRequestHead h ++ rest).toArray⟩ = .ok h (encRequestHead h).length := by
  have hk : h.fields.length < (encRequestHead h ++ rest).length + 1 := by
    have := length_encFields_gt h.fields
    simp [encRequestHead]; omega
  unfold parseRequestHead
  rw [size_ofList]
  exact (Grammar.requestHead _).complete.run_append (Grammar.requestHead_G hv hk) rest

theorem parseResponseHead_encode {h : ResponseHead} (hv : h.Valid) (rest : Bytes) :
    parseResponseHead ⟨(encResponseHead h ++ rest).toArray⟩ = .ok h (encResponseHead h).length := by
  have hk : h.fields.length < (encResponseHead h ++ rest).length + 1 := by
    have := length_encFields_gt h.fields
    simp [encResponseHead]; omega
  unfold parseResponseHead
  rw [size_ofList]
  exact (Grammar.responseHead _).complete.run_append (Grammar.responseHead_G hv hk) rest

/-- Soundness: a parsed request head is valid, and the octets it consumed are a request line
followed by a field section (RFC 9112 §2.1), so serializing it again gives a canonical form
that parses back to it (`parseRequestHead_encode`). -/
theorem parseRequestHead_sound {bs : ByteArray} {h : RequestHead} {j : Nat}
    (hp : parseRequestHead bs = .ok h j) :
    j ≤ bs.size ∧ h.Valid ∧ ∃ l₁ l₂, seg bs 0 j = l₁ ++ l₂ ∧ Grammar.requestLine.G l₁ h.line ∧
      FieldSection l₂ h.fields := by
  obtain ⟨-, hj, hg⟩ := (Grammar.requestHead (bs.size + 1)).sound (Nat.zero_le _) le_rfl hp
  refine ⟨hj, Grammar.requestHead_valid hg, ?_⟩
  obtain ⟨l₁, l₂, r, e, hr, fs, hfs, rfl⟩ := hg
  exact ⟨l₁, l₂, e, hr, (Grammar.fields_G_iff.1 hfs).1⟩

theorem parseResponseHead_sound {bs : ByteArray} {h : ResponseHead} {j : Nat}
    (hp : parseResponseHead bs = .ok h j) :
    j ≤ bs.size ∧ h.Valid ∧ ∃ l₁ l₂, seg bs 0 j = l₁ ++ l₂ ∧ Grammar.statusLine.G l₁ h.line ∧
      FieldSection l₂ h.fields := by
  obtain ⟨-, hj, hg⟩ := (Grammar.responseHead (bs.size + 1)).sound (Nat.zero_le _) le_rfl hp
  refine ⟨hj, Grammar.responseHead_valid hg, ?_⟩
  obtain ⟨l₁, l₂, s, e, hs, fs, hfs, rfl⟩ := hg
  exact ⟨l₁, l₂, e, hs, (Grammar.fields_G_iff.1 hfs).1⟩

/-- Unambiguity: the head encoded by a byte string is unique. -/
theorem requestHead_functional {k : Nat} {l : Bytes} {h h' : RequestHead}
    (hg : (Grammar.requestHead k).G l h) (hg' : (Grammar.requestHead k).G l h') : h = h' :=
  (Grammar.requestHead k).functional hg hg'

end Silmaril.Net.Http1
