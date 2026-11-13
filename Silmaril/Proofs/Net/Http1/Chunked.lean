module

public import Silmaril.Net.Http1.Chunked.Defs
public import Silmaril.Net.Http1.Message.Thms

/-!
# The chunked transfer coding: round trip, validity, rechunking

* hexadecimal numerals: `hexValue_hexDigits`, `hexDigits_hex`;
* `Grammar.chunkLine_G`, `Grammar.chunkData_G`, `Grammar.chunked_G` (introduction) and
  `Grammar.chunked_valid` (elimination);
* `parseChunked_encode`: round trip after any prefix (the head) and before any suffix;
* `parseChunked_sound`: a decoded body is valid;
* rechunking: `content_ofPieces`, `parseChunked_ofPieces`, `parseChunked_rechunk`.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse
open Silmaril.Parse.ByteParse.Grammar (lit then_ lit_G then_G bind_G map_G expect_G filterMap_G)

/-! ## The chunked-body grammars are lawful -/

namespace Grammar

instance lawful_chunkExtTail (c : UInt8) : (chunkExtTail c).Lawful := by
  unfold chunkExtTail; grammar_lawful

instance lawful_chunkLine : chunkLine.Lawful := by unfold chunkLine; grammar_lawful

instance lawful_chunkData (n : Nat) : (chunkData n).Lawful := by unfold chunkData; grammar_lawful

instance lawful_chunked : ∀ k, (chunked k).Lawful
  | 0 => inferInstanceAs (Silmaril.Parse.ByteParse.Grammar.fail : Grammar Chunked).Lawful
  | k + 1 => by
    have := lawful_chunked k
    unfold chunked
    grammar_lawful

end Grammar

/-! ## Hexadecimal numerals -/

theorem hexByte_ok : ∀ d < 16, isHexDig (hexByte d) = true ∧ hexVal (hexByte d) = d := by decide

theorem hexValue_append (l : Bytes) (x : UInt8) : hexValue (l ++ [x]) = 16 * hexValue l + hexVal x := by
  simp [hexValue, List.foldl_append]

theorem hexValue_hexDigits (n : Nat) : hexValue (hexDigits n) = n := by
  fun_induction hexDigits n with
  | case1 n hn => simp [hexValue, (hexByte_ok n hn).2]
  | case2 n hn ih =>
    rw [hexValue_append, ih, (hexByte_ok (n % 16) (Nat.mod_lt _ (by omega))).2]
    omega

theorem hexDigits_hex (n : Nat) : ∀ b ∈ hexDigits n, isHexDig b = true := by
  fun_induction hexDigits n with
  | case1 n hn => intro b hb; simp at hb; exact hb ▸ (hexByte_ok n hn).1
  | case2 n hn ih =>
    intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact ih b hb
    · simp at hb; exact hb ▸ (hexByte_ok (n % 16) (Nat.mod_lt _ (by omega))).1

theorem hexDigits_ne_nil (n : Nat) : hexDigits n ≠ [] := by
  fun_induction hexDigits n <;> simp

theorem isHexDig_CR : isHexDig CR = false := rfl

theorem not_hex_of_extHead : ∀ c : UInt8, (c == SEMI || isWS c) = true → isHexDig c = false := by
  decide

/-! ## Extensions -/

theorem isChunkExt_fieldBytes {e : Bytes} (h : isChunkExt e = true) : ∀ b ∈ e, isFieldByte b = true := by
  simp only [isChunkExt, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1

theorem isChunkExt_head {c : UInt8} {r : Bytes} (h : isChunkExt (c :: r) = true) :
    (c == SEMI || isWS c) = true := by
  simp only [isChunkExt, Bool.and_eq_true, List.head?_cons, Option.all_some] at h
  exact h.1.2

namespace Grammar

theorem chunkExtTail_G {c : UInt8} {r : Bytes} (h : isChunkExt (c :: r) = true) :
    (chunkExtTail c).G (r ++ [CR] ++ [LF]) (c :: r) := by
  have hc : c ≠ CR := by
    intro e; subst e; exact absurd (isChunkExt_head h) (by decide)
  have hr : ∀ b ∈ r, isFieldByte b = true := fun b hb =>
    isChunkExt_fieldBytes h b (List.mem_cons_of_mem c hb)
  unfold chunkExtTail
  simp only [hc, ↓reduceIte]
  exact filterMap_G (bind_G (delim_G hr isFieldByte_CR (by simp)) (map_G (expect_G "LF" LF)))
    (by simp [h])

theorem chunkLine_G (n : Nat) {e : Bytes} (he : isChunkExt e = true) :
    chunkLine.G (encChunkLine n e) (n, e) := by
  unfold chunkLine
  cases e with
  | nil =>
    have h := bind_G (Grammar.runThen_G (hexDigits_hex n) isHexDig_CR)
      (h := fun r => if r.1 = [] then Silmaril.Parse.ByteParse.Grammar.fail
        else (chunkExtTail r.2).map fun e => (hexValue r.1, e))
      (by
        simp only [hexDigits_ne_nil, ↓reduceIte]
        exact map_G (f := fun e => (hexValue (hexDigits n), e))
          (show (chunkExtTail CR).G [LF] [] by unfold chunkExtTail; exact map_G (expect_G "LF" LF)))
    simpa [encChunkLine, hexValue_hexDigits] using h
  | cons c r =>
    have h := bind_G (Grammar.runThen_G (hexDigits_hex n) (not_hex_of_extHead c (isChunkExt_head he)))
      (h := fun r => if r.1 = [] then Silmaril.Parse.ByteParse.Grammar.fail
        else (chunkExtTail r.2).map fun e => (hexValue r.1, e))
      (by
        simp only [hexDigits_ne_nil, ↓reduceIte]
        exact map_G (f := fun e => (hexValue (hexDigits n), e)) (chunkExtTail_G he))
    simpa [encChunkLine, hexValue_hexDigits] using h

theorem chunkData_G (d : Bytes) : (chunkData d.length).G (d ++ CRLF) d := by
  unfold chunkData
  exact bind_G (b := d) (a := ⟨d.toArray⟩) ⟨by simp, by simp⟩ (map_G (lit_G CRLF))

end Grammar

theorem encChunked_nil (e : Bytes) (tr : List FieldLine) :
    encChunked ⟨[], e, tr⟩ = encChunkLine 0 e ++ encFields tr := by
  simp [encChunked]

theorem encChunked_cons (x : Chunk) (xs : List Chunk) (e : Bytes) (tr : List FieldLine) :
    encChunked ⟨x :: xs, e, tr⟩ =
      encChunkLine x.data.length x.ext ++ ((x.data ++ CRLF) ++ encChunked ⟨xs, e, tr⟩) := by
  simp [encChunked, encChunk]

namespace Grammar

theorem chunked_G : ∀ {cs : List Chunk} {e : Bytes} {tr : List FieldLine} {k : Nat},
    (⟨cs, e, tr⟩ : Chunked).Valid → cs.length + tr.length < k →
      (chunked k).G (encChunked ⟨cs, e, tr⟩) ⟨cs, e, tr⟩
  | [], e, tr, k + 1, hv, hk => by
    rw [encChunked_nil]; unfold chunked
    refine bind_G (chunkLine_G 0 hv.2.1) ?_
    simp only [↓reduceIte]
    exact map_G (f := fun tr => (⟨[], e, tr⟩ : Chunked)) (fields_G hv.2.2 (by simp at hk; omega))
  | x :: xs, e, tr, k + 1, hv, hk => by
    have hx : x.Valid := hv.1 x (by simp)
    have hrest : (⟨xs, e, tr⟩ : Chunked).Valid :=
      ⟨fun y hy => hv.1 y (by simp [hy]), hv.2.1, hv.2.2⟩
    have hlen : x.data.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hx.1
    rw [encChunked_cons]; unfold chunked
    refine bind_G (chunkLine_G _ hx.2) ?_
    simp only [hlen, ↓reduceIte]
    exact bind_G (chunkData_G x.data) (map_G (f := fun c => { c with chunks := ⟨x.ext, x.data⟩ :: c.chunks })
      (chunked_G hrest (by simp at hk; omega)))

/-! ## Elimination -/

theorem chunkExtTail_valid {c : UInt8} {l e : Bytes} (h : (chunkExtTail c).G l e) :
    isChunkExt e = true := by
  unfold chunkExtTail at h
  split at h
  · obtain ⟨_, -, rfl⟩ := h; rfl
  · obtain ⟨e', -, he⟩ := h
    have he' : (if isChunkExt e' then some e' else none) = some e := he
    split at he'
    · next hc => cases he'; exact hc
    · cases he'

theorem chunkLine_valid {l : Bytes} {r : Nat × Bytes} (h : chunkLine.G l r) : isChunkExt r.2 = true := by
  obtain ⟨_, _, ds, -, -, h₂⟩ := h
  have h₂' : (if ds.1 = [] then Silmaril.Parse.ByteParse.Grammar.fail
      else (chunkExtTail ds.2).map fun e => (hexValue ds.1, e)).G _ r := h₂
  split at h₂'
  · exact h₂'.elim
  · obtain ⟨e, he, rfl⟩ := h₂'
    exact chunkExtTail_valid he

theorem chunkData_length {n : Nat} {l d : Bytes} (h : (chunkData n).G l d) : d.length = n := by
  obtain ⟨_, _, a, -, ⟨rfl, hn⟩, _, -, rfl⟩ := h
  exact hn

theorem chunked_valid : ∀ {k : Nat} {l : Bytes} {c : Chunked}, (chunked k).G l c → c.Valid
  | 0, _, _, h => h.elim
  | k + 1, _, c, ⟨_, _, r, _, hr, h₂⟩ => by
    have he : isChunkExt r.2 = true := chunkLine_valid hr
    have h₂' : (if r.1 = 0 then (fields (k + 1)).map fun tr => (⟨[], r.2, tr⟩ : Chunked)
        else (chunkData r.1).bind fun d => (chunked k).map fun c =>
          { c with chunks := ⟨r.2, d⟩ :: c.chunks }).G _ c := h₂
    split at h₂'
    · obtain ⟨tr, htr, rfl⟩ := h₂'
      exact ⟨by simp, he, fieldSection_valid (fields_G_iff.1 htr).1⟩
    · next hn =>
      obtain ⟨_, _, d, -, hd, c', hc', rfl⟩ := h₂'
      have hv : c'.Valid := chunked_valid hc'
      have hd' : d ≠ [] := by
        intro e; have := chunkData_length hd; rw [e] at this; exact hn this.symm
      refine ⟨?_, hv.2.1, hv.2.2⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hd', he⟩
      · exact hv.1 x hx

end Grammar

/-! ## The parser -/

theorem seg_middle (pre l rest : Bytes) :
    seg ⟨(pre ++ l ++ rest).toArray⟩ pre.length (pre.length + l.length) = l := by
  simp [seg, List.extract]

theorem length_encChunked_gt (c : Chunked) :
    c.chunks.length + c.trailers.length < (encChunked c).length := by
  obtain ⟨cs, e, tr⟩ := c
  induction cs with
  | nil =>
    have := length_encFields_gt tr
    simp [encChunked_nil, encChunkLine]; omega
  | cons x xs ih =>
    rw [encChunked_cons]
    simp only [List.length_append, List.length_cons] at ih ⊢
    omega

/-- Round trip: a valid chunked body is decoded back after any prefix (the head) and
before any suffix (the next message), and the decoder stops at its end. -/
theorem parseChunked_encode {c : Chunked} (hv : c.Valid) (pre rest : Bytes) :
    parseChunked ⟨(pre ++ encChunked c ++ rest).toArray⟩ pre.length =
      .ok c (pre.length + (encChunked c).length) := by
  have hk : c.chunks.length + c.trailers.length < (pre ++ encChunked c ++ rest).length + 1 := by
    have := length_encChunked_gt c
    simp; omega
  have hg : (Grammar.chunked ((pre ++ encChunked c ++ rest).length + 1)).G (encChunked c) c := by
    obtain ⟨cs, e, tr⟩ := c
    exact Grammar.chunked_G hv hk
  unfold parseChunked
  rw [size_ofList]
  exact (Grammar.chunked _).complete hg (by simp) (by rw [size_ofList]) (seg_middle pre _ rest)

/-- Soundness: a decoded chunked body is valid, and the decoder moved forward inside the
input. -/
theorem parseChunked_sound {bs : ByteArray} {i j : Nat} {c : Chunked} (hi : i ≤ bs.size)
    (hp : parseChunked bs i = .ok c j) :
    i ≤ j ∧ j ≤ bs.size ∧ c.Valid ∧ (Grammar.chunked (bs.size + 1)).G (seg bs i j) c := by
  obtain ⟨h1, h2, hg⟩ := (Grammar.chunked (bs.size + 1)).sound hi le_rfl hp
  exact ⟨h1, h2, Grammar.chunked_valid hg, hg⟩

/-! ## Rechunking -/

theorem flatten_filter_ne_nil (cs : List Bytes) :
    (cs.filter fun x => decide (x ≠ [])).flatten = cs.flatten := by
  induction cs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x = []
    · subst hx
      rw [List.filter_cons_of_neg (by simp), ih]; rfl
    · rw [List.filter_cons_of_pos (by simpa using hx), List.flatten_cons, ih, List.flatten_cons]

theorem content_ofPieces (cs : List Bytes) (tr : List FieldLine) :
    (Chunked.ofPieces cs tr).content = cs.flatten := by
  have h : (Chunked.ofPieces cs tr).content = (cs.filter fun x => decide (x ≠ [])).flatten := by
    simp [Chunked.ofPieces, Chunked.content, Function.comp_def]
  rw [h, flatten_filter_ne_nil]

theorem ofPieces_valid (cs : List Bytes) {tr : List FieldLine} (htr : ∀ f ∈ tr, f.Valid) :
    (Chunked.ofPieces cs tr).Valid := by
  refine ⟨?_, rfl, htr⟩
  intro x hx
  simp only [Chunked.ofPieces, List.mem_map, List.mem_filter] at hx
  obtain ⟨d, ⟨-, hd⟩, rfl⟩ := hx
  exact ⟨by simpa using hd, rfl⟩

/-- Any chunking `cs` of a byte string (empty pieces are dropped) is encoded so that decoding
gives that byte string back as the content. -/
theorem parseChunked_ofPieces (cs : List Bytes) {tr : List FieldLine} (htr : ∀ f ∈ tr, f.Valid)
    (pre rest : Bytes) :
    ∃ j, parseChunked ⟨(pre ++ encChunked (Chunked.ofPieces cs tr) ++ rest).toArray⟩ pre.length =
      .ok (Chunked.ofPieces cs tr) j ∧ (Chunked.ofPieces cs tr).content = cs.flatten :=
  ⟨_, parseChunked_encode (ofPieces_valid cs htr) pre rest, content_ofPieces cs tr⟩

/-- Rechunking: two chunkings with the same concatenation (`ChunkEq` of
`docs/projects/wasm-wasi.md`) decode to the same content and trailers, whatever their chunk
boundaries and extensions. -/
theorem parseChunked_rechunk {c d : Chunked} (hc : c.Valid) (hd : d.Valid)
    (heq : (c.chunks.map Chunk.data).flatten = (d.chunks.map Chunk.data).flatten)
    (htr : c.trailers = d.trailers) (pre rest pre' rest' : Bytes) :
    ∃ c' d' j j', parseChunked ⟨(pre ++ encChunked c ++ rest).toArray⟩ pre.length = .ok c' j ∧
      parseChunked ⟨(pre' ++ encChunked d ++ rest').toArray⟩ pre'.length = .ok d' j' ∧
      c'.content = d'.content ∧ c'.trailers = d'.trailers :=
  ⟨c, d, _, _, parseChunked_encode hc pre rest, parseChunked_encode hd pre' rest', heq, htr⟩

end Silmaril.Net.Http1
