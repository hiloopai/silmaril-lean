module

public import Silmaril.Formats.Compression.DeflateSpec.Defs
public import Silmaril.Formats.Compression.Deflate.Defs
public import Silmaril.Raw.Formats.Compression.Bits.BitstreamLemmas
public import Silmaril.Raw.Formats.Compression.Deflate.HuffmanLemmas
public import Silmaril.Raw.Formats.Compression.Deflate.RoundTrip

/-!
# Bridge lemmas between `DeflateSpec` and the decoder

The bit-level view of the decoder's `LSBReader` (`RR`), and the canonical
Huffman codes of `DeflateSpec.Code.ofLengths` against the decoder's tables
(`TSound`, `TComplete`).
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.DeflateSpec

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Deflate

/-! ### Bits -/

theorem fieldBits_eq (v n : Nat) : DeflateSpec.fieldBits v n = natBits v n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [DeflateSpec.fieldBits, natBits, ih]

theorem codeBits_eq (c n : Nat) : DeflateSpec.codeBits c n = msbBits c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [DeflateSpec.codeBits, msbBits, ih]

theorem inputBits_eq (bs : List UInt8) : DeflateSpec.inputBits bs = bytesBits bs := by
  simp [DeflateSpec.inputBits, bytesBits, fieldBits_eq]

/-- The reader `r` will produce the bits `bs`, and holds less than a byte. -/
def RR (r : LSBReader) (bs : List Bool) : Prop := r.Rep bs ∧ r.count < 8

theorem readBit_none_of_rep_nil {r : LSBReader} (h : r.Rep []) : r.readBit = none := by
  obtain ⟨_, h⟩ := h
  have h1 := congrArg List.length h
  simp only [List.length_append, length_natBits, length_bytesBits, List.length_nil] at h1
  rcases r with ⟨buf, cnt, input, tr⟩
  simp only at h1
  have hc : cnt = 0 := by omega
  have hi : input = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hc hi
  simp [LSBReader.readBit, LSBReader.refill]

theorem RR.readBit {r r' : LSBReader} {bs : List Bool} {b : Bool} (h : RR r bs)
    (hb : r.readBit = some (b, r')) : ∃ rest, bs = b :: rest ∧ RR r' rest := by
  cases bs with
  | nil => rw [readBit_none_of_rep_nil h.1] at hb; cases hb
  | cons b0 bs0 =>
    obtain ⟨r0, h0, hr0⟩ := h.1.readBit
    rw [h0] at hb
    obtain ⟨rfl, rfl⟩ : b0 = b ∧ r0 = r' := by simpa using hb
    exact ⟨bs0, rfl, hr0, by
      have := LSBReader.readBit_count h.2 h0; rw [this]; exact Nat.mod_lt _ (by decide)⟩

theorem RR.readBit_cons {r : LSBReader} {b : Bool} {bs : List Bool} (h : RR r (b :: bs)) :
    ∃ r', r.readBit = some (b, r') ∧ RR r' bs := by
  obtain ⟨r', h1, h2⟩ := h.1.readBit
  exact ⟨r', h1, h2, by
    have := LSBReader.readBit_count h.2 h1; rw [this]; exact Nat.mod_lt _ (by decide)⟩

theorem RR.readBits {n : Nat} : ∀ {r r' : LSBReader} {bs : List Bool} {v : Nat}, RR r bs →
    r.readBits n = some (v, r') → v < 2 ^ n ∧ ∃ rest, bs = natBits v n ++ rest ∧ RR r' rest := by
  induction n with
  | zero =>
    intro r r' bs v h hv
    simp only [LSBReader.readBits, Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨by simp, bs, by simp [natBits], h⟩
  | succ n ih =>
    intro r r' bs v h hv
    simp only [LSBReader.readBits] at hv
    split at hv
    · cases hv
    · next b r1 hb =>
      split at hv
      · cases hv
      · next val r2 hval =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        obtain ⟨rest1, rfl, h1⟩ := h.readBit hb
        obtain ⟨hlt, rest, rfl, h2⟩ := ih h1 hval
        refine ⟨by rw [Nat.pow_succ]; split <;> omega, rest, ?_, h2⟩
        have hm : ((if b then 1 else 0) + 2 * val) % 2 = (if b then 1 else 0) := by
          split <;> omega
        have hd : ((if b then 1 else 0) + 2 * val) / 2 = val := by split <;> omega
        simp only [natBits, hm, hd, List.cons_append]
        cases b <;> simp

theorem RR.readBits_of {n v : Nat} {r : LSBReader} {rest : List Bool} (hv : v < 2 ^ n)
    (h : RR r (natBits v n ++ rest)) : ∃ r', r.readBits n = some (v, r') ∧ RR r' rest := by
  obtain ⟨r', h1, h2⟩ := h.1.readBits
  rw [Nat.mod_eq_of_lt hv] at h1
  refine ⟨r', h1, h2, ?_⟩
  have := LSBReader.readBits_count n h.2 h1
  rw [this]; exact Nat.mod_lt _ (by decide)

theorem RR.alignToByte {r : LSBReader} {bs : List Bool} (h : RR r bs) :
    ∃ pad rest, bs = pad ++ rest ∧ pad.length = r.count ∧ rest.length % 8 = 0 ∧
      RR r.alignToByte rest := by
  obtain ⟨⟨hb, hbs⟩, hc⟩ := h
  refine ⟨natBits r.buffer r.count, bytesBits r.input, hbs.symm, by simp, by simp, ?_,
    by simp [LSBReader.alignToByte]⟩
  have := (LSBReader.Rep.alignToByte ⟨hb, hbs⟩)
  rw [← hbs, List.drop_left' (by simp)] at this
  exact this

theorem RR.init (bs : List UInt8) :
    RR { buffer := 0, count := 0, input := bs, totalRead := 0 } (bytesBits bs) :=
  ⟨⟨by simp, by simp [natBits]⟩, by simp⟩

/-- The value of a little-endian bit list. -/
def lsbVal : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * lsbVal bs

theorem lsbVal_natBits (v n : Nat) : lsbVal (natBits v n) = v % 2 ^ n := by
  induction n generalizing v with
  | zero => simp [natBits, lsbVal, Nat.mod_one]
  | succ n ih =>
    simp only [natBits, lsbVal, ih, decide_eq_true_eq]
    rw [Nat.pow_succ', Nat.mod_mul]
    split <;> omega

theorem natBits_inj {v w n : Nat} (hv : v < 2 ^ n) (hw : w < 2 ^ n)
    (h : natBits v n = natBits w n) : v = w := by
  have := congrArg lsbVal h
  rwa [lsbVal_natBits, lsbVal_natBits, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hw] at this

theorem bytesBits_inj : ∀ {a b : List UInt8}, bytesBits a = bytesBits b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by have := congrArg List.length h; simp at this
  | _ :: _, [], h => by have := congrArg List.length h; simp at this
  | x :: xs, y :: ys, h => by
    simp only [bytesBits, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    have hxy : x.toNat = y.toNat := natBits_inj x.toNat_lt y.toNat_lt h1
    rw [UInt8.toNat_inj.mp hxy, bytesBits_inj h2]

/-- The end of a run: the remaining bits are the rest of the current byte, then
the unread input. -/
theorem RR.tail {r : LSBReader} {pad : List Bool} {rest : List UInt8}
    (h : RR r (pad ++ bytesBits rest)) (hp : pad.length < 8) : r.input = rest := by
  obtain ⟨⟨_, hbs⟩, hc⟩ := h
  have hl := congrArg List.length hbs
  simp only [List.length_append, length_natBits, length_bytesBits] at hl
  have h1 : r.count = pad.length := by omega
  obtain ⟨_, h2⟩ := List.append_inj hbs (by simp [h1])
  exact bytesBits_inj h2

theorem RR.pad {r : LSBReader} {bs : List Bool} (h : RR r bs) :
    ∃ pad, pad.length < 8 ∧ bs = pad ++ bytesBits r.input :=
  ⟨natBits r.buffer r.count, by simpa using h.2, h.1.2.symm⟩

/-! ### Canonical codes -/

theorem assignCodes_getElem? (L : List Nat) : ∀ (nc : Nat → Nat) (n : Nat),
    (DeflateSpec.assignCodes nc L)[n]? = L[n]?.map (fun len =>
      if len = 0 then none
      else some (DeflateSpec.codeBits (nc len + (L.take n).count len) len)) := by
  induction L with
  | nil => intros; rfl
  | cons x L ih =>
    intro nc n
    cases n with
    | zero =>
      simp only [DeflateSpec.assignCodes]
      split <;> simp_all
    | succ n =>
      rw [List.getElem?_cons_succ, List.take_succ_cons]
      simp only [DeflateSpec.assignCodes]
      split
      · next hx =>
        rw [List.getElem?_cons_succ, ih]
        cases L[n]? with
        | none => rfl
        | some len =>
          simp only [Option.map_some, List.count_cons, beq_iff_eq]
          by_cases h0 : len = 0
          · simp [h0]
          · simp [h0, hx, Ne.symm h0]
      · next hx =>
        rw [List.getElem?_cons_succ, ih]
        cases L[n]? with
        | none => rfl
        | some len =>
          simp only [Option.map_some, List.count_cons, beq_iff_eq]
          by_cases h0 : len = 0
          · simp [h0]
          · by_cases h : len = x
            · subst h; simp [h0]; congr 1; omega
            · simp [h0, h, Ne.symm h]

theorem ofLengths_apply (L : List Nat) (n : Nat) :
    DeflateSpec.Code.ofLengths L n = L[n]?.bind (fun len =>
      if len = 0 then none
      else some (DeflateSpec.codeBits (DeflateSpec.nextCode L len + (L.take n).count len) len)) := by
  simp only [DeflateSpec.Code.ofLengths, assignCodes_getElem?]
  cases L[n]? <;> rfl

theorem ofLengths_eq_some {L : List Nat} {n : Nat} {w : List Bool}
    (h : DeflateSpec.Code.ofLengths L n = some w) :
    ∃ hn : n < L.length, L[n] ≠ 0 ∧
      w = DeflateSpec.codeBits (DeflateSpec.nextCode L L[n] + (L.take n).count L[n]) L[n] := by
  rw [ofLengths_apply] at h
  by_cases hn : n < L.length
  · rw [List.getElem?_eq_getElem hn] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h
    · next h0 => exact ⟨hn, h0, (Option.some.inj h).symm⟩
  · rw [List.getElem?_eq_none (by omega)] at h; cases h

theorem firstCode_eq_nextCode (L : CodeLengths) (M : Nat) :
    ∀ m < M, firstCode L M m = DeflateSpec.nextCode L (m + 1) := by
  intro m
  induction m with
  | zero => intro hM; rw [firstCode_zero L M hM]; rfl
  | succ m ih =>
    intro hm
    rw [firstCode_succ L M m hm, ih (by omega)]
    simp [DeflateSpec.nextCode, DeflateSpec.blCount]

/-- The code accumulated by `decodeSymbolLSBAux` from the bits it reads. -/
def accBits (code : Nat) (w : List Bool) : Nat :=
  w.foldl (fun c b => c * 2 + if b then 1 else 0) code

theorem accBits_eq (w : List Bool) : ∀ c, accBits c w = c * 2 ^ w.length + accBits 0 w := by
  induction w with
  | nil => intro c; simp [accBits]
  | cons b w ih =>
    intro c
    simp only [accBits, List.foldl_cons] at ih ⊢
    rw [ih, ih (0 * 2 + _), List.length_cons, Nat.pow_succ, Nat.mul_comm (2 ^ _) 2,
      ← Nat.mul_assoc, Nat.add_mul, Nat.zero_mul, Nat.zero_add, Nat.add_assoc]

theorem accBits_lt (w : List Bool) : accBits 0 w < 2 ^ w.length := by
  induction w with
  | nil => simp [accBits]
  | cons b w ih =>
    have h := accBits_eq w (0 * 2 + if b then 1 else 0)
    simp only [accBits, List.foldl_cons] at h ih ⊢
    rw [h, List.length_cons, Nat.pow_succ]
    split <;> simp <;> omega

theorem msbBits_accBits (w : List Bool) : ∀ c, msbBits (accBits c w) w.length = w := by
  induction w with
  | nil => intro c; rfl
  | cons b w ih =>
    intro c
    have h1 := ih (c * 2 + if b then 1 else 0)
    simp only [accBits, List.foldl_cons, List.length_cons] at h1 ⊢
    rw [msbBits, h1]
    congr 1
    have h2 := accBits_eq w (c * 2 + if b then 1 else 0)
    have h3 := accBits_lt w
    simp only [accBits] at h2 h3
    rw [h2, Nat.testBit_eq_decide_div_mod_eq, Nat.mul_comm _ (2 ^ _),
      Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt h3, Nat.add_zero]
    cases b <;> simp

/-! ### Decoder lookups -/

theorem lookupEntry_go_some {c l s : Nat} :
    ∀ {es : List CodeEntry}, lookupEntry.go c l es = some s →
      ∃ e ∈ es, 0 < e.length ∧ e.length = l ∧ e.code = c ∧ e.symbol = s
  | [], h => by cases h
  | e :: es, h => by
    simp only [lookupEntry.go] at h
    split at h
    · next hm => exact ⟨e, List.mem_cons_self, hm.1, hm.2.1, hm.2.2, Option.some.inj h⟩
    · obtain ⟨e', he', h'⟩ := lookupEntry_go_some h
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩

theorem assignCodes_mem {L : CodeLengths} {M : Nat} {e : CodeEntry}
    (he : e ∈ assignCodes L M) (hpos : 0 < e.length) :
    ∃ j, ∃ hj : j < L.length, e.length = L[j] ∧ L[j] ≤ M ∧
      e.code = firstCode L M (L[j] - 1) + (L.take j).count L[j] ∧ e.symbol = j := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
  rw [Silmaril.Formats.Compression.assignCodes_getElem? L M j] at hj
  cases hLj : L[j]? with
  | none => simp [hLj] at hj
  | some len =>
    have hjl : j < L.length := by
      rcases List.getElem?_eq_some_iff.mp hLj with ⟨h, _⟩; exact h
    have hLj' : L[j] = len := by
      rcases List.getElem?_eq_some_iff.mp hLj with ⟨_, h⟩; exact h
    simp only [hLj, Option.map_some, Option.some.injEq] at hj
    subst hj
    refine ⟨j, hjl, ?_⟩
    unfold canonEntry at hpos ⊢
    split at hpos
    · simp at hpos
    · next hlen =>
      rw [ite_eq_right hlen]
      simp only [hLj']
      refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | omega

theorem decodeAux_sound (entries : List CodeEntry) : ∀ (fuel : Nat) {r r' : LSBReader}
    {code len s : Nat} {bs : List Bool},
    decodeSymbolLSBAux entries r code len fuel = some (s, r') → RR r bs →
    ∃ w rest, bs = w ++ rest ∧ RR r' rest ∧
      lookupEntry entries (accBits code w) (len + w.length) = some s := by
  intro fuel
  induction fuel with
  | zero => intro r r' code len s bs h; cases h
  | succ n ih =>
    intro r r' code len s bs h hr
    simp only [decodeSymbolLSBAux] at h
    split at h
    · next sym hsym =>
      obtain ⟨rfl, rfl⟩ : sym = s ∧ r = r' := by simpa using h
      exact ⟨[], bs, rfl, hr, by simpa [accBits] using hsym⟩
    · split at h
      · cases h
      · next b r1 hb =>
        obtain ⟨bs1, rfl, h1⟩ := hr.readBit hb
        obtain ⟨w, rest, rfl, h2, h3⟩ := ih h h1
        refine ⟨b :: w, rest, rfl, h2, ?_⟩
        simp only [accBits, List.foldl_cons, List.length_cons] at h3 ⊢
        rw [show len + (w.length + 1) = len + 1 + w.length by omega]
        exact h3

theorem decodeAux_count (entries : List CodeEntry) : ∀ (fuel : Nat) {r r' : LSBReader}
    {code len s : Nat}, decodeSymbolLSBAux entries r code len fuel = some (s, r') →
    r.count < 8 → r'.count < 8 := by
  intro fuel
  induction fuel with
  | zero => intro r r' code len s h; cases h
  | succ n ih =>
    intro r r' code len s h hc
    simp only [decodeSymbolLSBAux] at h
    split at h
    · obtain ⟨rfl, rfl⟩ : _ ∧ r = r' := by simpa using h
      exact hc
    · split at h
      · cases h
      · next b r1 hb =>
        refine ih h ?_
        rw [LSBReader.readBit_count hc hb]; exact Nat.mod_lt _ (by decide)

/-- Every symbol the table `t` decodes is read according to the code `C`. -/
def TSound (t : HuffmanTable) (C : DeflateSpec.Code) : Prop :=
  ∀ {r r' : LSBReader} {bs : List Bool} {s : Nat}, RR r bs →
    t.readSymbolLSB r = some (s, r') → ∃ rest, C.Reads bs s rest ∧ RR r' rest

/-- The table `t` decodes every codeword of `C`. -/
def TComplete (t : HuffmanTable) (C : DeflateSpec.Code) : Prop :=
  ∀ {r : LSBReader} {s : Nat} {w rest : List Bool}, C s = some w → RR r (w ++ rest) →
    ∃ r', t.readSymbolLSB r = some (s, r') ∧ RR r' rest

theorem ofLengths_entries {L : CodeLengths} {M : Nat} {t : HuffmanTable}
    (h : HuffmanTable.ofLengths L M = some t) :
    t.entries = assignCodes L M ∧ isValidLengths L M = true ∧ t.maxBits = M := by
  unfold HuffmanTable.ofLengths at h
  split at h
  · cases h
  · next hv =>
    simp only [Option.some.injEq] at h
    subst h
    simpa using hv

theorem tSound_ofLengths {L : CodeLengths} {M : Nat} {t : HuffmanTable}
    (h : HuffmanTable.ofLengths L M = some t) : TSound t (DeflateSpec.Code.ofLengths L) := by
  intro r r' bs s hr hs
  obtain ⟨hent, hv, _⟩ := ofLengths_entries h
  obtain ⟨w, rest, rfl, hr', hl⟩ := decodeAux_sound t.entries _ hs hr
  refine ⟨rest, ⟨w, ?_, rfl⟩, hr'⟩
  rw [hent] at hl
  obtain ⟨e, he, hpos, hlen, hcode, hsym⟩ := lookupEntry_go_some hl
  obtain ⟨j, hj, hl', hle, hc', hsym'⟩ := assignCodes_mem he hpos
  have hjs : j = s := hsym' ▸ hsym
  subst hjs
  rw [ofLengths_apply, List.getElem?_eq_getElem hj]
  simp only [Option.bind_some]
  rw [ite_eq_right (by omega : ¬ L[j] = 0)]
  congr 1
  have hn := firstCode_eq_nextCode L M (L[j] - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at hn
  rw [← hn, ← hc', hcode, codeBits_eq, ← hl', hlen, Nat.zero_add, msbBits_accBits]

/-- The table built from `L` assigns each used symbol its canonical code. -/
theorem encodeSymbol_ofLengths {L : CodeLengths} {M : Nat} {t : HuffmanTable}
    (h : HuffmanTable.ofLengths L M = some t) {s : Nat} (hs : s < L.length) (h0 : L[s] ≠ 0)
    (hle : L[s] ≤ M) :
    t.encodeSymbol s = some (firstCode L M (L[s] - 1) + (L.take s).count L[s], L[s]) := by
  unfold HuffmanTable.ofLengths at h
  split at h
  · cases h
  simp only [Option.some.injEq] at h
  subst h
  have hc : ¬ (L[s] = 0 ∨ L[s] > M) := by omega
  have hp : L[s] > 0 := by omega
  simp only [HuffmanTable.encodeSymbol, listGet_eq, List.getElem?_map,
    Silmaril.Formats.Compression.assignCodes_getElem?, List.getElem?_eq_getElem hs,
    Option.map_some, canonEntry, hc, ↓reduceIte, hp]

theorem tComplete_ofLengths {L : CodeLengths} {M : Nat} {t : HuffmanTable}
    (h : HuffmanTable.ofLengths L M = some t) : TComplete t (DeflateSpec.Code.ofLengths L) := by
  intro r s w rest hw hr
  obtain ⟨hent, hv, hM⟩ := ofLengths_entries h
  obtain ⟨hs, h0, rfl⟩ := ofLengths_eq_some hw
  have hok := HuffmanTable.ofLengths_symOK h hs (Nat.pos_of_ne_zero h0)
  obtain ⟨c, l, henc, hcode⟩ := hok
  have hle : L[s] ≤ M := isValidLengths_le L M hv _ (List.getElem_mem hs)
  rw [encodeSymbol_ofLengths h hs h0 hle] at henc
  have hcl : c = firstCode L M (L[s] - 1) + (L.take s).count L[s] ∧ l = L[s] := by
    simp only [Option.some.injEq, Prod.mk.injEq] at henc
    exact ⟨henc.1.symm, henc.2.symm⟩
  obtain ⟨rfl, rfl⟩ := hcl
  have hn := firstCode_eq_nextCode L M (L[s] - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at hn
  rw [codeBits_eq, ← hn] at hr
  obtain ⟨r', h1, h2⟩ := HuffmanTable.readSymbolLSB_of_codeOK hcode hr.1
  exact ⟨r', h1, h2, decodeAux_count _ _ h1 hr.2⟩

/-! ### Fixed codes -/

theorem fixedLitLenLengths_eq' : DeflateSpec.fixedLitLenLengths = Deflate.fixedLitLenLengths := by
  rw [fixedLitLenLengths_eq]; rfl

theorem fixedDistCode_eq : DeflateSpec.fixedDistCode = DeflateSpec.Code.ofLengths fixedDistLengths := by
  funext d
  rw [ofLengths_apply]
  simp only [DeflateSpec.fixedDistCode, fixedDistLengths]
  by_cases hd : d < 32
  · rw [List.getElem?_replicate, ite_eq_left hd, ite_eq_left hd]
    simp only [Option.bind_some, List.take_replicate, List.count_replicate_self]
    have : DeflateSpec.nextCode (List.replicate 32 5) 5 = 0 := by decide
    rw [this]
    simp [Nat.min_eq_left (Nat.le_of_lt hd)]
  · rw [List.getElem?_replicate, ite_eq_right hd, ite_eq_right hd]; rfl

theorem fixed_tables : ∃ lt dt, fixedLitLenTable = some lt ∧ fixedDistTable = some dt ∧
    TSound lt DeflateSpec.fixedLitLenCode ∧ TComplete lt DeflateSpec.fixedLitLenCode ∧
    TSound dt DeflateSpec.fixedDistCode ∧ TComplete dt DeflateSpec.fixedDistCode := by
  obtain ⟨lt, hlt, _⟩ := fixedLitLenTable_spec
  obtain ⟨dt, hdt, _⟩ := fixedDistTable_spec
  refine ⟨lt, dt, hlt, hdt, ?_, ?_, ?_, ?_⟩
  · rw [DeflateSpec.fixedLitLenCode, fixedLitLenLengths_eq']; exact tSound_ofLengths hlt
  · rw [DeflateSpec.fixedLitLenCode, fixedLitLenLengths_eq']; exact tComplete_ofLengths hlt
  · rw [fixedDistCode_eq]; exact tSound_ofLengths hdt
  · rw [fixedDistCode_eq]; exact tComplete_ofLengths hdt

/-! ### Length and distance tables -/

theorem lengthCode_eq (sym : Nat) :
    DeflateSpec.lengthCode sym =
      if 257 ≤ sym ∧ sym ≤ 285 then
        some (lengthExtraBits.getD (sym - 257) 0, lengthBase.getD (sym - 257) 3)
      else none := by
  unfold DeflateSpec.lengthCode
  by_cases h : 257 ≤ sym
  · rw [ite_eq_left h]
    obtain ⟨i, rfl⟩ : ∃ i, sym = 257 + i := ⟨sym - 257, by omega⟩
    rw [show 257 + i - 257 = i by omega]
    by_cases hi : i < 29
    · rw [ite_eq_left ⟨h, by omega⟩]
      have key : ∀ i < 29, DeflateSpec.lengthTable[i]? =
          some (lengthExtraBits.getD i 0, lengthBase.getD i 3) := by decide
      exact key i hi
    · rw [ite_eq_right (by omega)]
      exact List.getElem?_eq_none (by simp [DeflateSpec.lengthTable]; omega)
  · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem distCode_eq (d : Nat) :
    DeflateSpec.distCode d =
      if d < 30 then some (distanceExtraBits.getD d 0, distanceBase.getD d 1) else none := by
  unfold DeflateSpec.distCode
  by_cases hd : d < 30
  · rw [ite_eq_left hd]
    have key : ∀ d < 30, DeflateSpec.distTable[d]? =
        some (distanceExtraBits.getD d 0, distanceBase.getD d 1) := by decide
    exact key d hd
  · rw [ite_eq_right hd]
    exact List.getElem?_eq_none (by simp [DeflateSpec.distTable]; omega)

theorem distanceBase_pos (d : Nat) (hd : d < 30) : 1 ≤ distanceBase.getD d 1 := by
  have key : ∀ d < 30, 1 ≤ distanceBase.getD d 1 := by decide
  exact key d hd

/-! ### LZ77 copies -/

theorem copyMatch_add (out : List UInt8) (d a : Nat) : ∀ b,
    DeflateSpec.copyMatch out d (a + b) =
      DeflateSpec.copyMatch (DeflateSpec.copyMatch out d a) d b := by
  intro b
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, DeflateSpec.copyMatch, ih]; rfl

theorem copyBack_eq (d : Nat) : ∀ (n : Nat) (out : List UInt8),
    copyBack d out n = DeflateSpec.copyMatch out d n := by
  intro n
  induction n with
  | zero => intro out; rfl
  | succ n ih =>
    intro out
    rw [copyBack, ih, Nat.add_comm n 1, copyMatch_add]
    rfl

/-! ### Stored lengths -/

theorem nlen_iff {len nlen : Nat} (hl : len < 2 ^ 16) (hn : nlen < 2 ^ 16) :
    (len ^^^ nlen) % 65536 = 65535 ↔ nlen = len ^^^ 0xFFFF := by
  have hx : len ^^^ nlen < 2 ^ 16 := Nat.xor_lt_two_pow hl hn
  rw [Nat.mod_eq_of_lt (by simpa using hx)]
  constructor
  · intro h
    rw [← h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · intro h
    rw [h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-! ### Stored bytes -/

theorem readStoredBytes_sound : ∀ (n : Nat) {acc acc' : List UInt8} {r r' : LSBReader}
    {bs : List Bool}, readStoredBytes acc r n = .ok (acc', r') → RR r bs →
    ∃ data rest, acc' = acc ++ data ∧ data.length = n ∧ bs = bytesBits data ++ rest ∧
      RR r' rest := by
  intro n
  induction n with
  | zero =>
    intro acc acc' r r' bs h hr
    simp only [readStoredBytes, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], bs, by simp, rfl, by simp [bytesBits], hr⟩
  | succ n ih =>
    intro acc acc' r r' bs h hr
    simp only [readStoredBytes] at h
    split at h
    · cases h
    · next b r1 hb =>
      simp only [LSBReader.readByte] at hb
      split at hb
      · cases hb
      · next v r2 hv =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        obtain ⟨hlt, bs1, rfl, h1⟩ := hr.readBits hv
        obtain ⟨data, rest, rfl, hlen, rfl, h2⟩ := ih h h1
        refine ⟨UInt8.ofNat v :: data, rest, by simp, by simp [hlen], ?_, h2⟩
        have : (UInt8.ofNat v).toNat = v := by
          simp at hlt ⊢; omega
        simp [bytesBits, this]

theorem readStoredBytes_complete : ∀ (data : List UInt8) {acc : List UInt8} {r : LSBReader}
    {rest : List Bool}, RR r (bytesBits data ++ rest) →
    ∃ r', readStoredBytes acc r data.length = .ok (acc ++ data, r') ∧ RR r' rest := by
  intro data
  induction data with
  | nil => intro acc r rest h; exact ⟨r, by simp [readStoredBytes], by simpa [bytesBits] using h⟩
  | cons b data ih =>
    intro acc r rest h
    simp only [bytesBits, List.flatMap_cons, List.append_assoc] at h
    obtain ⟨r1, h1, hr1⟩ := RR.readBits_of b.toNat_lt h
    obtain ⟨r', h2, hr'⟩ := ih (acc := acc ++ [b]) hr1
    refine ⟨r', ?_, hr'⟩
    show readStoredBytes acc r (data.length + 1) = _
    rw [readStoredBytes]
    simp only [LSBReader.readByte, h1, UInt8.ofNat_toNat]
    simpa using h2

end Silmaril.Proofs.Formats.Compression.DeflateSpec
