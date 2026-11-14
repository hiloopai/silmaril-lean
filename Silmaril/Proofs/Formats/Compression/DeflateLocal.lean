module

public import Silmaril.Formats.Compression.Deflate.Defs

/-!
Proofs for the append law of `Silmaril.Formats.Compression.Deflate.Thms`
(`Deflate.local`): every successful decoding stage, run on a reader whose unread
input is extended by `tail`, succeeds with the same result and the final reader
extended by the same `tail`. Fuel bounds only grow with the input, and success
is monotone in fuel.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.DeflateLocal

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Deflate

/-- The reader with `tail` appended to its unread input. -/
def ext (r : LSBReader) (tail : List UInt8) : LSBReader := { r with input := r.input ++ tail }

theorem ext_bitsLeft (r : LSBReader) (tail : List UInt8) :
    (ext r tail).bitsLeft = r.bitsLeft + 8 * tail.length := by
  simp only [ext, LSBReader.bitsLeft, List.length_append]
  omega

theorem readBit_ext {r r' : LSBReader} {bit : Bool}
    (h : r.readBit = some (bit, r')) (tail : List UInt8) :
    (ext r tail).readBit = some (bit, ext r' tail) := by
  by_cases empty : r.count = 0
  · cases input : r.input with
    | nil => simp [LSBReader.readBit, LSBReader.refill, empty, input] at h
    | cons byte rest =>
      simp only [LSBReader.readBit, empty, ite_true, LSBReader.refill, input,
        Nat.reduceEqDiff, ite_false, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [ext, LSBReader.readBit, empty, ite_true, LSBReader.refill,
        input, List.cons_append, Nat.reduceEqDiff, ite_false]
  · simp only [LSBReader.readBit, empty, ite_false,
      Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp only [ext, LSBReader.readBit, empty, ite_false]
    rfl

theorem readBits_ext (n : Nat) {r r' : LSBReader} {value : Nat}
    (h : r.readBits n = some (value, r')) (tail : List UInt8) :
    (ext r tail).readBits n = some (value, ext r' tail) := by
  induction n generalizing r r' value with
  | zero =>
    simp only [LSBReader.readBits, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | succ n ih =>
    simp only [LSBReader.readBits] at h
    cases hb : r.readBit with
    | none => simp only [hb, reduceCtorEq] at h
    | some pair =>
      rcases pair with ⟨bit, middle⟩
      cases hr : middle.readBits n with
      | none => simp only [hb, hr, reduceCtorEq] at h
      | some pair =>
        rcases pair with ⟨rest, final⟩
        simp only [hb, hr, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp only [LSBReader.readBits, readBit_ext hb, ih hr]

theorem readByte_ext {r r' : LSBReader} {b : UInt8}
    (h : r.readByte = some (b, r')) (tail : List UInt8) :
    (ext r tail).readByte = some (b, ext r' tail) := by
  unfold LSBReader.readByte at h ⊢
  cases hr : r.readBits 8 with
  | none => simp [hr] at h
  | some pair =>
    rcases pair with ⟨v, r1⟩
    simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rw [readBits_ext 8 hr]

theorem alignToByte_ext (r : LSBReader) (tail : List UInt8) :
    (ext r tail).alignToByte = ext r.alignToByte tail := rfl

theorem readStoredBytes_ext (tail : List UInt8) : ∀ (n : Nat) (acc : List UInt8)
    {r r' : LSBReader} {out : List UInt8}, readStoredBytes acc r n = .ok (out, r') →
    readStoredBytes acc (ext r tail) n = .ok (out, ext r' tail)
  | 0, acc, r, r', out, h => by
    simp only [readStoredBytes, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | n + 1, acc, r, r', out, h => by
    simp only [readStoredBytes] at h ⊢
    cases hb : r.readByte with
    | none => simp [hb] at h
    | some pair =>
      rcases pair with ⟨b, r1⟩
      simp only [hb] at h
      rw [readByte_ext hb]
      exact readStoredBytes_ext tail n _ h

theorem decompressStored_ext {r r' : LSBReader} {out : List UInt8}
    (h : decompressStored r = .ok (out, r')) (tail : List UInt8) :
    decompressStored (ext r tail) = .ok (out, ext r' tail) := by
  unfold decompressStored at h ⊢
  rw [alignToByte_ext]
  cases h1 : r.alignToByte.readBits 16 with
  | none => simp [h1] at h
  | some p1 =>
    rcases p1 with ⟨len, r1⟩
    cases h2 : r1.readBits 16 with
    | none => simp [h1, h2] at h
    | some p2 =>
      rcases p2 with ⟨nlen, r2⟩
      simp only [h1, h2] at h
      simp only [readBits_ext 16 h1, readBits_ext 16 h2]
      split at h
      · simp at h
      · next hne =>
        simp only [hne, ↓reduceIte]
        exact readStoredBytes_ext tail len [] h

theorem decodeSymbolLSBAux_ext (entries : List CodeEntry) (tail : List UInt8) :
    ∀ (n code len : Nat) {r r' : LSBReader} {sym : Nat},
      decodeSymbolLSBAux entries r code len n = some (sym, r') →
      decodeSymbolLSBAux entries (ext r tail) code len n = some (sym, ext r' tail)
  | 0, code, len, r, r', sym, h => by simp [decodeSymbolLSBAux] at h
  | n + 1, code, len, r, r', sym, h => by
    simp only [decodeSymbolLSBAux] at h ⊢
    cases hl : lookupEntry entries code len with
    | some s =>
      simp only [hl, Option.some.injEq, Prod.mk.injEq] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    | none =>
      simp only [hl] at h ⊢
      cases hb : r.readBit with
      | none => simp [hb] at h
      | some pair =>
        rcases pair with ⟨b, r1⟩
        simp only [hb] at h
        rw [readBit_ext hb]
        exact decodeSymbolLSBAux_ext entries tail n _ _ h

theorem readSymbolLSB_ext {t : HuffmanTable} {r r' : LSBReader} {sym : Nat}
    (h : t.readSymbolLSB r = some (sym, r')) (tail : List UInt8) :
    t.readSymbolLSB (ext r tail) = some (sym, ext r' tail) :=
  decodeSymbolLSBAux_ext t.entries tail _ _ _ h

/-- A symbol step with its reader extended. -/
def stepExt (tail : List UInt8) : SymbolStep → SymbolStep
  | .done o r => .done o (DeflateLocal.ext r tail)
  | .more o r => .more o (DeflateLocal.ext r tail)

theorem decodeStep_ext {litLen dist : HuffmanTable} {r : LSBReader} {output : List UInt8}
    {st : SymbolStep} (h : decodeStep litLen dist r output = .ok st) (tail : List UInt8) :
    decodeStep litLen dist (ext r tail) output = .ok (stepExt tail st) := by
  unfold decodeStep at h ⊢
  split at h
  · cases h
  next sym r1 h1 =>
  rw [readSymbolLSB_ext h1]
  dsimp only
  split at h
  · next hlt => cases h; simp only [hlt, ↓reduceIte]; rfl
  split at h
  · next h256 => cases h; simp only [h256, ↓reduceIte]; rfl
  split at h
  · next hn h256 hle =>
    simp only [hn, h256, hle, ↓reduceIte]
    dsimp only at h
    split at h
    · cases h
    next ev r2 h2 =>
    rw [readBits_ext _ h2]
    dsimp only
    split at h
    · cases h
    next ds r3 h3 =>
    rw [readSymbolLSB_ext h3]
    dsimp only
    split at h
    · cases h
    next hds =>
    simp only [hds, ↓reduceIte]
    split at h
    · cases h
    next dv r4 h4 =>
    rw [readBits_ext _ h4]
    dsimp only
    split at h
    · cases h
    next hgt =>
    simp only [hgt, ↓reduceIte]
    cases h
    rfl
  · cases h

/-- Decoding symbols succeeds on the extended input, with any larger fuel. -/
theorem decodeSymbolsFuel_ext (litLen dist : HuffmanTable) (tail : List UInt8) :
    ∀ (fuel fuel' : Nat) {r r' : LSBReader} {output out : List UInt8}, fuel ≤ fuel' →
      decodeSymbolsFuel litLen dist fuel r output = .ok (out, r') →
      decodeSymbolsFuel litLen dist fuel' (ext r tail) output = .ok (out, ext r' tail)
  | 0, _, r, r', output, out, _, h => by simp [decodeSymbolsFuel] at h
  | fuel + 1, 0, r, r', output, out, hle, h => by omega
  | fuel + 1, fuel' + 1, r, r', output, out, hle, h => by
    simp only [decodeSymbolsFuel] at h ⊢
    cases hs : decodeStep litLen dist r output with
    | error e => simp [hs] at h
    | ok st =>
      rw [decodeStep_ext hs]
      cases st with
      | done o r1 =>
        simp only [hs, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rfl
      | more o r1 =>
        simp only [hs] at h
        exact decodeSymbolsFuel_ext litLen dist tail fuel fuel' (by omega) h

theorem decodeSymbol_ext {litLen dist : HuffmanTable} {r r' : LSBReader}
    {output out : List UInt8} (h : decodeSymbol litLen dist r output = .ok (out, r'))
    (tail : List UInt8) :
    decodeSymbol litLen dist (ext r tail) output = .ok (out, ext r' tail) :=
  decodeSymbolsFuel_ext litLen dist tail _ _ (by rw [ext_bitsLeft]; omega) h

theorem readCLLengths_ext (tail : List UInt8) : ∀ (n i : Nat) (acc : List Nat)
    {r r' : LSBReader} {lens : List Nat}, readCLLengths n i acc r = .ok (lens, r') →
    readCLLengths n i acc (ext r tail) = .ok (lens, ext r' tail)
  | 0, i, acc, r, r', lens, h => by
    simp only [readCLLengths, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | n + 1, i, acc, r, r', lens, h => by
    unfold readCLLengths at h ⊢
    split at h
    · cases h
    next v r1 h1 =>
    rw [readBits_ext _ h1]
    exact readCLLengths_ext tail n _ _ h

theorem readCodeLengths_ext (clTable : HuffmanTable) (total : Nat) (tail : List UInt8) :
    ∀ (fuel : Nat) (acc : List Nat) {r r' : LSBReader} {lens : List Nat},
      readCodeLengths clTable total fuel acc r = .ok (lens, r') →
      readCodeLengths clTable total fuel acc (ext r tail) = .ok (lens, ext r' tail)
  | 0, acc, r, r', lens, h => by
    unfold readCodeLengths at h ⊢
    split at h
    · next he => cases h; simp only [he, ↓reduceIte]
    · cases h
  | fuel + 1, acc, r, r', lens, h => by
    unfold readCodeLengths at h ⊢
    split at h
    · next hle =>
      simp only [hle, ↓reduceIte]
      split at h
      · next he => cases h; simp only [he, ↓reduceIte]
      · cases h
    next hle =>
    simp only [hle, ↓reduceIte]
    split at h
    · cases h
    next sym r1 h1 =>
    rw [readSymbolLSB_ext h1]
    dsimp only
    split at h
    · next hs => simp only [hs, ↓reduceIte]; exact readCodeLengths_ext clTable total tail fuel _ h
    next hs =>
    simp only [hs, ↓reduceIte]
    split at h
    · next h16 =>
      simp only [h16, ↓reduceIte]
      split at h
      · cases h
      next prev hprev =>
      split at h
      · cases h
      next e r2 h2 =>
      rw [readBits_ext _ h2]
      exact readCodeLengths_ext clTable total tail fuel _ h
    next h16 =>
    simp only [h16, ↓reduceIte]
    split at h
    · next h17 =>
      simp only [h17, ↓reduceIte]
      split at h
      · cases h
      next e r2 h2 =>
      rw [readBits_ext _ h2]
      exact readCodeLengths_ext clTable total tail fuel _ h
    next h17 =>
    simp only [h17, ↓reduceIte]
    split at h
    · next h18 =>
      simp only [h18, ↓reduceIte]
      split at h
      · cases h
      next e r2 h2 =>
      rw [readBits_ext _ h2]
      exact readCodeLengths_ext clTable total tail fuel _ h
    · cases h

theorem readDynamicTables_ext {r r' : LSBReader} {lt dt : HuffmanTable}
    (h : readDynamicTables r = .ok (lt, dt, r')) (tail : List UInt8) :
    readDynamicTables (ext r tail) = .ok (lt, dt, ext r' tail) := by
  unfold readDynamicTables at h ⊢
  split at h
  · cases h
  next hlit r1 h1 =>
  rw [readBits_ext _ h1]
  dsimp only
  split at h
  · cases h
  next hdist r2 h2 =>
  rw [readBits_ext _ h2]
  dsimp only
  split at h
  · cases h
  next hclen r3 h3 =>
  rw [readBits_ext _ h3]
  dsimp only at h ⊢
  split at h
  · cases h
  next hrange =>
  simp only [hrange, ↓reduceIte]
  split at h
  · cases h
  next clLens r4 h4 =>
  rw [readCLLengths_ext tail _ _ _ h4]
  dsimp only
  split at h
  · cases h
  next hcomplete =>
  simp only [hcomplete, Bool.false_eq_true, ↓reduceIte]
  split at h
  · cases h
  next clTable hcl =>
  split at h
  · cases h
  next lens r5 h5 =>
  rw [readCodeLengths_ext _ _ tail _ _ h5]
  dsimp only at h ⊢
  split at h
  · cases h
  next h256 =>
  simp only [h256, ↓reduceIte]
  split at h
  · cases h
  next hlv =>
  simp only [hlv, Bool.false_eq_true, ↓reduceIte]
  split at h
  · cases h
  next hdv =>
  simp only [hdv, Bool.false_eq_true, ↓reduceIte]
  split at h
  · cases h
    rfl
  · cases h

theorem decompressBlockBody_ext {btype : Nat} {r r' : LSBReader} {out out' : List UInt8}
    (h : decompressBlockBody btype r out = .ok (out', r')) (tail : List UInt8) :
    decompressBlockBody btype (ext r tail) out = .ok (out', ext r' tail) := by
  unfold decompressBlockBody at h ⊢
  split at h
  · next h0 =>
    simp only [h0, ↓reduceIte]
    split at h
    · cases h
    next bytes r1 h1 =>
    rw [decompressStored_ext h1]
    cases h
    rfl
  next h0 =>
  simp only [h0, ↓reduceIte]
  split at h
  · next h1 =>
    simp only [h1, ↓reduceIte]
    split at h
    · exact decodeSymbol_ext h tail
    · cases h
  next h1 =>
  simp only [h1, ↓reduceIte]
  split at h
  · next h2 =>
    simp only [h2, ↓reduceIte]
    split at h
    · cases h
    next lt dt r1 hr =>
    rw [readDynamicTables_ext hr]
    exact decodeSymbol_ext h tail
  · cases h

/-- Decoding blocks succeeds on the extended input, with any larger fuel. -/
theorem decompressBlocks_ext (tail : List UInt8) :
    ∀ (fuel fuel' : Nat) {r r' : LSBReader} {out out' : List UInt8}, fuel ≤ fuel' →
      decompressBlocks fuel r out = .ok (out', r') →
      decompressBlocks fuel' (ext r tail) out = .ok (out', ext r' tail)
  | 0, _, r, r', out, out', _, h => by simp [decompressBlocks] at h
  | fuel + 1, 0, r, r', out, out', hle, h => by omega
  | fuel + 1, fuel' + 1, r, r', out, out', hle, h => by
    unfold decompressBlocks at h ⊢
    split at h
    · cases h
    next bfinal r1 h1 =>
    rw [readBit_ext h1]
    dsimp only
    split at h
    · cases h
    next btype r2 h2 =>
    rw [readBits_ext _ h2]
    dsimp only
    split at h
    · cases h
    next o r3 h3 =>
    rw [decompressBlockBody_ext h3]
    dsimp only
    split at h
    · next hf => cases h; simp only [hf, ↓reduceIte]
    · next hf =>
      simp only [hf]
      exact decompressBlocks_ext tail fuel fuel' (by omega) h

theorem deflateTake_append {bs out rest : List UInt8} (h : deflateTake bs = .ok (out, rest))
    (tail : List UInt8) : deflateTake (bs ++ tail) = .ok (out, rest ++ tail) := by
  unfold deflateTake at h ⊢
  dsimp only at h ⊢
  split at h
  · cases h
  next o r' hr =>
  have := decompressBlocks_ext tail _ ((⟨0, 0, bs ++ tail, 0⟩ : LSBReader).bitsLeft + 1)
    (by simp only [LSBReader.bitsLeft, List.length_append]; omega) hr
  simp only [ext] at this
  rw [this]
  cases h
  rfl

theorem deflateTakeWithHistory_append {history bs out rest : List UInt8}
    (h : deflateTakeWithHistory history bs = .ok (out, rest)) (tail : List UInt8) :
    deflateTakeWithHistory history (bs ++ tail) = .ok (out, rest ++ tail) := by
  unfold deflateTakeWithHistory resultWithHistory at h ⊢
  dsimp only at h ⊢
  cases hr : decompressBlocks ((⟨0, 0, bs, 0⟩ : LSBReader).bitsLeft + 1) ⟨0, 0, bs, 0⟩ history with
  | error e => rw [hr] at h; cases h
  | ok p =>
    rcases p with ⟨o, r'⟩
    rw [hr] at h
    have := decompressBlocks_ext tail _ ((⟨0, 0, bs ++ tail, 0⟩ : LSBReader).bitsLeft + 1)
      (by simp only [LSBReader.bitsLeft, List.length_append]; omega) hr
    simp only [ext] at this
    rw [this]
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [← h.2]⟩

theorem decoder_local : decoder.Local := by
  intro bytes out rest tail h
  simp only [decoder, Decoder.ofExcept] at h ⊢
  cases hd : deflateTake bytes with
  | error e => rw [hd] at h; cases h
  | ok p =>
    rw [hd] at h
    cases h
    rw [deflateTake_append hd]
    rfl

end Silmaril.Proofs.Formats.Compression.DeflateLocal
