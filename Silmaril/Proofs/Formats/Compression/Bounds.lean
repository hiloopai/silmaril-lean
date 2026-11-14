module

public import Silmaril.Formats.Compression.Deflate.Defs
public import Silmaril.Proofs.Formats.Compression.Deflate
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Fuel
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.ParserPhases
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Blocks
public import Silmaril.Raw.Formats.Compression.Bits.BitstreamFacts

/-!
Proofs of the intrinsic output bounds of `Silmaril.Formats.Compression.Deflate.Thms`.

Every decoding stage keeps `output.length + 258 * unread bits` from growing: a
Huffman token consumes at least one bit and appends at most 258 bytes (the
longest match), a stored byte consumes eight bits and appends one, and table
reads, alignment and end-of-block append nothing. Hence a DEFLATE member that
consumes `n` bytes produces at most `258 * 8 * n = 2064 * n` bytes.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.Bounds

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Deflate

/-- The potential `output.length + 258 * bitsLeft` does not grow. -/
def Bounded (out : List UInt8) (r : LSBReader) (out' : List UInt8) (r' : LSBReader) : Prop :=
  out'.length + 258 * r'.bitsLeft ≤ out.length + 258 * r.bitsLeft

theorem copyBack_length (d : Nat) : ∀ (n : Nat) (out : List UInt8),
    (copyBack d out n).length = out.length + n
  | 0, out => rfl
  | n + 1, out => by
    rw [copyBack, copyBack_length d n]
    simp only [List.length_append, List.length_singleton]
    omega

/-- The longest match is 258 bytes (RFC 1951 §3.2.5). -/
theorem length_max : ∀ i < 29, lengthBase.getD i 3 + 2 ^ lengthExtraBits.getD i 0 ≤ 259 := by
  decide

theorem decodeStep_bounded {litLen dist : HuffmanTable} {r : LSBReader} {out : List UInt8}
    {st : SymbolStep} (h : decodeStep litLen dist r out = .ok st) :
    match st with
    | .done o r' => Bounded out r o r'
    | .more o r' => Bounded out r o r' := by
  unfold decodeStep at h
  split at h
  · cases h
  next sym r1 h1 =>
  have hs1 := readSymbolLSB_bitsLeft_lt h1
  split at h
  · cases h
    simp only [Bounded, List.length_append, List.length_singleton]
    omega
  split at h
  · cases h
    simp only [Bounded]
    omega
  split at h
  · next hn h256 hle =>
    dsimp only at h
    split at h
    · cases h
    next ev r2 h2 =>
    have hs2 := readBits_bitsLeft h2
    have hev := LSBReader.readBits_lt h2
    split at h
    · cases h
    next ds r3 h3 =>
    have hs3 := readSymbolLSB_bitsLeft_lt h3
    split at h
    · cases h
    split at h
    · cases h
    next dv r4 h4 =>
    have hs4 := readBits_bitsLeft h4
    split at h
    · cases h
    cases h
    have hmax := length_max (sym - 257) (by omega)
    simp only [Bounded, copyBack_length]
    omega
  · cases h

theorem decodeSymbolsFuel_bounded (litLen dist : HuffmanTable) :
    ∀ (fuel : Nat) {r r' : LSBReader} {out out' : List UInt8},
      decodeSymbolsFuel litLen dist fuel r out = .ok (out', r') → Bounded out r out' r'
  | 0, _, _, _, _, h => by simp [decodeSymbolsFuel] at h
  | fuel + 1, r, r', out, out', h => by
    simp only [decodeSymbolsFuel] at h
    cases hs : decodeStep litLen dist r out with
    | error e => rw [hs] at h; cases h
    | ok st =>
      rw [hs] at h
      have hb := decodeStep_bounded hs
      cases st with
      | done o r1 =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hb
      | more o r1 =>
        have := decodeSymbolsFuel_bounded litLen dist fuel h
        simp only [Bounded] at hb this ⊢
        omega

theorem readStoredBytes_bounded : ∀ (n : Nat) {acc : List UInt8} {r r' : LSBReader}
    {out' : List UInt8}, readStoredBytes acc r n = .ok (out', r') → Bounded acc r out' r'
  | 0, acc, r, r', out', h => by
    simp only [readStoredBytes, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bounded]
    omega
  | n + 1, acc, r, r', out', h => by
    simp only [readStoredBytes] at h
    cases hb : r.readByte with
    | none => rw [hb] at h; cases h
    | some p =>
      obtain ⟨b, r1⟩ := p
      rw [hb] at h
      have := readStoredBytes_bounded n h
      cases h8 : r.readBits 8 with
      | none => simp [LSBReader.readByte, h8] at hb
      | some q =>
        obtain ⟨v, r2⟩ := q
        simp only [LSBReader.readByte, h8, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨_, rfl⟩ := hb
        have h8' := readBits_bitsLeft h8
        simp only [Bounded, List.length_append, List.length_singleton] at this ⊢
        omega

theorem decompressStored_bounded {r r' : LSBReader} {bytes : List UInt8}
    (h : decompressStored r = .ok (bytes, r')) : Bounded [] r bytes r' := by
  unfold decompressStored at h
  dsimp only at h
  split at h
  · cases h
  next len r1 h1 =>
  split at h
  · cases h
  next nlen r2 h2 =>
  split at h
  · cases h
  have hb := readStoredBytes_bounded len h
  have hs1 := readBits_bitsLeft h1
  have hs2 := readBits_bitsLeft h2
  have ha : r.alignToByte.bitsLeft ≤ r.bitsLeft := by
    simp only [LSBReader.alignToByte, LSBReader.bitsLeft]
    omega
  simp only [Bounded] at hb ⊢
  omega

theorem readDynamicTables_bitsLeft {r r' : LSBReader} {lt dt : HuffmanTable}
    (h : readDynamicTables r = .ok (lt, dt, r')) : r'.bitsLeft ≤ r.bitsLeft := by
  have he := Inflate.Stream.ParserPhases.dynamicTables_eval r
  rw [h] at he
  exact Inflate.Stream.Parser.eval_bitsLeft_le _ he

theorem decompressBlockBody_bounded {btype : Nat} {r r' : LSBReader} {out out' : List UInt8}
    (h : decompressBlockBody btype r out = .ok (out', r')) : Bounded out r out' r' := by
  unfold decompressBlockBody at h
  split at h
  · split at h
    · cases h
    next bytes r1 h1 =>
    cases h
    have := decompressStored_bounded h1
    simp only [Bounded, List.length_append, List.length_nil] at this ⊢
    omega
  split at h
  · split at h
    · exact decodeSymbolsFuel_bounded _ _ _ h
    · cases h
  split at h
  · split at h
    · cases h
    next lt dt r1 h1 =>
    have := decodeSymbolsFuel_bounded _ _ _ h
    have := readDynamicTables_bitsLeft h1
    simp only [Bounded] at *
    omega
  · cases h

theorem decompressBlocks_bounded : ∀ (fuel : Nat) {r r' : LSBReader} {out out' : List UInt8},
    decompressBlocks fuel r out = .ok (out', r') → Bounded out r out' r'
  | 0, _, _, _, _, h => by simp [decompressBlocks] at h
  | fuel + 1, r, r', out, out', h => by
    unfold decompressBlocks at h
    split at h
    · cases h
    next bfinal r1 h1 =>
    split at h
    · cases h
    next btype r2 h2 =>
    have hs1 := readBit_bitsLeft h1
    have hs2 := readBits_bitsLeft h2
    split at h
    · cases h
    next o r3 h3 =>
    have hb := decompressBlockBody_bounded h3
    split at h
    · cases h
      simp only [Bounded] at hb ⊢
      omega
    · have := decompressBlocks_bounded fuel h
      simp only [Bounded] at hb this ⊢
      omega

/-- A DEFLATE member consuming `bs.length - rest.length` bytes produces at most
`2064` bytes per consumed byte. -/
theorem deflateTake_output_le {bs out rest : List UInt8} (h : deflateTake bs = .ok (out, rest)) :
    out.length ≤ 2064 * (bs.length - rest.length) := by
  unfold deflateTake at h
  dsimp only at h
  split at h
  · cases h
  next o r' hr =>
  cases h
  have hb := decompressBlocks_bounded _ hr
  simp only [Bounded, LSBReader.bitsLeft, List.length_nil] at hb
  rw [Nat.mul_sub]
  omega

theorem deflateTakeWithHistory_output_le {history bs out rest : List UInt8}
    (h : deflateTakeWithHistory history bs = .ok (out, rest)) :
    out.length ≤ 2064 * (bs.length - rest.length) := by
  unfold deflateTakeWithHistory resultWithHistory at h
  dsimp only at h
  cases hr : decompressBlocks ((⟨0, 0, bs, 0⟩ : LSBReader).bitsLeft + 1) ⟨0, 0, bs, 0⟩ history with
  | error e => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨o, r'⟩ := p
    rw [hr] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb := decompressBlocks_bounded _ hr
    simp only [Bounded, LSBReader.bitsLeft] at hb
    simp only [List.length_drop]
    rw [Nat.mul_sub]
    omega

/-- The whole-buffer `ByteArray` decoder obeys the same bound. -/
theorem decompress_output_le {c d : ByteArray} (h : decompress c = some d) :
    d.size ≤ 2064 * c.size := by
  unfold decompress decompressBlock at h
  split at h
  · cases h
  next o hb =>
  cases h
  split at hb
  · cases hb
  next o' r' hr =>
  cases hb
  have := decompressBlocks_bounded _ hr
  simp only [Bounded, LSBReader.bitsLeft, LSBReader.ofByteArray, List.length_nil] at this
  simp only [ByteArray.size, List.size_toArray, ByteArray_toList_eq, Array.length_toList] at this ⊢
  omega

/-! ## Member decoders and containers -/

/-- A member decoder produces at most `k` bytes per consumed input byte. -/
def OutputLe (d : Decoder) (k : Nat) : Prop :=
  ∀ ⦃bytes out rest : List UInt8⦄, d bytes = some (out, rest) →
    out.length ≤ k * (bytes.length - rest.length)

theorem decoder_outputLe : OutputLe decoder 2064 := fun _ _ _ h =>
  deflateTake_output_le (Proofs.Formats.Compression.Deflate.decoder_eq_some.mp h)

/-- A container whose header and trailer consume prefixes inherits the bound. -/
theorem wrap_outputLe {H : Type} {f : Framing H} {body : Decoder} {k : Nat} (hf : f.Consumes)
    (hb : OutputLe body k) : OutputLe (f.wrap body) k := by
  intro bytes out rest h
  simp only [Framing.wrap] at h
  split at h
  · cases h
  next hd a hhd =>
  split at h
  · cases h
  next o b hbd =>
  split at h
  · cases h
  next r htr =>
  cases h
  have h1 := (hf.1 hhd).length_le
  have h2 := (hf.2 htr).length_le
  exact (hb hbd).trans (Nat.mul_le_mul_left _ (by omega))

theorem membersFuel_le {d : Decoder} {k : Nat} (hc : d.Consumes) (hb : OutputLe d k) :
    ∀ (fuel : Nat) (bytes acc res : List UInt8), d.membersFuel fuel bytes acc = some res →
      res.length ≤ acc.length + k * bytes.length
  | 0, _, _, _, h => by cases h
  | fuel + 1, bytes, acc, res, h => by
    simp only [Decoder.membersFuel] at h
    split at h
    · cases h
    · next out heq =>
      cases h
      have := hb heq
      simp only [List.length_nil, Nat.sub_zero] at this
      simp only [List.length_append]
      omega
    · next out rest _ heq =>
      have ih := membersFuel_le hc hb fuel rest _ _ h
      have hs := (hc heq).length_le
      have ho := hb heq
      have hm : k * rest.length ≤ k * bytes.length := Nat.mul_le_mul_left _ hs
      rw [Nat.mul_sub] at ho
      simp only [List.length_append] at ih
      omega

/-- A multi-member file produces at most `k` bytes per input byte. -/
theorem members_le {d : Decoder} {k : Nat} (hc : d.Consumes) (hb : OutputLe d k)
    {bytes res : List UInt8} (h : d.members bytes = some res) : res.length ≤ k * bytes.length := by
  have := membersFuel_le hc hb _ bytes [] res h
  simpa using this

end Silmaril.Proofs.Formats.Compression.Bounds
