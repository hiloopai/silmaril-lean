module

public import Silmaril.Formats.Compression.Deflate.StoredWriter
public import Silmaril.Raw.Formats.Compression.Deflate.Stored

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Deflate.StoredWriter`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate.StoredWriter

@[simp] theorem headerByte_false : headerByte false = 0 := rfl
@[simp] theorem headerByte_true : headerByte true = 1 := rfl

@[simp] theorem headerBytes_length (final : Bool) (len : Nat) :
    (headerBytes final len).length = 5 := by
  simp [headerBytes, storedLenBytes]

theorem storedBlockBytes_eq (final : Bool) (chunk : List UInt8) :
    storedBlockBytes final chunk = headerBytes final chunk.length ++ chunk := by
  rfl

@[simp] theorem storedBlockBytes_length (final : Bool) (chunk : List UInt8) :
    (storedBlockBytes final chunk).length = chunk.length + 5 := by
  simp [storedBlockBytes_eq, Nat.add_comm]

/-- A final stored block decodes independently of any following trailer bytes. -/
theorem deflateTake_final (chunk trailer : List UInt8)
    (h : chunk.length ≤ storedMax) :
    deflateTake (headerBytes true chunk.length ++ chunk ++ trailer) =
      .ok (chunk, trailer) := by
  have hb : storedBytes chunk = storedBlockBytes true chunk := by
    rw [storedBytes]
    simp only [h, ↓reduceDIte]
  simpa only [hb, storedBlockBytes_eq, List.append_assoc] using
    deflateTake_storedBytes chunk trailer

theorem appendBlock_eq (pending chunk : List UInt8) (final : Bool) :
    appendBlock pending final chunk = pending ++ storedBlockBytes final chunk := by
  rfl

@[simp] theorem appendBlock_length (pending chunk : List UInt8) (final : Bool) :
    (appendBlock pending final chunk).length = pending.length + 5 + chunk.length := by
  simp [appendBlock, Nat.add_assoc]

/-- Bytes already pending are a prefix of the writer's output. -/
theorem appendBlock_prefix (pending chunk : List UInt8) (final : Bool) :
    pending <+: appendBlock pending final chunk := by
  exact ⟨_, rfl⟩

/-- Appending a block commutes with framing an earlier pending prefix. -/
theorem appendBlock_frame (frame pending chunk : List UInt8) (final : Bool) :
    appendBlock (frame ++ pending) final chunk = frame ++ appendBlock pending final chunk := by
  simp [appendBlock, List.append_assoc]

/-- Arbitrary partitions pay exactly five header bytes per emitted block. -/
theorem blocksBytes_length (chunks : List (List UInt8)) :
    (blocksBytes chunks).length = chunks.flatten.length + 5 * blockCount chunks := by
  induction chunks with
  | nil => simp [blocksBytes, blockCount]
  | cons chunk rest ih =>
    cases rest with
    | nil => simp [blocksBytes, blockCount]
    | cons next tail =>
      simp only [blocksBytes, List.cons_ne_nil, ↓reduceIte, List.length_append,
        storedBlockBytes_length, List.flatten_cons] at *
      simp only [blockCount, List.length_cons] at *
      omega

/-- Decode arbitrary bounded blocks, including noncanonical streaming
partitions. The accumulated output and following bytes are preserved exactly. -/
theorem decompressBlocks_blocksBytes (chunks : List (List UInt8)) (h : Valid chunks)
    (fuel : Nat) (trailer out : List UInt8) (t : Nat)
    (hfuel : blockCount chunks ≤ fuel) :
    ∃ t', decompressBlocks fuel ⟨0, 0, blocksBytes chunks ++ trailer, t⟩ out =
      .ok (out ++ chunks.flatten, ⟨0, 0, trailer, t'⟩) := by
  induction chunks generalizing fuel out t with
  | nil =>
    have hf : 1 ≤ fuel := by simpa [blockCount] using hfuel
    obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    refine ⟨t + 1 + 2 + 5 + 16 + 16, ?_⟩
    simpa [blocksBytes] using
      decompressBlocks_step true [] trailer out t f (by simp [storedMax])
  | cons chunk rest ih =>
    have hc : chunk.length ≤ storedMax := h chunk (by simp)
    have hr : Valid rest := by
      intro c hm
      exact h c (by simp [hm])
    have hf : 1 ≤ fuel := by
      simp only [blockCount, List.length_cons] at hfuel
      omega
    obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    cases rest with
    | nil =>
      refine ⟨t + 1 + 2 + 5 + 16 + 16 + 8 * chunk.length, ?_⟩
      simpa [blocksBytes] using decompressBlocks_step true chunk trailer out t f hc
    | cons next tail =>
      have hf' : blockCount (next :: tail) ≤ f := by
        simp only [blockCount, List.length_cons] at hfuel ⊢
        omega
      obtain ⟨t', ht'⟩ := ih hr f (out ++ chunk)
        (t + 1 + 2 + 5 + 16 + 16 + 8 * chunk.length) hf'
      refine ⟨t', ?_⟩
      simp only [blocksBytes, List.cons_ne_nil, ↓reduceIte, List.append_assoc]
      rw [decompressBlocks_step false chunk _ out t f hc]
      simpa only [blocksBytes, Bool.false_eq_true, ↓reduceIte, List.flatten_cons,
        List.append_assoc] using ht'

/-- The independent DEFLATE decoder accepts every bounded partition and
returns exactly its flattened payload and the untouched trailer. -/
theorem deflateTake_blocksBytes (chunks : List (List UInt8)) (h : Valid chunks)
    (trailer : List UInt8) :
    deflateTake (blocksBytes chunks ++ trailer) = .ok (chunks.flatten, trailer) := by
  have hlen := blocksBytes_length chunks
  have hfuel : blockCount chunks ≤
      (LSBReader.bitsLeft ⟨0, 0, blocksBytes chunks ++ trailer, 0⟩) + 1 := by
    simp only [LSBReader.bitsLeft, List.length_append]
    omega
  obtain ⟨t', ht'⟩ := decompressBlocks_blocksBytes chunks h _ trailer [] 0 hfuel
  rw [deflateTake]
  dsimp only
  rw [ht']
  simp

/-- The raw DEFLATE interface also accepts the bytes of any bounded partition.
This is a semantic contract, rather than equality with a particular encoder's
choice of block boundaries. -/
theorem decompress_blocksBytes (chunks : List (List UInt8)) (h : Valid chunks) :
    decompress ⟨(blocksBytes chunks).toArray⟩ = some ⟨chunks.flatten.toArray⟩ := by
  have hbs : LSBReader.ofByteArray ⟨(blocksBytes chunks).toArray⟩ =
      ⟨0, 0, blocksBytes chunks ++ [], 0⟩ := by
    simp [LSBReader.ofByteArray, ByteArray_toList_eq]
  have hd := deflateTake_blocksBytes chunks h []
  rw [deflateTake] at hd
  dsimp only at hd
  simp only [decompress, decompressBlock]
  rw [hbs]
  revert hd
  cases he : decompressBlocks
      (LSBReader.bitsLeft ⟨0, 0, blocksBytes chunks ++ [], 0⟩ + 1)
      ⟨0, 0, blocksBytes chunks ++ [], 0⟩ [] with
  | error e => intro hd; simp at hd
  | ok p =>
    intro hd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hd
    simp [hd.1]

end Silmaril.Formats.Compression.Deflate.StoredWriter
