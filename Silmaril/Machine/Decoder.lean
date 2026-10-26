module

public import Silmaril.Machine.Retire

/-!
# Byte decoders for variable-length encodings

A `Decoder` reads one instruction from the front of a byte list and reports how
many bytes it consumed. Its laws say that consumption is positive and within the
input, that the result depends only on the consumed bytes (appending bytes to a
decoded input, or dropping the bytes after the consumed ones, preserves it;
`decode_eq_some_iff_take`), and that the decoder recovers every encoder output
followed by arbitrary bytes. A fetch may therefore read exactly the consumed
bytes.

The decoder may accept encodings that `encode` never produces (for example,
redundant prefixes); only the encoder direction is a round trip. For arbitrary
bytes, `decodeBlock_sound` and `decodeAll_sound` show only that each decoded
entry is accepted at its offset. `none` means
that the bytes are outside the decoder's supported subset, not an architectural
fault. Fetch from memory, permissions, alignment, and fault behavior are not part
of this contract.
-/

@[expose] public section

namespace Silmaril.Machine

universe u v w x

/-- A byte decoder paired with an encoder that it recovers. -/
structure Decoder (Instr : Type u) where
  /-- Decode one instruction from the front of the bytes, with its byte length. -/
  decode : List (BitVec 8) → Option (Instr × Nat)
  encode : Instr → List (BitVec 8)
  decode_length_pos : ∀ {bytes instr length}, decode bytes = some (instr, length) → 0 < length
  decode_length_le : ∀ {bytes instr length}, decode bytes = some (instr, length) →
    length ≤ bytes.length
  decode_append : ∀ {bytes instr length} (extra : List (BitVec 8)),
    decode bytes = some (instr, length) → decode (bytes ++ extra) = some (instr, length)
  decode_take : ∀ {bytes instr length}, decode bytes = some (instr, length) →
    decode (bytes.take length) = some (instr, length)
  decode_encode_append : ∀ instr rest,
    decode (encode instr ++ rest) = some (instr, (encode instr).length)

namespace Decoder

variable {Instr : Type u} (decoder : Decoder Instr)

@[simp] theorem decode_encode (instr : Instr) :
    decoder.decode (decoder.encode instr) = some (instr, (decoder.encode instr).length) := by
  simpa using decoder.decode_encode_append instr []

/-- Decoding succeeds exactly when the consumed bytes are present and decode
on their own: the bytes after them are irrelevant. -/
theorem decode_eq_some_iff_take {bytes : List (BitVec 8)} {instr : Instr} {length : Nat} :
    decoder.decode bytes = some (instr, length) ↔
      length ≤ bytes.length ∧ decoder.decode (bytes.take length) = some (instr, length) := by
  constructor
  · intro h
    exact ⟨decoder.decode_length_le h, decoder.decode_take h⟩
  · rintro ⟨-, h⟩
    have := decoder.decode_append (bytes.drop length) h
    rwa [List.take_append_drop] at this

theorem encode_length_pos (instr : Instr) : 0 < (decoder.encode instr).length :=
  decoder.decode_length_pos (decoder.decode_encode instr)

theorem encode_ne_nil (instr : Instr) : decoder.encode instr ≠ [] :=
  List.ne_nil_of_length_pos (decoder.encode_length_pos instr)

/-- Encodings are prefix-free: an encoded instruction followed by any bytes
determines both the instruction and the remaining bytes. -/
theorem encode_append_inj {first second : Instr} {firstRest secondRest : List (BitVec 8)}
    (h : decoder.encode first ++ firstRest = decoder.encode second ++ secondRest) :
    first = second ∧ firstRest = secondRest := by
  have hd := decoder.decode_encode_append first firstRest
  rw [h, decoder.decode_encode_append] at hd
  obtain ⟨hinstr, -⟩ := Prod.mk.inj (Option.some.inj hd)
  subst hinstr
  exact ⟨rfl, List.append_cancel_left h⟩

theorem encode_injective : Function.Injective decoder.encode := by
  intro first second h
  exact (decoder.encode_append_inj (firstRest := []) (secondRest := [])
    (by simpa using h)).1

/-- Encoding of a straight-line block, without padding between instructions. -/
def encodeBlock (code : List Instr) : List (BitVec 8) := code.flatMap decoder.encode

@[simp] theorem encodeBlock_nil : decoder.encodeBlock [] = [] := rfl

@[simp] theorem encodeBlock_cons (instr : Instr) (rest : List Instr) :
    decoder.encodeBlock (instr :: rest) = decoder.encode instr ++ decoder.encodeBlock rest := by
  simp [encodeBlock]

theorem encodeBlock_append (first second : List Instr) :
    decoder.encodeBlock (first ++ second) =
      decoder.encodeBlock first ++ decoder.encodeBlock second := by
  simp [encodeBlock]

/-- The byte length of a block is the sum of its instructions' encoded lengths. -/
theorem encodeBlock_length (code : List Instr) :
    (decoder.encodeBlock code).length = (code.map fun instr => (decoder.encode instr).length).sum := by
  induction code with
  | nil => rfl
  | cons instr rest ih => simp [ih]

theorem length_le_encodeBlock_length (code : List Instr) :
    code.length ≤ (decoder.encodeBlock code).length := by
  induction code with
  | nil => simp
  | cons instr rest ih =>
    have := decoder.encode_length_pos instr
    simp only [encodeBlock_cons, List.length_append, List.length_cons]
    omega

/-- The byte offset of instruction `index` within an encoded block. -/
def offset (code : List Instr) (index : Nat) : Nat := (decoder.encodeBlock (code.take index)).length

/-- Decoding at an instruction's offset recovers that instruction and its length. -/
theorem decode_drop_offset (code : List Instr) (index : Nat) (bound : index < code.length) :
    decoder.decode ((decoder.encodeBlock code).drop (decoder.offset code index)) =
      some (code[index], (decoder.encode code[index]).length) := by
  have split : decoder.encodeBlock code = decoder.encodeBlock (code.take index) ++
      (decoder.encode code[index] ++ decoder.encodeBlock (code.drop (index + 1))) := by
    conv => lhs; rw [← List.take_append_drop index code, List.drop_eq_getElem_cons bound]
    rw [encodeBlock_append, encodeBlock_cons]
  rw [split, offset, List.drop_left, decode_encode_append]

/-- Instructions paired with their byte offsets from `base`. -/
def layout : Nat → List Instr → List (Nat × Instr)
  | _, [] => []
  | base, instr :: rest => (base, instr) :: layout (base + (decoder.encode instr).length) rest

@[simp] theorem layout_nil (base : Nat) : decoder.layout base [] = [] := rfl

@[simp] theorem layout_cons (base : Nat) (instr : Instr) (rest : List Instr) :
    decoder.layout base (instr :: rest) =
      (base, instr) :: decoder.layout (base + (decoder.encode instr).length) rest := rfl

@[simp] theorem layout_length (base : Nat) (code : List Instr) :
    (decoder.layout base code).length = code.length := by
  induction code generalizing base with
  | nil => rfl
  | cons instr rest ih => simp [ih]

@[simp] theorem layout_map_snd (base : Nat) (code : List Instr) :
    (decoder.layout base code).map Prod.snd = code := by
  induction code generalizing base with
  | nil => rfl
  | cons instr rest ih => simp [ih]

/-- Each layout entry records the instruction at the corresponding block offset. -/
theorem layout_getElem (base : Nat) (code : List Instr) (index : Nat)
    (bound : index < (decoder.layout base code).length) :
    (decoder.layout base code)[index] =
      (base + decoder.offset code index, code[index]'(by simpa using bound)) := by
  induction code generalizing base index with
  | nil => simp at bound
  | cons instr rest ih =>
    cases index with
    | zero => simp [offset]
    | succ index =>
      simp only [layout_cons, List.getElem_cons_succ, offset, List.take_succ_cons,
        encodeBlock_cons, List.length_append]
      rw [ih]
      simp only [offset, Prod.mk.injEq, and_true]
      omega

/--
Decode successive instructions, recording each instruction's byte offset from
`base`. `fuel` bounds the number of instructions; `none` means that some
position failed to decode or the fuel ran out before the bytes did.
-/
def decodeBlock : Nat → Nat → List (BitVec 8) → Option (List (Nat × Instr))
  | _, _, [] => some []
  | 0, _, _ :: _ => none
  | fuel + 1, base, byte :: bytes =>
    match decoder.decode (byte :: bytes) with
    | none => none
    | some (instr, length) =>
      (decodeBlock fuel (base + length) ((byte :: bytes).drop length)).map
        ((base, instr) :: ·)

@[simp] theorem decodeBlock_nil (fuel base : Nat) : decoder.decodeBlock fuel base [] = some [] := by
  cases fuel <;> rfl

/-- Sequential decoding of an encoded block recovers the block and its offsets,
given at least one unit of fuel per instruction. -/
theorem decodeBlock_encodeBlock (code : List Instr) (fuel base : Nat) (enough : code.length ≤ fuel) :
    decoder.decodeBlock fuel base (decoder.encodeBlock code) = some (decoder.layout base code) := by
  induction code generalizing fuel base with
  | nil => simp
  | cons instr rest ih =>
    obtain ⟨fuel, rfl⟩ : ∃ previous, fuel = previous + 1 :=
      ⟨fuel - 1, by simp only [List.length_cons] at enough; omega⟩
    obtain ⟨byte, bytes, hbytes⟩ : ∃ byte bytes,
        decoder.encodeBlock (instr :: rest) = byte :: bytes := by
      cases h : decoder.encodeBlock (instr :: rest) with
      | nil =>
        have := congrArg List.length h
        simp only [encodeBlock_cons, List.length_append, List.length_nil] at this
        have := decoder.encode_length_pos instr
        omega
      | cons byte bytes => exact ⟨byte, bytes, rfl⟩
    rw [hbytes, decodeBlock, ← hbytes, encodeBlock_cons, decode_encode_append]
    simp only [List.drop_left]
    rw [ih fuel _ (by simp only [List.length_cons] at enough; omega)]
    rfl

/-- Soundness of sequential decoding for arbitrary bytes: every recorded entry
is at or after `base`, and the decoder accepts the instruction at the entry's
offset. The decoder may accept non-canonical encodings, so the bytes need not be
the encoder's output. -/
theorem decodeBlock_sound {fuel base : Nat} {bytes : List (BitVec 8)}
    {entries : List (Nat × Instr)} (h : decoder.decodeBlock fuel base bytes = some entries) :
    ∀ entry ∈ entries, base ≤ entry.1 ∧
      ∃ length, decoder.decode (bytes.drop (entry.1 - base)) = some (entry.2, length) := by
  induction fuel generalizing base bytes entries with
  | zero =>
    cases bytes with
    | nil =>
      simp only [decodeBlock_nil, Option.some.injEq] at h
      subst h
      simp
    | cons => cases h
  | succ fuel ih =>
    cases bytes with
    | nil =>
      simp only [decodeBlock_nil, Option.some.injEq] at h
      subst h
      simp
    | cons byte bytes =>
      simp only [decodeBlock] at h
      split at h
      next => cases h
      next instr length hdecode =>
        obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.mp h
        intro entry hentry
        rcases List.mem_cons.mp hentry with rfl | hentry
        · exact ⟨Nat.le_refl _, length, by simpa using hdecode⟩
        · obtain ⟨hle, length', hd⟩ := ih hrest entry hentry
          refine ⟨by omega, length', ?_⟩
          rw [List.drop_drop] at hd
          rwa [show length + (entry.1 - (base + length)) = entry.1 - base by omega] at hd

/-- Decode a whole byte list, with one unit of fuel per byte. -/
def decodeAll (bytes : List (BitVec 8)) : Option (List (Nat × Instr)) :=
  decoder.decodeBlock bytes.length 0 bytes

/-- Every entry of a successful whole-list decode is accepted by the decoder at
its offset. -/
theorem decodeAll_sound {bytes : List (BitVec 8)} {entries : List (Nat × Instr)}
    (h : decoder.decodeAll bytes = some entries) :
    ∀ entry ∈ entries, ∃ length, decoder.decode (bytes.drop entry.1) = some (entry.2, length) :=
  fun entry hentry => by
    simpa using (decoder.decodeBlock_sound h entry hentry).2

theorem decodeAll_encodeBlock (code : List Instr) :
    decoder.decodeAll (decoder.encodeBlock code) = some (decoder.layout 0 code) :=
  decoder.decodeBlock_encodeBlock code _ 0 (decoder.length_le_encodeBlock_length code)

/-- With the retirement model's PC advance equal to the encoded length, the PC
after a block advances by the block's byte length, modulo `2^64`. -/
theorem run_pc_encodeBlock {State : Type v} {Reg : Type w} {Word : Type x}
    (model : RetireModel Instr State Reg Word)
    (delta : ∀ instr, model.pcDelta instr = (decoder.encode instr).length)
    (code : List Instr) (state : State) :
    model.pc (Block.run model.step code state) =
      model.pc state + BitVec.ofNat 64 (decoder.encodeBlock code).length := by
  have size : model.size code = (decoder.encodeBlock code).length := by
    induction code with
    | nil => rfl
    | cons instr rest ih => simp [ih, delta]
  rw [model.run_pc, size]

end Decoder
end Silmaril.Machine
