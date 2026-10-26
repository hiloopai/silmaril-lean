module

public import Silmaril.Process.CLI.Sha256

/-! # SHA driver invariants, independent of instruction coverage

These are source/trace lemmas for `apps/sha256-cli/src/sha256.c`, not a
functional proof of its machine code. The write-loop invariant covers arbitrary
short writes, zero transfers and errors. It retains complete input and an
explicit EOF event; offset 64 is not success (the newline is still pending).
Connecting the invariants to the decoded read/padding/hex/write loops is residual.
No lemma assumes termination or turns an unsupported instruction into a crash.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.Driver

open Silmaril.Process.Syscall
open Silmaril.Process.CLI

/-- The source read loop has consumed full blocks followed by a partial block.
This is a byte accounting invariant, with no unproved compression assertion. -/
structure ReadInv (consumed : List Byte) (blocks : List (List Byte)) (tail : List Byte) : Prop where
  bytes : consumed = blocks.flatten ++ tail
  full : ∀ block ∈ blocks, block.length = 64
  room : tail.length < 64

theorem read_init : ReadInv [] [] [] := ⟨rfl, by simp, by decide⟩

theorem ReadInv.short {consumed : List Byte} {blocks : List (List Byte)} {tail : List Byte}
    (h : ReadInv consumed blocks tail) (chunk : List Byte)
    (short : tail.length + chunk.length < 64) :
    ReadInv (consumed ++ chunk) blocks (tail ++ chunk) := by
  refine ⟨?_, h.full, ?_⟩
  · rw [h.bytes, List.append_assoc]
  · simpa only [List.length_append] using short

theorem ReadInv.flush {consumed : List Byte} {blocks : List (List Byte)} {tail : List Byte}
    (h : ReadInv consumed blocks tail) (chunk : List Byte)
    (filled : tail.length + chunk.length = 64) :
    ReadInv (consumed ++ chunk) (blocks ++ [tail ++ chunk]) [] := by
  refine ⟨?_, ?_, by decide⟩
  · simp only [h.bytes, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.append_assoc]
  · intro block member
    rcases List.mem_append.mp member with old | new
    · exact h.full block old
    · have eq := List.mem_singleton.mp new
      subst block
      simpa only [List.length_append] using filled

/-- The C source always requests a positive count before interpreting `read = 0`
as EOF. `CLI.SawEof` alone does not distinguish zero-count requests. -/
theorem ReadInv.read_count_positive {consumed : List Byte} {blocks : List (List Byte)}
    {tail : List Byte} (h : ReadInv consumed blocks tail) : 0 < 64 - tail.length := by
  have := h.room
  omega

/-- Each accounting block is exactly one compression call's 64-byte input. -/
theorem ReadInv.block_bytes {consumed : List Byte} {blocks : List (List Byte)}
    {tail : List Byte} (h : ReadInv consumed blocks tail) :
    blocks.flatten.length = 64 * blocks.length := by
  have full := h.full
  clear h
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    have size := full block (by simp)
    have rest := ih (fun b hb => full b (by simp [hb]))
    simp only [List.flatten_cons, List.length_append, List.length_cons, size, rest]
    omega

theorem ReadInv.remainder {consumed : List Byte} {blocks : List (List Byte)}
    {tail : List Byte} (h : ReadInv consumed blocks tail) :
    consumed.length % 64 = tail.length := by
  have count : consumed.length = 64 * blocks.length + tail.length := by
    rw [h.bytes, List.length_append, h.block_bytes]
  rw [count, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt h.room]
  exact Nat.mod_eq_of_lt h.room

/-- The source's one/two-block padding branch uses the specification's exact
zero count. This does not yet connect C stores or the length-field bytes. -/
theorem ReadInv.padding_zeros {consumed : List Byte} {blocks : List (List Byte)}
    {tail : List Byte} (h : ReadInv consumed blocks tail) :
    Silmaril.Crypto.paddingZeroCount consumed.length =
      if tail.length + 1 > 56 then (64 - (tail.length + 1)) + 56
      else 56 - (tail.length + 1) := by
  rw [Silmaril.Crypto.paddingZeroCount, h.remainder]
  have := h.room
  split_ifs <;> omega

/-- One abstract compression call, using the existing SHA specification. -/
def compressBlock (state : Silmaril.Crypto.SHA256.State) (block : List Byte) :
    Silmaril.Crypto.SHA256.State :=
  Silmaril.Crypto.SHA256.processBlock state
    (Silmaril.Crypto.SHA256.parseBlock (block.map UInt8.ofBitVec))

/-- Strengthen byte accounting with the actual compression state. The machine
callee contract must establish each `compressBlock` transition separately. -/
structure StreamInv (consumed : List Byte) (blocks : List (List Byte)) (tail : List Byte)
    (state : Silmaril.Crypto.SHA256.State) : Prop extends ReadInv consumed blocks tail where
  hash : state = blocks.foldl compressBlock Silmaril.Crypto.SHA256.H0

theorem stream_init : StreamInv [] [] [] Silmaril.Crypto.SHA256.H0 := ⟨read_init, rfl⟩

theorem StreamInv.short {consumed : List Byte} {blocks : List (List Byte)} {tail : List Byte}
    {state : Silmaril.Crypto.SHA256.State} (h : StreamInv consumed blocks tail state)
    (chunk : List Byte) (short : tail.length + chunk.length < 64) :
    StreamInv (consumed ++ chunk) blocks (tail ++ chunk) state :=
  ⟨h.toReadInv.short chunk short, h.hash⟩

/-- A full source buffer advances exactly one compression fold step. No
cryptographic recomputation or proof search is needed. -/
theorem StreamInv.flush {consumed : List Byte} {blocks : List (List Byte)} {tail : List Byte}
    {state : Silmaril.Crypto.SHA256.State} (h : StreamInv consumed blocks tail state)
    (chunk : List Byte) (filled : tail.length + chunk.length = 64) :
    StreamInv (consumed ++ chunk) (blocks ++ [tail ++ chunk]) []
      (compressBlock state (tail ++ chunk)) := by
  refine ⟨h.toReadInv.flush chunk filled, ?_⟩
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [h.hash]

/-- Canonical padded block sequence of the existing digest specification.
Proving that the C read/padding stores produce this sequence remains separate. -/
def paddedBlocks (message : List Byte) : List (List Byte) :=
  let padded := Silmaril.Crypto.paddingMD (message.map UInt8.ofBitVec)
  (List.range (padded.length / 64)).map fun i =>
    ((padded.drop (64 * i)).take 64).map UInt8.toBitVec

/-- The stream fold uses the existing hash specification, not a second hash
algorithm. This proof only normalizes the block representation. -/
theorem fold_paddedBlocks (message : List Byte) :
    (paddedBlocks message).foldl compressBlock Silmaril.Crypto.SHA256.H0 =
      Silmaril.Crypto.SHA256.hash (message.map UInt8.ofBitVec) := by
  simp only [paddedBlocks, List.foldl_map, compressBlock, List.map_map,
    Function.comp_def, UInt8.ofBitVec_toBitVec, List.map_id', Silmaril.Crypto.SHA256.hash]

theorem StreamInv.final_hash {consumed message : List Byte} {blocks : List (List Byte)}
    {state : Silmaril.Crypto.SHA256.State} (h : StreamInv consumed blocks [] state)
    (padding : blocks = paddedBlocks message) :
    state = Silmaril.Crypto.SHA256.hash (message.map UInt8.ofBitVec) := by
  rw [h.hash, padding, fold_paddedBlocks]

/-- During output, the bytes accepted so far are exactly `take off` of the
canonical answer. The hash-to-buffer equality is an explicit obligation here. -/
structure OutputInv (message : List Byte) (events : List Event) (off : Nat) : Prop where
  input : stdinRead events = message
  eof : SawEof 0 events
  only : WritesOnlyTo [1] events
  output : stdout events = (Sha256.expected message).take off
  bound : off ≤ 65

theorem OutputInv.start {message : List Byte} {events : List Event}
    (input : stdinRead events = message) (eof : SawEof 0 events)
    (only : WritesOnlyTo [1] events) (silent : stdout events = []) :
    OutputInv message events 0 := ⟨input, eof, only, by simpa, by decide⟩

/-- Accepted-byte accounting for one short write, including an accepted empty
write. The OS request/return binding remains the caller's obligation. -/
theorem OutputInv.write {message : List Byte} {events : List Event} {off : Nat}
    (h : OutputInv message events off) (n : Nat) (fits : n ≤ 65 - off) :
    OutputInv message
      (events ++ [.write 1 (((Sha256.expected message).drop off).take n)]) (off + n) := by
  refine ⟨?_, ?_, ?_, ?_, by have := h.bound; omega⟩
  · simpa [stdinRead, readOn_append, readOn] using h.input
  · exact List.mem_append_left _ h.eof
  · intro fd bytes member
    rcases List.mem_append.mp member with old | new
    · exact h.only fd bytes old
    · have eq := List.mem_singleton.mp new
      cases eq
      simp
  · change writtenOn 1 _ = _
    rw [writtenOn_append]
    simp only [writtenOn, List.append_nil]
    change stdout events ++ ((Sha256.expected message).drop off).take n = _
    rw [h.output, ← List.take_add]

/-- An error changes no accepted bytes. A caller may stop, crash, or block
after this point without invalidating prefix safety. No retry is assumed. -/
theorem OutputInv.error {message : List Byte} {events : List Event} {off : Nat}
    (h : OutputInv message events off) (request : Request) (errno : Errno) :
    OutputInv message (events ++ [.error request errno]) off := by
  refine ⟨?_, List.mem_append_left _ h.eof, ?_, ?_, h.bound⟩
  · simpa [stdinRead, readOn_append, readOn] using h.input
  · intro fd bytes member
    have old : Event.write fd bytes ∈ events := by simpa using member
    exact h.only fd bytes old
  · simpa [stdout, writtenOn_append, writtenOn] using h.output

theorem OutputInv.prefix {input : ProcInput} {message : List Byte} {events : List Event}
    {off : Nat} (h : OutputInv message events off)
    (finite : input.stdin = .ofList message) : Sha256.PrefixOk input events := by
  refine ⟨h.only, .inr ⟨message, finite, ?_⟩⟩
  rw [h.output]
  exact List.take_prefix _ _

theorem OutputInv.success {input : ProcInput} {message : List Byte} {events : List Event}
    (h : OutputInv message events 65) (finite : input.stdin = .ofList message) :
    Sha256.Success input events := by
  refine ⟨message, finite, h.input, h.eof, ?_⟩
  simpa only [← Sha256.expected_length message, List.take_length] using h.output

/-- A missing newline (or any earlier short result) cannot count as success. -/
theorem OutputInv.incomplete {input : ProcInput} {message : List Byte} {events : List Event}
    {off : Nat} (h : OutputInv message events off) (short : off < 65) :
    ¬ Sha256.Success input events := by
  rintro ⟨other, _, _, _, exactOutput⟩
  have count := congrArg List.length exactOutput
  rw [h.output, List.length_take, Sha256.expected_length, Sha256.expected_length] at count
  omega

/-- Hex is formatted byte by byte; no digest computation or proof search is
needed when the driver has produced the canonical 32 digest bytes. -/
theorem hex_append (first second : List UInt8) :
    (first ++ second).flatMap Sha256.hexByte =
      first.flatMap Sha256.hexByte ++ second.flatMap Sha256.hexByte :=
  List.flatMap_append

/-- The C driver's lookup table agrees with the shared lowercase digit
specification at every index the nibble operations may produce. -/
theorem hexDigit_table : ∀ n : Fin 16,
    ([0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
      0x38, 0x39, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66] : List Byte)[n.val]? =
        some (Sha256.hexDigit n.val) := by decide

end Silmaril.Process.CLI.Sha256Cli.Driver
