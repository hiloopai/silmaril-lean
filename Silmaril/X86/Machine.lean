module

public import Silmaril.X86.Stack
public import Silmaril.Machine.Execution

/-!
# A memory-backed fetch/decode/execute machine for the x86-64 subset

`MState` pairs the register state with a `Process.Memory`. One `MState.step`
fetches at RIP, decodes one `Insn` and executes it. This is a handwritten local model
of a single sequential user-mode thread; it is not derived from, or proved to
correspond with, the Sail, ACL2 or any hardware description.

## Fetch policy

A 15-byte executable window is not required. The fetcher collects the
*available* bytes: the longest run, of at most `maxInstrLength` bytes starting at
RIP, of bytes each of which is mapped executable, below `2^64` and backed
(`fetchWindow`). The decoder runs on that window, and the fetch then requires
execute permission on exactly the consumed span. `fetch_eq_decoded_iff` shows
that this is the same as decoding exactly the consumed bytes, obtained from one
checked `fetchBytes` of that span; an instruction whose own bytes are executable
is therefore fetched whatever follows it.

A failed decode is classified from the available bytes alone:

* `Fetch.truncated`: some extension of the available bytes decodes. The
  available bytes are then a proper prefix of a supported encoding, and the next
  byte cannot be fetched (`fetch_truncated`). This is reported as a fetch fault.
* `Fetch.undecodable`: no extension decodes (`fetch_undecodable_iff`). These
  bytes are outside the supported canonical subset; they may be invalid
  encodings or valid instructions that the model does not cover.

The classification quantifies over all extensions of the available bytes; it is
computed by decoding them once more after a fixed structural `completion`, which
`exists_decode_iff_completion` proves equivalent. `fetch` and `step` are
therefore executable.

## Outcomes

`MState.step exit` reports a retired instruction, an unsupported or invalid
encoding, a fetch fault, a data-memory fault of a stack access, or `returned`
when a RET pops exactly the designated return address `exit`. Fault outcomes
carry no successor state, and a faulting instruction has no partial effect.
`MState.stepOpt exit` keeps only retirements, for use with
`Machine.Execution.run`; `MState.Returns` is a finite run of retirements
followed by a return.

Fetch reads the current memory, so a store to executable memory is visible to
the next fetch; the hardware rules for cross-modifying code and instruction-fetch
synchronization are not modeled. Also not modeled: canonical-address checks,
paging and translation, alignment checks, interrupts and exceptions as
architectural events, concurrency, and the ABI stack alignment requirement
(which is neither checked nor needed by the proofs here).
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.Process (Memory)

/-- The register state and memory of one user-mode thread. -/
structure MState where
  core : State
  memory : Memory

/-- The architectural limit on x86 instruction length. Every encoding in `Insn`
has at most seven bytes (`Insn.length_le`). -/
def maxInstrLength : Nat := 15

/-! ## Checked byte accesses -/

namespace Memory

/-- A checked access succeeds exactly when the span is permitted and backed. -/
theorem readWith_eq_some_iff {memory : Memory} {access : Process.Access} {address length : Nat}
    {bytes : List Byte} :
    memory.readWith access address length = some bytes ↔
      bytes.length = length ∧ memory.Permitted access address length ∧
        ∀ index (bound : index < bytes.length),
          memory.bytes.get? (address + index) = some (bytes[index]) := by
  constructor
  · intro h
    exact ⟨Memory.readWith_length h, Memory.readWith_permitted h,
      fun index bound => Memory.readWith_get h index bound⟩
  · rintro ⟨rfl, permitted, installed⟩
    exact Memory.readWith_eq memory access address bytes permitted installed

/-- A nonempty sub-span of a successful access succeeds with the corresponding bytes. -/
theorem readWith_slice {memory : Memory} {access : Process.Access} {address length : Nat}
    {bytes : List Byte} (h : memory.readWith access address length = some bytes)
    (offset count : Nat) (positive : 0 < count) (bound : offset + count ≤ length) :
    memory.readWith access (address + offset) count = some ((bytes.drop offset).take count) := by
  obtain ⟨hlen, permitted, installed⟩ := readWith_eq_some_iff.mp h
  rw [Memory.Permitted, Memory.checkSpan_iff] at permitted
  obtain ⟨start, limit, perm⟩ := permitted
  refine readWith_eq_some_iff.mpr ⟨by simp; omega, ?_, ?_⟩
  · rw [Memory.Permitted, Memory.checkSpan_iff]
    refine ⟨by omega, by omega, fun k hk => ?_⟩
    have := perm (offset + k) (by omega)
    rwa [Nat.add_assoc]
  · intro index hindex
    simp only [List.length_take, List.length_drop] at hindex
    have := installed (offset + index) (by omega)
    simp only [List.getElem_take, List.getElem_drop]
    rwa [Nat.add_assoc]

/-- Two adjacent successful accesses combine. -/
theorem readWith_cons {memory : Memory} {access : Process.Access} {address length : Nat}
    {byte : Byte} {bytes : List Byte} (first : memory.readWith access address 1 = some [byte])
    (rest : memory.readWith access (address + 1) length = some bytes) :
    memory.readWith access address (length + 1) = some (byte :: bytes) := by
  obtain ⟨-, p1, i1⟩ := readWith_eq_some_iff.mp first
  obtain ⟨hlen, p2, i2⟩ := readWith_eq_some_iff.mp rest
  rw [Memory.Permitted, Memory.checkSpan_iff] at p1 p2
  refine readWith_eq_some_iff.mpr ⟨by simp [hlen], ?_, ?_⟩
  · rw [Memory.Permitted, Memory.checkSpan_iff]
    refine ⟨p1.1, by omega, fun k hk => ?_⟩
    cases k with
    | zero => simpa using p1.2.2 0 (by omega)
    | succ k =>
      have := p2.2.2 k (by omega)
      rwa [Nat.add_assoc, Nat.add_comm 1 k] at this
  · intro index hindex
    cases index with
    | zero => simpa using i1 0 (by simp)
    | succ k =>
      have := i2 k (by simp at hindex; omega)
      simp only [List.getElem_cons_succ]
      rwa [Nat.add_assoc, Nat.add_comm 1 k] at this

end Memory

/-! ## Available instruction bytes -/

/-- The longest run, of at most `limit` bytes from `address`, of bytes that can
each be fetched: mapped executable, below `2^64` and backed. Reading stops at the
first byte that cannot be fetched; that byte does not fault. -/
def fetchWindow (memory : Memory) : Nat → Nat → List Byte
  | 0, _ => []
  | limit + 1, address =>
    match memory.fetchBytes address 1 with
    | some [byte] => byte :: fetchWindow memory limit (address + 1)
    | _ => []

theorem fetchWindow_length_le (memory : Memory) (limit address : Nat) :
    (fetchWindow memory limit address).length ≤ limit := by
  induction limit generalizing address with
  | zero => simp [fetchWindow]
  | succ limit ih =>
    simp only [fetchWindow]
    split
    · simpa using ih (address + 1)
    · simp

/-- Every byte string that can be fetched as a whole starts the window. -/
theorem fetchBytes_prefix_fetchWindow {memory : Memory} {address length limit : Nat}
    {bytes : List Byte} (h : memory.fetchBytes address length = some bytes)
    (bound : length ≤ limit) : bytes <+: fetchWindow memory limit address := by
  induction length generalizing address limit bytes with
  | zero =>
    have := Memory.readWith_length h
    rw [List.length_eq_zero_iff] at this
    subst this
    exact List.nil_prefix
  | succ length ih =>
    obtain ⟨limit, rfl⟩ : ∃ l, limit = l + 1 := ⟨limit - 1, by omega⟩
    have hlen := Memory.readWith_length h
    obtain ⟨byte, tail, rfl⟩ : ∃ b t, bytes = b :: t := by
      cases bytes with
      | nil => simp at hlen
      | cons b t => exact ⟨b, t, rfl⟩
    have first : memory.fetchBytes address 1 = some [byte] := by
      have := Memory.readWith_slice h 0 1 (by omega) (by omega)
      simpa [Memory.fetchBytes] using this
    simp only [fetchWindow, first]
    refine List.prefix_cons_inj _ |>.mpr ?_
    by_cases hz : length = 0
    · subst hz
      have : tail = [] := by simpa using hlen
      subst this
      exact List.nil_prefix
    · have rest := Memory.readWith_slice h 1 length (by omega) (by omega)
      simp only [List.drop_succ_cons, List.drop_zero] at rest
      rw [List.take_of_length_le (by simp at hlen; omega)] at rest
      exact ih rest (by omega)

/-- Every nonempty prefix of the window can be fetched as a whole. -/
theorem fetchWindow_fetchBytes (memory : Memory) (limit address count : Nat)
    (positive : 0 < count) (bound : count ≤ (fetchWindow memory limit address).length) :
    memory.fetchBytes address count = some ((fetchWindow memory limit address).take count) := by
  induction limit generalizing address count with
  | zero => simp [fetchWindow] at bound; omega
  | succ limit ih =>
    cases hfirst : memory.fetchBytes address 1 with
    | none => simp [fetchWindow, hfirst] at bound; omega
    | some first =>
      match first, hfirst with
      | [], hfirst => simp [fetchWindow, hfirst] at bound; omega
      | _ :: _ :: _, hfirst => simp [fetchWindow, hfirst] at bound; omega
      | [byte], hfirst =>
        simp only [fetchWindow, hfirst, List.length_cons] at bound ⊢
        obtain ⟨count, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by omega⟩
        by_cases hz : count = 0
        · subst hz; simpa using hfirst
        · have rest := ih (address + 1) count (by omega) (by omega)
          have := Memory.readWith_cons hfirst rest
          simpa [Memory.fetchBytes] using this

/-- A window shorter than its limit stops at a byte that cannot be fetched. -/
theorem fetchWindow_stop (memory : Memory) (limit address : Nat)
    (short : (fetchWindow memory limit address).length < limit) :
    memory.fetchBytes (address + (fetchWindow memory limit address).length) 1 = none := by
  induction limit generalizing address with
  | zero => omega
  | succ limit ih =>
    cases hfirst : memory.fetchBytes address 1 with
    | none => simp [fetchWindow, hfirst]
    | some first =>
      match first, hfirst with
      | [], hfirst => simpa using Memory.readWith_length hfirst
      | _ :: _ :: _, hfirst => simpa using Memory.readWith_length hfirst
      | [byte], hfirst =>
        simp only [fetchWindow, hfirst, List.length_cons] at short ⊢
        have := ih (address + 1) (by omega)
        rwa [Nat.add_assoc, Nat.add_comm 1] at this

/-! ## Completing a prefix of an encoding -/

/-- Bytes appended to the available bytes to test whether they can still begin a
supported encoding: a structural completion for the prefix, opcode and ModRM
positions, then four bytes of immediate or displacement. -/
def completion : List Byte → List Byte
  | [] => [0xC3, 0, 0, 0, 0]
  | [b] => (if b = rexB then [0x50] else [0x89, 0xC0]) ++ [0, 0, 0, 0]
  | [_, opcode] => (if opcode = 0xF7#8 then [0xD0] else [0xC0]) ++ [0, 0, 0, 0]
  | _ :: _ :: _ :: _ => [0, 0, 0, 0]

private theorem decodeImm32_exists {bytes : List Byte} (h : 4 ≤ bytes.length) :
    ∃ v, decodeImm32 bytes = some v := by
  match bytes, h with
  | _ :: _ :: _ :: _ :: _, _ => exact ⟨_, rfl⟩

private theorem isSome_of_encode_prefix {bytes : List Byte} {i : Insn} (h : i.encode <+: bytes) :
    (Insn.decode bytes).isSome := by
  rw [Insn.decode_eq_some_iff.mpr ⟨rfl, h⟩]
  rfl

/-- A 32-bit immediate can be read from any four or more bytes. -/
private theorem imm32_prefix {bytes : List Byte} (h : 4 ≤ bytes.length) :
    ∃ v, imm32Bytes v <+: bytes := by
  obtain ⟨v, hv⟩ := decodeImm32_exists h
  exact ⟨v, _, imm32Bytes_of_decodeImm32 hv⟩

private theorem completion_long {w : List Byte} (h : 3 ≤ w.length) : completion w = [0, 0, 0, 0] := by
  match w, h with
  | _ :: _ :: _ :: _, _ => rfl

private theorem length_completion (w : List Byte) : 4 ≤ (completion w).length := by
  unfold completion
  split <;> (try split) <;> simp

private theorem completion_one (r b : BitVec 1) :
    (Insn.decode ([rex r b] ++ completion [rex r b])).isSome := by
  revert r b; decide

private theorem completion_movRR (r b : BitVec 1) :
    (Insn.decode ([rex r b, 0x89] ++ completion [rex r b, 0x89])).isSome := by
  revert r b; decide

private theorem completion_alu (op : AluOp) (r b : BitVec 1) :
    (Insn.decode ([rex r b, op.opcode] ++ completion [rex r b, op.opcode])).isSome := by
  revert r b; cases op <;> decide

private theorem completion_aluI (b : BitVec 1) :
    (Insn.decode ([rex 0 b, 0x81] ++ completion [rex 0 b, 0x81])).isSome := by
  revert b; decide

private theorem completion_movRI (b : BitVec 1) :
    (Insn.decode ([rex 0 b, 0xC7] ++ completion [rex 0 b, 0xC7])).isSome := by
  revert b; decide

private theorem completion_unary (b : BitVec 1) :
    (Insn.decode ([rex 0 b, 0xF7] ++ completion [rex 0 b, 0xF7])).isSome := by
  revert b; decide

/-- A seven-byte `REX.W opcode ModRM imm32` form whose immediate is cut short is
completed by the four appended bytes. -/
private theorem completion_imm {r b : BitVec 1} {opcode modrmByte : Byte} {imm : BitVec 32}
    {k : Nat} (form : BitVec 32 → Instr)
    (encoded : ∀ v, X86.encode (form v) = [rex r b, opcode, modrmByte] ++ imm32Bytes v) :
    (Insn.decode ([rex r b, opcode, modrmByte] ++ (imm32Bytes imm).take k ++
      completion ([rex r b, opcode, modrmByte] ++ (imm32Bytes imm).take k))).isSome := by
  rw [completion_long (by simp)]
  obtain ⟨v, hv⟩ := imm32_prefix (bytes := (imm32Bytes imm).take k ++ [0, 0, 0, 0]) (by simp)
  apply isSome_of_encode_prefix (i := .base (form v))
  simp only [Insn.encode, encoded, List.append_assoc]
  exact (List.prefix_append_right_inj _).mpr hv

/-- Every prefix of a supported encoding, followed by its `completion`, decodes. -/
theorem decode_completion {w : List Byte} {i : Insn} (hw : w <+: i.encode) :
    (Insn.decode (w ++ completion w)).isSome := by
  rw [List.prefix_iff_eq_take.mp hw]
  generalize w.length = k
  by_cases full : i.encode.length ≤ k
  · rw [List.take_of_length_le full]
    exact isSome_of_encode_prefix (List.prefix_append _ _)
  cases i with
  | base instr =>
    cases instr with
    | movRR d src =>
      rcases k with _ | _ | _ | k
      · rw [List.take_zero]; decide
      · exact completion_one _ _
      · exact completion_movRR _ _
      · exact absurd (by simp [Insn.encode, encode]) full
    | alu op d src =>
      rcases k with _ | _ | _ | k
      · rw [List.take_zero]; decide
      · exact completion_one _ _
      · exact completion_alu _ _ _
      · exact absurd (by simp [Insn.encode, encode]) full
    | not d =>
      rcases k with _ | _ | _ | k
      · rw [List.take_zero]; decide
      · exact completion_one _ _
      · exact completion_unary _
      · exact absurd (by simp [Insn.encode, encode]) full
    | neg d =>
      rcases k with _ | _ | _ | k
      · rw [List.take_zero]; decide
      · exact completion_one _ _
      · exact completion_unary _
      · exact absurd (by simp [Insn.encode, encode]) full
    | aluI op d imm =>
      rcases k with _ | _ | _ | k
      · rw [List.take_zero]; decide
      · exact completion_one _ _
      · exact completion_aluI _
      · have := completion_imm (imm := imm) (k := k) (fun v => .aluI op d v) (fun v => rfl)
        simpa [Insn.encode, encode] using this
    | movRI d imm =>
      rcases k with _ | _ | _ | k
      · rw [List.take_zero]; decide
      · exact completion_one _ _
      · exact completion_movRI _
      · have := completion_imm (imm := imm) (k := k) (fun v => .movRI d v) (fun v => rfl)
        simpa [Insn.encode, encode] using this
  | push src =>
    rcases k with _ | _ | k
    · rw [List.take_zero]; decide
    · have hhi : src.hi ≠ 0#1 := by
        intro h; apply full; simp [Insn.encode, encodeRegOpcode, h]
      simp only [Insn.encode, encodeRegOpcode, hhi, ite_false, List.take_succ_cons,
        List.take_zero]
      decide
    · refine absurd ?_ full
      simp only [Insn.encode, encodeRegOpcode]
      split <;> simp
  | pop src =>
    rcases k with _ | _ | k
    · rw [List.take_zero]; decide
    · have hhi : src.hi ≠ 0#1 := by
        intro h; apply full; simp [Insn.encode, encodeRegOpcode, h]
      simp only [Insn.encode, encodeRegOpcode, hhi, ite_false, List.take_succ_cons,
        List.take_zero]
      decide
    · refine absurd ?_ full
      simp only [Insn.encode, encodeRegOpcode]
      split <;> simp
  | call rel =>
    rcases k with _ | k
    · rw [List.take_zero]; decide
    · have hlen := length_completion ((Insn.call rel).encode.take (k + 1))
      simp only [Insn.encode, List.take_succ_cons, List.cons_append] at hlen ⊢
      generalize completion _ = tail at hlen ⊢
      obtain ⟨v, hv⟩ := imm32_prefix (bytes := (imm32Bytes rel).take k ++ tail) (by simp; omega)
      apply isSome_of_encode_prefix (i := .call v)
      simp only [Insn.encode]
      exact (List.prefix_cons_inj _).mpr hv
  | ret =>
    rcases k with _ | k
    · rw [List.take_zero]; decide
    · exact absurd (by simp [Insn.encode]) full

/-- The available bytes can be extended to a supported encoding exactly when
they can be extended by their `completion`. -/
theorem exists_decode_iff_completion (w : List Byte) :
    (∃ more, (Insn.decode (w ++ more)).isSome) ↔ (Insn.decode (w ++ completion w)).isSome := by
  constructor
  · rintro ⟨more, hsome⟩
    obtain ⟨⟨instr, n⟩, hdec⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨-, hpre⟩ := Insn.decode_eq_some_iff.mp hdec
    rcases List.prefix_or_prefix_of_prefix hpre (List.prefix_append w more) with henc | hwin
    · obtain ⟨t, ht⟩ := henc
      have := Insn.decode_encode_append instr (t ++ completion w)
      rw [← List.append_assoc, ht] at this
      rw [this]
      rfl
    · exact decode_completion hwin
  · intro h
    exact ⟨_, h⟩

/-! ## Fetch and decode -/

/-- The result of fetching and decoding at an address. -/
inductive Fetch where
  /-- An instruction and the number of bytes it occupies. -/
  | decoded (instr : Insn) (length : Nat)
  /-- The available bytes are a proper prefix of a supported encoding, and the
  next byte cannot be fetched. -/
  | truncated
  /-- No supported encoding begins with the available bytes. -/
  | undecodable

/-- Decode from the available executable bytes, then require execute permission
on exactly the consumed span. If nothing decodes, the available bytes are a
truncated encoding when they decode after their `completion`, which by
`exists_decode_iff_completion` is the case exactly when some extension of them
decodes. -/
def fetch (memory : Memory) (address : Nat) : Fetch :=
  match Insn.decode (fetchWindow memory maxInstrLength address) with
  | some (instr, length) =>
    if memory.Permitted .execute address length then .decoded instr length else .truncated
  | none =>
    if (Insn.decode (fetchWindow memory maxInstrLength address ++
        completion (fetchWindow memory maxInstrLength address))).isSome then .truncated
    else .undecodable

/-- Fetching succeeds exactly when the consumed bytes, fetched as one checked
span, decode to the instruction on their own. -/
theorem fetch_eq_decoded_iff {memory : Memory} {address : Nat} {instr : Insn} {length : Nat} :
    fetch memory address = .decoded instr length ↔
      ∃ bytes, memory.fetchBytes address length = some bytes ∧
        Insn.decode bytes = some (instr, length) := by
  constructor
  · intro h
    unfold fetch at h
    split at h
    · rename_i i n hdecode
      split at h
      · cases h
        obtain ⟨-, pos, -, le⟩ := Insn.decode_length hdecode
        exact ⟨_, fetchWindow_fetchBytes memory _ address length pos le, Insn.decode_take hdecode⟩
      · cases h
    · split at h <;> cases h
  · rintro ⟨bytes, fetched, decoded⟩
    obtain ⟨-, -, le, -⟩ := Insn.decode_length decoded
    have hlen := Memory.readWith_length fetched
    obtain ⟨more, hmore⟩ := fetchBytes_prefix_fetchWindow fetched
      (limit := maxInstrLength) (by unfold maxInstrLength; omega)
    have hdecode := Insn.decode_append more decoded
    rw [hmore] at hdecode
    unfold fetch
    rw [hdecode]
    simp only [Memory.readWith_permitted fetched, ite_true]

/-- The consumed length is the instruction's encoded length. -/
theorem fetch_length {memory : Memory} {address : Nat} {instr : Insn} {length : Nat}
    (h : fetch memory address = .decoded instr length) : length = instr.length := by
  obtain ⟨_, -, decoded⟩ := fetch_eq_decoded_iff.mp h
  exact (Insn.decode_length decoded).1

/-- A fetch fault: the available bytes are a proper prefix of the encoding of a
supported instruction, and the byte after them cannot be fetched. -/
theorem fetch_truncated {memory : Memory} {address : Nat}
    (h : fetch memory address = .truncated) :
    (∃ instr : Insn, fetchWindow memory maxInstrLength address <+: instr.encode ∧
        (fetchWindow memory maxInstrLength address).length < instr.encode.length) ∧
      memory.fetchBytes (address + (fetchWindow memory maxInstrLength address).length) 1 =
        none := by
  unfold fetch at h
  split at h
  · rename_i i n hdecode
    split at h
    · cases h
    · rename_i hperm
      obtain ⟨-, pos, -, le⟩ := Insn.decode_length hdecode
      exact absurd (Memory.readWith_permitted
        (fetchWindow_fetchBytes memory _ address n pos le)) hperm
  · rename_i hnone
    split at h
    · rename_i hmore
      obtain ⟨more, hsome⟩ := (exists_decode_iff_completion _).mpr hmore
      obtain ⟨⟨instr, n⟩, hdec⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨-, hpre⟩ := Insn.decode_eq_some_iff.mp hdec
      set window := fetchWindow memory maxInstrLength address
      have hprefix : window <+: instr.encode ∧ window.length < instr.encode.length := by
        rcases List.prefix_or_prefix_of_prefix hpre (List.prefix_append window more) with
          henc | hwin
        · obtain ⟨t, ht⟩ := henc
          have := Insn.decode_encode_append instr t
          rw [ht, hnone] at this
          cases this
        · refine ⟨hwin, ?_⟩
          rcases Nat.lt_or_ge window.length instr.encode.length with hlt | hge
          · exact hlt
          · have heq := List.IsPrefix.eq_of_length hwin (by
              have := hwin.length_le
              omega)
            have := Insn.decode_encode instr
            rw [← heq, hnone] at this
            cases this
      refine ⟨⟨instr, hprefix⟩, fetchWindow_stop memory _ address ?_⟩
      have := Insn.length_le instr
      have h15 : maxInstrLength = 15 := rfl
      have hw : (fetchWindow memory maxInstrLength address).length = window.length := rfl
      rw [Insn.length_encode] at hprefix
      omega
    · cases h

/-- Undecodable bytes: no extension of the available bytes decodes. -/
theorem fetch_undecodable_iff {memory : Memory} {address : Nat} :
    fetch memory address = .undecodable ↔
      ∀ more, Insn.decode (fetchWindow memory maxInstrLength address ++ more) = none := by
  constructor
  · intro h more
    unfold fetch at h
    split at h
    · split at h <;> cases h
    · split at h
      · cases h
      · rename_i hmore
        cases hd : Insn.decode (fetchWindow memory maxInstrLength address ++ more) with
        | none => rfl
        | some r => exact absurd ((exists_decode_iff_completion _).mp ⟨more, by simp [hd]⟩) hmore
  · intro h
    have hnone := h []
    rw [List.append_nil] at hnone
    have hno : ¬ (Insn.decode (fetchWindow memory maxInstrLength address ++
        completion (fetchWindow memory maxInstrLength address))).isSome := by
      simp [h]
    unfold fetch
    rw [hnone]
    simp only [hno, Bool.false_eq_true, ite_false]

/-! ## One step -/

/-- The result of one step. Faults change nothing. -/
inductive Outcome where
  /-- The instruction retired with this successor state. -/
  | retired (next : MState)
  /-- A RET popped the designated return address; this is the state after it. -/
  | returned (final : MState)
  /-- The bytes at RIP are outside the supported canonical subset. -/
  | undecodable
  /-- The bytes at RIP are a proper prefix of a supported encoding and the next
  byte cannot be fetched. -/
  | fetchFault
  /-- A stack access of this instruction was not permitted or not backed. -/
  | memoryFault (instr : Insn)

namespace MState

/-- Fetch, decode and execute one instruction. A RET whose popped target is
`exit` reports `returned`; any other RET, including one returning into a
caller, retires normally. -/
def step (exit : Word) (m : MState) : Outcome :=
  match fetch m.memory m.core.rip.toNat with
  | .undecodable => .undecodable
  | .truncated => .fetchFault
  | .decoded instr _ =>
    match instr.exec m.core m.memory with
    | none => .memoryFault instr
    | some (core, memory) =>
      if instr = .ret ∧ core.rip = exit then .returned ⟨core, memory⟩
      else .retired ⟨core, memory⟩

/-- Retirement only, as a partial transition function for `Machine.Execution.run`. -/
def stepOpt (exit : Word) (m : MState) : Option MState :=
  match step exit m with
  | .retired next => some next
  | _ => none

/-- A finite run of retirements followed by a return to `exit`. -/
def Returns (exit : Word) (initial final : MState) : Prop :=
  ∃ n mid, Machine.Execution.run (stepOpt exit) n initial = some mid ∧
    step exit mid = .returned final

/-- One step from exactly fetched bytes and a successful execution. -/
theorem step_of_exec {exit : Word} {m : MState} {bytes : List Byte} {instr : Insn}
    {length : Nat} {core : State} {memory : Memory}
    (fetched : m.memory.fetchBytes m.core.rip.toNat length = some bytes)
    (decoded : Insn.decode bytes = some (instr, length))
    (executed : instr.exec m.core m.memory = some (core, memory)) :
    step exit m = if instr = .ret ∧ core.rip = exit then .returned ⟨core, memory⟩
      else .retired ⟨core, memory⟩ := by
  have hf := fetch_eq_decoded_iff.mpr ⟨bytes, fetched, decoded⟩
  simp only [step, hf, executed]

theorem stepOpt_of_exec {exit : Word} {m : MState} {bytes : List Byte} {instr : Insn}
    {length : Nat} {core : State} {memory : Memory}
    (fetched : m.memory.fetchBytes m.core.rip.toNat length = some bytes)
    (decoded : Insn.decode bytes = some (instr, length))
    (executed : instr.exec m.core m.memory = some (core, memory))
    (continues : ¬ (instr = .ret ∧ core.rip = exit)) :
    stepOpt exit m = some ⟨core, memory⟩ := by
  simp only [stepOpt, step_of_exec fetched decoded executed, continues, ite_false]

theorem step_returned_of_exec {exit : Word} {m : MState} {bytes : List Byte}
    {length : Nat} {core : State} {memory : Memory}
    (fetched : m.memory.fetchBytes m.core.rip.toNat length = some bytes)
    (decoded : Insn.decode bytes = some (.ret, length))
    (executed : Insn.ret.exec m.core m.memory = some (core, memory))
    (target : core.rip = exit) :
    step exit m = .returned ⟨core, memory⟩ := by
  simp only [step_of_exec fetched decoded executed, target, and_self, ite_true]

/-- A retiring or returning step changes at most the eight bytes below the
incoming RSP, and no mapping. -/
theorem step_writesOnly {exit : Word} {m next : MState}
    (h : step exit m = .retired next ∨ step exit m = .returned next) :
    Memory.WritesOnly m.memory next.memory (m.core.read .rsp - 8#64).toNat 8 := by
  unfold step at h
  split at h
  · simp at h
  · simp at h
  · rename_i instr _ _
    split at h
    · simp at h
    · rename_i core memory hexec
      have frame := Insn.exec_writesOnly hexec
      split at h <;> rcases h with h | h <;> cases h <;> exact frame

/-- Retirement never passes through a return to `exit`: `stepOpt` is `none`
exactly on faults and returns. -/
theorem stepOpt_eq_some_iff {exit : Word} {m next : MState} :
    stepOpt exit m = some next ↔ step exit m = .retired next := by
  unfold stepOpt
  split <;> simp_all

end MState

end Silmaril.X86
