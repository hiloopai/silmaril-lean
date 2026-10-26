module

public import Silmaril.X86.Float.Semantics
public import Silmaril.X86.Float.Control
public import Silmaril.X86.Machine

/-!
# A fetch/decode/execute machine for the integer and scalar SSE subsets

`MState` pairs the SSE-extended register state `Float.State` with a
`Process.Memory`. One `MState.step` fetches at RIP, decodes an integer
instruction of `X86.Insn` (the register subset with PUSH, POP, CALL and RET), a
scalar SSE instruction of `Float.Instr`, or a `Jcc rel8`/`UD2` of
`Float.CtlInstr`, and executes it. This is a
handwritten local model of one sequential user-mode thread, not derived from,
or proved to correspond with, the Sail, ACL2 or any hardware description.

## Decoding

`Insn.decode` tries the integer decoder first, the SSE decoder second and the
`Jcc`/`UD2` decoder last. The canonical subsets are disjoint in a strong sense:
no byte string that starts with an SSE encoding is accepted by the integer
decoder (`int_decode_encode_sse`), because every SSE encoding starts with `66`,
`F2`, `F3` or `0F`, or with a REX prefix followed by `0F`, none of which begins
an integer encoding; and no byte string that starts with `70+cc` or `0F 0B` is
accepted by either (`int_decode_encode_ctl`, `sse_decode_encode_ctl`). Hence the
combined decoder is again a prefix code with the shared `Machine.Decoder` laws
(`Insn.byteDecoder`): decoding reads only the bytes of the instruction, and
every encoding decodes to itself whatever follows it.

## Fetch policy

As in `X86.Machine`, the fetcher collects the available bytes
(`X86.fetchWindow`: at most 15 bytes, each mapped executable, below `2^64` and
backed), decodes them, and requires execute permission on exactly the consumed
span. `fetch_eq_decoded_iff` shows that this is the same as decoding exactly
the consumed bytes obtained from one checked `fetchBytes`, so an instruction
whose own bytes are executable is fetched whatever follows it.

A failed decode is reported as `Fetch.undecoded`. Unlike `X86.fetch`, this
machine does not separate a truncated encoding from unsupported bytes:
`fetch_undecoded_full` shows that a failure on a full 15-byte window means no
byte string starting with the window decodes, and `fetch_undecoded_short` that
a shorter window stopped at a byte that cannot be fetched, which may have cut
an encoding short.

## Outcomes

`MState.step exit` reports a retired instruction, `returned` when a RET pops
exactly `exit`, a failed decode, a data-memory fault, #GP(0) from an SSE
instruction (a misaligned 128-bit operand or reserved MXCSR bits), #XM with
the MXCSR that the handler would observe, #UD from `UD2`, or `undefinedFlag`
when a `Jcc` reads a status flag the model leaves undefined (the model does not
choose a branch). Faults carry no successor state: nothing else changes and RIP
still addresses the faulting instruction.

A `Jcc rel8` (SDM Vol. 2A, `Jcc`) retires to the address after it plus the
sign-extended displacement when its condition (`condHolds`) holds, and to the
address after it otherwise (`step_of_jcc`); `UD2` (SDM Vol. 2B) raises #UD
(`step_of_ud2`). The branch target is not checked for canonical form.

Integer instructions leave the XMM registers and MXCSR unchanged, and on the
integer state they step exactly as `X86.MState.step` does (`step_of_int_retired`,
`step_of_int_returned`). With every SIMD exception masked, as at reset, no step
raises #XM (`step_ne_simd_of_allMasked`).
-/

@[expose] public section

namespace Silmaril.X86.Float

open Silmaril.Process (Memory)

/-! ## Combined instructions and decoding -/

/-- An instruction of the combined machine. -/
inductive Insn where
  /-- An integer instruction (`X86.Insn`). -/
  | int (i : X86.Insn)
  /-- A scalar SSE instruction. -/
  | sse (i : Instr)
  /-- `Jcc rel8` or `UD2`. -/
  | ctl (i : CtlInstr)
  deriving DecidableEq, Repr

namespace Insn

def encode : Insn → List Byte
  | .int i => i.encode
  | .sse i => Float.encode i
  | .ctl i => i.encode

/-- The integer decoder first, then the SSE decoder, then `Jcc`/`UD2`. -/
def decode (bytes : List Byte) : Option (Insn × Nat) :=
  match X86.Insn.decode bytes with
  | some (i, n) => some (.int i, n)
  | none =>
    match Float.decode bytes with
    | some (i, n) => some (.sse i, n)
    | none => (CtlInstr.decode bytes).map fun r => (.ctl r.1, r.2)

end Insn

/-! ### Disjointness of the two subsets -/

private theorem x86_decode_of_type {b : Byte} (h : b.extractLsb' 3 5 ≠ 0x09#5)
    (rest : List Byte) : X86.decode (b :: rest) = none := by
  unfold X86.decode
  split
  · rename_i p opc m rest' he
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he
    simp [h]
  · rfl

private theorem decodeBody_escape (r b : BitVec 1) (reg rm : BitVec 3) (rest : List Byte) :
    X86.decodeBody r b 0x0F#8 reg rm rest = none := by
  have hop : X86.AluOp.ofOpcode 0x0F#8 = none := by decide
  unfold X86.decodeBody
  simp only [hop]
  split <;> simp_all

private theorem x86_decode_escape (b : Byte) (tail : List Byte) :
    X86.decode (b :: 0x0F#8 :: tail) = none := by
  match tail with
  | [] => rfl
  | m :: rest => simp only [X86.decode, decodeBody_escape, ite_self]

/-- A byte that begins no integer encoding: not a REX.W prefix, `C3`, `E8`,
`50+r`, `58+r` or REX.B. -/
private theorem insn_decode_of_lead (b : Byte) (rest : List Byte)
    (ht : b.extractLsb' 3 5 ≠ 0x09#5) (h1 : b ≠ 0xC3#8) (h2 : b ≠ 0xE8#8)
    (h3 : b.extractLsb' 3 5 ≠ 0b01010#5) (h4 : b.extractLsb' 3 5 ≠ 0b01011#5)
    (h5 : b ≠ X86.rexB) :
    X86.Insn.decode (b :: rest) = none := by
  simp [X86.Insn.decode, h1, h2, h3, h4, h5, x86_decode_of_type ht]

/-- A byte that begins no integer encoding on its own. -/
private theorem insn_decode_lead (b : Byte) (rest : List Byte)
    (h66 : b = 0x66#8 ∨ b = 0xF2#8 ∨ b = 0xF3#8 ∨ b = 0x0F#8) :
    X86.Insn.decode (b :: rest) = none := by
  apply insn_decode_of_lead <;> rcases h66 with rfl | rfl | rfl | rfl <;> decide

/-- No byte string starting with a `Jcc` or `UD2` encoding is accepted by the
integer decoder: `70+cc` and `0F` begin no integer encoding. -/
theorem int_decode_encode_ctl (i : CtlInstr) (rest : List Byte) :
    X86.Insn.decode (i.encode ++ rest) = none := by
  cases i with
  | jcc cc rel =>
    apply insn_decode_of_lead <;> revert cc <;> decide
  | ud2 => exact insn_decode_lead _ _ (by simp)

/-- No byte string starting with a `Jcc` or `UD2` encoding is accepted by the
SSE decoder: `70+cc` is neither a prefix nor the `0F` escape, and `0F 0B` is not
in the SSE opcode tables. -/
theorem sse_decode_encode_ctl (i : CtlInstr) (rest : List Byte) :
    Float.decode (i.encode ++ rest) = none := by
  cases i with
  | jcc cc rel =>
    have h1 : (0x7#4 ++ cc) ≠ 0x66#8 := by revert cc; decide
    have h2 : (0x7#4 ++ cc) ≠ 0xF2#8 := by revert cc; decide
    have h3 : (0x7#4 ++ cc) ≠ 0xF3#8 := by revert cc; decide
    have h4 : (0x7#4 ++ cc).extractLsb' 4 4 ≠ 0x4#4 := by revert cc; decide
    have h5 : (0x7#4 ++ cc) ≠ 0x0F#8 := by revert cc; decide
    simp [Float.decode, Raw.parse, CtlInstr.encode, parsePrefix, parseRex, h1, h2, h3, h4, h5]
  | ud2 =>
    simp only [Float.decode, CtlInstr.encode, List.cons_append, List.nil_append]
    cases hp : Raw.parse (0x0F#8 :: 0x0B#8 :: rest) with
    | none => rfl
    | some pr =>
      obtain ⟨r, rest'⟩ := pr
      have hb := Raw.parse_sound hp
      obtain ⟨pfx, w, map, opc, reg, rm, imm⟩ := r
      have hpfx : pfx = .none := by
        cases pfx <;> simp_all [Raw.bytes, Prefix.bytes]
      subst hpfx
      have hrex : rexBytes (Raw.rex ⟨.none, w, map, opc, reg, rm, imm⟩) = [] := by
        by_cases hn : Raw.rex ⟨.none, w, map, opc, reg, rm, imm⟩ = 0#4
        · simp [rexBytes, hn]
        · exfalso
          simp only [Raw.bytes, Prefix.bytes, rexBytes, hn, ite_false, List.nil_append,
            List.cons_append, List.cons.injEq] at hb
          have := congrArg (fun b : Byte => b.extractLsb' 4 4) hb.1
          simp only [rexByte_high] at this
          exact absurd this (by decide)
      simp only [Raw.bytes, Prefix.bytes, hrex, List.nil_append, List.cons_append,
        List.cons.injEq, true_and] at hb
      have hmap : map = .m0F := by
        cases map <;> simp_all [OpMap.bytes]
      subst hmap
      simp only [OpMap.bytes, List.nil_append] at hb
      obtain ⟨rfl, -⟩ := hb
      simp [ofRaw, candidate, packedCandidate]

/-- A REX prefix followed by the `0F` escape begins no integer encoding. -/
private theorem insn_decode_rex_escape (n : BitVec 4) (tail : List Byte) :
    X86.Insn.decode (rexByte n :: 0x0F#8 :: tail) = none := by
  have h1 : rexByte n ≠ 0xC3#8 := by revert n; decide
  have h2 : rexByte n ≠ 0xE8#8 := by revert n; decide
  have h3 : (rexByte n).extractLsb' 3 5 ≠ 0b01010#5 := by revert n; decide
  have h4 : (rexByte n).extractLsb' 3 5 ≠ 0b01011#5 := by revert n; decide
  have e3 : (0x0F#8 : Byte).extractLsb' 3 5 ≠ 0b01010#5 := by decide
  have e4 : (0x0F#8 : Byte).extractLsb' 3 5 ≠ 0b01011#5 := by decide
  simp only [X86.Insn.decode, h1, h2, h3, h4, e3, e4, ite_false, x86_decode_escape,
    Option.map_none]
  split <;> rfl

/-- No byte string starting with an SSE encoding is accepted by the integer
decoder. -/
theorem int_decode_encode_sse (j : Instr) (rest : List Byte) :
    X86.Insn.decode (Float.encode j ++ rest) = none := by
  simp only [Float.encode, Raw.bytes]
  generalize toRaw j = r
  obtain ⟨pfx, w, map, opc, reg, rm, imm⟩ := r
  simp only [List.append_assoc, List.cons_append]
  cases pfx with
  | none =>
    simp only [Prefix.bytes, List.nil_append, rexBytes]
    split
    · exact insn_decode_lead _ _ (by simp)
    · exact insn_decode_rex_escape _ _
  | p66 => exact insn_decode_lead _ _ (by simp)
  | pF2 => exact insn_decode_lead _ _ (by simp)
  | pF3 => exact insn_decode_lead _ _ (by simp)

namespace Insn

@[simp] theorem decode_encode_append (i : Insn) (rest : List Byte) :
    decode (i.encode ++ rest) = some (i, i.encode.length) := by
  cases i with
  | int i => simp [decode, encode]
  | sse i => simp [decode, encode, int_decode_encode_sse]
  | ctl i => simp [decode, encode, int_decode_encode_ctl, sse_decode_encode_ctl]

/-- A successful decode consumed the canonical encoding of its result. -/
theorem decode_eq_some_iff {bytes : List Byte} {i : Insn} {n : Nat} :
    decode bytes = some (i, n) ↔ n = i.encode.length ∧ i.encode <+: bytes := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · rename_i j m hj
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact X86.Insn.decode_eq_some_iff.mp hj
    · split at h
      · rename_i j m hd
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Float.decode_eq_some_iff.mp hd
      · cases hc : CtlInstr.decode bytes with
        | none => simp [hc] at h
        | some r =>
          obtain ⟨j, m⟩ := r
          simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact CtlInstr.decode_eq_some_iff.mp hc
  · rintro ⟨rfl, rest, rfl⟩
    exact decode_encode_append i rest

theorem length_encode_pos (i : Insn) : 0 < i.encode.length := by
  cases i with
  | int i => rw [encode, X86.Insn.length_encode]; exact X86.Insn.length_pos i
  | sse i => have := Float.encode_length_ge i; simp only [encode]; omega
  | ctl i => simp [encode]

/-- Every encoding has at most 12 bytes. -/
theorem length_encode_le (i : Insn) : i.encode.length ≤ 12 := by
  cases i with
  | int i => rw [encode, X86.Insn.length_encode]; have := X86.Insn.length_le i; omega
  | sse i => exact Float.encode_length_le i
  | ctl i => simp [encode]

theorem decode_append {bytes : List Byte} (more : List Byte) {i : Insn} {n : Nat}
    (h : decode bytes = some (i, n)) : decode (bytes ++ more) = some (i, n) := by
  obtain ⟨hn, rest, rfl⟩ := decode_eq_some_iff.mp h
  rw [List.append_assoc, decode_encode_append, hn]

theorem decode_take {bytes : List Byte} {i : Insn} {n : Nat}
    (h : decode bytes = some (i, n)) : decode (bytes.take n) = some (i, n) := by
  obtain ⟨hn, rest, rfl⟩ := decode_eq_some_iff.mp h
  rw [hn, List.take_left, ← List.append_nil i.encode, decode_encode_append]
  simp

/-- A successful decode consumes between one and twelve bytes of its input. -/
theorem decode_length {bytes : List Byte} {i : Insn} {n : Nat}
    (h : decode bytes = some (i, n)) : n = i.encode.length ∧ 0 < n ∧ n ≤ 12 ∧ n ≤ bytes.length := by
  obtain ⟨hn, hp⟩ := decode_eq_some_iff.mp h
  subst hn
  exact ⟨rfl, length_encode_pos i, length_encode_le i, hp.length_le⟩

/-- The combined codec as a shared `Machine.Decoder`. -/
def byteDecoder : Machine.Decoder Insn where
  decode := decode
  encode := encode
  decode_length_pos h := (decode_length h).2.1
  decode_length_le h := (decode_length h).2.2.2
  decode_append extra h := decode_append extra h
  decode_take h := decode_take h
  decode_encode_append := decode_encode_append

/-- The integer decoder's successes are the combined decoder's `int` results. -/
theorem decode_of_int {bytes : List Byte} {i : X86.Insn} {n : Nat}
    (h : X86.Insn.decode bytes = some (i, n)) : decode bytes = some (.int i, n) := by
  simp [decode, h]

end Insn

/-! ## Fetch -/

/-- The result of fetching and decoding at an address. -/
inductive Fetch where
  | decoded (instr : Insn) (length : Nat)
  /-- The available bytes decode to no supported instruction. -/
  | undecoded

/-- Decode from the available executable bytes, then require execute permission
on exactly the consumed span. -/
def fetch (memory : Memory) (address : Nat) : Fetch :=
  match Insn.decode (X86.fetchWindow memory X86.maxInstrLength address) with
  | some (instr, length) =>
    if memory.Permitted .execute address length then .decoded instr length else .undecoded
  | none => .undecoded

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
        exact ⟨_, X86.fetchWindow_fetchBytes memory _ address length pos le,
          Insn.decode_take hdecode⟩
      · cases h
    · cases h
  · rintro ⟨bytes, fetched, decoded⟩
    obtain ⟨-, -, le, -⟩ := Insn.decode_length decoded
    have hlen := Memory.readWith_length fetched
    obtain ⟨more, hmore⟩ := X86.fetchBytes_prefix_fetchWindow fetched
      (limit := X86.maxInstrLength) (by unfold X86.maxInstrLength; omega)
    have hdecode := Insn.decode_append more decoded
    rw [hmore] at hdecode
    unfold fetch
    rw [hdecode]
    simp only [Memory.readWith_permitted fetched, ite_true]

/-- The consumed length is the instruction's encoded length. -/
theorem fetch_length {memory : Memory} {address : Nat} {instr : Insn} {length : Nat}
    (h : fetch memory address = .decoded instr length) : length = instr.encode.length := by
  obtain ⟨_, -, decoded⟩ := fetch_eq_decoded_iff.mp h
  exact (Insn.decode_length decoded).1

/-- Fetching fails exactly when the available bytes do not decode. -/
theorem fetch_undecoded_iff {memory : Memory} {address : Nat} :
    fetch memory address = .undecoded ↔
      Insn.decode (X86.fetchWindow memory X86.maxInstrLength address) = none := by
  unfold fetch
  split
  · rename_i i n hdecode
    obtain ⟨-, pos, -, le⟩ := Insn.decode_length hdecode
    have := Memory.readWith_permitted (X86.fetchWindow_fetchBytes memory _ address n pos le)
    simp [this, hdecode]
  · simp_all

/-- A failure on a full 15-byte window: no byte string that starts with the
window decodes, so the bytes are outside the supported subset. -/
theorem fetch_undecoded_full {memory : Memory} {address : Nat}
    (h : fetch memory address = .undecoded)
    (full : (X86.fetchWindow memory X86.maxInstrLength address).length = X86.maxInstrLength) :
    ∀ more, Insn.decode (X86.fetchWindow memory X86.maxInstrLength address ++ more) = none := by
  rw [fetch_undecoded_iff] at h
  intro more
  cases hd : Insn.decode (X86.fetchWindow memory X86.maxInstrLength address ++ more) with
  | none => rfl
  | some r =>
    obtain ⟨i, n⟩ := r
    obtain ⟨hn, rest, he⟩ := Insn.decode_eq_some_iff.mp hd
    have hle := Insn.length_encode_le i
    have h15 : X86.maxInstrLength = 15 := rfl
    set w := X86.fetchWindow memory X86.maxInstrLength address
    have hpre : i.encode <+: w := by
      rw [List.prefix_iff_eq_take]
      have := congrArg (List.take i.encode.length) he
      rw [List.take_left, List.take_append_of_le_length (by omega)] at this
      exact this
    obtain ⟨rest', hw⟩ := hpre
    have := Insn.decode_encode_append i rest'
    rw [hw, h] at this
    cases this

/-- A failure on a window shorter than 15 bytes: the byte after the window
cannot be fetched. The available bytes may be an encoding cut short there. -/
theorem fetch_undecoded_short {memory : Memory} {address : Nat}
    (short : (X86.fetchWindow memory X86.maxInstrLength address).length < X86.maxInstrLength) :
    memory.fetchBytes (address + (X86.fetchWindow memory X86.maxInstrLength address).length) 1 =
      none :=
  X86.fetchWindow_stop memory _ address short

/-- The integer machine's successful fetches are fetches of this machine. -/
theorem fetch_of_int {memory : Memory} {address : Nat} {i : X86.Insn} {n : Nat}
    (h : X86.fetch memory address = .decoded i n) : fetch memory address = .decoded (.int i) n := by
  obtain ⟨bytes, fetched, decoded⟩ := X86.fetch_eq_decoded_iff.mp h
  exact fetch_eq_decoded_iff.mpr ⟨bytes, fetched, Insn.decode_of_int decoded⟩

/-! ## One step -/

/-- Set RIP, leaving every other register and flag unchanged. -/
def State.setRip (s : State) (rip : Word) : State := { s with core := { s.core with rip } }

/-- The SSE-extended register state and memory of one user-mode thread. -/
structure MState where
  state : State
  memory : Memory

/-- The result of one step. Faults change nothing. -/
inductive Outcome where
  /-- The instruction retired with this successor state. -/
  | retired (next : MState)
  /-- A RET popped the designated return address; this is the state after it. -/
  | returned (final : MState)
  /-- The available bytes at RIP decode to no supported instruction. -/
  | undecoded
  /-- A data access of this instruction was not permitted or not backed. -/
  | memoryFault (instr : Insn)
  /-- #GP(0) from an SSE instruction: a misaligned 128-bit operand, or LDMXCSR
  with reserved bits set. -/
  | generalProtection (instr : Instr)
  /-- #XM from an SSE instruction, with the MXCSR the handler observes. -/
  | simdException (instr : Instr) (mxcsr : MXCSR)
  /-- #UD raised by `UD2`. -/
  | invalidOpcode
  /-- A `Jcc` with condition code `cc` read a status flag that the model leaves
  undefined; the model does not choose a branch. -/
  | undefinedFlag (cc : BitVec 4)

namespace MState

/-- Fetch, decode and execute one instruction. A RET whose popped target is
`exit` reports `returned`; any other RET retires normally. -/
def step (exit : Word) (m : MState) : Outcome :=
  match fetch m.memory m.state.core.rip.toNat with
  | .undecoded => .undecoded
  | .decoded (.int i) _ =>
    match i.exec m.state.core m.memory with
    | none => .memoryFault (.int i)
    | some (core, memory) =>
      if i = .ret ∧ core.rip = exit then .returned ⟨{ m.state with core }, memory⟩
      else .retired ⟨{ m.state with core }, memory⟩
  | .decoded (.sse i) _ =>
    match i.exec m.state m.memory with
    | .commit next memory => .retired ⟨next, memory⟩
    | .fault .memory => .memoryFault (.sse i)
    | .fault .alignment => .generalProtection i
    | .fault .reservedMxcsr => .generalProtection i
    | .fault (.simd mxcsr) => .simdException i mxcsr
  | .decoded (.ctl (.jcc cc rel)) _ =>
    match condHolds cc m.state.core.flags with
    | some true =>
      .retired ⟨m.state.setRip (m.state.core.rip + 2#64 + rel.signExtend 64), m.memory⟩
    | some false => .retired ⟨m.state.setRip (m.state.core.rip + 2#64), m.memory⟩
    | none => .undefinedFlag cc
  | .decoded (.ctl .ud2) _ => .invalidOpcode

/-- Retirement only, as a partial transition function for `Machine.Execution.run`. -/
def stepOpt (exit : Word) (m : MState) : Option MState :=
  match step exit m with
  | .retired next => some next
  | _ => none

/-- A finite run of retirements followed by a return to `exit`. -/
def Returns (exit : Word) (initial final : MState) : Prop :=
  ∃ n mid, Machine.Execution.run (stepOpt exit) n initial = some mid ∧
    step exit mid = .returned final

theorem stepOpt_eq_some_iff {exit : Word} {m next : MState} :
    stepOpt exit m = some next ↔ step exit m = .retired next := by
  unfold stepOpt
  split <;> simp_all

/-- One SSE step from exactly fetched bytes. -/
theorem step_of_sse {exit : Word} {m : MState} {bytes : List Byte} {i : Instr} {length : Nat}
    (fetched : m.memory.fetchBytes m.state.core.rip.toNat length = some bytes)
    (decoded : Insn.decode bytes = some (.sse i, length)) :
    step exit m =
      match i.exec m.state m.memory with
      | .commit next memory => .retired ⟨next, memory⟩
      | .fault .memory => .memoryFault (.sse i)
      | .fault .alignment => .generalProtection i
      | .fault .reservedMxcsr => .generalProtection i
      | .fault (.simd mxcsr) => .simdException i mxcsr := by
  have hf := fetch_eq_decoded_iff.mpr ⟨bytes, fetched, decoded⟩
  simp only [step, hf]

/-- A committed SSE instruction at RIP retires with its `exec` result. -/
theorem step_of_sse_commit {exit : Word} {m : MState} {bytes : List Byte} {i : Instr}
    {length : Nat} {next : State} {memory : Memory}
    (fetched : m.memory.fetchBytes m.state.core.rip.toNat length = some bytes)
    (decoded : Insn.decode bytes = some (.sse i, length))
    (executed : i.exec m.state m.memory = .commit next memory) :
    step exit m = .retired ⟨next, memory⟩ := by
  rw [step_of_sse fetched decoded, executed]

/-- A `Jcc` at RIP: when the condition holds, RIP becomes the address after the
two-byte instruction plus the sign-extended displacement; when it fails, the
address after the instruction. Nothing else changes. -/
theorem step_of_jcc {exit : Word} {m : MState} {bytes : List Byte} {cc : BitVec 4}
    {rel : BitVec 8} {length : Nat}
    (fetched : m.memory.fetchBytes m.state.core.rip.toNat length = some bytes)
    (decoded : Insn.decode bytes = some (.ctl (.jcc cc rel), length)) :
    step exit m =
      match condHolds cc m.state.core.flags with
      | some true =>
        .retired ⟨m.state.setRip (m.state.core.rip + 2#64 + rel.signExtend 64), m.memory⟩
      | some false => .retired ⟨m.state.setRip (m.state.core.rip + 2#64), m.memory⟩
      | none => .undefinedFlag cc := by
  have hf := fetch_eq_decoded_iff.mpr ⟨bytes, fetched, decoded⟩
  simp only [step, hf]

/-- `UD2` at RIP raises #UD. -/
theorem step_of_ud2 {exit : Word} {m : MState} {bytes : List Byte} {length : Nat}
    (fetched : m.memory.fetchBytes m.state.core.rip.toNat length = some bytes)
    (decoded : Insn.decode bytes = some (.ctl .ud2, length)) :
    step exit m = .invalidOpcode := by
  have hf := fetch_eq_decoded_iff.mpr ⟨bytes, fetched, decoded⟩
  simp only [step, hf]

/-- On the integer state, an integer instruction retires exactly as in
`X86.MState.step`; the XMM registers and MXCSR are unchanged. -/
theorem step_of_int_retired {exit : Word} {m : MState} {core : X86.State} {memory : Memory}
    (h : X86.MState.step exit ⟨m.state.core, m.memory⟩ = .retired ⟨core, memory⟩) :
    step exit m = .retired ⟨{ m.state with core }, memory⟩ := by
  unfold X86.MState.step at h
  split at h
  · cases h
  · cases h
  · rename_i i n hf
    split at h
    · cases h
    · rename_i core' memory' hexec
      have hf' := fetch_of_int hf
      simp only [step, hf', hexec]
      split at h
      · cases h
      · rename_i hret
        simp only [X86.Outcome.retired.injEq, X86.MState.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [hret]

/-- On the integer state, a return to `exit` is exactly as in
`X86.MState.step`; the XMM registers and MXCSR are unchanged. -/
theorem step_of_int_returned {exit : Word} {m : MState} {core : X86.State} {memory : Memory}
    (h : X86.MState.step exit ⟨m.state.core, m.memory⟩ = .returned ⟨core, memory⟩) :
    step exit m = .returned ⟨{ m.state with core }, memory⟩ := by
  unfold X86.MState.step at h
  split at h
  · cases h
  · cases h
  · rename_i i n hf
    split at h
    · cases h
    · rename_i core' memory' hexec
      have hf' := fetch_of_int hf
      simp only [step, hf', hexec]
      split at h
      · rename_i hret
        simp only [X86.Outcome.returned.injEq, X86.MState.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [hret]
      · cases h

/-- A retiring integer step leaves the XMM registers and MXCSR unchanged. -/
theorem step_int_frame {exit : Word} {m next : MState} {i : X86.Insn} {n : Nat}
    (hf : fetch m.memory m.state.core.rip.toNat = .decoded (.int i) n)
    (h : step exit m = .retired next ∨ step exit m = .returned next) :
    next.state.xmm = m.state.xmm ∧ next.state.mxcsr = m.state.mxcsr := by
  simp only [step, hf] at h
  split at h
  · simp at h
  · split at h <;> rcases h with h | h <;> cases h <;> exact ⟨rfl, rfl⟩

/-- With every SIMD exception masked, no step raises #XM. -/
theorem step_ne_simd_of_allMasked {exit : Word} {m : MState} (h : m.state.mxcsr.AllMasked)
    (i : Instr) (mxcsr : MXCSR) : step exit m ≠ .simdException i mxcsr := by
  intro e
  unfold step at e
  split at e
  · cases e
  · split at e
    · cases e
    · split at e <;> cases e
  · rename_i j n hf
    split at e
    · cases e
    · cases e
    · cases e
    · cases e
    · rename_i mx hexec
      exact exec_ne_simd_of_allMasked _ _ _ _ h hexec
  · split at e <;> cases e
  · cases e

/-- Under the reset MXCSR no step raises #XM. -/
theorem step_ne_simd_of_reset {exit : Word} {m : MState} (h : m.state.mxcsr = MXCSR.reset)
    (i : Instr) (mxcsr : MXCSR) : step exit m ≠ .simdException i mxcsr :=
  step_ne_simd_of_allMasked (h ▸ MXCSR.reset_allMasked) i mxcsr

/-- A retired or returned step keeps MXCSR well formed. -/
theorem step_wellFormed {exit : Word} {m next : MState} (hw : m.state.mxcsr.WellFormed)
    (h : step exit m = .retired next ∨ step exit m = .returned next) :
    next.state.mxcsr.WellFormed := by
  unfold step at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h <;> rcases h with h | h <;> cases h <;> exact hw
  · split at h <;> rcases h with h | h <;> (try cases h)
    rename_i hexec
    exact exec_commit_wellFormed hexec hw
  · split at h <;> rcases h with h | h <;> cases h <;> exact hw
  · rcases h with h | h <;> cases h

end MState

/-! ## Kernel-checked vectors

Concrete instances evaluated by the kernel (`decide +kernel`). Byte strings
are the assembler encodings of `Float/Examples.lean` and `X86/Examples.lean`.
Expected values follow the SDM rules cited in `Semantics.lean`, not execution
on hardware. -/

namespace Examples

private def st (xmm : XReg → BitVec 128) (mxcsr : MXCSR := MXCSR.reset) : State :=
  { core := { regs := fun _ => 0, rip := 0x1000, flags := ⟨none, none, none, none, none, none⟩ },
    xmm, mxcsr }

private def mem0 : Memory := ⟨[], {}⟩

/-- xmm0 = 1.0f with nonzero upper bits, xmm1 = 2.0f, xmm2 = a quiet NaN,
xmm4 = the least positive binary32 subnormal, xmm5 = +0. -/
private def regs : XReg → BitVec 128
  | .xmm0 => 0xdeadbeef_cafebabe_12345678_3f800000#128
  | .xmm1 => 0x40000000#128
  | .xmm2 => 0x7fc00000#128
  | .xmm4 => 0x1#128
  | _ => 0

private def xmmAfter (r : Result) (x : XReg) : Option (BitVec 128) :=
  match r with
  | .commit t _ => some (t.readX x)
  | _ => none

private def mxcsrAfter (r : Result) : Option (BitVec 32) :=
  match r with
  | .commit t _ => some t.mxcsr.bits
  | .fault (.simd m) => some m.bits
  | _ => none

private def simd (r : Result) : Bool :=
  match r with
  | .fault (.simd _) => true
  | _ => false

-- `F3 0F 58 C1` is ADDSS xmm0, xmm1; `48 01 F0` is ADD rax, rsi; `41 0F 28 C0`
-- is MOVAPS xmm0, xmm8.
example : Insn.decode [0xF3, 0x0F, 0x58, 0xC1, 0xC3] =
    some (.sse (.arith .add .single .xmm0 (.reg .xmm1)), 4) := by decide +kernel
example : Insn.decode [0x48, 0x01, 0xF0] = some (.int (.base (.alu .add .rax .rsi)), 3) := by
  decide +kernel
example : Insn.decode [0x41, 0x0F, 0x28, 0xC0] = some (.sse (.movap .single .xmm0 .xmm8), 4) := by
  decide +kernel
-- `77 02` is JA +2 and `0F 0B` is UD2.
example : Insn.decode [0x77, 0x02, 0x0F, 0x0B] = some (.ctl (.jcc 7 2), 2) := by decide +kernel
example : Insn.decode [0x0F, 0x0B, 0xC3] = some (.ctl .ud2, 2) := by decide +kernel
-- JA after an unordered UCOMISS (ZF = PF = CF = 1) is not taken; JB is.
example : condHolds 7 ⟨some true, some true, some false, some true, some false, some false⟩ =
    some false := by decide +kernel
example : condHolds 2 ⟨some true, some true, some false, some true, some false, some false⟩ =
    some true := by decide +kernel

-- ADDSS: 1 + 2 = 3 (`40400000H`) in the low lane; bits 127:32 are kept; exact,
-- so MXCSR is unchanged.
example : xmmAfter ((Instr.arith .add .single .xmm0 (.reg .xmm1)).exec (st regs) mem0) .xmm0 =
    some 0xdeadbeef_cafebabe_12345678_40400000#128 := by decide +kernel
example : mxcsrAfter ((Instr.arith .add .single .xmm0 (.reg .xmm1)).exec (st regs) mem0) =
    some 0x1F80#32 := by decide +kernel

-- ADDSS with a subnormal operand: DE and PE (`1FA2H`); under DAZ neither (the
-- operand is zero, the sum exact).
example : mxcsrAfter ((Instr.arith .add .single .xmm0 (.reg .xmm4)).exec (st regs) mem0) =
    some 0x1FA2#32 := by decide +kernel
example : mxcsrAfter
    ((Instr.arith .add .single .xmm0 (.reg .xmm4)).exec (st regs ⟨0x1FC0#32⟩) mem0) =
    some 0x1FC0#32 := by decide +kernel

-- DIVSS by zero: ZE when masked; #XM when ZM is clear.
example : mxcsrAfter ((Instr.arith .div .single .xmm0 (.reg .xmm5)).exec (st regs) mem0) =
    some 0x1F84#32 := by decide +kernel
example : simd ((Instr.arith .div .single .xmm0 (.reg .xmm5)).exec (st regs ⟨0x1D80#32⟩) mem0) =
    true := by decide +kernel

-- UCOMISS with a quiet NaN: unordered (ZF = PF = CF = 1, OF = SF = AF = 0), no
-- IE; COMISS signals IE, and faults when IM is clear.
example : (match (Instr.ucomi .single .xmm0 (.reg .xmm2)).exec (st regs) mem0 with
      | .commit t _ => some t.core.flags
      | _ => none) =
    some ⟨some true, some true, some false, some true, some false, some false⟩ := by decide +kernel
example : mxcsrAfter ((Instr.ucomi .single .xmm0 (.reg .xmm2)).exec (st regs) mem0) =
    some 0x1F80#32 := by decide +kernel
example : mxcsrAfter ((Instr.comi .single .xmm0 (.reg .xmm2)).exec (st regs) mem0) =
    some 0x1F81#32 := by decide +kernel
example : simd ((Instr.comi .single .xmm0 (.reg .xmm2)).exec (st regs ⟨0x1F00#32⟩) mem0) = true := by
  decide +kernel

-- CVTTSS2SI eax, NaN: the indefinite value `80000000H`, zero-extended into RAX.
example : (match (Instr.cvtToIntTrunc .single .w32 .rax (.reg .xmm2)).exec (st regs) mem0 with
      | .commit t _ => some (t.core.read .rax)
      | _ => none) = some 0x80000000#64 := by decide +kernel

-- CMPSS EQ of xmm0 with itself: all ones in the low lane, upper bits kept.
example : xmmAfter ((Instr.cmp .single .eq .xmm0 (.reg .xmm0)).exec (st regs) mem0) .xmm0 =
    some 0xdeadbeef_cafebabe_12345678_ffffffff#128 := by decide +kernel

-- ROUNDSS 1.5 to nearest: 2.0; PE unless imm8[3] suppresses it.
example : mxcsrAfter ((Instr.round .single .xmm0 (.reg .xmm3) ⟨0, false, false⟩).exec
    (st fun r => if r = .xmm3 then 0x3fc00000#128 else 0) mem0) = some 0x1FA0#32 := by
  decide +kernel
example : mxcsrAfter ((Instr.round .single .xmm0 (.reg .xmm3) ⟨0, false, true⟩).exec
    (st fun r => if r = .xmm3 then 0x3fc00000#128 else 0) mem0) = some 0x1F80#32 := by
  decide +kernel

-- MULSS of the least normal binary32 by 0.5: an exact tiny result. With UM set
-- no flag is raised; with UM clear the underflow condition is tininess alone,
-- so the instruction faults.
example : mxcsrAfter ((Instr.arith .mul .single .xmm0 (.reg .xmm3)).exec
    (st fun r => if r = .xmm3 then 0x3f000000#128 else if r = .xmm0 then 0x00800000#128 else 0)
    mem0) = some 0x1F80#32 := by decide +kernel
example : simd ((Instr.arith .mul .single .xmm0 (.reg .xmm3)).exec
    (st (fun r => if r = .xmm3 then 0x3f000000#128 else if r = .xmm0 then 0x00800000#128 else 0)
      ⟨0x1780#32⟩) mem0) = true := by decide +kernel

end Examples

end Silmaril.X86.Float
