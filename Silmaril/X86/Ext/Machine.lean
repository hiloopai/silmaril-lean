module

public import Silmaril.X86.Ext.Semantics

/-!
# A memory-backed fetch/decode/execute machine for the extended model

`step exit m` fetches at RIP, decodes one `Ext.Instr` and executes it on
`X86.MState` (registers, RIP, flags and a `Process.Memory`). This is a
handwritten local model of a single sequential user-mode thread; it is not
derived from, or proved to correspond with, the Sail, ACL2 or any hardware
description.

## Fetch

As in `X86/Machine.lean`, no 15-byte executable window is required. The
fetcher collects the available bytes (`X86.fetchWindow`: at most 15 bytes from
RIP, each mapped executable, below 2^64 and backed) and decodes them;
`fetch_eq_decoded_iff` shows that this is the same as decoding exactly the
consumed bytes, fetched as one checked span.

A failed decode is classified by the length decoder `parseRaw`:

* `Fetch.truncated`: the length decoder ran out of available bytes, and fewer
  than 15 were available. The next byte cannot be fetched, and every
  instruction that decodes from an extension of the available bytes is longer
  than them (`fetch_truncated`). It is reported as a fetch fault. This is a
  statement about the instruction's length structure (prefixes, opcode, ModRM,
  SIB, displacement, immediate); the bytes need not begin a supported
  instruction.
* `Fetch.undecodable`: no extension of the available bytes decodes
  (`fetch_undecodable`). These bytes are outside the supported canonical
  subset.

## Outcomes

`Outcome` distinguishes a retirement, a RET that pops the designated return
address `exit`, the UD2 trap, a SETcc/Jcc/CMOVcc that depends on an undefined flag, a
divide fault (`#DE`), a data-access fault, a fetch fault and undecodable bytes.
No fault outcome carries a successor state, and a faulting instruction has no
partial effect.

## Consilience with `X86.MState.step`

`fetch_ofInsn_iff` shows that this fetch decodes an embedded instruction
exactly when `X86.fetch` decodes the original, and `step_of_x86_decoded`
that the outcomes then agree (`Outcome.ofX86`). Hence every retirement,
return and finite `X86.MState.Returns` run of the existing machine is one of
this machine (`stepOpt_of_x86`, `returns_of_x86`). The converse does not hold
for bytes the existing model rejects: those may decode here.
-/

@[expose] public section

namespace Silmaril.X86.Ext

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.Process (Memory)
open ByteParser

/-! ## Fetch -/

/-- The result of fetching and decoding at an address. -/
inductive Fetch where
  | decoded (instr : Instr) (length : Nat)
  | truncated
  | undecodable

def fetch (memory : Memory) (address : Nat) : Fetch :=
  match decode (fetchWindow memory maxInstrLength address) with
  | some (instr, length) =>
    if memory.Permitted .execute address length then .decoded instr length else .truncated
  | none =>
    match parseRaw (fetchWindow memory maxInstrLength address) with
    | .eof =>
      if (fetchWindow memory maxInstrLength address).length < maxInstrLength then .truncated
      else .undecodable
    | _ => .undecodable

/-- Fetching succeeds exactly when the consumed bytes, fetched as one checked
span, decode to the instruction on their own. -/
theorem fetch_eq_decoded_iff {memory : Memory} {address : Nat} {instr : Instr} {length : Nat} :
    fetch memory address = .decoded instr length ↔
      ∃ bytes, memory.fetchBytes address length = some bytes ∧
        decode bytes = some (instr, length) := by
  constructor
  · intro h
    unfold fetch at h
    split at h
    · rename_i i n hdecode
      split at h
      · cases h
        obtain ⟨-, pos, -, le⟩ := decode_length hdecode
        exact ⟨_, X86.fetchWindow_fetchBytes memory _ address length pos le, decode_take hdecode⟩
      · cases h
    · split at h
      · split at h <;> cases h
      · cases h
  · rintro ⟨bytes, fetched, decoded⟩
    obtain ⟨-, -, le, -⟩ := decode_length decoded
    obtain ⟨more, hmore⟩ := X86.fetchBytes_prefix_fetchWindow fetched
      (limit := maxInstrLength) (by unfold maxInstrLength; omega)
    have hdecode := decode_append more decoded
    rw [hmore] at hdecode
    unfold fetch
    rw [hdecode]
    simp only [Memory.readWith_permitted fetched, ite_true]

theorem fetch_length {memory : Memory} {address : Nat} {instr : Instr} {length : Nat}
    (h : fetch memory address = .decoded instr length) : length = instr.length := by
  obtain ⟨_, -, decoded⟩ := fetch_eq_decoded_iff.mp h
  exact (decode_length decoded).1

/-- If the length decoder runs out of bytes, every decode of an extension
consumes more than the given bytes. -/
theorem decode_append_long {w more : List Byte} {i : Instr} {n : Nat}
    (heof : parseRaw w = .eof) (h : decode (w ++ more) = some (i, n)) : w.length < n := by
  obtain ⟨hn, t, ht⟩ := decode_eq_some_iff.mp h
  have hp := parseRaw_encode i t
  rw [ht] at hp
  have := good_parseRaw.eof heof more _ _ hp
  have hlen := congrArg List.length ht
  simp only [List.length_append] at hlen
  omega

/-- A fetch fault: the length decoder needs a byte beyond the available ones,
fewer than fifteen bytes are available, the next byte cannot be fetched, and
every instruction decoding from an extension of the available bytes is longer
than them. -/
theorem fetch_truncated {memory : Memory} {address : Nat}
    (h : fetch memory address = .truncated) :
    parseRaw (fetchWindow memory maxInstrLength address) = .eof ∧
      (fetchWindow memory maxInstrLength address).length < maxInstrLength ∧
      memory.fetchBytes (address + (fetchWindow memory maxInstrLength address).length) 1 =
        none ∧
      ∀ more i n, decode (fetchWindow memory maxInstrLength address ++ more) = some (i, n) →
        (fetchWindow memory maxInstrLength address).length < n := by
  unfold fetch at h
  split at h
  · rename_i i n hdecode
    split at h
    · cases h
    · rename_i hperm
      obtain ⟨-, pos, -, le⟩ := decode_length hdecode
      exact absurd (Memory.readWith_permitted
        (X86.fetchWindow_fetchBytes memory _ address n pos le)) hperm
  · split at h
    · rename_i heof
      split at h
      · rename_i hshort
        exact ⟨heof, hshort, X86.fetchWindow_stop memory _ address hshort,
          fun more i n hd => decode_append_long heof hd⟩
      · cases h
    · cases h

/-- Undecodable bytes: no extension of the available bytes decodes. -/
theorem fetch_undecodable {memory : Memory} {address : Nat}
    (h : fetch memory address = .undecodable) :
    ∀ more, decode (fetchWindow memory maxInstrLength address ++ more) = none := by
  intro more
  unfold fetch at h
  split at h
  · split at h <;> cases h
  · rename_i hnone
    set w := fetchWindow memory maxInstrLength address
    cases hd : decode (w ++ more) with
    | none => rfl
    | some res =>
      obtain ⟨i, n⟩ := res
      exfalso
      obtain ⟨hn, t, ht⟩ := decode_eq_some_iff.mp hd
      have hp := parseRaw_encode i t
      rw [ht] at hp
      split at h
      · rename_i heof
        split at h
        · cases h
        · rename_i hlong
          have := decode_append_long heof hd
          have := (decode_length hd).2.2.1
          unfold maxInstrLength at hlong
          omega
      · rename_i hne
        cases hw : parseRaw w with
        | eof => exact hne hw
        | bad =>
          rw [good_parseRaw.bad hw more] at hp
          cases hp
        | ok r rest =>
          obtain ⟨hle, hext⟩ := good_parseRaw.ok hw
          rw [hext more] at hp
          obtain ⟨-, hrest⟩ := PResult.ok.inj hp
          subst hrest
          have hw' : w = encode i ++ rest := by
            have : w ++ more = (encode i ++ rest) ++ more := by rw [List.append_assoc, ht]
            exact List.append_cancel_right this
          have := decode_encode_append i rest
          rw [← hw', hnone] at this
          cases this

/-! ## One step -/

/-- The result of one step. Faults change nothing. -/
inductive Outcome where
  /-- The instruction retired with this successor state. -/
  | retired (next : MState)
  /-- A RET popped the designated return address; this is the state after it. -/
  | returned (final : MState)
  /-- UD2 at RIP. -/
  | trapped
  /-- A SETcc, Jcc or CMOVcc whose condition depends on an undefined flag. -/
  | undefinedCondition (c : Cond)
  /-- `#DE` from DIV or IDIV. -/
  | divideFault
  /-- A data access of this instruction was not permitted or not backed. -/
  | dataFault (instr : Instr)
  /-- The length decoder needs a byte that cannot be fetched. -/
  | fetchFault
  /-- The bytes at RIP are outside the supported canonical subset. -/
  | undecodable

/-- Fetch, decode and execute one instruction. A RET whose popped target is
`exit` reports `returned`; any other RET retires normally. -/
def step (exit : Word) (m : MState) : Outcome :=
  match fetch m.memory m.core.rip.toNat with
  | .undecodable => .undecodable
  | .truncated => .fetchFault
  | .decoded instr _ =>
    match exec instr m.core m.memory with
    | .ok core memory =>
      if instr = .ret ∧ core.rip = exit then .returned ⟨core, memory⟩
      else .retired ⟨core, memory⟩
    | .dataFault => .dataFault instr
    | .divideError => .divideFault
    | .undefinedCondition c => .undefinedCondition c
    | .trap => .trapped

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

/-- One step from exactly fetched bytes. -/
theorem step_of_fetch {exit : Word} {m : MState} {bytes : List Byte} {instr : Instr}
    {length : Nat} (fetched : m.memory.fetchBytes m.core.rip.toNat length = some bytes)
    (decoded : decode bytes = some (instr, length)) :
    step exit m =
      match exec instr m.core m.memory with
      | .ok core memory =>
        if instr = .ret ∧ core.rip = exit then .returned ⟨core, memory⟩
        else .retired ⟨core, memory⟩
      | .dataFault => .dataFault instr
      | .divideError => .divideFault
      | .undefinedCondition c => .undefinedCondition c
      | .trap => .trapped := by
  have hf := fetch_eq_decoded_iff.mpr ⟨bytes, fetched, decoded⟩
  simp only [step, hf]

/-- UD2 traps. -/
theorem step_ud2 {exit : Word} {m : MState}
    (fetched : m.memory.fetchBytes m.core.rip.toNat 2 = some [0x0F, 0x0B]) :
    step exit m = .trapped := by
  rw [step_of_fetch fetched (by decide : decode [0x0F, 0x0B] = some (.ud2, 2))]
  rfl

/-! ## Consilience with the existing machine -/

/-- The outcomes of `X86.MState.step`, read as outcomes of this machine. -/
def Outcome.ofX86 : X86.Outcome → Outcome
  | .retired next => .retired next
  | .returned final => .returned final
  | .undecodable => .undecodable
  | .fetchFault => .fetchFault
  | .memoryFault instr => .dataFault (ofInsn instr)

/-- This fetch decodes an embedded instruction exactly when the existing
fetch decodes the original. -/
theorem fetch_ofInsn_iff {memory : Memory} {address : Nat} {i : X86.Insn} {n : Nat} :
    fetch memory address = .decoded (ofInsn i) n ↔ X86.fetch memory address = .decoded i n := by
  rw [fetch_eq_decoded_iff, X86.fetch_eq_decoded_iff]
  simp only [decode_ofInsn_iff]

/-- Whenever the existing machine decodes an instruction, both machines take
the same step. -/
theorem step_of_x86_decoded {exit : Word} {m : MState} {i : X86.Insn} {n : Nat}
    (h : X86.fetch m.memory m.core.rip.toNat = .decoded i n) :
    step exit m = Outcome.ofX86 (X86.MState.step exit m) := by
  have hf := fetch_ofInsn_iff.mpr h
  simp only [step, hf, X86.MState.step, h, exec_ofInsn]
  cases hx : i.exec m.core m.memory with
  | none => rfl
  | some r =>
    obtain ⟨core, memory⟩ := r
    simp only
    have hret : (ofInsn i = .ret) ↔ (i = .ret) := by
      constructor
      · intro e
        have := congrArg toInsn? e
        rw [toInsn?_ofInsn] at this
        exact Option.some.inj (this.trans rfl)
      · rintro rfl; rfl
    by_cases hc : i = .ret ∧ core.rip = exit
    · have : ofInsn i = .ret ∧ core.rip = exit := ⟨hret.mpr hc.1, hc.2⟩
      rw [ite_eq_left this, ite_eq_left hc]
      rfl
    · have : ¬ (ofInsn i = .ret ∧ core.rip = exit) := fun e => hc ⟨hret.mp e.1, e.2⟩
      simp only [this, hc, ite_false, Outcome.ofX86]

/-- The same statement, from the decoded embedded instruction. -/
theorem step_of_decoded_ofInsn {exit : Word} {m : MState} {i : X86.Insn} {n : Nat}
    (h : fetch m.memory m.core.rip.toNat = .decoded (ofInsn i) n) :
    step exit m = Outcome.ofX86 (X86.MState.step exit m) :=
  step_of_x86_decoded (fetch_ofInsn_iff.mp h)

private theorem x86_decoded_of_retired_or_returned {exit : Word} {m next : MState}
    (h : X86.MState.step exit m = .retired next ∨ X86.MState.step exit m = .returned next) :
    ∃ i n, X86.fetch m.memory m.core.rip.toNat = .decoded i n := by
  unfold X86.MState.step at h
  split at h
  · simp at h
  · simp at h
  · exact ⟨_, _, by assumption⟩

/-- Every retirement of the existing machine is a retirement of this one. -/
theorem stepOpt_of_x86 {exit : Word} {m next : MState}
    (h : X86.MState.stepOpt exit m = some next) : stepOpt exit m = some next := by
  rw [X86.MState.stepOpt_eq_some_iff] at h
  obtain ⟨i, n, hf⟩ := x86_decoded_of_retired_or_returned (.inl h)
  rw [stepOpt_eq_some_iff, step_of_x86_decoded hf, h]
  rfl

/-- Every return of the existing machine is a return of this one. -/
theorem step_returned_of_x86 {exit : Word} {m final : MState}
    (h : X86.MState.step exit m = .returned final) : step exit m = .returned final := by
  obtain ⟨i, n, hf⟩ := x86_decoded_of_retired_or_returned (.inr h)
  rw [step_of_x86_decoded hf, h]
  rfl

theorem run_of_x86 {exit : Word} (n : Nat) {initial mid : MState}
    (h : Machine.Execution.run (X86.MState.stepOpt exit) n initial = some mid) :
    Machine.Execution.run (stepOpt exit) n initial = some mid := by
  induction n generalizing initial with
  | zero => simpa using h
  | succ n ih =>
    simp only [Machine.Execution.run_succ] at h ⊢
    cases hs : X86.MState.stepOpt exit initial with
    | none => simp [hs] at h
    | some next =>
      rw [hs] at h
      rw [stepOpt_of_x86 hs]
      exact ih h

/-- Every finite run of the existing machine that returns to `exit` is one of
this machine, with the same final state. -/
theorem returns_of_x86 {exit : Word} {initial final : MState}
    (h : X86.MState.Returns exit initial final) : Returns exit initial final := by
  obtain ⟨n, mid, hrun, hret⟩ := h
  exact ⟨n, mid, run_of_x86 n hrun, step_returned_of_x86 hret⟩

end Silmaril.X86.Ext
