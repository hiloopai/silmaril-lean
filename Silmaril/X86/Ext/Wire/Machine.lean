module

public import Silmaril.X86.Ext.Wire.Semantics
public import Silmaril.X86.Ext.Wire.Prefix
public import Silmaril.X86.Ext.Machine

/-!
# Memory-backed machine for byte-faithful instructions

Fetch checks the entire consumed execute span. Data faults, divide errors,
undefined conditions and traps remain distinct and have no successor state.
The canonical extended machine embeds with identical register/memory states.
-/

@[expose] public section

namespace Silmaril.X86.Ext.Wire

open Silmaril.X86 (Byte Word State MState fetchWindow maxInstrLength)
open Silmaril.Process (Memory)

inductive Fetch where
  | decoded (d : Decoded)
  | truncated
  | undecodable

def fetch (memory : Memory) (address : Nat) : Fetch :=
  let bytes := fetchWindow memory maxInstrLength address
  match decode bytes with
  | some d => if memory.Permitted .execute address d.length then .decoded d else .truncated
  | none =>
    match parseRaw bytes with
    | .eof => if bytes.length < maxInstrLength then .truncated else .undecodable
    | _ => .undecodable

/-- Bounds needed to fetch precisely the bytes consumed by a successful decode. -/
theorem decode_length {bytes : List Byte} {d : Decoded} (h : decode bytes = some d) :
    0 < d.length ∧ d.length ≤ maxInstrLength ∧ d.length ≤ bytes.length := by
  obtain ⟨pos, limit, retained, -⟩ := decode_sound h
  have hl := congrArg List.length retained
  simp only [encode, Decoded.length, List.length_take] at hl
  exact ⟨pos, limit, by change d.bytes.length ≤ bytes.length; omega⟩

theorem decode_take {bytes : List Byte} {d : Decoded} (h : decode bytes = some d) :
    decode (bytes.take d.length) = some d := by
  rw [← (decode_sound h).2.2.1]
  exact decode_encode h

/-- Successful fetches are exactly checked byte spans that decode on their own. -/
theorem fetch_eq_decoded_iff {memory : Memory} {address : Nat} {d : Decoded} :
    fetch memory address = .decoded d ↔
      ∃ bytes, memory.fetchBytes address d.length = some bytes ∧ decode bytes = some d := by
  constructor
  · intro h
    dsimp only [fetch] at h
    split at h
    · rename_i candidate hd
      split at h
      · cases h
        obtain ⟨pos, -, bound⟩ := decode_length hd
        exact ⟨_, X86.fetchWindow_fetchBytes memory _ address d.length pos bound, decode_take hd⟩
      · cases h
    · split at h
      · split at h <;> cases h
      · cases h
  · rintro ⟨bytes, fetched, decoded⟩
    obtain ⟨-, limit, -⟩ := decode_length decoded
    obtain ⟨more, hmore⟩ := X86.fetchBytes_prefix_fetchWindow fetched limit
    have hd := decode_append decoded more
    rw [hmore] at hd
    dsimp only [fetch]
    rw [hd]
    exact ite_eq_left (Memory.readWith_permitted fetched)

inductive Outcome where
  | retired (next : MState)
  | returned (final : MState)
  | trapped
  | undefinedCondition (c : Cond)
  | divideFault
  | dataFault (instr : Instr)
  | fetchFault
  | undecodable

/-- Fetch and execute with the exact consumed length. -/
def step (platform : Platform) (exit : Word) (m : MState) : Outcome :=
  match fetch m.memory m.core.rip.toNat with
  | .undecodable => .undecodable
  | .truncated => .fetchFault
  | .decoded d =>
    match exec platform d m.core m.memory with
    | .ok core memory =>
      if d.instr = .canonical .ret ∧ core.rip = exit then .returned ⟨core, memory⟩
      else .retired ⟨core, memory⟩
    | .dataFault => .dataFault d.instr
    | .divideError => .divideFault
    | .undefinedCondition c => .undefinedCondition c
    | .trap => .trapped

def stepOpt (platform : Platform) (exit : Word) (m : MState) : Option MState :=
  match step platform exit m with
  | .retired next => some next
  | _ => none

def Returns (platform : Platform) (exit : Word) (initial final : MState) : Prop :=
  ∃ n mid, Machine.Execution.run (stepOpt platform exit) n initial = some mid ∧
    step platform exit mid = .returned final

theorem stepOpt_eq_some_iff {platform : Platform} {exit : Word} {m next : MState} :
    stepOpt platform exit m = some next ↔ step platform exit m = .retired next := by
  unfold stepOpt
  split <;> simp_all

/-- A decoded canonical prefix is read identically by the lossless decoder. -/
theorem decode_of_ext {bytes : List Byte} {i : Ext.Instr} {n : Nat}
    (h : Ext.decode bytes = some (i, n)) :
    decode bytes = some ⟨.canonical i, Ext.encode i⟩ := by
  obtain ⟨-, ht⟩ := Ext.decode_sound h
  rw [ht, decode_canonical_append]

/-- Every successful fetch of the canonical machine is preserved. -/
theorem fetch_of_ext {memory : Memory} {address : Nat} {i : Ext.Instr} {n : Nat}
    (h : Ext.fetch memory address = .decoded i n) :
    fetch memory address = .decoded ⟨.canonical i, Ext.encode i⟩ := by
  unfold Ext.fetch at h
  split at h
  · rename_i instr length hd
    split at h
    · rename_i hp
      cases h
      have hl := (Ext.decode_length hd).1
      simp only [fetch, decode_of_ext hd, Decoded.length]
      have hp' : memory.Permitted .execute address (Ext.encode i).length := by simpa [hl] using hp
      exact ite_eq_left hp'
    · cases h
  · split at h
    · split at h <;> cases h
    · cases h

def Outcome.ofExt : Ext.Outcome → Outcome
  | .retired next => .retired next
  | .returned final => .returned final
  | .trapped => .trapped
  | .undefinedCondition c => .undefinedCondition c
  | .divideFault => .divideFault
  | .dataFault i => .dataFault (.canonical i)
  | .fetchFault => .fetchFault
  | .undecodable => .undecodable

/-- All results of a decoded canonical instruction are preserved, including faults. -/
theorem step_of_ext_decoded {platform : Platform} {exit : Word} {m : MState}
    {i : Ext.Instr} {n : Nat}
    (h : Ext.fetch m.memory m.core.rip.toNat = .decoded i n) :
    step platform exit m = Outcome.ofExt (Ext.step exit m) := by
  simp only [step, fetch_of_ext h, exec_canonical, Ext.step, h]
  cases he : Ext.exec i m.core m.memory with
  | ok core memory =>
    simp only [Instr.canonical.injEq]
    split <;> rfl
  | _ => rfl

private theorem ext_decoded_of_retired_or_returned {exit : Word} {m next : MState}
    (h : Ext.step exit m = .retired next ∨ Ext.step exit m = .returned next) :
    ∃ i n, Ext.fetch m.memory m.core.rip.toNat = .decoded i n := by
  unfold Ext.step at h
  split at h
  · simp at h
  · simp at h
  · exact ⟨_, _, by assumption⟩

theorem stepOpt_of_ext {platform : Platform} {exit : Word} {m next : MState}
    (h : Ext.stepOpt exit m = some next) : stepOpt platform exit m = some next := by
  rw [Ext.stepOpt_eq_some_iff] at h
  obtain ⟨i, n, hf⟩ := ext_decoded_of_retired_or_returned (.inl h)
  rw [stepOpt_eq_some_iff, step_of_ext_decoded hf, h]
  rfl

theorem step_returned_of_ext {platform : Platform} {exit : Word} {m final : MState}
    (h : Ext.step exit m = .returned final) : step platform exit m = .returned final := by
  obtain ⟨i, n, hf⟩ := ext_decoded_of_retired_or_returned (.inr h)
  rw [step_of_ext_decoded hf, h]
  rfl

theorem run_of_ext {platform : Platform} {exit : Word} (n : Nat) {initial mid : MState}
    (h : Machine.Execution.run (Ext.stepOpt exit) n initial = some mid) :
    Machine.Execution.run (stepOpt platform exit) n initial = some mid := by
  induction n generalizing initial with
  | zero => simpa using h
  | succ n ih =>
    simp only [Machine.Execution.run_succ] at h ⊢
    cases hs : Ext.stepOpt exit initial with
    | none => simp [hs] at h
    | some next =>
      rw [hs] at h
      rw [stepOpt_of_ext hs]
      exact ih h

theorem returns_of_ext {platform : Platform} {exit : Word} {initial final : MState}
    (h : Ext.Returns exit initial final) : Returns platform exit initial final := by
  obtain ⟨n, mid, hrun, hret⟩ := h
  exact ⟨n, mid, run_of_ext n hrun, step_returned_of_ext hret⟩

/-- Execute from an observed fetch window and a checked consumed execute span. -/
theorem step_of_decodeWindow {platform : Platform} {exit : Word} {m : MState} {d : Decoded}
    (decoded : decode (fetchWindow m.memory maxInstrLength m.core.rip.toNat) = some d)
    (permitted : m.memory.Permitted .execute m.core.rip.toNat d.length) :
    step platform exit m =
      match exec platform d m.core m.memory with
      | .ok core memory =>
        if d.instr = .canonical .ret ∧ core.rip = exit then .returned ⟨core, memory⟩
        else .retired ⟨core, memory⟩
      | .dataFault => .dataFault d.instr
      | .divideError => .divideFault
      | .undefinedCondition c => .undefinedCondition c
      | .trap => .trapped := by
  simp only [step, fetch, decoded, permitted, ite_true]

/-- One step from a checked consumed span; trailing code need not be specified. -/
theorem step_of_fetch {platform : Platform} {exit : Word} {m : MState}
    {bytes : List Byte} {d : Decoded}
    (fetched : m.memory.fetchBytes m.core.rip.toNat d.length = some bytes)
    (decoded : decode bytes = some d) :
    step platform exit m =
      match exec platform d m.core m.memory with
      | .ok core memory =>
        if d.instr = .canonical .ret ∧ core.rip = exit then .returned ⟨core, memory⟩
        else .retired ⟨core, memory⟩
      | .dataFault => .dataFault d.instr
      | .divideError => .divideFault
      | .undefinedCondition c => .undefinedCondition c
      | .trap => .trapped := by
  have hf := fetch_eq_decoded_iff.mpr ⟨bytes, fetched, decoded⟩
  simp only [step, hf]

end Silmaril.X86.Ext.Wire
