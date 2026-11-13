module

public import Silmaril.Proofs.X86.Atomic9.Decode
public import Silmaril.X86.Open9.Thms

/-!
# `Atomic9`: the conservative-extension laws and the listing law

Proofs for `Silmaril/X86/Atomic9/Thms.lean`.

* `step_of_open9`, `step_cases`, `run_of_open9`: every `Open9` step is a step, and every step
  is one of those or an atomic step.
* `step_of_fetch_new`, `step_of_listed_new`, `step_of_listed`: a listed form at the program
  counter that executes is one step.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Atomic9

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Atomic9

/-- **Every `Open9` step is a step.** -/
theorem step_of_open9 {m m' : MState} (h : Open9.step m = some m') : step m = some m' := by
  by_cases he : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat = .inl .undecodable
  · unfold Open9.step at h
    rw [he] at h
    simp only at h
    unfold step
    rw [he]
    simp only
    split
    · rename_i i n hf
      rw [hf] at h
      exact h
    · rename_i hf
      rw [hf] at h
      cases h
    · rename_i hf
      rw [hf] at h
      cases h
  · rw [Open9.step_eq_open he] at h
    unfold step
    split
    · rename_i he'; exact absurd he' he
    · exact h

/-- **Every step is an `Open9` step, or an atomic step** at bytes that `Ext8` and `Ext9`
reject. -/
theorem step_cases {m m' : MState} (h : step m = some m') :
    Open9.step m = some m' ∨
      (Open9.step m = none ∧ ∃ i n, fetchNew m.memory m.core.rip.toNat = some (some (i, n)) ∧
        Open.ofResult (execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n)) = some m') := by
  unfold step at h
  split at h
  · rename_i he
    split at h
    · rename_i i n hf
      left
      unfold Open9.step
      rw [he]
      simp only
      rw [hf]
      exact h
    · cases h
    · rename_i hf
      split at h
      · rename_i i n hs
        right
        refine ⟨?_, i, n, hs, h⟩
        unfold Open9.step
        rw [he]
        simp only
        rw [hf]
      · cases h
  · rename_i he
    left
    unfold Open9.step
    split
    · rename_i he'; exact absurd he' he
    · exact h

theorem run_of_open9 : ∀ (k : Nat) {a b : MState}, run Open9.step k a = some b →
    run step k a = some b
  | 0, _, _, h => h
  | k + 1, a, b, h => by
    simp only [run] at h ⊢
    cases e : Open9.step a with
    | none => simp [e] at h
    | some c =>
      rw [e] at h
      simp only [Option.bind_some] at h
      rw [step_of_open9 e]
      exact run_of_open9 k h

theorem reaches_of_open9 {a b : MState} (h : Reaches Open9.step a b) : Reaches step a b := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, run_of_open9 k hk⟩

/-- **The fetch form of the atomic law**: bytes `w` fetched (with execute permission) at the
program counter that `decodeL` reads as an atomic form of length `l`, and that execute, are one
step. -/
theorem step_of_fetch_new {m : MState} {l : Nat} {w : List Byte} {i : New} {c : State}
    {mem : Memory} (fetched : m.memory.fetchBytes m.core.rip.toNat l = some w)
    (hdec : decodeL w = some (i, l))
    (hx : execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  obtain ⟨hnone, hbad, hne, hbad9, hnew, -, h15⟩ := decodeL_spec hdec
  obtain ⟨more, hmore, hf8⟩ := Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn : Ext9.fetchNew m.memory m.core.rip.toNat = none := by
    unfold Ext9.fetchNew
    rw [hmore, ext9_decodeNew_none_of_bad hbad9 more]
    rfl
  have hfs : fetchNew m.memory m.core.rip.toNat = some (some (i, l)) := by
    unfold fetchNew
    rw [hmore, decodeNew_append hnew more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hf8, hfn, hfs, hx, Open.ofResult]

/-- **The atomic listing law.** -/
theorem step_of_listed_new {m : MState} {base : Word} {code : List Byte} {o l : Nat} {i : New}
    {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decodeL ((code.drop o).take l) = some (i, l))
    (hx : execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  obtain ⟨-, -, -, -, -, h1, -⟩ := decodeL_spec hdec
  have hA : m.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : m.memory.fetchBytes m.core.rip.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  exact step_of_fetch_new fetched hdec hx

/-- **The listing law of the machine** (both `Open9` and atomic listings). -/
theorem step_of_listed {m : MState} {base : Word} {code : List Byte} {o l : Nat} {i : Instr}
    {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : exec i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  rcases decode_cases hdec with ⟨j, rfl, hd⟩ | ⟨j, rfl, -, hd⟩
  · exact step_of_open9 (Open9.step_of_listed hl hrip hfit hd hx)
  · exact step_of_listed_new hl hrip hfit hd hx

end Silmaril.Proofs.X86.Atomic9
