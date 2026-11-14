module

public import Silmaril.Proofs.Machine.X86.Open.Step

/-!
# The listing law of the open machine

A listed instruction that `Open.decode` reads at the program counter of a loaded image and
that executes is one open step (`step_of_listed`). The decoder lemmas are copied from public
silmaril-lean `Silmaril/Apps/Sha256sum/X86Sys/SegVC8.lean` (rev `35a6f60`; there `decode8`,
`decode8_base`, `decode8_new`, `decode_none_append`, `fetch_undecodable_of`,
`rStep8_of_new`), with the Linux `syscall` interception removed.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.Open

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (parseRaw PResult Loaded)
open Silmaril.Process (Memory)
open Silmaril.Machine.X86.Open

/-- If the length decoder finishes inside `w` and `w` does not decode, no extension of `w`
decodes. -/
theorem decode_none_append {w : List Byte} (hnone : Silmaril.X86.Ext.decode w = none)
    (hne : parseRaw w ≠ .eof) (more : List Byte) :
    Silmaril.X86.Ext.decode (w ++ more) = none := by
  cases hd : Silmaril.X86.Ext.decode (w ++ more) with
  | none => rfl
  | some res =>
    obtain ⟨i, n⟩ := res
    exfalso
    obtain ⟨_, t, ht⟩ := Silmaril.X86.Ext.decode_eq_some_iff.mp hd
    have hp := Silmaril.X86.Ext.parseRaw_encode i t
    rw [ht] at hp
    cases hw : parseRaw w with
    | eof => exact hne hw
    | bad =>
      rw [Silmaril.X86.Ext.good_parseRaw.bad hw more] at hp
      cases hp
    | ok r rest =>
      obtain ⟨_, hext⟩ := Silmaril.X86.Ext.good_parseRaw.ok hw
      rw [hext more] at hp
      obtain ⟨-, hrest⟩ := PResult.ok.inj hp
      subst hrest
      have hw' : w = Silmaril.X86.Ext.encode i ++ rest := by
        have : w ++ more = (Silmaril.X86.Ext.encode i ++ rest) ++ more := by
          rw [List.append_assoc, ht]
        exact List.append_cancel_right this
      have := Silmaril.X86.Ext.decode_encode_append i rest
      rw [← hw', hnone] at this
      cases this

/-- The fetch at an address whose window extends such a slice is undecodable. -/
theorem fetch_undecodable_of {memory : Memory} {address : Nat} {w more : List Byte}
    (hwin : fetchWindow memory maxInstrLength address = w ++ more)
    (hnone : Silmaril.X86.Ext.decode w = none) (hne : parseRaw w ≠ .eof) :
    Silmaril.X86.Ext.fetch memory address = .undecodable := by
  unfold Silmaril.X86.Ext.fetch
  rw [hwin, decode_none_append hnone hne more]
  simp only
  split
  · rename_i heof
    exfalso
    cases hw : parseRaw w with
    | eof => exact hne hw
    | bad => rw [Silmaril.X86.Ext.good_parseRaw.bad hw more] at heof; cases heof
    | ok r rest => rw [(Silmaril.X86.Ext.good_parseRaw.ok hw).2 more] at heof; cases heof
  · rfl

theorem decode_base {bytes : List Byte} {i : Silmaril.X86.Ext.Instr} {n : Nat}
    (h : decode bytes = some (.base i, n)) : Silmaril.X86.Ext.decode bytes = some (i, n) := by
  unfold decode at h
  split at h
  · rename_i i' n' he
    simp only [Option.some.injEq, Prod.mk.injEq, Silmaril.X86.Ext8.Instr.base.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Silmaril.X86.Ext8.decode_base_iff.mp he
  · split at h
    · cases h
    · split at h <;> cases h
  · cases h

theorem decode_new {bytes : List Byte} {i : Silmaril.X86.Ext8.New} {n : Nat}
    (h : decode bytes = some (.new i, n)) :
    Silmaril.X86.Ext.decode bytes = none ∧ Silmaril.X86.Ext8.decodeNew bytes = some (i, n) ∧
      parseRaw bytes ≠ .eof ∧ 2 ≤ n ∧ n ≤ maxInstrLength := by
  unfold decode at h
  split at h
  · cases h
  · rename_i i' n' he
    have hd : Silmaril.X86.Ext.decode bytes = none ∧
        Silmaril.X86.Ext8.decodeNew bytes = some (i', n') := by
      unfold Silmaril.X86.Ext8.decode at he
      split at he
      · cases he
      · rename_i hn
        cases hdn : Silmaril.X86.Ext8.decodeNew bytes with
        | none => rw [hdn] at he; cases he
        | some r =>
          rw [hdn] at he
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨i'', n''⟩ := r
          simp only [Silmaril.X86.Ext8.Instr.new.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨hn, rfl⟩
    split at h
    · cases h
    · rename_i hne
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq, Silmaril.X86.Ext8.Instr.new.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hd.1, hd.2, hne, hc⟩
      · cases h
  · cases h

/-- **The law for an `X86.Ext` form.** -/
theorem step_of_base {m : MState} {base : Word} {code : List Byte} {o l : Nat}
    {i : Silmaril.X86.Ext.Instr} {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Ext.exec i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  have hlen : l = i.length := (Silmaril.X86.Ext.decode_length hdec).1
  subst hlen
  have hs := Silmaril.X86.Ext.step_of_loaded (exit := 0) hl hrip hfit hdec
  rw [hx] at hs
  simp only at hs
  have hne : Silmaril.X86.Ext.step 0 m ≠ .undecodable := by
    rw [hs]; split <;> simp
  have h8 := Silmaril.X86.Ext8.step_eq_of_ne_undecodable hne
  by_cases hc : i = .ret ∧ c.rip = 0
  · simp only [hc, and_self, ite_true] at hs
    rw [hs] at h8
    exact step_of_ext8_returned h8
  · simp only [hc, ite_false] at hs
    rw [hs] at h8
    exact step_of_ext8 (exit := 0) (.inl h8)

/-- **The law for a new 8-bit form.** -/
theorem step_of_new {m : MState} {base : Word} {code : List Byte} {o l : Nat}
    {i : Silmaril.X86.Ext8.New} {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (.new i, l))
    (hx : Silmaril.X86.Ext8.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) =
      .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  obtain ⟨hnone, hnew, hne, h2, h15⟩ := decode_new hdec
  have hA : m.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : m.memory.fetchBytes m.core.rip.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  obtain ⟨more, hmore⟩ :=
    Silmaril.X86.fetchBytes_prefix_fetchWindow fetched (limit := maxInstrLength) h15
  have hund : Silmaril.X86.Ext.fetch m.memory m.core.rip.toNat = .undecodable :=
    fetch_undecodable_of hmore.symm hnone hne
  have hf8 : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat = .inr (i, l) := by
    unfold Silmaril.X86.Ext8.fetch
    rw [hund]
    simp only
    rw [← hmore, Silmaril.X86.Ext8.decodeNew_append hnew more]
    simp only [Silmaril.Process.Memory.readWith_permitted fetched, ite_true]
  simp only [step, hf8, hx, ofResult]

/-- **The listing law.** A listed instruction at the program counter that `Open.decode`
reads and that executes is one open step. -/
theorem step_of_listed {m : MState} {base : Word} {code : List Byte} {o l : Nat}
    {i : Silmaril.X86.Ext8.Instr} {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Ext8.exec i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  cases i with
  | base i => exact step_of_base hl hrip hfit (decode_base hdec) hx
  | new i => exact step_of_new hl hrip hfit hdec hx

end Silmaril.Proofs.Machine.X86.Open
