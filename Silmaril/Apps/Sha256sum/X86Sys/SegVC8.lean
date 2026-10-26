module

public import Silmaril.Apps.Sha256sum.X86Sys.SegVC

/-!
# The segment VC generator over the `Ext8` variant

`Isa.sys8` is the `SegVC.Isa` of the `Ext8` process machine's retiring steps (`rStep8`, the
silent steps of `GStep`): instructions of `X86.Ext8` (those of `X86.Ext` and the 8-bit forms
`movzbl %ah`, `test $1,%al`, …), decoded by `decode8`, executed by `X86.Ext8.exec`.

**Decode failure is stable from the slice to the fetch window.** The machine does not decode
the listed slice: it fetches a 15-byte window and tries `X86.Ext` first, falling back to the
new forms only on bytes `X86.Ext` cannot decode (`Ext8.fetch`). A slice on which `X86.Ext.decode`
fails could, in principle, be the prefix of a longer `X86.Ext` instruction. It is not when the
length decoder `parseRaw` finishes inside the slice (it is prefix-stable, `good_parseRaw`):
`decode_none_append`. `decode8` accepts a new form only then (and with its length at most 15
and its first two bytes not `syscall`), which `Listing.valid` checks by `decide` on each
listing, so the law needs no assumption about the decoder's internals. The new-form decoder is
prefix-stable as well (`decodeNew_append`).

Everything here is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.X86Sys

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (parseRaw PResult Loaded)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.Execution (run Reaches)

/-! ## `X86.Ext` decode failure on an extension -/

/-- If the length decoder finishes inside `w` and `w` does not decode, no extension of `w`
decodes. -/
theorem decode_none_append {w : List Byte} (hnone : X86.Ext.decode w = none)
    (hne : parseRaw w ≠ .eof) (more : List Byte) : X86.Ext.decode (w ++ more) = none := by
  cases hd : X86.Ext.decode (w ++ more) with
  | none => rfl
  | some res =>
    obtain ⟨i, n⟩ := res
    exfalso
    obtain ⟨_, t, ht⟩ := X86.Ext.decode_eq_some_iff.mp hd
    have hp := X86.Ext.parseRaw_encode i t
    rw [ht] at hp
    cases hw : parseRaw w with
    | eof => exact hne hw
    | bad =>
      rw [X86.Ext.good_parseRaw.bad hw more] at hp
      cases hp
    | ok r rest =>
      obtain ⟨_, hext⟩ := X86.Ext.good_parseRaw.ok hw
      rw [hext more] at hp
      obtain ⟨-, hrest⟩ := PResult.ok.inj hp
      subst hrest
      have hw' : w = X86.Ext.encode i ++ rest := by
        have : w ++ more = (X86.Ext.encode i ++ rest) ++ more := by rw [List.append_assoc, ht]
        exact List.append_cancel_right this
      have := X86.Ext.decode_encode_append i rest
      rw [← hw', hnone] at this
      cases this

/-- The fetch at an address whose window extends such a slice is undecodable. -/
theorem fetch_undecodable_of {memory : Silmaril.Process.Memory} {address : Nat} {w more : List Byte}
    (hwin : fetchWindow memory maxInstrLength address = w ++ more)
    (hnone : X86.Ext.decode w = none) (hne : parseRaw w ≠ .eof) :
    X86.Ext.fetch memory address = .undecodable := by
  unfold X86.Ext.fetch
  rw [hwin, decode_none_append hnone hne more]
  simp only
  split
  · rename_i heof
    exfalso
    cases hw : parseRaw w with
    | eof => exact hne hw
    | bad => rw [X86.Ext.good_parseRaw.bad hw more] at heof; cases heof
    | ok r rest => rw [(X86.Ext.good_parseRaw.ok hw).2 more] at heof; cases heof
  · rfl

/-! ## The new-form decoder is prefix-stable -/

/-- **The new-form decoder ignores trailing bytes** (`X86.Ext8.decodeNew_append`). -/
theorem decodeNew_append {xs : List Byte} {i : X86.Ext8.New} {n : Nat}
    (h : X86.Ext8.decodeNew xs = some (i, n)) (more : List Byte) :
    X86.Ext8.decodeNew (xs ++ more) = some (i, n) :=
  X86.Ext8.decodeNew_append h more

/-! ## The instance -/

/-- The variant's decoder for listings: `Ext8.decode`, accepting a new form only where the
machine's fetch reaches it (the length decoder finishes inside the slice, at most 15 bytes,
not a `syscall`). Checked on each listing by `decide`. -/
def decode8 (bytes : List Byte) : Option (X86.Ext8.Instr × Nat) :=
  match X86.Ext8.decode bytes with
  | some (.base i, n) => some (.base i, n)
  | some (.new i, n) =>
    match parseRaw bytes with
    | .eof => none
    | _ => if 2 ≤ n ∧ n ≤ maxInstrLength ∧ bytes.take 2 ≠ [0x0f#8, 0x05#8] then
        some (.new i, n) else none
  | none => none

theorem decode8_base {bytes : List Byte} {i : X86.Ext.Instr} {n : Nat}
    (h : decode8 bytes = some (.base i, n)) : X86.Ext.decode bytes = some (i, n) := by
  unfold decode8 at h
  split at h
  · rename_i i' n' he
    simp only [Option.some.injEq, Prod.mk.injEq, X86.Ext8.Instr.base.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact X86.Ext8.decode_base_iff.mp he
  · split at h
    · cases h
    · split at h <;> cases h
  · cases h

theorem decode8_new {bytes : List Byte} {i : X86.Ext8.New} {n : Nat}
    (h : decode8 bytes = some (.new i, n)) :
    X86.Ext.decode bytes = none ∧ X86.Ext8.decodeNew bytes = some (i, n) ∧
      parseRaw bytes ≠ .eof ∧ 2 ≤ n ∧ n ≤ maxInstrLength ∧ bytes.take 2 ≠ [0x0f#8, 0x05#8] := by
  unfold decode8 at h
  split at h
  · cases h
  · rename_i i' n' he
    have hd : X86.Ext.decode bytes = none ∧ X86.Ext8.decodeNew bytes = some (i', n') := by
      unfold X86.Ext8.decode at he
      split at he
      · cases he
      · rename_i hn
        cases hdn : X86.Ext8.decodeNew bytes with
        | none => rw [hdn] at he; cases he
        | some r =>
          rw [hdn] at he
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨i'', n''⟩ := r
          simp only [X86.Ext8.Instr.new.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨hn, rfl⟩
    split at h
    · cases h
    · rename_i hne
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq, X86.Ext8.Instr.new.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hd.1, hd.2, hne, hc⟩
      · cases h
  · cases h

/-- **The law for a new form.** At a listed new form, the `Ext8` machine fetches it (the
`X86.Ext` fetch is undecodable, the new-form decoder reads it from the window) and retires it. -/
theorem rStep8_of_new {s : XState} {base : Word} {code : List Byte} {o l : Nat}
    {i : X86.Ext8.New} {c : State} {m : Silmaril.Process.Memory} (hlv : s.faulted = false)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 o)
    (hfit : o + l ≤ code.length) (hdec : decode8 ((code.drop o).take l) = some (.new i, l))
    (hx : X86.Ext8.execNew i s.core s.memory (s.core.rip + BitVec.ofNat 64 l) = .ok c m) :
    rStep8 s = some { s with core := c, memory := m } := by
  obtain ⟨hnone, hnew, hne, h2, h15, hsys⟩ := decode8_new hdec
  have hA : s.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : s.memory.fetchBytes s.core.rip.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  obtain ⟨more, hmore⟩ := X86.fetchBytes_prefix_fetchWindow fetched (limit := maxInstrLength) h15
  have hund : X86.Ext.fetch s.memory s.core.rip.toNat = .undecodable :=
    fetch_undecodable_of hmore.symm hnone hne
  have hf8 : X86.Ext8.fetch s.memory s.core.rip.toNat = .inr (i, l) := by
    unfold X86.Ext8.fetch
    rw [hund]
    simp only
    rw [← hmore, decodeNew_append hnew more]
    simp only [Silmaril.Process.Memory.readWith_permitted fetched, ite_true]
  have hnsys : s.memory.fetchBytes s.core.rip.toNat 2 ≠ some Process.CLI.X86Linux.syscallBytes := by
    rw [hA, hl.fetchBytes_sub (by omega) (by omega)]
    intro e
    apply hsys
    have : ((code.drop o).take l).take 2 = (code.drop o).take 2 := by
      rw [List.take_take, Nat.min_eq_left h2]
    rw [this]
    simpa [Process.CLI.X86Linux.syscallBytes] using e
  have hstep : Process.CLI.X86Linux8.step s.core s.memory = .retired c m := by
    unfold Process.CLI.X86Linux8.step
    rw [ite_eq_right hnsys, hf8]
    simp only
    rw [hx]
    rfl
  simp [rStep8, hlv, hstep]

/-- The `Ext8` process machine's retiring steps, as a `SegVC` instance. -/
@[reducible] def Isa.sys8 : Isa XState where
  Instr := X86.Ext8.Instr
  instDecEq := inferInstance
  decode := decode8
  exec := X86.Ext8.exec
  core := XState.core
  mem := XState.memory
  upd := fun s c m => { s with core := c, memory := m }
  core_upd := fun _ _ _ => rfl
  mem_upd := fun _ _ _ => rfl
  upd_self := fun _ => rfl
  ok := fun _ _ => True
  live := fun s => s.faulted = false
  step := rStep8
  live_step := fun {s t} hs h => by
    unfold rStep8 at h
    rw [hs] at h
    simp only [Bool.false_eq_true, ite_false] at h
    split at h
    · cases h; rfl
    · cases h
  step_of := by
    intro s base code o l i c m hlv hl hrip hfit hdec hx _
    cases i with
    | base i =>
      have hd := decode8_base hdec
      have := (Isa.sys (fun _ => 0)).step_of (s := s) hlv hl hrip hfit hd hx trivial
      exact rStep8_of_rStep this
    | new i => exact rStep8_of_new hlv hl hrip hfit hdec hx

/-- A `SegVC` run over `Isa.sys8` is a run of `rStep8` (the silent steps of `GStep`). -/
theorem reaches_sys8 {s t : XState} (h : Reaches Isa.sys8.step s t) : Reaches rStep8 s t := h

/-- Non-vacuity of the new-form case: `movzbl %ah,%ebx` of `sha_final` (`0x4030e6`) is
accepted by `decode8` as the new form (`X86.Ext` does not decode it). -/
theorem decode8_movzbl_ah :
    decode8 [0x0f#8, 0xb6#8, 0xdc#8] =
      some (.new (.movx false .d .rbx (.reg (.high .rax))), 3) := by decide

end Silmaril.Apps.Sha256sum.X86Sys
