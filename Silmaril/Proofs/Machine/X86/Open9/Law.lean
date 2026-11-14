module

public import Silmaril.Machine.X86.Open9.Defs
public import Silmaril.Machine.X86.Open.Thms
public import Silmaril.Machine.X86.Ext9.Thms

/-!
# The listing law of the open machine over `Ext9`

* `step_of_open`: every open step is an `Open9` step;
* `step_of_listed`: a listed instruction that `Open9.decode` reads at the program counter of
  a loaded image and that executes is one `Open9` step.

`decode_none_append` and `fetch_undecodable_of` are copied from
`Silmaril/Proofs/Machine/X86/Open/Law.lean` (itself from public silmaril-lean
`Silmaril/Apps/Sha256sum/X86Sys/SegVC8.lean`, rev `35a6f60`), because the `Open` topic exports
them only from its `Proofs` module.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.Open9

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (parseRaw PResult Loaded)
open Silmaril.Process (Memory)
open Silmaril.Machine.X86
open Silmaril.Machine.X86.Open9

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

/-- **Every open step is an `Open9` step.** -/
theorem step_of_open {m n : MState} (h : Open.step m = some n) : step m = some n := by
  unfold step
  split
  · rename_i e
    exfalso
    unfold Open.step at h
    rw [e] at h
    cases h
  · exact h

theorem decode_ext8 {bytes : List Byte} {i : Silmaril.X86.Ext8.Instr} {n : Nat}
    (h : decode bytes = some (.ext8 i, n)) : Open.decode bytes = some (i, n) := by
  unfold decode at h
  split at h
  · rename_i i' n' he
    simp only [Option.some.injEq, Prod.mk.injEq, Ext9.Instr.ext8.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact he
  · split at h
    · split at h <;> cases h
    · cases h

theorem decode_new {bytes : List Byte} {i : Ext9.New} {n : Nat}
    (h : decode bytes = some (.new i, n)) :
    Silmaril.X86.Ext.decode bytes = none ∧ newBad bytes = true ∧ rawNotEof bytes = true ∧
      Ext9.decodeNew bytes = some (i, n) ∧ 0 < n ∧ n ≤ maxInstrLength := by
  unfold decode at h
  split at h
  · cases h
  · split at h
    · rename_i i' n' hd
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq, Ext9.Instr.new.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hc.1, hc.2.1, hc.2.2.1, hd, hc.2.2.2⟩
      · cases h
    · cases h

theorem pNew8_bad_append {w : List Byte} (h : newBad w = true) (more : List Byte) :
    Silmaril.X86.Ext8.decodeNew (w ++ more) = none := by
  unfold newBad at h
  split at h
  · rename_i hb
    unfold Silmaril.X86.Ext8.decodeNew
    rw [Silmaril.X86.Ext8.good_pNew.bad hb more]
  · cases h

theorem parseRaw_ne_eof {w : List Byte} (h : rawNotEof w = true) : parseRaw w ≠ .eof := by
  unfold rawNotEof at h
  intro he
  rw [he] at h
  cases h

/-- **The fall-through to bytes no `Ext8` form decodes** (exported for `Sse9`): bytes `w`
fetched at an address, of at most 15 bytes, that `Ext` rejects with its length decoder
finishing inside them and whose `Ext8` new-form parse fails, extend to the fetch window and
make `Ext8.fetch` report `undecodable`. -/
theorem fetch8_undecodable_of {memory : Memory} {address l : Nat} {w : List Byte}
    (fetched : memory.fetchBytes address l = some w) (hl : l ≤ maxInstrLength)
    (hnone : Silmaril.X86.Ext.decode w = none) (hbad : newBad w = true)
    (hne : rawNotEof w = true) :
    ∃ more, fetchWindow memory maxInstrLength address = w ++ more ∧
      Silmaril.X86.Ext8.fetch memory address = .inl .undecodable := by
  obtain ⟨more, hmore⟩ := Silmaril.X86.fetchBytes_prefix_fetchWindow fetched hl
  have hund : Silmaril.X86.Ext.fetch memory address = .undecodable :=
    fetch_undecodable_of hmore.symm hnone (parseRaw_ne_eof hne)
  refine ⟨more, hmore.symm, ?_⟩
  unfold Silmaril.X86.Ext8.fetch
  rw [hund]
  simp only
  rw [← hmore, pNew8_bad_append hbad more]

/-- **The fetch form of the law for a new `Ext9` form**: the bytes `w` fetched (with execute
permission) at the program counter decode as a new form of length `l`. -/
theorem step_of_fetch_new {m : MState} {l : Nat} {w : List Byte} {i : Ext9.New} {c : State}
    {mem : Memory} (fetched : m.memory.fetchBytes m.core.rip.toNat l = some w)
    (hdec : decode w = some (.new i, l))
    (hx : Ext9.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  obtain ⟨hnone, hbad, hne, hnew, h1, h15⟩ := decode_new hdec
  obtain ⟨more, hmore⟩ :=
    Silmaril.X86.fetchBytes_prefix_fetchWindow fetched (limit := maxInstrLength) h15
  have hund : Silmaril.X86.Ext.fetch m.memory m.core.rip.toNat = .undecodable :=
    fetch_undecodable_of hmore.symm hnone (parseRaw_ne_eof hne)
  have hf8 : Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat = .inl .undecodable := by
    unfold Silmaril.X86.Ext8.fetch
    rw [hund]
    simp only
    rw [← hmore, pNew8_bad_append hbad more]
  have hfn : Ext9.fetchNew m.memory m.core.rip.toNat = some (some (i, l)) := by
    unfold Ext9.fetchNew
    rw [← hmore, Ext9.decodeNew_append hnew more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hf8, hfn, hx, Open.ofResult]

/-- **The law for a new `Ext9` form.** -/
theorem step_of_new {m : MState} {base : Word} {code : List Byte} {o l : Nat}
    {i : Ext9.New} {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (.new i, l))
    (hx : Ext9.execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  obtain ⟨-, -, -, -, h1, -⟩ := decode_new hdec
  have hA : m.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : m.memory.fetchBytes m.core.rip.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  exact step_of_fetch_new fetched hdec hx

/-- **The listing law.** -/
theorem step_of_listed {m : MState} {base : Word} {code : List Byte} {o l : Nat}
    {i : Ext9.Instr} {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : Ext9.exec i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ := by
  cases i with
  | ext8 i => exact step_of_open (Open.step_of_listed hl hrip hfit (decode_ext8 hdec) hx)
  | new i => exact step_of_new hl hrip hfit hdec hx

end Silmaril.Proofs.Machine.X86.Open9
