module

public import Silmaril.Proofs.X86.Atomic9.Decode

/-!
# `Atomic9.decode` is prefix-stable

`decode_append`: a reading of
`Atomic9.decode` survives any bytes appended after the window it was read from. Each layer of
the listing decoder is prefix-stable:

* `Ext.decode`: a successful decode reads the canonical encoding (`Ext.decode_sound`) and
  `Ext.decode_encode_append`; a failed one stays failed when the length decoder `parseRaw`
  finishes inside the window (`ext_none_append`, copied from
  `Silmaril/Proofs/X86/Open9/Law.lean`, which the `Open9` topic exports only from its
  `Proofs` module);
* the new-form parsers of `Ext8`, `Ext9` and `Atomic9` have the prefix laws of
  `Ext.ByteParser.Good` (`good_pNew`), so a read form keeps its reading (`decodeNew_append`)
  and a rejected one stays rejected;
* the side conditions of the listing decoders (`Ext.decode = none`, `newBad`, `rawNotEof`,
  `ext9Bad`) are exactly what makes the earlier layers' failures persist.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Atomic9

open Silmaril.X86 (Byte maxInstrLength)
open Silmaril.X86.Ext (parseRaw PResult)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte

theorem ite_of {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

/-- If the length decoder finishes inside `w` and `w` does not decode, no extension of `w`
decodes. -/
theorem ext_none_append {w : List Byte} (hnone : Silmaril.X86.Ext.decode w = none)
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

/-- A reading of `Ext.decode` survives appended bytes. -/
theorem ext_some_append {w : List Byte} {i : Silmaril.X86.Ext.Instr} {n : Nat}
    (h : Silmaril.X86.Ext.decode w = some (i, n)) (more : List Byte) :
    Silmaril.X86.Ext.decode (w ++ more) = some (i, n) := by
  obtain ⟨hn, hw⟩ := Silmaril.X86.Ext.decode_sound h
  rw [hw, List.append_assoc, Silmaril.X86.Ext.decode_encode_append, hn]

theorem rawNotEof_append {w : List Byte} (h : parseRaw w ≠ .eof) (more : List Byte) :
    parseRaw (w ++ more) ≠ .eof := by
  cases hw : parseRaw w with
  | eof => exact absurd hw h
  | bad => rw [Silmaril.X86.Ext.good_parseRaw.bad hw more]; simp
  | ok r rest => rw [(Silmaril.X86.Ext.good_parseRaw.ok hw).2 more]; simp

theorem parseRaw_ne_eof {w : List Byte} (h : Open9.rawNotEof w = true) : parseRaw w ≠ .eof := by
  unfold Open9.rawNotEof at h
  intro he
  rw [he] at h
  cases h

theorem rawNotEof_of {w : List Byte} (h : parseRaw w ≠ .eof) : Open9.rawNotEof w = true := by
  unfold Open9.rawNotEof
  split
  · rename_i he; exact absurd he h
  · rfl

theorem newBad_append {w : List Byte} (h : Open9.newBad w = true) (more : List Byte) :
    Open9.newBad (w ++ more) = true := by
  unfold Open9.newBad at h ⊢
  split at h
  · rename_i hb; rw [Silmaril.X86.Ext8.good_pNew.bad hb more]
  · cases h

theorem ext9Bad_append {w : List Byte} (h : Sse9.ext9Bad w = true) (more : List Byte) :
    Sse9.ext9Bad (w ++ more) = true := by
  unfold Sse9.ext9Bad at h ⊢
  split at h
  · rename_i hb; rw [Ext9.good_pNew.bad hb more]
  · cases h

theorem ext8New_none_append {w : List Byte} (h : Open9.newBad w = true) (more : List Byte) :
    Silmaril.X86.Ext8.decodeNew (w ++ more) = none := by
  unfold Open9.newBad at h
  split at h
  · rename_i hb
    unfold Silmaril.X86.Ext8.decodeNew
    rw [Silmaril.X86.Ext8.good_pNew.bad hb more]
  · cases h

theorem ext9New_none_append {w : List Byte} (h : Sse9.ext9Bad w = true) (more : List Byte) :
    Ext9.decodeNew (w ++ more) = none := by
  unfold Sse9.ext9Bad at h
  split at h
  · rename_i hb
    unfold Ext9.decodeNew
    rw [Ext9.good_pNew.bad hb more]
  · cases h

/-- `Open.decode` fails on every extension of a window that `Ext` and `Ext8`'s new forms
reject with the length decoder finishing inside it. -/
theorem open_none_append {w : List Byte} (hnone : Silmaril.X86.Ext.decode w = none)
    (hbad : Open9.newBad w = true) (hne : Open9.rawNotEof w = true) (more : List Byte) :
    Open.decode (w ++ more) = none := by
  unfold Open.decode Silmaril.X86.Ext8.decode
  rw [ext_none_append hnone (parseRaw_ne_eof hne) more, ext8New_none_append hbad more]
  rfl

theorem open_some_append {w : List Byte} {i : Silmaril.X86.Ext8.Instr} {n : Nat}
    (h : Open.decode w = some (i, n)) (more : List Byte) :
    Open.decode (w ++ more) = some (i, n) := by
  unfold Open.decode Silmaril.X86.Ext8.decode at h ⊢
  cases hx : Silmaril.X86.Ext.decode w with
  | some p =>
    obtain ⟨j, m⟩ := p
    rw [hx] at h
    rw [ext_some_append hx more]
    exact h
  | none =>
    rw [hx] at h
    cases hn : Silmaril.X86.Ext8.decodeNew w with
    | none => rw [hn] at h; cases h
    | some p =>
      obtain ⟨j, m⟩ := p
      rw [hn] at h
      simp only [Option.map_some] at h
      split at h
      · cases h
      · rename_i hraw
        have hraw' : parseRaw w ≠ .eof := fun he => hraw he
        rw [ext_none_append hx hraw' more, Silmaril.X86.Ext8.decodeNew_append hn more]
        simp only [Option.map_some]
        split
        · rename_i he; exact absurd he (rawNotEof_append hraw' more)
        · exact h

theorem open9_some_append {w : List Byte} {i : Ext9.Instr} {n : Nat}
    (h : Open9.decode w = some (i, n)) (more : List Byte) :
    Open9.decode (w ++ more) = some (i, n) := by
  unfold Open9.decode at h ⊢
  cases ho : Open.decode w with
  | some p =>
    rw [ho] at h
    rw [open_some_append ho more]
    exact h
  | none =>
    rw [ho] at h
    cases hn : Ext9.decodeNew w with
    | none => rw [hn] at h; cases h
    | some p =>
      obtain ⟨j, m⟩ := p
      rw [hn] at h
      simp only at h
      split at h
      · rename_i hc
        rw [open_none_append hc.1 hc.2.1 hc.2.2.1 more, Ext9.decodeNew_append hn more]
        simp only
        rw [ite_of ⟨ext_none_append hc.1 (parseRaw_ne_eof hc.2.2.1) more,
          newBad_append hc.2.1 more, rawNotEof_of (rawNotEof_append (parseRaw_ne_eof hc.2.2.1) more),
          hc.2.2.2⟩]
        exact h
      · cases h

/-- **`Atomic9.decode` is prefix-stable**: a reading survives appended bytes. -/
theorem decode_append {w : List Byte} {i : Atomic9.Instr} {n : Nat}
    (h : Atomic9.decode w = some (i, n)) (more : List Byte) :
    Atomic9.decode (w ++ more) = some (i, n) := by
  unfold Atomic9.decode at h ⊢
  cases ho : Open9.decode w with
  | some p =>
    rw [ho] at h
    rw [open9_some_append ho more]
    exact h
  | none =>
    rw [ho] at h
    cases hl : Atomic9.decodeL w with
    | none => rw [hl] at h; cases h
    | some p =>
      obtain ⟨j, m⟩ := p
      rw [hl] at h
      obtain ⟨hx, hbad, hne, h9, hnew, h1, h15⟩ := decodeL_spec hl
      have ho' : Open9.decode (w ++ more) = none := by
        unfold Open9.decode
        rw [open_none_append hx hbad hne more, ext9New_none_append h9 more]
      have hl' : Atomic9.decodeL (w ++ more) = some (j, m) := by
        unfold Atomic9.decodeL
        rw [decodeNew_append hnew more]
        simp only
        rw [ite_of ⟨ext_none_append hx (parseRaw_ne_eof hne) more,
          newBad_append hbad more, rawNotEof_of (rawNotEof_append (parseRaw_ne_eof hne) more),
          ext9Bad_append h9 more, h1, h15⟩]
      rw [ho', hl']
      exact h

/-- Nothing decodes from no bytes. -/
theorem decode_nil : Atomic9.decode [] = none := by decide

end Silmaril.Proofs.X86.Atomic9
