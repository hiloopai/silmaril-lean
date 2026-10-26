module

public import Silmaril.X86.Ext.Wire.Encoding

/-! # Prefix stability of the wire decoder -/
@[expose] public section
namespace Silmaril.X86.Ext.Wire
open Silmaril.X86 (Byte)
open ByteParser

private theorem ext_parseRaw_ds (tail : List Byte) :
    Ext.parseRaw (0x3E#8 :: tail) = .bad := by rfl

private theorem pHead_no_ds (b : Byte) (tail : List Byte) (h : b ≠ 0x3E#8) :
    pHead (b :: tail) = (ByteParser.map (false, ·) Ext.pHead) (b :: tail) := by
  simp only [pHead, Ext.pHead, ByteParser.bind, ByteParser.map, ByteParser.pure, byte, h, ite_false]

/-- A complete wire layout cannot leave the canonical length parser at EOF.
It either rejects there, shares its fields, or uses the new F7 /0 immediate
form, which the canonical meaning function rejects. -/
theorem parseRaw_compat {bytes : List Byte} {raw : Raw} {rest : List Byte}
    (h : parseRaw bytes = .ok raw rest) :
    Ext.parseRaw bytes = .bad ∨
      ∃ r t, Ext.parseRaw bytes = .ok r t ∧ ((raw.ds = false ∧ r = raw.fields) ∨ Ext.ofRaw r = none) := by
  cases bytes with
  | nil => simp only [parseRaw, pHead, ByteParser.bind, byte] at h; cases h
  | cons b tail =>
    by_cases hb : b = 0x3E#8
    · subst hb; exact .inl (ext_parseRaw_ds tail)
    · simp only [parseRaw, ByteParser.bind, pHead_no_ds b tail hb] at h
      cases hh : Ext.pHead (b :: tail) with
      | bad => simp only [hh, ByteParser.bind, ByteParser.map] at h; cases h
      | eof => simp only [hh, ByteParser.bind, ByteParser.map] at h; cases h
      | ok head t =>
        obtain ⟨fs, pfx, rex, opc⟩ := head
        simp only [hh, ByteParser.bind, ByteParser.map, ByteParser.pure] at h; cases hs : Ext.shape pfx (rex.getD Rex.zero).w opc with
        | none =>
          exact .inl (by simp only [Ext.parseRaw, ByteParser.bind, hh, hs, fail])
        | some sh =>
          simp only [shape, hs] at h
          cases hm : pModrm sh.modrm t with
          | bad => simp only [hm, ByteParser.bind] at h; cases h
          | eof => simp only [hm, ByteParser.bind] at h; cases h
          | ok mp t' =>
            simp only [hm, ByteParser.bind] at h
            by_cases hk : immKind opc mp sh.imm = sh.imm
            · rw [hk] at h
              cases hi : pImm sh.imm t' with
              | bad => simp only [hi] at h; cases h
              | eof => simp only [hi] at h; cases h
              | ok imm remaining =>
                simp only [hi, ByteParser.pure, PResult.ok.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact .inr ⟨_, remaining, by simp only [Ext.parseRaw, hh, hs, hm, hi, ByteParser.bind, ByteParser.map, ByteParser.pure], .inl ⟨rfl, rfl⟩⟩
            · cases opc with
              | two op => simp [immKind] at hk
              | one op =>
                cases mp with
                | none => simp [immKind] at hk
                | some part =>
                  obtain ⟨m, sib, disp⟩ := part
                  by_cases hop : op = 0xF7#8 ∧ m.reg = 0#3
                  · obtain ⟨rfl, hreg⟩ := hop
                    have himm : sh.imm = .none := by
                      cases pfx <;> simp [Ext.shape] at hs
                      cases hs
                      rfl
                    refine .inr ⟨⟨fs, pfx, rex, .one 0xF7, some (m, sib, disp), .none⟩, t', ?_, .inr ?_⟩
                    · simp only [Ext.parseRaw, hh, hs, hm, himm, pImm, ByteParser.bind, ByteParser.map, ByteParser.pure]
                      rfl
                    · simp [Ext.ofRaw, Ext.ofModrm, hreg]
                  · simp [immKind, hop] at hk

private theorem ext_decode_none_append {bytes : List Byte} {raw : Raw} {rest : List Byte}
    (parsed : parseRaw bytes = .ok raw rest)
    (hprefix : bytes.take raw.bytes.length = raw.bytes)
    (rejected : Ext.decode bytes = none) (more : List Byte) :
    Ext.decode (bytes ++ more) = none := by
  cases hd : Ext.decode (bytes ++ more) with
  | none => rfl
  | some result =>
    obtain ⟨i, n⟩ := result
    exfalso
    obtain ⟨hn, ht⟩ := Ext.decode_sound hd
    have hc : Ext.parseRaw (bytes ++ more) = .ok (Ext.toRaw i) ((bytes ++ more).drop n) := by
      conv_lhs => rw [ht]
      exact Ext.parseRaw_encode i _
    rcases parseRaw_compat parsed with hb | ⟨r, t, hp, hmeaning⟩
    · rw [Ext.good_parseRaw.bad hb more] at hc
      cases hc
    · have he := (Ext.good_parseRaw.ok hp).2 more
      rw [he] at hc
      have hr : r = Ext.toRaw i := (PResult.ok.inj hc).1
      rcases hmeaning with ⟨hds, heq⟩ | hnone
      · have hbytes : raw.bytes = Ext.encode i := by
          simp only [Raw.bytes, hds, Bool.false_eq_true, ↓reduceIte, List.nil_append]
          rw [← heq, hr]
          rfl
        rw [hbytes] at hprefix
        have hext : Ext.decode bytes = some (i, (Ext.encode i).length) := by
          apply Ext.decode_eq_some_iff.mpr
          refine ⟨rfl, bytes.drop (Ext.encode i).length, ?_⟩
          have h := List.take_append_drop (Ext.encode i).length bytes
          rw [hprefix] at h
          exact h
        rw [rejected] at hext
        cases hext
      · rw [hr, Ext.ofRaw_toRaw] at hnone
        cases hnone

/-- Appending bytes does not change a complete wire candidate. -/
theorem decodeCandidate_append {bytes : List Byte} {d : Decoded}
    (h : decodeCandidate bytes = some d) (more : List Byte) :
    decodeCandidate (bytes ++ more) = some d := by
  unfold decodeCandidate at h
  cases hc : Ext.decode bytes with
  | some result =>
    obtain ⟨i, n⟩ := result
    simp only [hc] at h
    cases h
    have bound := (Ext.decode_length hc).2.2.2
    simp only [decodeCandidate, Ext.decode_append more hc]
    rw [List.take_append_of_le_length bound]
  | none =>
    simp only [hc] at h
    cases hp : parseRaw bytes with
    | bad => simp [hp] at h
    | eof => simp [hp] at h
    | ok raw rest =>
      simp only [hp] at h
      cases hi : ofRaw raw with
      | none => simp [hi] at h
      | some i =>
        simp only [hi] at h
        split at h
        · rename_i hg
          cases h
          obtain ⟨pos, limit, hprefix⟩ := hg
          have bound : raw.bytes.length ≤ bytes.length := by
            have hl := congrArg List.length hprefix
            simp only [List.length_take] at hl
            omega
          simp only [decodeCandidate, ext_decode_none_append hp hprefix hc more,
            (good_parseRaw.ok hp).2 more, hi]
          rw [List.take_append_of_le_length bound]
          simp [pos, limit, hprefix]
        · cases h

/-- Appending arbitrary bytes preserves both the instruction and original spelling. -/
theorem decode_append {bytes : List Byte} {d : Decoded}
    (h : decode bytes = some d) (more : List Byte) : decode (bytes ++ more) = some d := by
  unfold decode at h
  split at h
  · cases h
  · rename_i candidate hc
    split at h
    · rename_i hself
      cases h
      simp [decode, decodeCandidate_append hc more, hself]
    · cases h

end Silmaril.X86.Ext.Wire
