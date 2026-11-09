module

public import Silmaril.Formats.Compression.Inflate.Stream.GzipHeaderSpec
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.GzipHeader

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.GzipHeaderSpec`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.GzipHeaderSpec

open Silmaril.Formats.Compression
open GzipHeader

private theorem extend_prefix (member covered : List UInt8) (first : UInt8) (rest : List UInt8)
    (h : member = covered ++ first :: rest) : member = (covered ++ [first]) ++ rest := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using h

private theorem evaluate_afterComment (flags : UInt8) (member covered input : List UInt8)
    (hmember : member = covered ++ input) :
    evaluate ⟨afterComment flags, flags, covered⟩ input = checkHcrc flags member input := by
  unfold afterComment
  by_cases hflag : flags &&& gzipFHCRC ≠ 0
  · rw [ite_eq_left hflag]
    cases input with
    | nil => simp [evaluate_nil, checkHcrc, hflag]
    | cons c0 rest =>
      rw [evaluate_cons _ _ _ (by rfl)]
      cases rest with
      | nil => simp [Control.advance, evaluate_nil, checkHcrc, hflag]
      | cons c1 rest =>
        change evaluate ⟨.hcrcHigh c0, flags, covered⟩ (c1 :: rest) = _
        rw [evaluate_cons _ _ _ (by rfl)]
        have htake : member.take (member.length - (c0 :: c1 :: rest).length) = covered := by
          rw [hmember]
          simp
        rw [checkHcrc, ite_eq_left hflag]
        dsimp only
        rw [htake]
        simp only [Control.advance]
        split <;> simp only [evaluate_done, evaluate_bad]
  · rw [ite_eq_right hflag]
    simp only [evaluate_done, checkHcrc, ite_eq_right hflag]

private theorem evaluate_comment (flags : UInt8) (member covered input : List UInt8)
    (hmember : member = covered ++ input) :
    evaluate ⟨.comment, flags, covered⟩ input =
      (gzipDropZeroTerminated input).bind (checkHcrc flags member) := by
  induction input generalizing covered with
  | nil => simp [evaluate_nil, gzipDropZeroTerminated]
  | cons first rest ih =>
    rw [evaluate_cons _ _ _ (by rfl)]
    have hnext := extend_prefix member covered first rest hmember
    by_cases hzero : first = 0
    · subst first
      simpa only [Control.advance, ite_true, gzipDropZeroTerminated, Option.bind_some] using
        evaluate_afterComment flags member (covered ++ [0]) rest hnext
    · simp only [Control.advance, hzero, ite_false]
      rw [ih (covered ++ [first]) hnext]
      simp only [gzipDropZeroTerminated]

private theorem evaluate_afterName (flags : UInt8) (member covered input : List UInt8)
    (hmember : member = covered ++ input) :
    evaluate ⟨afterName flags, flags, covered⟩ input = checkAfterName flags member input := by
  unfold afterName checkAfterName
  by_cases hflag : flags &&& gzipFCOMMENT ≠ 0
  · rw [ite_eq_left hflag, ite_eq_left hflag]
    exact evaluate_comment flags member covered input hmember
  · rw [ite_eq_right hflag, ite_eq_right hflag, Option.bind_some]
    exact evaluate_afterComment flags member covered input hmember

private theorem evaluate_name (flags : UInt8) (member covered input : List UInt8)
    (hmember : member = covered ++ input) :
    evaluate ⟨.name, flags, covered⟩ input =
      (gzipDropZeroTerminated input).bind (checkAfterName flags member) := by
  induction input generalizing covered with
  | nil => simp [evaluate_nil, gzipDropZeroTerminated]
  | cons first rest ih =>
    rw [evaluate_cons _ _ _ (by rfl)]
    have hnext := extend_prefix member covered first rest hmember
    by_cases hzero : first = 0
    · subst first
      simpa only [Control.advance, ite_true, gzipDropZeroTerminated, Option.bind_some] using
        evaluate_afterName flags member (covered ++ [0]) rest hnext
    · simp only [Control.advance, hzero, ite_false]
      rw [ih (covered ++ [first]) hnext]
      simp only [gzipDropZeroTerminated]

private theorem evaluate_afterExtra (flags : UInt8) (member covered input : List UInt8)
    (hmember : member = covered ++ input) :
    evaluate ⟨afterExtra flags, flags, covered⟩ input = checkAfterExtra flags member input := by
  unfold afterExtra checkAfterExtra
  by_cases hflag : flags &&& gzipFNAME ≠ 0
  · rw [ite_eq_left hflag, ite_eq_left hflag]
    exact evaluate_name flags member covered input hmember
  · rw [ite_eq_right hflag, ite_eq_right hflag, Option.bind_some]
    exact evaluate_afterName flags member covered input hmember

private theorem evaluate_extra (remaining : Nat) (flags : UInt8)
    (member covered input : List UInt8) (hmember : member = covered ++ input) :
    evaluate ⟨.extra remaining, flags, covered⟩ input =
      (gzipDropExact (remaining + 1) input).bind (checkAfterExtra flags member) := by
  induction remaining generalizing covered input with
  | zero =>
    cases input with
    | nil => simp [evaluate_nil, gzipDropExact]
    | cons first rest =>
      rw [evaluate_cons _ _ _ (by rfl)]
      have hnext := extend_prefix member covered first rest hmember
      simpa only [Control.advance, gzipDropExact, List.length_cons, Nat.succ_le_succ_iff,
        Nat.zero_le, ite_true, List.drop_succ_cons, List.drop_zero, Option.bind_some] using
        evaluate_afterExtra flags member (covered ++ [first]) rest hnext
  | succ remaining ih =>
    cases input with
    | nil => simp [evaluate_nil, gzipDropExact]
    | cons first rest =>
      rw [evaluate_cons _ _ _ (by rfl)]
      change evaluate ⟨.extra remaining, flags, covered ++ [first]⟩ rest = _
      rw [ih (covered ++ [first]) rest (extend_prefix member covered first rest hmember)]
      simp only [gzipDropExact, List.length_cons, Nat.succ_le_succ_iff, List.drop_succ_cons]

private theorem evaluate_afterFixed (flags : UInt8) (member covered input : List UInt8)
    (hmember : member = covered ++ input) :
    evaluate ⟨afterFixed flags, flags, covered⟩ input = checkAfterFixed flags member input := by
  unfold afterFixed checkAfterFixed
  by_cases hflag : flags &&& gzipFEXTRA ≠ 0
  · rw [ite_eq_left hflag, ite_eq_left hflag]
    cases input with
    | nil => simp [evaluate_nil]
    | cons low rest =>
      rw [evaluate_cons _ _ _ (by rfl)]
      cases rest with
      | nil => simp [Control.advance, evaluate_nil]
      | cons high rest =>
        change evaluate ⟨.xlenHigh low, flags, covered ++ [low]⟩ (high :: rest) = _
        rw [evaluate_cons _ _ _ (by rfl)]
        have hnext : member = ((covered ++ [low]) ++ [high]) ++ rest :=
          extend_prefix member (covered ++ [low]) high rest
            (extend_prefix member covered low (high :: rest) hmember)
        simp only [Control.advance]
        by_cases hzero : low.toNat + 256 * high.toNat = 0
        · rw [ite_eq_left hzero]
          simpa only [hzero, gzipDropExact, Nat.zero_le, ite_true, List.drop_zero,
            Option.bind_some] using
            evaluate_afterExtra flags member ((covered ++ [low]) ++ [high]) rest hnext
        · rw [ite_eq_right hzero]
          rw [evaluate_extra _ flags member _ rest hnext]
          have hcount : low.toNat + 256 * high.toNat - 1 + 1 = low.toNat + 256 * high.toNat := by
            omega
          rw [hcount]
  · rw [ite_eq_right hflag, ite_eq_right hflag, Option.bind_some]
    exact evaluate_afterExtra flags member covered input hmember

private theorem checkAfterFixed_eq (flags : UInt8) (member input : List UInt8) :
    checkAfterFixed flags member input = gzipSkipHeaderFields flags member input := by
  unfold checkAfterFixed checkAfterExtra checkAfterName checkHcrc
    gzipSkipHeaderFields gzipSkipOptional
  dsimp only
  split <;> split <;> simp_all [Option.bind]
  all_goals repeat' first | rfl | (split <;> simp_all)

private theorem evaluate_fixedTail (remaining : Nat) (flags : UInt8)
    (member covered input : List UInt8) (hmember : member = covered ++ input) :
    evaluate ⟨.fixedTail remaining, flags, covered⟩ input =
      (gzipDropExact (remaining + 1) input).bind (checkAfterFixed flags member) := by
  induction remaining generalizing covered input with
  | zero =>
    cases input with
    | nil => simp [evaluate_nil, gzipDropExact]
    | cons first rest =>
      rw [evaluate_cons _ _ _ (by rfl)]
      have hnext := extend_prefix member covered first rest hmember
      simpa only [Control.advance, gzipDropExact, List.length_cons, Nat.succ_le_succ_iff,
        Nat.zero_le, ite_true, List.drop_succ_cons, List.drop_zero, Option.bind_some] using
        evaluate_afterFixed flags member (covered ++ [first]) rest hnext
  | succ remaining ih =>
    cases input with
    | nil => simp [evaluate_nil, gzipDropExact]
    | cons first rest =>
      rw [evaluate_cons _ _ _ (by rfl)]
      change evaluate ⟨.fixedTail remaining, flags, covered ++ [first]⟩ rest = _
      rw [ih (covered ++ [first]) rest (extend_prefix member covered first rest hmember)]
      simp only [gzipDropExact, List.length_cons, Nat.succ_le_succ_iff, List.drop_succ_cons]

private theorem evaluate_magic1_cons (flags : UInt8) (covered : List UInt8)
    (first : UInt8) (rest : List UInt8) :
    evaluate ⟨.magic1, flags, covered⟩ (first :: rest) =
      if first = 0x1f then evaluate ⟨.magic2, flags, covered ++ [first]⟩ rest else none := by
  rw [evaluate_cons _ _ _ (by rfl)]
  simp only [Control.advance]
  split <;> simp only [evaluate_bad]

private theorem evaluate_magic2_cons (flags : UInt8) (covered : List UInt8)
    (first : UInt8) (rest : List UInt8) :
    evaluate ⟨.magic2, flags, covered⟩ (first :: rest) =
      if first = 0x8b then evaluate ⟨.method, flags, covered ++ [first]⟩ rest else none := by
  rw [evaluate_cons _ _ _ (by rfl)]
  simp only [Control.advance]
  split <;> simp only [evaluate_bad]

private theorem evaluate_method_cons (flags : UInt8) (covered : List UInt8)
    (first : UInt8) (rest : List UInt8) :
    evaluate ⟨.method, flags, covered⟩ (first :: rest) =
      if first = 8 then evaluate ⟨.flags, flags, covered ++ [first]⟩ rest else none := by
  rw [evaluate_cons _ _ _ (by rfl)]
  simp only [Control.advance]
  split <;> simp only [evaluate_bad]

private theorem evaluate_flags_cons (flags : UInt8) (covered : List UInt8)
    (first : UInt8) (rest : List UInt8) :
    evaluate ⟨.flags, flags, covered⟩ (first :: rest) =
      if first &&& gzipFRESERVED = 0 then
        evaluate ⟨.fixedTail 5, first, covered ++ [first]⟩ rest else none := by
  rw [evaluate_cons _ _ _ (by rfl)]
  simp only [Control.advance]
  split <;> simp only [evaluate_bad]

/-- The full incremental header controller implements the existing gzip header
observation, including every optional field and FHCRC. -/
theorem evaluate_initial_eq_gzipBody (input : List UInt8) :
    evaluate initialControl input = RawContainers.gzipBody input := by
  match input with
  | [] | [_] | [_, _] | [_, _, _] =>
    simp [initialControl, evaluate_nil, evaluate_magic1_cons, evaluate_magic2_cons,
      evaluate_method_cons, RawContainers.gzipBody]
  | id1 :: id2 :: method :: flags :: afterFlags =>
    rw [show initialControl = ⟨.magic1, 0, []⟩ from rfl,
      evaluate_magic1_cons, evaluate_magic2_cons, evaluate_method_cons, evaluate_flags_cons]
    rw [evaluate_fixedTail 5 flags (id1 :: id2 :: method :: flags :: afterFlags)
      ((([] ++ [id1]) ++ [id2]) ++ [method] ++ [flags]) afterFlags (by simp)]
    simp only [checkAfterFixed_eq]
    match afterFlags with
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] =>
      simp [gzipDropExact, RawContainers.gzipBody]
    | mt0 :: mt1 :: mt2 :: mt3 :: xfl :: os :: rest =>
      simp only [gzipDropExact, List.length_cons, Nat.succ_le_succ_iff, Nat.zero_le,
        ite_true, List.drop_succ_cons, List.drop_zero, Option.bind_some]
      by_cases h1 : id1 = 0x1f
      · subst id1
        by_cases h2 : id2 = 0x8b
        · subst id2
          by_cases hm : method = 8
          · subst method
            by_cases hf : flags &&& gzipFRESERVED = 0
            · simp [hf, RawContainers.gzipBody]
            · simp [hf, RawContainers.gzipBody]
          · simp [hm, RawContainers.gzipBody]
        · simp [h2, RawContainers.gzipBody]
      · simp [h1, RawContainers.gzipBody]

theorem denote_initial (physical : Reservoir) (reader : LSBReader) :
    Machine.denote ⟨initialControl, physical⟩ reader = RawContainers.gzipBody reader.input :=
  evaluate_initial_eq_gzipBody reader.input

/-- Exact successful header reader: the suffix is unchanged, the bit buffer
is empty, and the consumed-bit counter advances by the full header length. -/
theorem denoteReader_initial (physical : Reservoir) (input : List UInt8) (total : Nat) :
    Machine.denoteReader ⟨initialControl, physical⟩ (ContainerFields.alignedReader input total) =
      (RawContainers.gzipBody input).map (fun rest =>
        ContainerFields.alignedReader rest (total + 8 * (input.length - rest.length))) := by
  simp only [Machine.denoteReader, denote_initial, ContainerFields.alignedReader]

/-! The following header has EXTRA bytes 17,34, NAME "A", COMMENT "B" and
FHCRC. Its low CRC16 is 0x4409; FHCRC bytes themselves are outside coverage. -/

theorem optional_fields_hcrc_accepts (tail : List UInt8) :
    evaluate initialControl (optionalHeaderPrefix ++ 9 :: 68 :: tail) = some tail := by
  simp only [optionalHeaderPrefix, List.cons_append, List.nil_append]
  iterate 20 rw [evaluate_cons _ _ _ (by decide)]
  rw [evaluate.eq_def]
  rfl

theorem optional_fields_hcrc_rejects (tail : List UInt8) :
    evaluate initialControl (optionalHeaderPrefix ++ 9 :: 69 :: tail) = none := by
  simp only [optionalHeaderPrefix, List.cons_append, List.nil_append]
  iterate 20 rw [evaluate_cons _ _ _ (by decide)]
  rw [evaluate.eq_def]
  rfl

end Silmaril.Formats.Compression.Inflate.Stream.GzipHeaderSpec
