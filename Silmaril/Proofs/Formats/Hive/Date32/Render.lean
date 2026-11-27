module

public import Silmaril.Formats.Hive.Date32.Render.Defs
public import Silmaril.Formats.Hive.Date32.Thms
public import Silmaril.Formats.Csv.Typed.Codecs.Date32.Thms
import Silmaril.Formats.Hive.PartitionPath.Thms
import Silmaril.Formats.Utf8.Thms
import Silmaril.Numeric.Gregorian.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Date32.Render

open Silmaril.Formats Silmaril.Formats.Hive Silmaril.Formats.Hive.Date32
open Silmaril.Numeric.Gregorian
open Csv.Typed.Codecs.Date32

private theorem digits_ascii (width n : Nat) (fits : n < 10 ^ width) :
    ∀ byte ∈ Internal.digits width n, byte < 0x80 := by
  induction width generalizing n with
  | zero => simp [Internal.digits]
  | succ width ih =>
    intro byte hit
    simp only [Internal.digits, List.mem_cons] at hit
    have power : 0 < 10 ^ width := Nat.pow_pos (by decide)
    rcases hit with rfl | tail
    · have digit : n / 10 ^ width < 10 := (Nat.div_lt_iff_lt_mul power).mpr (by
        simpa [Nat.pow_succ, Nat.mul_comm] using fits)
      have byteBound : 48 + n / 10 ^ width < 256 := by omega
      rw [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat_of_lt' byteBound]
      change 48 + n / 10 ^ width < 128
      omega
    · exact ih _ (Nat.mod_lt _ power) byte tail

private theorem calendar_ascii (date : CivilDate) (year : 0 ≤ date.year ∧ date.year < 10000)
    (valid : date.Valid) : ∀ byte ∈ Internal.calendarText date, byte < 0x80 := by
  have monthLength : daysInMonth date.year date.month ≤ 31 := by
    rw [daysInMonth_eq]
    repeat' first | omega | split
  have dayBound := valid.2.2.2.trans monthLength
  have monthBound := valid.2.1
  have yearFits : date.year.toNat < 10 ^ 4 := by omega
  have monthFits : date.month < 10 ^ 2 := by omega
  have dayFits : date.day < 10 ^ 2 := by omega
  intro byte hit
  simp only [Internal.calendarText, List.mem_append, List.mem_singleton] at hit
  rcases hit with (((h | h) | h) | h) | h
  · exact digits_ascii _ _ yearFits byte h
  · subst byte
    decide
  · exact digits_ascii _ _ monthFits byte h
  · subst byte
    decide
  · exact digits_ascii _ _ dayFits byte h

theorem encodeText_ok_iff (day : Payload) (text : String) :
    encodeText day = .ok text ↔ decodeText text = .ok day := by
  rw [Hive.Date32.decodeText_ok_iff]
  cases printed : Csv.Typed.Codecs.Date32.print day with
  | none => simp [encodeText, printed]
  | some bytes =>
    obtain ⟨year, rfl⟩ := (Csv.Typed.Codecs.Date32.print_eq_some_iff day bytes).mp printed
    let bytes := Internal.calendarText (DateInterop.Date32.toCivil day)
    have ascii := calendar_ascii _ year (CivilDate.ofEpochDay_valid day.toInt)
    have exactBytes : (String.ofList (Utf8.ofAscii bytes)).toUTF8.data.toList = bytes := by
      simp only [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
      exact Utf8.encode_ofAscii ascii
    simp only [encodeText, printed, Except.ok.injEq, Option.some.injEq]
    constructor
    · rintro rfl
      exact exactBytes.symm
    · intro same
      apply String.toByteArray_inj.mp
      apply ByteArray.ext
      apply Array.toList_inj.mp
      change (String.ofList (Utf8.ofAscii bytes)).toUTF8.data.toList = text.toUTF8.data.toList
      exact exactBytes.trans same

theorem encodeText_outside (day : Payload) :
    encodeText day = .error (.outsideDateProfile day) ↔ ¬ Admitted day := by
  rw [← Csv.Typed.Codecs.Date32.print_eq_none_iff]
  cases h : Csv.Typed.Codecs.Date32.print day <;> simp [encodeText, h]

theorem decodeDirectory_renderDirectory (key : String) (options : PartitionPath.Options)
    (day : Option Payload) (directory : String) (written : renderDirectory key options day = .ok directory) :
    WritePlan.decodeDirectory (partition key) options convert directory = .ok (fun _ => day) := by
  unfold renderDirectory at written
  cases encoded : day.mapM encodeText with
  | error => simp [encoded, Bind.bind, Except.bind] at written
  | ok text =>
    have rendered : PartitionPath.render options [(key, text)] = .ok directory := by
      cases out : PartitionPath.render options [(key, text)] <;>
        simp_all [Bind.bind, Except.bind, Except.mapError]
    have nonempty : key ≠ "" := by
      rintro rfl
      unfold PartitionPath.render at rendered
      split at rendered <;>
        simp [PartitionPath.validate, PartitionPath.validateKeys, Bind.bind, Except.bind] at rendered
    have parsed := PartitionPath.parse_render_of_ok rendered
    have decoded : text.mapM decodeText = .ok day := by
      cases day with
      | none =>
        have same : text = none := Except.ok.inj encoded.symm
        subst text
        rfl
      | some value =>
        cases h : encodeText value with
        | error => simp [Option.mapM, h] at encoded
        | ok raw =>
          have same : text = some raw := by simpa [Option.mapM, h] using encoded.symm
          subst text
          simp [Option.mapM, (encodeText_ok_iff value raw).mp h]
    rw [Hive.Date32.decodeDirectory_singleton key options directory text nonempty parsed, decoded]
    rfl

theorem renderDirectory_markerCollision (key : String) (options : PartitionPath.Options)
    (day : Payload) (printed : encodeText day = .ok options.nullMarker)
    (marker : options.nullMarker.isEmpty = false)
    (valid : PartitionPath.validate options [(key, some options.nullMarker)] = .ok ()) :
    renderDirectory key options (some day) = .error (.path (.nullMarkerCollision key)) := by
  simp [renderDirectory, Option.mapM, printed, PartitionPath.render, marker, valid,
    PartitionPath.renderSegment, Bind.bind, Except.bind, Except.mapError]
  rfl

end Silmaril.Proofs.Formats.Hive.Date32.Render
