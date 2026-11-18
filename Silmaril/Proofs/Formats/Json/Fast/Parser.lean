module

public import Silmaril.Formats.Json.Fast.Parser.Trace.Defs
public import Silmaril.Formats.Json.Fast.Wire.Defs
public import Silmaril.Formats.JsonWire.Grammar.Defs
import Silmaril.Prelude.ChunkSeq.Thms
import Silmaril.Formats.JsonWire.Grammar.Thms

public section
namespace Silmaril.Proofs.Json.Fast.Parser

open Silmaril.Formats
open Silmaril.Formats.Json.Fast (Error Value)
open Silmaril.Formats.Json.Fast.Parser
open Silmaril.Formats.JsonWire

theorem whitespace_consumes (offset : Nat) (input : List Char) :
    ∃ consumed, input = consumed ++ (whitespace offset input).rest ∧
      ∀ char ∈ consumed, Internal.white .rfc8259 char = true := by
  induction input generalizing offset with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons char input ih =>
    by_cases white : Internal.white .rfc8259 char = true
    · obtain ⟨consumed, inputEq, allWhite⟩ := ih (offset + char.utf8Size)
      refine ⟨char :: consumed, ?_, ?_⟩
      · simpa only [whitespace, white, ↓reduceIte, List.cons_append, List.cons.injEq, true_and] using inputEq
      · intro item member
        rcases List.mem_cons.mp member with rfl | member
        · exact white
        · exact allWhite _ member
    · exact ⟨[], by simp [whitespace, white], by simp⟩

private theorem numberLoop_end {start pos stop : Pos} {fuel : Nat} {acc : List Char} {value : Value}
    (finished : numberChar pos.get = false) (result : numberLoop start fuel pos acc = .ok (value, stop)) :
    ∃ decimal, pos = stop ∧ value = .number decimal ∧
      Internal.decimal? .rfc8259 acc.reverse = some (.finite decimal) := by
  cases fuel <;> simp only [numberLoop, finished, Bool.not_false, ↓reduceIte] at result
  all_goals
    split at result
    · rename_i decimal parsed
      cases result
      exact ⟨decimal, rfl, rfl, parsed⟩
    · simp [fail] at result

theorem numberLoop_consumes {start pos stop : Pos} {fuel : Nat} {acc : List Char} {value : Value}
    (result : numberLoop start fuel pos acc = .ok (value, stop)) :
    ∃ read decimal, pos.rest = read ++ stop.rest ∧ value = .number decimal ∧
      Internal.decimal? .rfc8259 (acc.reverse ++ read) = some (.finite decimal) := by
  induction fuel generalizing pos acc with
  | zero =>
    cases next : numberChar pos.get
    · obtain ⟨decimal, rfl, rfl, parsed⟩ := numberLoop_end next result
      exact ⟨[], decimal, rfl, rfl, by simpa using parsed⟩
    · simp [numberLoop, next, fail] at result
  | succ fuel ih =>
    cases next : numberChar pos.get
    · obtain ⟨decimal, rfl, rfl, parsed⟩ := numberLoop_end next result
      exact ⟨[], decimal, rfl, rfl, by simpa using parsed⟩
    · cases pos with
      | mk offset rest =>
        cases rest with
        | nil => exact False.elim ((by decide : numberChar (Char.ofNat 0) ≠ true) next)
        | cons char rest =>
          have charNext : numberChar char = true := next
          have step : numberLoop start fuel ⟨offset + char.utf8Size, rest⟩ (char :: acc) = .ok (value, stop) := by
            simpa [numberLoop, charNext, Pos.get, Pos.next] using result
          obtain ⟨read, decimal, consumed, output, parsed⟩ := ih step
          exact ⟨char :: read, decimal, congrArg (char :: ·) consumed, output,
            by simpa [List.reverse_cons, List.append_assoc] using parsed⟩

/-- The successful production number scanner consumes an independent RFC 8259 number
lexeme and emits the exact decimal of the wire lexer on that lexeme. -/
theorem numberLoop_sound {start stop : Pos} {fuel : Nat} {value : Value}
    (result : numberLoop start fuel start [] = .ok (value, stop)) :
    ∃ read decimal, start.rest = read ++ stop.rest ∧ value = .number decimal ∧
      Internal.NumberChars read ∧ Internal.decimal? .rfc8259 read = some (.finite decimal) := by
  obtain ⟨read, decimal, consumed, output, parsed⟩ := numberLoop_consumes result
  rw [List.reverse_nil, List.nil_append] at parsed
  exact ⟨read, decimal, consumed, output, (Internal.decimal?_sound parsed).1, parsed⟩



private theorem skip_consumes (pos : Pos) : ∃ read, pos.rest = read ++ (skip pos).rest ∧ White read :=
  whitespace_consumes pos.byteIdx pos.rest

private theorem char_consumes {pos : Pos} {char : Char} (notSentinel : char ≠ Char.ofNat 0)
    (found : pos.get = char) : pos.rest = char :: pos.next.rest := by
  cases pos with
  | mk offset rest =>
    cases rest with
    | nil => exact False.elim (notSentinel found.symm)
    | cons head tail => simpa [Pos.get, Pos.next] using found

theorem literal_consumes {literalChars : List Char} {pos stop : Pos}
    (result : literal literalChars pos = .ok stop) : pos.rest = literalChars ++ stop.rest := by
  induction literalChars generalizing pos with
  | nil => cases result; rfl
  | cons char moreChars ih =>
    have expectation := result
    simp only [literal, expect] at expectation
    split at expectation
    · rename_i accepted
      rcases Bool.and_eq_true_iff.mp accepted with ⟨nonempty, matching⟩
      have found : pos.get = char := beq_iff_eq.mp matching
      have step : pos.rest = char :: pos.next.rest := by
        cases pos with
        | mk offset rest =>
          cases rest with
          | nil => simp [Pos.atEnd] at nonempty
          | cons head tail => simpa [Pos.get, Pos.next] using found
      exact step.trans (congrArg (char :: ·) (ih expectation))
    · change Except.error _ = Except.ok _ at expectation
      cases expectation

/-- On success the actual production loop preserves every emitted item in source order. -/
theorem more_sound {Item : Type} {close : Char} {Accept : List Char → Item → Prop}
    {parseItem : Pos → Except Error (Item × Pos)}
    (closeNotSentinel : close ≠ Char.ofNat 0)
    (soundItem : ∀ {pos stop item}, parseItem pos = .ok (item, stop) →
      ∃ lexeme, pos.rest = lexeme ++ stop.rest ∧ Accept lexeme item)
    {fuel : Nat} {pos stop : Pos} {acc output : Array Item}
    (result : more close parseItem fuel pos acc = .ok (output, stop)) :
    ∃ span items, pos.rest = span ++ stop.rest ∧
      output.toList = acc.toList ++ items ∧ Tail close Accept span items := by
  induction fuel generalizing pos acc with
  | zero => simp [more, fail] at result
  | succ fuel ih =>
    simp only [more] at result
    split at result
    · cases result
    · rename_i item itemStop parsed
      obtain ⟨left, before, leftWhite⟩ := skip_consumes pos
      obtain ⟨lexeme, consumed, accepted⟩ := soundItem parsed
      obtain ⟨right, after, rightWhite⟩ := skip_consumes itemStop
      have consumedPrefix : pos.rest = left ++ lexeme ++ right ++ (skip itemStop).rest := by
        rw [before, consumed, after]; simp [List.append_assoc]
      split at result
      · rename_i closed
        have closeStep := char_consumes closeNotSentinel (beq_iff_eq.mp closed)
        cases result
        refine ⟨_, _, ?_, Array.toList_push, .last leftWhite accepted rightWhite⟩
        rw [consumedPrefix, closeStep]; simp [List.append_assoc]
      · split at result
        · rename_i comma
          have commaStep := char_consumes (by decide : ',' ≠ Char.ofNat 0) (beq_iff_eq.mp comma)
          obtain ⟨span, items, read, ordered, trace⟩ := ih result
          refine ⟨_, _, ?_, ?_, .next leftWhite accepted rightWhite trace⟩
          · rw [consumedPrefix, commaStep, read]; simp [List.append_assoc]
          · simpa [List.append_assoc] using ordered
        · simp [fail] at result


/-- Include the empty case of the actual production container parser. The span starts
after the open delimiter and includes its close delimiter, but not the suffix. -/
theorem series_sound {Item : Type} {close : Char} {Accept : List Char → Item → Prop}
    {parseItem : Pos → Except Error (Item × Pos)}
    (closeNotSentinel : close ≠ Char.ofNat 0)
    (soundItem : ∀ {pos stop item}, parseItem pos = .ok (item, stop) →
      ∃ lexeme, pos.rest = lexeme ++ stop.rest ∧ Accept lexeme item)
    {size : Nat} {pos stop : Pos} {output : Array Item}
    (result : series size close parseItem pos = .ok (output, stop)) :
    ∃ left span, pos.rest = left ++ span ++ stop.rest ∧ White left ∧
      ((span = [close] ∧ output.toList = []) ∨ Tail close Accept span output.toList) := by
  obtain ⟨left, skipped, leftWhite⟩ := skip_consumes pos
  simp only [series] at result
  split at result
  · rename_i closed
    have closeStep := char_consumes closeNotSentinel (beq_iff_eq.mp closed)
    cases result
    exact ⟨left, [close], by rw [skipped, closeStep, List.append_assoc]; rfl, leftWhite, .inl ⟨rfl, rfl⟩⟩
  · obtain ⟨span, items, read, ordered, trace⟩ := more_sound closeNotSentinel soundItem result
    have outputItems : output.toList = items := ordered
    exact ⟨left, span, by rw [skipped, read, List.append_assoc], leftWhite,
      .inr (outputItems ▸ trace)⟩


/-- Same suffix and numeric output as the independent wire hex decoder, accounting
for the accumulator in the production loop. -/
theorem hex_sound {count acc decoded : Nat} {pos stop : Pos}
    (result : hex count pos acc = .ok (decoded, stop)) :
    ∃ code, Internal.hexes? count pos.rest = some (code, stop.rest) ∧ decoded = acc * 16 ^ count + code := by
  induction count generalizing pos acc with
  | zero =>
    cases result
    exact ⟨0, rfl, by simp⟩
  | succ count ih =>
    cases pos with
    | mk offset rest =>
      cases rest with
      | nil => simp [hex, Pos.atEnd, fail] at result
      | cons char rest =>
        cases digitResult : Internal.hex? char with
        | none => simp [hex, Pos.atEnd, Pos.get, digitResult, fail] at result
        | some digit =>
          have step : hex count ⟨offset + char.utf8Size, rest⟩ (16 * acc + digit) =
              .ok (decoded, stop) := by
            simpa [hex, Pos.atEnd, Pos.get, digitResult, Pos.next] using result
          obtain ⟨code, wire, value⟩ := ih step
          refine ⟨digit * 16 ^ count + code, ?_, ?_⟩
          · simp [Internal.hexes?, digitResult, wire]
          · rw [value, Nat.pow_succ', Nat.add_mul, Nat.mul_comm 16 acc, Nat.mul_assoc, Nat.add_assoc]


private theorem digit_bound {char : Char} {digit : Nat}
    (parsed : Internal.hex? char = some digit) : digit < 16 := by
  unfold Internal.hex? at parsed
  split at parsed
  · rename_i isDigit
    obtain ⟨above, below⟩ := Char.isDigit_iff_toNat.mp isDigit
    change 48 ≤ char.toNat at above
    change char.toNat ≤ 57 at below
    cases parsed; omega
  · split at parsed
    · rename_i lowerCase
      have below := (Bool.and_eq_true_iff.mp lowerCase).2
      simp only [decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at below
      change char.toNat ≤ 102 at below
      cases parsed; omega
    · split at parsed
      · rename_i upperCase
        have below := (Bool.and_eq_true_iff.mp upperCase).2
        simp only [decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at below
        change char.toNat ≤ 70 at below
        cases parsed; omega
      · cases parsed

private theorem hexes_bound {count code : Nat} {input output : List Char}
    (parsed : Internal.hexes? count input = some (code, output)) : code < 16 ^ count := by
  induction count generalizing input code with
  | zero => cases parsed; decide
  | succ count ih =>
    cases input with
    | nil => cases parsed
    | cons char rest =>
      cases digitResult : Internal.hex? char with
      | none => simp [Internal.hexes?, digitResult] at parsed
      | some digit =>
        cases tailResult : Internal.hexes? count rest with
        | none => simp [Internal.hexes?, digitResult, tailResult] at parsed
        | some result =>
          obtain ⟨tail, suffix⟩ := result
          simp [Internal.hexes?, digitResult, tailResult] at parsed
          obtain ⟨rfl, rfl⟩ := parsed
          calc
            digit * 16 ^ count + tail < digit * 16 ^ count + 16 ^ count :=
              Nat.add_lt_add_left (ih tailResult) _
            _ = (digit + 1) * 16 ^ count := by simp [Nat.add_mul]
            _ ≤ 16 * 16 ^ count := Nat.mul_le_mul_right _ (digit_bound digitResult)
            _ = 16 ^ (count + 1) := (Nat.pow_succ' ..).symm

private theorem units_single {unit : Nat} (bmp : unit < 0x10000)
    (notHigh : ¬ (0xD800 ≤ unit ∧ unit ≤ 0xDBFF)) (notLow : ¬ (0xDC00 ≤ unit ∧ unit ≤ 0xDFFF)) :
    charUnits (Char.ofNat unit) = [UInt16.ofNat unit] := by
  have valid : unit.isValidChar := by unfold Nat.isValidChar; omega
  have point : (Char.ofNat unit).toNat = unit := by simp [Char.ofNat, valid, Char.ofNatAux, Char.toNat]
  simp [charUnits, point, bmp]

private theorem units_pair {high low : Nat} (highOK : 0xD800 ≤ high ∧ high ≤ 0xDBFF)
    (lowOK : 0xDC00 ≤ low ∧ low ≤ 0xDFFF) :
    charUnits (Char.ofNat (0x10000 + (high - 0xD800) * 1024 + low - 0xDC00)) =
      [UInt16.ofNat high, UInt16.ofNat low] := by
  let point := 0x10000 + (high - 0xD800) * 1024 + low - 0xDC00
  have valid : point.isValidChar := by unfold Nat.isValidChar; dsimp [point]; omega
  have pointNat : (Char.ofNat point).toNat = point := by simp [Char.ofNat, valid, Char.ofNatAux, Char.toNat]
  have notBmp : ¬ point < 0x10000 := by dsimp [point]; omega
  have fstUnit : 0xD800 + (point - 0x10000) / 1024 = high := by dsimp [point]; omega
  have sndUnit : 0xDC00 + (point - 0x10000) % 1024 = low := by dsimp [point]; omega
  change charUnits (Char.ofNat point) = _
  simp [charUnits, pointNat, notBmp, fstUnit, sndUnit]

/-- The wire lexer consumes either one Unicode escape or two adjacent escapes forming a
surrogate pair. Their independent UTF-16 decoding agrees with the production scalar. -/
theorem unicodeEscape_sound {start stop : Pos} {char : Char}
    (parsed : unicodeEscape start = .ok (char, stop)) :
    ∃ units : Units, charUnits char = units ∧ unitsChars? units = some [char] ∧
      ((∃ unit, Internal.hexes? 4 start.rest = some (unit, stop.rest) ∧ units = [UInt16.ofNat unit]) ∨
        ∃ high low middle, Internal.hexes? 4 start.rest = some (high, '\\' :: 'u' :: middle) ∧
          Internal.hexes? 4 middle = some (low, stop.rest) ∧
          units = [UInt16.ofNat high, UInt16.ofNat low]) := by
  cases first : hex 4 start 0 with
  | error error => simp [unicodeEscape, first, bind, Except.bind] at parsed
  | ok result =>
    obtain ⟨unit, pos⟩ := result
    obtain ⟨wireUnit, wireFirst, numberFirst⟩ := hex_sound first
    simp at numberFirst
    subst wireUnit
    have firstBound := hexes_bound wireFirst
    have unitNat : (UInt16.ofNat unit).toNat = unit := by
      exact UInt16.toNat_ofNat_of_lt' firstBound
    simp only [unicodeEscape, first, bind, Except.bind] at parsed
    split at parsed
    · rename_i high
      split at parsed
      · simp [fail] at parsed
      · rename_i pair
        have backslash : pos.get = '\\' := by
          by_contra different
          exact pair (by simp [different])
        have letter : pos.next.get = 'u' := by
          by_contra different
          exact pair (by simp [different])
        have middle : pos.rest = '\\' :: 'u' :: pos.next.next.rest :=
          (char_consumes (by decide) backslash).trans (congrArg ('\\' :: ·) (char_consumes (by decide) letter))
        cases second : hex 4 pos.next.next 0 with
        | error error => simp [second] at parsed
        | ok result =>
          obtain ⟨low, tail⟩ := result
          simp only [second] at parsed
          split at parsed
          · rename_i lowOK
            obtain ⟨charEq, stopEq⟩ := Prod.mk.inj (Except.ok.inj parsed)
            subst char
            subst stop
            obtain ⟨wireLow, wireSecond, numberSecond⟩ := hex_sound second
            simp at numberSecond
            subst wireLow
            have secondBound := hexes_bound wireSecond
            have lowNat : (UInt16.ofNat low).toNat = low := by
              exact UInt16.toNat_ofNat_of_lt' secondBound
            exact ⟨[UInt16.ofNat unit, UInt16.ofNat low],
              units_pair (by simpa using high) (by simpa using lowOK),
              by simp [unitsChars?, unitNat, lowNat, high, lowOK],
              .inr ⟨unit, low, _, middle ▸ wireFirst, wireSecond, rfl⟩⟩
          · simp [fail] at parsed
    · rename_i notHigh
      split at parsed
      · simp [fail] at parsed
      · rename_i notLow
        obtain ⟨charEq, stopEq⟩ := Prod.mk.inj (Except.ok.inj parsed)
        subst char
        subst stop
        exact ⟨[UInt16.ofNat unit], units_single firstBound (by simpa using notHigh) (by simpa using notLow),
          by simp [unitsChars?, unitNat, notHigh, notLow],
          .inl ⟨unit, wireFirst, rfl⟩⟩


private theorem hexes_length {count code : Nat} {source suffix : List Char}
    (read : Internal.hexes? count source = some (code, suffix)) :
    suffix.length + count = source.length := by
  induction count generalizing source suffix code with
  | zero => cases read; simp
  | succ count ih =>
    cases source with
    | nil => cases read
    | cons char rest =>
      cases digit : Internal.hex? char with
      | none => simp [Internal.hexes?, digit] at read
      | some digitVal =>
        cases moreDigits : Internal.hexes? count rest with
        | none => simp [Internal.hexes?, digit, moreDigits] at read
        | some output =>
          obtain ⟨value, tail⟩ := output
          simp only [Internal.hexes?, digit, moreDigits, pure, Pure.pure] at read
          have same := congrArg Prod.snd (Option.some.inj read)
          change tail = suffix at same
          subst suffix
          have length := ih moreDigits
          simp only [List.length_cons]; omega

private inductive EscapeRead : List Char → List Char → Units → Prop where
  | one {source suffix : List Char} {units : Units} :
    Internal.escape? .rfc8259 source = some (units, suffix) → suffix.length < source.length →
    EscapeRead source suffix units
  | pair {source middle suffix : List Char} {high low : Units} :
    Internal.escape? .rfc8259 source = some (high, '\\' :: middle) →
    Internal.escape? .rfc8259 middle = some (low, suffix) → suffix.length + 1 < source.length →
    EscapeRead source suffix (high ++ low)

private theorem escaped_wire {pos stop : Pos} {char : Char}
    (ok : escaped pos = .ok (char, stop)) : EscapeRead pos.rest stop.rest (charUnits char) := by
  cases pos with
  | mk offset rest =>
    cases rest with
    | nil => cases ok
    | cons head tail =>
      simp only [escaped, Pos.get, Pos.next, List.headD_cons] at ok
      split at ok
      · obtain ⟨units, unitsEq, _, one | pair⟩ := unicodeEscape_sound ok
        · obtain ⟨unit, read, rfl⟩ := one
          change Internal.hexes? 4 tail = _ at read
          rw [unitsEq]
          exact .one (by simp [Internal.escape?, read]) (by
            have length := hexes_length read
            simp only [List.length_cons]; omega)
        · obtain ⟨high, low, middle, readFirst, readSecond, rfl⟩ := pair
          change Internal.hexes? 4 tail = _ at readFirst
          rw [unitsEq]
          refine @EscapeRead.pair ('u' :: tail) ('u' :: middle) stop.rest
            [UInt16.ofNat high] [UInt16.ofNat low] ?_ ?_ ?_
          · simp [Internal.escape?, readFirst]
          · simp [Internal.escape?, readSecond]
          · have first := hexes_length readFirst
            have second := hexes_length readSecond
            simp only [List.length_cons] at *
            omega
      all_goals first | (cases ok; exact .one rfl (by simp)) | cases ok

private theorem escape_continuation {fuel : Nat} {input suffix : List Char} {units output : Units}
    {stop : List Char} (read : EscapeRead input suffix units)
    (enough : input.length ≤ fuel)
    (continuation : ∀ restFuel, suffix.length < restFuel →
      Internal.quoted? .rfc8259 '"' restFuel suffix = some (output, stop)) :
    Internal.quoted? .rfc8259 '"' (fuel + 1) ('\\' :: input) = some (units ++ output, stop) := by
  cases read with
  | one first consumed =>
    simp [Internal.quoted?, first, continuation fuel (by omega)]
  | pair first second consumed =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have next := continuation fuel (by omega)
      simp [Internal.quoted?, first, second, next, List.append_assoc]

theorem stringLoop_wire {fastFuel : Nat} {pos stop : Pos} {acc : List Char} {text : String}
    (ok : stringLoop fastFuel pos acc = .ok (text, stop)) :
    ∃ units, stringUnits text = acc.reverse.flatMap charUnits ++ units ∧
      ∀ wireFuel, pos.rest.length < wireFuel → Internal.quoted? .rfc8259 '"' wireFuel pos.rest = some (units, stop.rest) := by
  induction fastFuel generalizing pos acc with
  | zero => cases ok
  | succ fastFuel ih =>
    cases pos with
    | mk offset rest =>
      cases rest with
      | nil => cases ok
      | cons char tail =>
        let next : Pos := ⟨offset + char.utf8Size, tail⟩
        change (if char == '"' then .ok (String.ofList acc.reverse, next)
          else if char == '\\' then
            match escaped next with
            | .ok (decoded, after) => stringLoop fastFuel after (decoded :: acc)
            | .error err => .error err
          else if char.toNat < 32 then fail ⟨offset, char :: tail⟩
          else stringLoop fastFuel next (char :: acc)) = .ok (text, stop) at ok
        by_cases close : (char == '"') = true
        · rw [ite_eq_left close] at ok
          have same : char = '"' := beq_iff_eq.mp close
          subst char
          obtain ⟨textEq, stopEq⟩ := Prod.mk.inj (Except.ok.inj ok)
          rw [← textEq, ← stopEq]
          refine ⟨[], by simp [stringUnits], ?_⟩
          intro wireFuel enough
          cases wireFuel with
          | zero => omega
          | succ _ => rfl
        · rw [ite_eq_right close] at ok
          by_cases slash : (char == '\\') = true
          · rw [ite_eq_left slash] at ok
            have same : char = '\\' := beq_iff_eq.mp slash
            subst char
            split at ok
            · rename_i scalar charStop escapedOK
              obtain ⟨units, textEq, restEq⟩ := ih ok
              refine ⟨charUnits scalar ++ units, by simpa [List.reverse_cons, List.append_assoc] using textEq, ?_⟩
              intro wireFuel enough
              cases wireFuel with
              | zero => omega
              | succ fuel =>
                change ('\\' :: tail).length < fuel + 1 at enough
                exact escape_continuation (escaped_wire escapedOK) (by
                  simp only [List.length_cons] at enough
                  omega) restEq
            · cases ok
          · rw [ite_eq_right slash] at ok
            by_cases control : char.toNat < 32
            · simp [control, fail] at ok
            · rw [ite_eq_right control] at ok
              obtain ⟨units, textEq, restEq⟩ := ih ok
              refine ⟨charUnits char ++ units, by simpa [List.reverse_cons, List.append_assoc] using textEq, ?_⟩
              intro wireFuel enough
              cases wireFuel with
              | zero => omega
              | succ fuel =>
                change (char :: tail).length < fuel + 1 at enough
                have restRead := restEq fuel (by
                  change tail.length < fuel
                  simpa using enough)
                change Internal.quoted? .rfc8259 '"' fuel tail = _ at restRead
                simp [Internal.quoted?, close, slash, control, restRead]

theorem quoted_tokens {size : Nat} {pos stop : Pos} {text : String}
    (ok : quoted size pos = .ok (text, stop)) :
    Internal.tokensOf pos.rest = (Internal.tokensOf stop.rest).map (.string (stringUnits text) :: ·) := by
  have check : expect pos '"' = .ok pos.next := by
    unfold expect
    split
    · rfl
    · rename_i rejected
      simp [quoted, expect, rejected, fail, bind, Except.bind] at ok
  have isQuote : pos.get = '"' := by
    unfold expect at check
    split at check
    · rename_i accepted
      exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp accepted).2
    · simp [fail] at check
  have consumed := char_consumes (by decide : '"' ≠ Char.ofNat 0) isQuote
  have loop : stringLoop (size - pos.next.byteIdx + 1) pos.next [] = .ok (text, stop) := by
    simpa [quoted, check, bind, Except.bind] using ok
  obtain ⟨units, view, read⟩ := stringLoop_wire loop
  simp only [List.reverse_nil, List.flatMap_nil, List.nil_append] at view
  subst units
  have lexRead := read (pos.next.rest.length + 1 + 1) (by omega)
  obtain ⟨body, span, _⟩ := Internal.quoted?_sound lexRead
  have shorter : stop.rest.length < pos.next.rest.length + 1 := by
    rw [span]; simp only [List.length_append, List.length_cons]; omega
  rw [consumed, Internal.tokensOf_cons]
  simp [Internal.step, Internal.white, lexRead, shorter]

theorem ofArray_wire (depth : Nat) (items : Array Value) :
    (Value.ofArray items).toWire? (depth + 1) = do
      let children ← items.toList.mapM (Value.toWire? depth)
      return .list (children.foldr .cons .nil) := by
  rw [Value.ofArray, Value.toWire?, ChunkSeq.toList_ofArray]

theorem ofObject_wire (depth : Nat) (entries : Array (String × Value)) :
    (Value.ofObject entries).toWire? (depth + 1) = do
      let children ← entries.toList.mapM fun (key, child) => do
        return (stringUnits key, ← child.toWire? depth)
      return .map (children.foldr (fun (key, child) tail => .objCons key child tail) .objNil) := by
  rw [Value.ofObject, Value.toWire?, ChunkSeq.toList_ofArray]

end Silmaril.Proofs.Json.Fast.Parser
