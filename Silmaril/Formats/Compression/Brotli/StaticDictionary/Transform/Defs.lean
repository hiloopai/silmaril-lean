module

public import Silmaril.Formats.Compression.Brotli.StaticDictionary.Defs

/-! RFC 7932 §8 and Appendix B, including the bytewise ferment rules.
See https://www.rfc-editor.org/rfc/rfc7932.html#section-8. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform

inductive Action where
  | identity
  | fermentFirst
  | fermentAll
  | omitFirst (count : Nat)
  | omitLast (count : Nat)
  deriving DecidableEq, Repr

/-- Appendix B's check-value encoding, independent of libbrotli's internal IDs. -/
def Action.code : Action → UInt8
  | .identity => 0
  | .fermentFirst => 1
  | .fermentAll => 2
  | .omitFirst count => UInt8.ofNat (2 + count)
  | .omitLast count => UInt8.ofNat (11 + count)

structure Entry where
  leading : List UInt8
  action : Action
  trailing : List UInt8
  deriving DecidableEq, Repr

/-- Appendix B in transform ordinal order. The quoted affixes are ASCII;
    ordinal 102 gives its two non-ASCII bytes explicitly. -/
def table : Vector Entry transformCount :=
  let entry (leading : String) (action : Action) (trailing : String) : Entry :=
    ⟨leading.toUTF8.toList, action, trailing.toUTF8.toList⟩
  #v[
    entry "" .identity "", -- 0
    entry "" .identity " ", -- 1
    entry " " .identity " ", -- 2
    entry "" (.omitFirst 1) "", -- 3
    entry "" .fermentFirst " ", -- 4
    entry "" .identity " the ", -- 5
    entry " " .identity "", -- 6
    entry "s " .identity " ", -- 7
    entry "" .identity " of ", -- 8
    entry "" .fermentFirst "", -- 9
    entry "" .identity " and ", -- 10
    entry "" (.omitFirst 2) "", -- 11
    entry "" (.omitLast 1) "", -- 12
    entry ", " .identity " ", -- 13
    entry "" .identity ", ", -- 14
    entry " " .fermentFirst " ", -- 15
    entry "" .identity " in ", -- 16
    entry "" .identity " to ", -- 17
    entry "e " .identity " ", -- 18
    entry "" .identity "\"", -- 19
    entry "" .identity ".", -- 20
    entry "" .identity "\">", -- 21
    entry "" .identity "\n", -- 22
    entry "" (.omitLast 3) "", -- 23
    entry "" .identity "]", -- 24
    entry "" .identity " for ", -- 25
    entry "" (.omitFirst 3) "", -- 26
    entry "" (.omitLast 2) "", -- 27
    entry "" .identity " a ", -- 28
    entry "" .identity " that ", -- 29
    entry " " .fermentFirst "", -- 30
    entry "" .identity ". ", -- 31
    entry "." .identity "", -- 32
    entry " " .identity ", ", -- 33
    entry "" (.omitFirst 4) "", -- 34
    entry "" .identity " with ", -- 35
    entry "" .identity "'", -- 36
    entry "" .identity " from ", -- 37
    entry "" .identity " by ", -- 38
    entry "" (.omitFirst 5) "", -- 39
    entry "" (.omitFirst 6) "", -- 40
    entry " the " .identity "", -- 41
    entry "" (.omitLast 4) "", -- 42
    entry "" .identity ". The ", -- 43
    entry "" .fermentAll "", -- 44
    entry "" .identity " on ", -- 45
    entry "" .identity " as ", -- 46
    entry "" .identity " is ", -- 47
    entry "" (.omitLast 7) "", -- 48
    entry "" (.omitLast 1) "ing ", -- 49
    entry "" .identity "\n\t", -- 50
    entry "" .identity ":", -- 51
    entry " " .identity ". ", -- 52
    entry "" .identity "ed ", -- 53
    entry "" (.omitFirst 9) "", -- 54
    entry "" (.omitFirst 7) "", -- 55
    entry "" (.omitLast 6) "", -- 56
    entry "" .identity "(", -- 57
    entry "" .fermentFirst ", ", -- 58
    entry "" (.omitLast 8) "", -- 59
    entry "" .identity " at ", -- 60
    entry "" .identity "ly ", -- 61
    entry " the " .identity " of ", -- 62
    entry "" (.omitLast 5) "", -- 63
    entry "" (.omitLast 9) "", -- 64
    entry " " .fermentFirst ", ", -- 65
    entry "" .fermentFirst "\"", -- 66
    entry "." .identity "(", -- 67
    entry "" .fermentAll " ", -- 68
    entry "" .fermentFirst "\">", -- 69
    entry "" .identity "=\"", -- 70
    entry " " .identity ".", -- 71
    entry ".com/" .identity "", -- 72
    entry " the " .identity " of the ", -- 73
    entry "" .fermentFirst "'", -- 74
    entry "" .identity ". This ", -- 75
    entry "" .identity ",", -- 76
    entry "." .identity " ", -- 77
    entry "" .fermentFirst "(", -- 78
    entry "" .fermentFirst ".", -- 79
    entry "" .identity " not ", -- 80
    entry " " .identity "=\"", -- 81
    entry "" .identity "er ", -- 82
    entry " " .fermentAll " ", -- 83
    entry "" .identity "al ", -- 84
    entry " " .fermentAll "", -- 85
    entry "" .identity "='", -- 86
    entry "" .fermentAll "\"", -- 87
    entry "" .fermentFirst ". ", -- 88
    entry " " .identity "(", -- 89
    entry "" .identity "ful ", -- 90
    entry " " .fermentFirst ". ", -- 91
    entry "" .identity "ive ", -- 92
    entry "" .identity "less ", -- 93
    entry "" .fermentAll "'", -- 94
    entry "" .identity "est ", -- 95
    entry " " .fermentFirst ".", -- 96
    entry "" .fermentAll "\">", -- 97
    entry " " .identity "='", -- 98
    entry "" .fermentFirst ",", -- 99
    entry "" .identity "ize ", -- 100
    entry "" .fermentAll ".", -- 101
    ⟨[0xc2, 0xa0], .identity, []⟩, -- 102
    entry " " .identity ",", -- 103
    entry "" .fermentFirst "=\"", -- 104
    entry "" .fermentAll "=\"", -- 105
    entry "" .identity "ous ", -- 106
    entry "" .fermentAll ", ", -- 107
    entry "" .fermentFirst "='", -- 108
    entry " " .fermentFirst ",", -- 109
    entry " " .fermentAll "=\"", -- 110
    entry " " .fermentAll ", ", -- 111
    entry "" .fermentAll ",", -- 112
    entry "" .fermentAll "(", -- 113
    entry "" .fermentAll ". ", -- 114
    entry " " .fermentAll ".", -- 115
    entry "" .fermentAll "='", -- 116
    entry " " .fermentAll ". ", -- 117
    entry " " .fermentFirst "=\"", -- 118
    entry " " .fermentAll "='", -- 119
    entry " " .fermentFirst "='" -- 120
  ]

/-- Modify the first RFC step and return its untouched suffix. A short
    two- or three-byte step has no in-range byte to modify. -/
def fermentStep : List UInt8 → List UInt8 × List UInt8
  | [] => ([], [])
  | head :: tail =>
    if head < 0xc0 then
      ([if 0x61 ≤ head ∧ head ≤ 0x7a then head ^^^ 32 else head], tail)
    else if head < 0xe0 then
      match tail with
      | [] => ([head], [])
      | second :: rest => ([head, second ^^^ 32], rest)
    else
      match tail with
      | [] => ([head], [])
      | [second] => ([head, second], [])
      | second :: third :: rest => ([head, second, third ^^^ 5], rest)

def fermentFirst (word : List UInt8) : List UInt8 :=
  let (leading, trailing) := fermentStep word
  leading ++ trailing

namespace Internal

def fermentAllWithFuel : Nat → List UInt8 → List UInt8
  | 0, word => word
  | _ + 1, [] => []
  | fuel + 1, head :: tail =>
    let (leading, trailing) := fermentStep (head :: tail)
    leading ++ fermentAllWithFuel fuel trailing

end Internal

/-- Traverse the entire word in one-, two- or three-byte RFC steps. -/
def fermentAll (word : List UInt8) : List UInt8 :=
  Internal.fermentAllWithFuel word.length word

/-- The RFC byte ranges and xor targets, including short final steps.
    A byte at or above E0 selects a three-byte step. -/
inductive StepWire : List UInt8 → List UInt8 → List UInt8 → Prop where
  | empty : StepWire [] [] []
  | single {head : UInt8} {tail : List UInt8} :
      head < 0xc0 →
      StepWire (head :: tail) [if 0x61 ≤ head ∧ head ≤ 0x7a then head ^^^ 32 else head] tail
  | two {head second : UInt8} {tail : List UInt8} :
      0xc0 ≤ head → head < 0xe0 → StepWire (head :: second :: tail) [head, second ^^^ 32] tail
  | twoShort {head : UInt8} :
      0xc0 ≤ head → head < 0xe0 → StepWire [head] [head] []
  | three {head second third : UInt8} {tail : List UInt8} :
      0xe0 ≤ head → StepWire (head :: second :: third :: tail) [head, second, third ^^^ 5] tail
  | threeShortOne {head : UInt8} : 0xe0 ≤ head → StepWire [head] [head] []
  | threeShortTwo {head second : UInt8} : 0xe0 ≤ head → StepWire [head, second] [head, second] []

inductive FermentAllWire : List UInt8 → List UInt8 → Prop where
  | empty : FermentAllWire [] []
  | next {input leading trailing rest : List UInt8} :
      input ≠ [] → StepWire input leading trailing → FermentAllWire trailing rest →
      FermentAllWire input (leading ++ rest)

def middle (action : Action) (word : List UInt8) : List UInt8 :=
  match action with
  | .identity => word
  | .fermentFirst => fermentFirst word
  | .fermentAll => fermentAll word
  | .omitFirst count => word.drop count
  | .omitLast count => word.take (word.length - count)

inductive MiddleWire : Action → List UInt8 → List UInt8 → Prop where
  | identity (word : List UInt8) : MiddleWire .identity word word
  | fermentFirst {word leading trailing : List UInt8} :
      StepWire word leading trailing → MiddleWire .fermentFirst word (leading ++ trailing)
  | fermentAll {word result : List UInt8} :
      FermentAllWire word result → MiddleWire .fermentAll word result
  | omitFirst (word : List UInt8) (count : Nat) :
      MiddleWire (.omitFirst count) word (word.drop count)
  | omitLast (word : List UInt8) (count : Nat) :
      MiddleWire (.omitLast count) word (word.take (word.length - count))

def middleSize (action : Action) (length : Nat) : Nat :=
  match action with
  | .omitFirst count | .omitLast count => length - count
  | _ => length

def outputSize (row : Entry) (length : Nat) : Nat :=
  row.leading.length + middleSize row.action length + row.trailing.length

inductive Error where
  | address (reason : StaticDictionary.Error)
  | baseLength
  | transformOrdinal
  deriving DecidableEq, Repr

/-- Materialize a checked base word and transform ordinal as raw bytes. -/
def applyTransform (ordinal : Nat) (word : ByteArray) : Except Error ByteArray :=
  if ¬WordLength word.size then .error .baseLength
  else
    match table[ordinal]? with
    | none => .error .transformOrdinal
    | some row => .ok ⟨(row.leading ++ middle row.action word.data.toList ++ row.trailing).toArray⟩

/-- Compose the address split, the canonical lookup and the chosen row. -/
def materialize (length wordId : Nat) : Except Error ByteArray := do
  let address ← (splitAddress length wordId).mapError Error.address
  let word ← (lookup length address.index).mapError Error.address
  applyTransform address.transform word

/-- The returned byte array has the original row's exact affixes and a
    witnessed middle transformation. -/
def Wire (ordinal : Nat) (word result : ByteArray) : Prop :=
  ∃ row content, table[ordinal]? = some row ∧ MiddleWire row.action word.data.toList content ∧
    result.data.toList = row.leading ++ content ++ row.trailing

end Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform
