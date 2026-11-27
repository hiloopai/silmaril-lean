module

public import Silmaril.Formats.Compression.Brotli.Command.Defs
import Init.Data.Nat.Bitwise.Lemmas
import Init.Omega

/-! The RFC 7932 §7.1 literal context and a bounded §9.3 insertion for
one literal block type, starting after the command's length fields. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Literal

open ContextHeader (Mode)
open ContextMap.Decode (Map)
open Huffman.Description (Table)

structure History where
  mostRecent : UInt8
  secondRecent : UInt8
  deriving DecidableEq, Repr

def History.start : History := ⟨0, 0⟩

def History.push (history : History) (byte : UInt8) : History :=
  ⟨byte, history.mostRecent⟩

def History.advance (history : History) (bytes : List UInt8) : History :=
  bytes.foldl History.push history

set_option maxRecDepth 1024 in
/-- Lut0 in RFC 7932 §7.1. -/
def utf8MostRecent : Vector (Fin 64) 256 := #v[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 4, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  8, 12, 16, 12, 12, 20, 12, 16, 24, 28, 12, 12, 32, 12, 36, 12,
  44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 32, 32, 24, 40, 28, 12,
  12, 48, 52, 52, 52, 48, 52, 52, 52, 48, 52, 52, 52, 52, 52, 48,
  52, 52, 52, 52, 52, 48, 52, 52, 52, 52, 52, 24, 12, 28, 12, 12,
  12, 56, 60, 60, 60, 56, 60, 60, 60, 56, 60, 60, 60, 60, 60, 56,
  60, 60, 60, 60, 60, 56, 60, 60, 60, 60, 60, 24, 12, 28, 12, 0,
  0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
  0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
  0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
  0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
  2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3,
  2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3,
  2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3,
  2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3]

set_option maxRecDepth 1024 in
/-- Lut1 in RFC 7932 §7.1. -/
def utf8SecondRecent : Vector (Fin 4) 256 := #v[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1,
  1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1,
  1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 1, 1, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

set_option maxRecDepth 1024 in
/-- Lut2 in RFC 7932 §7.1. -/
def signedClasses : Vector (Fin 8) 256 := #v[
  0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
  4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
  4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
  4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
  4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
  5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
  6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7]

/-- The RFC context ID is always one of the 64 entries of a literal block. -/
def contextId (mode : Mode) (history : History) : Fin 64 :=
  let first := history.mostRecent.toNat
  let second := history.secondRecent.toNat
  have firstBound : first < 256 := history.mostRecent.toNat_lt_size
  have secondBound : second < 256 := history.secondRecent.toNat_lt_size
  match mode with
  | .lsb6 => ⟨first % 64, by omega⟩
  | .msb6 => ⟨first / 4, by omega⟩
  | .utf8 =>
    let left := utf8MostRecent[first]
    let right := utf8SecondRecent[second]
    ⟨left.val ||| right.val, Nat.or_lt_two_pow (n := 6) left.isLt (by have := right.isLt; omega)⟩
  | .signed =>
    let left := signedClasses[first]
    let right := signedClasses[second]
    have high : left.val <<< 3 < 64 := by
      rw [Nat.shiftLeft_eq]
      have := left.isLt
      omega
    ⟨(left.val <<< 3) ||| right.val, Nat.or_lt_two_pow (n := 6) high (by have := right.isLt; omega)⟩

structure Source where
  mode : Mode
  map : Map
  trees : List Table

/-- Look up one context-map entry without expanding the implicit map. -/
def lookup (map : Map) (index : Nat) : Option Nat :=
  match map with
  | .implicit entries => if index < entries then some 0 else none
  | .coded _ values => values[index]?

/-- Index the original map using the current two-byte history. -/
def Source.treeIndex? (source : Source) (history : History) : Option Nat :=
  lookup source.map (contextId source.mode history).val

structure Limits where
  /-- Total output allowed so far in this meta-block, including the new literals. -/
  output : Nat
  /-- Committed source bits for the insertion. -/
  bits : Nat

structure State where
  produced : Nat
  history : History
  deriving DecidableEq, Repr

def State.start : State := ⟨0, History.start⟩

inductive Next where
  | endOfMetaBlock
  | copyPending
  deriving DecidableEq, Repr

structure Result where
  bytes : List UInt8
  state : State
  next : Next
  deriving DecidableEq, Repr

inductive Error where
  | literalBlockTypes
  | modes
  | mapExtent
  | treeGroup
  | contextEntry
  | treeIndex
  | treeAlphabet
  | symbol (reason : Huffman.Description.SymbolError)
  | symbolRange
  | metaBlockExtent
  | outputLimit
  deriving DecidableEq, Repr

def mapExtent : Map → Nat
  | .implicit entries => entries
  | .coded _ values => values.length

/-- Limit the header to one literal block type. The command group is
    independent. The caller may already have selected its command tree. -/
def source (header : CompressedHeader.Header) : Except Error Source :=
  match header.initial.controls.literal with
  | .multiple .. => .error .literalBlockTypes
  | .single =>
    match header.initial.fields.modes with
    | [mode] =>
      if mapExtent header.literalMap ≠ 64 then .error .mapExtent
      else if header.literalTrees.length ≠ header.literalMap.treeCount then .error .treeGroup
      else .ok ⟨mode, header.literalMap, header.literalTrees⟩
    | _ => .error .modes

structure FromHeader (header : CompressedHeader.Header) (tables : Source) : Prop where
  single : header.initial.controls.literal = .single
  mode : header.initial.fields.modes = [tables.mode]
  map : tables.map = header.literalMap
  trees : tables.trees = header.literalTrees

/-- Each literal's selected tree depends on the exact history before it.
    The step records just the original code bits for that literal. -/
inductive Wire (source : Source) : History → List Bool → List UInt8 → History → Prop where
  | done (history : History) : Wire source history [] [] history
  | step {history final : History} {byte : UInt8} {tree code width : Nat} {table : Table}
      {tailBits : List Bool} {tail : List UInt8} :
      source.treeIndex? history = some tree →
      source.trees[tree]? = some table →
      table.alphabetSize = 256 →
      table.codeFor byte.toNat = some (code, width) →
      width ≤ 15 →
      Wire source (history.push byte) tailBits tail final →
      Wire source history (msbBits code width ++ tailBits) (byte :: tail) final

/-- Decode a checked byte symbol using the selected literal table. -/
def readByte (table : Table) (bitLimit : Nat) (before : LSBReader) : Except Error (UInt8 × LSBReader) :=
  if table.alphabetSize ≠ 256 then .error .treeAlphabet
  else do
    let (symbol, after) ← (table.readBounded bitLimit before).mapError Error.symbol
    if fits : symbol < 256 then .ok (UInt8.ofNatLT symbol fits, after)
    else .error .symbolRange

namespace Internal

structure Cursor where
  reader : LSBReader
  remaining : Nat

def Cursor.advance (cursor : Cursor) (after : LSBReader) : Cursor :=
  ⟨after, cursor.remaining - (after.totalRead - cursor.reader.totalRead)⟩

def readOne (source : Source) (history : History) (cursor : Cursor) :
    Except Error (UInt8 × Cursor) :=
  match source.treeIndex? history with
  | none => .error .contextEntry
  | some tree =>
    match source.trees[tree]? with
    | none => .error .treeIndex
    | some table => do
      let (byte, after) ← readByte table cursor.remaining cursor.reader
      pure (byte, cursor.advance after)

/-- The insertion quota is fuel even for zero-bit singleton trees. -/
def scan (source : Source) :
    Nat → History → List UInt8 → Cursor → Except Error (List UInt8 × History × Cursor)
  | 0, history, reversed, cursor => .ok (reversed.reverse, history, cursor)
  | count + 1, history, reversed, cursor => do
    let (byte, after) ← readOne source history cursor
    scan source count (history.push byte) (byte :: reversed) after

end Internal

/-- Read the insertion of a checked command within the advertised MLEN.
    If those literals reach MLEN, the cursor is already at the end of
    the meta-block and no distance field is required. -/
def read (header : CompressedHeader.Header) (command : Command.Value)
    (metaLength : Nat) (limits : Limits) (state : State) (before : LSBReader) :
    Except Error (Result × LSBReader) := do
  let tables ← source header
  let produced := state.produced + command.insertLength
  if metaLength ≤ state.produced ∨ metaLength < produced then .error .metaBlockExtent
  else if limits.output < produced then .error .outputLimit
  else
    let (bytes, history, after) ←
      Internal.scan tables command.insertLength state.history [] ⟨before, limits.bits⟩
    let next := if produced = metaLength then Next.endOfMetaBlock else .copyPending
    pure (⟨bytes, ⟨produced, history⟩, next⟩, after.reader)

end Silmaril.Formats.Compression.Brotli.Literal
