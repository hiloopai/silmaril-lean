module

import Silmaril.Formats.Csv.Typed.Utf8.Bounded.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Defs
import Batteries.Data.Except
meta import Silmaril.Formats.Csv.Typed.Utf8.Bounded.Defs
meta import Silmaril.Formats.Csv.Typed.Codecs.Defs

namespace Silmaril.Formats.Csv.Typed.Utf8.Bounded

private def bytes (text : String) : Bytes := text.toUTF8.data.toList

private def Value : Bool → Type
  | false => String
  | true => Int32

private def codecs : (kind : Bool) → CellCodec (Value kind)
  | false => Typed.Utf8.string
  | true => Typed.Codecs.int32

private def schema : Schema Bool :=
  ⟨2, Fin.cases (bytes "名前", false) (fun _ => (bytes "i32", true))⟩

private def zero : Schema Bool := ⟨0, Fin.elim0⟩

private def observed (rows : Table schema Value) : List (Option String × Option Int32) :=
  rows.map fun row => (row (0 : Fin 2), row (1 : Fin 2))

private def checkRows (cap : Nat) (wire : Bytes) :=
  (decode cap schema codecs wire).map observed

private def checkCount (cap : Nat) (wire : Bytes) :=
  (decode cap zero codecs wire).map List.length

#guard checkRows 0 [] == .error (.csv .missingHeader)
#guard checkRows 0 (bytes "名前,i32") == .ok []
#guard checkRows 0 (bytes "名前,i32\r\nT1,T2") == .error .rowLimit
#guard checkRows 1 (bytes "名前,i32\r\nT1,T2") == .ok [(some "1", some 2)]
#guard checkRows 1 (bytes "名前,i32\r\nN,N\r") == .error (.csv .malformedWire)
#guard checkRows 0 (bytes "i32,名前\r\nN,N") == .error (.csv .headerMismatch)
#guard checkRows 1 (bytes "名前,i32\r\nN,T+1\r\n\"unterminated") ==
  .error (.csv (.parseCell 1))
#guard checkRows 1 (bytes "名前,i32\r\nN,N\r\n\"unterminated") == .error .rowLimit
#guard checkRows 2 (bytes "名前,i32\r\nN,N\r\n\"unterminated") == .error (.csv .malformedWire)
#guard checkRows 1 (bytes "名前,i32\r\nN,N\r\nT" ++ [0xFF] ++ bytes ",N") == .error .rowLimit
#guard checkRows 2 (bytes "名前,i32\r\nN,N\r\nT" ++ [0xFF] ++ bytes ",N") ==
  .error (.csv .malformedWire)
#guard checkCount 0 (bytes "\"\"\r\n") == .ok 0
#guard checkCount 2 (bytes "\"\"\r\n\"\"\r\n\r\n") == .ok 2
#guard checkCount 1 (bytes "\"\"\r\n\"\"\r\n\r\n") == .error .rowLimit

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

/-- Check independent CSV framing, typed rows, and budget/error precedence. -/
public def checkFixtures (directory : System.FilePath) : IO Unit := do
  let wire file := (IO.FS.readBinFile (directory / file)).map (·.data.toList)
  let expected : List (Option String × Option Int32) :=
    [(some "café, \"first\"\r\nsecond", some 7), (some "", some (-1)), (none, none)]
  let data ← wire "data.csv"
  require "exact full-data cap" (checkRows 3 data == .ok expected)
  require "zero full-data cap" (checkRows 0 data == .error .rowLimit)
  require "complete decoder agreement" ((Typed.Utf8.decode schema codecs data).map observed == .ok expected)
  let finalRecord ← wire "unterminated-record.csv"
  require "optional last CRLF" (checkRows 3 finalRecord == .ok expected)
  let headerOnly ← wire "header.csv"
  require "positive-width header-only at zero cap" (checkRows 0 headerOnly == .ok [])
  let cell ← wire "late-cell.csv"
  require "unreached bad cell" (checkRows 2 cell == .error .rowLimit)
  require "reached bad cell" (checkRows 3 cell == .error (.csv (.parseCell 1)))
  let width ← wire "late-width.csv"
  require "unreached blank typed record" (checkRows 2 width == .error .rowLimit)
  require "reached blank typed record" (checkRows 3 width == .error (.csv (.width 2 1)))
  let malformed ← wire "late-wire.csv"
  require "unreached malformed wire" (checkRows 2 malformed == .error .rowLimit)
  require "reached malformed wire" (checkRows 3 malformed == .error (.csv .malformedWire))
  let markers ← wire "markers.csv"
  require "exact width-zero cap" (checkCount 3 markers == .ok 3)
  require "short width-zero cap" (checkCount 2 markers == .error .rowLimit)
  let markerHeader ← wire "marker-header.csv"
  require "zero-column header-only at zero cap" (checkCount 0 markerHeader == .ok 0)
  IO.println "Eight CPython CSV controls passed."

#print axioms decode_ok_iff

end Silmaril.Formats.Csv.Typed.Utf8.Bounded

public def main (args : List String) : IO Unit :=
  match args with
  | [directory] => Silmaril.Formats.Csv.Typed.Utf8.Bounded.checkFixtures directory
  | _ => throw (IO.userError "expected the CPython fixture directory")
