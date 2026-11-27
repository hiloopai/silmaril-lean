module

import Silmaril.Formats.Compression.Brotli.BlockTypes.Switch.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Brotli.BlockTypes.Switch.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression (LSBReader)
open Silmaril.Formats.Compression.Brotli.BlockTypes (Control Controls)
open Silmaril.Formats.Compression.Brotli.BlockTypes.Switch

private def reader (bits : Nat) (value : Nat := 0) : LSBReader := ⟨value, bits, [], 96⟩
private def runOut : Run := ⟨0, 1, 0⟩
private def mkControl (symbol : Fin 4) : Control :=
  .multiple 2 (.singleton 4 symbol.val symbol.isLt) (.singleton 26 0 (by decide)) 1

private def transition (symbol : Fin 4) (run : Run) (extra : Nat) :
    Except Error (Run × Nat) :=
  (read .insertCopy (mkControl symbol) 2 run (reader 3 extra)).map
    (fun (next, after) => (next, after.totalRead))

#guard Run.start (mkControl 0) = ⟨0, 1, 1⟩
#guard transition 0 runOut 0 = .ok (⟨1, 0, 0⟩, 98)
#guard transition 1 runOut 2 = .ok (⟨1, 0, 2⟩, 98)
#guard transition 1 ⟨1, 0, 0⟩ 0 = .ok (⟨0, 1, 0⟩, 98)
#guard transition 2 runOut 0 = .ok (⟨0, 0, 0⟩, 98)
#guard transition 3 runOut 0 = .ok (⟨1, 0, 0⟩, 98)

private def outcome (category : Category) (spec : Control) (bitLimit : Nat) (run : Run)
    (before : LSBReader) : Except Error Run :=
  (read category spec bitLimit run before).map Prod.fst

#guard outcome .literal (mkControl 0) 0 ⟨1, 0, 2⟩ (reader 0) = .ok ⟨1, 0, 1⟩
#guard outcome .distance (mkControl 0) 1 runOut (reader 3) = .error ⟨96, .distance, .length .bitLimit⟩
#guard outcome .literal (mkControl 0) 2 runOut (reader 1) = .error ⟨96, .literal, .length .truncated⟩
#guard outcome .insertCopy (mkControl 0) 2 ⟨0, 2, 1⟩ (reader 2) = .error ⟨96, .insertCopy, .invalidState⟩
#guard outcome .distance .single 0 ⟨0, 0, 0⟩ (reader 0) = .error ⟨96, .distance, .singleExhausted⟩

-- A fabricated control with a type outside its declared alphabet is rejected.
private def outside : Control :=
  .multiple 2 (.singleton 5 4 (by decide)) (.singleton 26 0 (by decide)) 1
#guard outcome .literal outside 2 runOut (reader 2) = .error ⟨96, .literal, .typeRange⟩

private def controls : Controls := ⟨mkControl 0, mkControl 1, mkControl 3⟩
private def three : State := ⟨runOut, ⟨1, 0, 3⟩, ⟨1, 1, 4⟩⟩
private def isolated (category : Category) : Except Error State :=
  (select controls category 2 three (reader 2)).map Prod.fst
#guard isolated .literal = .ok { three with literal := ⟨1, 0, 0⟩ }
#guard isolated .insertCopy = .ok { three with insertCopy := ⟨1, 0, 2⟩ }
#guard isolated .distance = .ok { three with distance := ⟨1, 1, 3⟩ }
