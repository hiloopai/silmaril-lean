module

public import Silmaril.Wasm.Binaryen.Exe.EncodeBase
public import Silmaril.Wasm.Binary.Core.Types

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm

/-- A tag type: the exception attribute `0x00`, then its function type index. -/
def encTagType (t : TagType) : List UInt8 := [0x00] ++ encIdx t

/-- A `try_table` catch clause: its kind byte, then the tag index (for `catch` and
`catch_ref`) and the label index. -/
def encCatch : Catch → List UInt8
  | .catch_ x l => [0x00] ++ encIdx x ++ encIdx l
  | .catchRef x l => [0x01] ++ encIdx x ++ encIdx l
  | .catchAll l => [0x02] ++ encIdx l
  | .catchAllRef l => [0x03] ++ encIdx l

end Silmaril.Wasm.Binaryen.Exe
