module

public import Silmaril.Wasm.Binaryen.Exe.TagEncode
public import Silmaril.Wasm.Binaryen.Exe.EncodeBaseSound
public import Silmaril.Wasm.Binary.Core.Instructions

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm

theorem encTagType_sound (t : TagType) : Binary.Core.TagType (encTagType t) t :=
  .mk (encIdx_sound t)

theorem encCatch_sound (c : Catch) : Binary.Core.Catch (encCatch c) c := by
  cases c with
  | catch_ x l => exact .catch_ (encIdx_sound x) (encIdx_sound l)
  | catchRef x l => exact .catchRef (encIdx_sound x) (encIdx_sound l)
  | catchAll l => exact .catchAll (encIdx_sound l)
  | catchAllRef l => exact .catchAllRef (encIdx_sound l)

end Silmaril.Wasm.Binaryen.Exe
