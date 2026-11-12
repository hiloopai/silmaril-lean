module

public import Silmaril.Wasm.Tools.Layout.Defs
public import Silmaril.Wasm.Tools.Names.Thms
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound

/-!
# The layout check is sound

* `accepts_sound`: a candidate the check accepts encodes the module of the canonical bytes.
* `relayout_sound`: whatever `relayout` returns encodes that module (the accepted candidate,
  or the canonical bytes followed by custom sections).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Layout

open Silmaril Silmaril.Wasm

theorem accepts_sound {dc : Bool} {canon cand : List UInt8} {m : Wasm.Module}
    (hc : Binary.Core.Encodes canon m) (h : accepts dc canon cand = true) :
    Binary.Core.Encodes cand m := by
  unfold accepts at h
  split at h
  · rename_i m' hd
    split at h
    · rename_i c' he
      have hEq : c' = canon := by simpa using h
      subst hEq
      have hm : m' = m := Binary.Core.functional (Binaryen.Exe.encodeModuleWith?_sound he) hc
      subst hm
      simpa using Binary.Core.Decode.decodeModule_sound hd
    · cases h
  · cases h

theorem relayout_sound {h : Hints} {cs : List Annot.Custom} {names : List UInt8} {dc : Bool}
    {m : Wasm.Module} {canon : List UInt8} (hc : Binary.Core.Encodes canon m)
    (hn : Binary.Customs names) : Binary.Core.Encodes (relayout h cs names dc m canon) m := by
  unfold relayout
  split
  · split
    · exact accepts_sound hc (by assumption)
    · exact Names.encodes_append_custom hc hn
  · exact Names.encodes_append_custom hc hn

end Silmaril.Wasm.Tools.Layout
