module

public import Silmaril.Wasm.Tools.Reencode.Defs
public import Silmaril.Wasm.Tools.Layout.Thms
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound

/-!
# The re-encoder encodes the same module

* `firstAccepted_sound`: the chosen candidate encodes the module of the canonical bytes;
* `reencodeModule_sound`: re-encoding a module gives bytes of that module;
* `reencode_sound`: `reencode b` and `b` encode the same module, in silmaril-lean's binary
  grammar `Binary.Core.Encodes` (byte equality with the input is tested, not claimed).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Reencode

open Silmaril Silmaril.Wasm

theorem firstAccepted_sound {dc : Bool} {canon : List UInt8} {m : Wasm.Module}
    (hc : Binary.Core.Encodes canon m) :
    ∀ cs : List (Option (List UInt8)), Binary.Core.Encodes (firstAccepted dc canon cs) m
  | [] => hc
  | some c :: cs => by
    unfold firstAccepted
    split
    · exact Layout.accepts_sound hc (by assumption)
    · exact firstAccepted_sound hc cs
  | none :: cs => firstAccepted_sound hc cs

theorem reencodeModule_sound {b : ByteArray} {m : Wasm.Module} {r : List UInt8}
    (h : reencodeModule b m = .ok r) : Binary.Core.Encodes r m := by
  unfold reencodeModule at h
  cases he : Binaryen.Exe.encodeModuleWith? (hasDataCount b) m with
  | error e => simp [he, bind, Except.bind] at h
  | ok canon =>
    simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact firstAccepted_sound (Binaryen.Exe.encodeModuleWith?_sound he) _

/-- `reencode b` encodes the module `b` encodes. -/
theorem reencode_sound {b r : ByteArray} (h : reencode b = .ok r) :
    ∃ m, Binary.Core.Encodes b.data.toList m ∧ Binary.Core.Encodes r.data.toList m := by
  unfold reencode at h
  cases hd : Binary.Core.Decode.decodeModule b with
  | error e => simp [hd, bind, Except.bind] at h
  | ok m =>
    cases hr : reencodeModule b m with
    | error e => simp [hd, hr, bind, Except.bind] at h
    | ok l =>
      simp only [hd, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨m, Binary.Core.Decode.decodeModule_sound hd, by simpa using reencodeModule_sound hr⟩

end Silmaril.Wasm.Tools.Reencode
