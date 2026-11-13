module

public import Silmaril.Wasm.Wac.WatX.Defs
public import Silmaril.Wasm.Wit.Tool.Defs

/-!
# The extended component WAT reader and `Wit.Tool.parseWat`

* `parseWatX_of_parseWat`: on the text `Wit.Tool.parseWat` reads, `parseWatX` writes the
  same bytes.

Kept apart from `Silmaril.Wasm.Wac.WatX.Defs` so that the reader does not import the WIT tool
(`wasm-tools wast` reads component text through `parseWatX`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.WatX

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Wat

/-- On the text `Wit.Tool.parseWat` reads, `parseWatX` writes the same bytes. -/
theorem parseWatX_of_parseWat {t : String} {b : ByteArray} (h : Wit.Tool.parseWat t = .ok b) :
    parseWatX t = .ok b := by
  unfold Wit.Tool.parseWat at h
  unfold parseWatX
  cases hr : Wat.read t with
  | none => simp [hr] at h
  | some c =>
    rw [hr] at h
    simp only [readX_of_read hr]
    exact h

end Silmaril.Wasm.Wac.WatX

end
