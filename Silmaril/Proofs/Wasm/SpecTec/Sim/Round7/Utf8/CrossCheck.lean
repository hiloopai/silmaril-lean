module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Utf8.Env
public import Silmaril.Wasm.SpecTec.Versions.Thms

/-!
# Round 7, `$utf8`: the erratum against the pinned clauses and main's `$utf8single` (#656)

The erratum `utf8Env` answers `$utf8` by `String.toUTF8` (`applies_utf8`). This file checks that
answer against the two SpecTec texts on the four-byte character U+1F601, whose UTF-8 encoding is
`F0 9F 98 81`:

* the pinned (fixed) wasm-3.0 script's own four-byte clause of `$utf8` (clause 4) **rejects**
  these bytes (#656, `Versions.utf8ClauseRejectsGrin_original`), so the pinned clauses do not
  define UTF-8 there and the erratum departs from them;
* the main stream's split into `$utf8` = `concat_` of `$utf8single` (#656 fixed upstream)
  **accepts** them in `$utf8single`'s four-byte clause (clause 3,
  `Versions.utf8singleAcceptsGrin_main`), which is what the erratum computes;
* the erratum is per character, as main's split is: `$utf8` of a list is the concatenation of
  `$utf8` of its characters (`utf8Call_concat`).

So on this witness the erratum agrees with main and not with the pinned clause it replaces. This
is a check on one character, by kernel evaluation of the premises; it is not a proof that main's
`$utf8single` clauses define `String.utf8EncodeChar` for every character.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.RuntimeBridge (charToValue)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Round6.MemSimd (utf8Call)

/-- U+1F601 encodes as `F0 9F 98 81`. -/
theorem toUTF8_grin :
    ("😁" : String).toUTF8.data.toList.map (fun b => pctV b.toNat) =
      [pctV 0xF0, pctV 0x9F, pctV 0x98, pctV 0x81] := by
  decide +kernel

/-- **The erratum answers `$utf8(U+1F601)` with `F0 9F 98 81`.** -/
theorem applies_utf8_grin (B : Builtins) :
    Applies (utf8Env B) "utf8" [.val (.list [charToValue '😁'])]
      (.list [pctV 0xF0, pctV 0x9F, pctV 0x98, pctV 0x81]) := by
  have h := applies_utf8 B "😁"
  rwa [toUTF8_grin] at h

set_option maxRecDepth 100000 in
/-- **Cross-check with #656**: the erratum's bytes for U+1F601 are accepted by main's
`$utf8single` and rejected by the pinned script's own four-byte clause of `$utf8`. -/
theorem utf8_crossCheck_656 (B : Builtins) :
    Applies (utf8Env B) "utf8" [.val (.list [charToValue '😁'])]
        (.list [pctV 0xF0, pctV 0x9F, pctV 0x98, pctV 0x81]) ∧
      Versions.Utf8ClauseAcceptsGrin Versions.Main.Wasm30.original "utf8single" 3 ∧
      Versions.Utf8ClauseRejectsGrin Scripts.Wasm30.original "utf8" 4 :=
  ⟨applies_utf8_grin B, Versions.utf8singleAcceptsGrin_main,
    Versions.utf8ClauseRejectsGrin_original⟩

/-- **The erratum is per character, as main's `$utf8 = concat_($utf8single(ch)*)` is**: `$utf8`
of a list of characters is the concatenation of `$utf8` of each character. -/
theorem utf8Call_concat (cs : List Char) :
    utf8Call [.val (.list (cs.map charToValue))] =
      some (.list (cs.flatMap fun c => charBytesV c)) ∧
    ∀ c : Char, utf8Call [.val (.list [charToValue c])] = some (.list (charBytesV c)) :=
  ⟨utf8Call_chars cs, fun c => by simpa using utf8Call_chars [c]⟩

end Silmaril.Wasm.SpecTec.Sim.Round7
