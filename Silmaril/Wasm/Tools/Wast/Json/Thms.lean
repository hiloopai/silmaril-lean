module

public import Silmaril.Wasm.Tools.Wast.Json.Defs
import Silmaril.Proofs.Wasm.Tools.Wast.Json

/-!
# `json-from-wast`: what the values mean

The numbers `json-from-wast` writes are the values silmaril-lean's literal relations give
the tokens (`Silmaril.Wasm.Text`, SpecTec `6.1-text.values`):

* `intLit?_sound`: `intLit? N s = some b → Text.IN N s b` (`iN`: unsigned, or signed in
  range, decimal or hexadecimal, `_` separators);
* `floatLit?_sound`: `floatLit? t s = some b → Text.FN t s b` (decimal and hexadecimal
  floats rounded to nearest-even by Lean's IEEE model, `inf`, `nan`, `nan:0x…`), and
  `floatLitFast?_sound` for the fast path the conversion uses (it cuts the token once
  instead of searching every cut; proof in `Silmaril.Proofs.Wasm.Tools.Wast.Json`);
* `natLit?_sound`: `natLit? N s = some n → Text.UN N cs n` for `s` without its optional `+`;
* `coreJ_i32`, `coreJ_i64`, `coreJ_f32`, `coreJ_f64`: the JSON of `(i32.const s)` … is
  `{"type": "i32", "value": "<signed decimal of b>"}` (`f32`/`f64`: the bit pattern's
  unsigned decimal), as `wasm-tools` 1.262.0 serializes `IntString<i32>` and
  `FloatConst<f32>`.

The printers the tool runs are the specification printers (`Json.compactFast_eq`,
`Json.prettyFast_eq`: one accumulator instead of nested `++`). The JSON syntax itself
(`Json.compact`, `Json.pretty`) and the command layout are tested byte for byte against the
pinned `wasm-tools` (`tools/wasm-tools/tests/wast`), not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

open Silmaril.Wasm Silmaril.Wasm.Text

theorem mem_of_head? {α : Type} {l : List α} {a : α} (h : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => simp at h
  | cons x xs => simp only [List.head?_cons, Option.some.injEq] at h; subst h; simp

theorem intLit?_sound {N : Nat} {s : String} {b : BitVec N} (h : intLit? N s = some b) :
    IN N s.toList b :=
  ValuesExamples.in_iff.mpr (mem_of_head? h)

theorem floatLit?_sound {t : FloatType} {s : String} {b : BitVec t.width}
    (h : floatLit? t s = some b) : FN t s.toList b :=
  ValuesExamples.fn_iff.mpr (mem_of_head? h)

/-- The fast path `json-from-wast` uses is sound for `Text.FN` too. -/
theorem floatLitFast?_sound {t : FloatType} {s : String} {b : BitVec t.width}
    (h : floatLitFast? t s = some b) : FN t s.toList b :=
  floatLitFast?_sound' h

theorem natLit?_sound {N : Nat} {s : String} {n : Nat} (h : natLit? N s = some n) :
    UN N (if s.startsWith "+" then (s.drop 1).toString.toList else s.toList) n :=
  ValuesExamples.un_iff.mpr (mem_of_head? h)

theorem coreJ_i32 (r : Bool) {s : String} {b : BitVec 32} (h : intLit? 32 s = some b) :
    coreJ r (.lit "i32.const" [s]) = .ok (tyObj "i32" [("value", .str (signedStr b))]) := by
  simp [coreJ, oneArg, lit, h, bind, Except.bind, pure, Except.pure]

theorem coreJ_i64 (r : Bool) {s : String} {b : BitVec 64} (h : intLit? 64 s = some b) :
    coreJ r (.lit "i64.const" [s]) = .ok (tyObj "i64" [("value", .str (signedStr b))]) := by
  simp [coreJ, oneArg, lit, h, bind, Except.bind, pure, Except.pure]

theorem coreJ_f32 {s : String} {b : BitVec 32} (h : floatLitFast? .f32 s = some b) :
    coreJ false (.lit "f32.const" [s]) =
      .ok (tyObj "f32" [("value", .str (toString b.toNat))]) := by
  simp [coreJ, oneArg, floatJ, lit, h, bind, Except.bind, pure, Except.pure]
  rfl

theorem coreJ_f64 {s : String} {b : BitVec 64} (h : floatLitFast? .f64 s = some b) :
    coreJ false (.lit "f64.const" [s]) =
      .ok (tyObj "f64" [("value", .str (toString b.toNat))]) := by
  simp [coreJ, oneArg, floatJ, lit, h, bind, Except.bind, pure, Except.pure]
  rfl

/-- The fast compact printer is `serde_json::to_string`'s specification `Json.compact`. -/
theorem Json.compactFast_eq (j : Json) : j.compactFast = j.compact := by
  simp [Json.compactFast, Json.compactInto_eq']

/-- The fast pretty printer is the specification `Json.pretty`. -/
theorem Json.prettyFast_eq (j : Json) : j.prettyFast = j.pretty := by
  simp [Json.prettyFast, Json.pretty, Json.prettyInto_eq']

end Silmaril.Wasm.Tools.Wast
