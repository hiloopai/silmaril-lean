module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.Thms

/-!
# Round 7: what the `$utf8` erratum changes, and what it keeps

* `findDef_utf8_base`: in `baseEnv`, `$utf8` has the parameters `utf8Params`, the result type
  `utf8Res` and the looping first clause `Round5.Pos.utf8Clause1`. The erratum keeps the
  signature and drops the clauses.
* `findDef?_utf8Env`, `findDef?_utf8Env_of_ne`, `findTyp?_utf8Env`, `findRel?_utf8Env`,
  `findGram?_utf8Env`, `call_utf8Env_of_ne`: `utf8Env B` agrees with `simEnv B` on every type,
  relation and grammar, on every definition but `$utf8`, and on every primitive but `$utf8`.
* `utf8Call_chars`, `utf8Call_string`: the primitive answers a list of characters with their
  UTF-8 bytes, `String.toUTF8` for the characters of a string.
* `applies_utf8`: in `utf8Env B`, `$utf8` of a string's characters is its UTF-8 bytes.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.RuntimeBridge (charToValue nameToValue)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Round6.MemSimd (withUtf8 utf8Call utf8CharV charCode?)

variable {B : Builtins}

/-! ## The erratum replaces the clauses of `$utf8`, and nothing else -/

set_option maxRecDepth 100000 in
/-- `$utf8` in the fixed script: the erratum keeps its signature. -/
theorem findDef_utf8_base :
    ∃ rest, baseEnv.findDef? "utf8" = some (utf8Params, utf8Res, Round5.Pos.utf8Clause1 :: rest) :=
  ⟨_, rfl⟩

@[simp] theorem findDef?_utf8Env (B : Builtins) :
    (utf8Env B).findDef? "utf8" = some (utf8Params, utf8Res, []) := by
  simp [utf8Env, utf8BaseEnv]

theorem findDef?_utf8Env_of_ne (B : Builtins) {x : IL.Id} (hx : x ≠ "utf8") :
    (utf8Env B).findDef? x = (simEnv B).findDef? x := by
  simp [utf8Env, utf8BaseEnv, simEnv, Ne.symm hx]

@[simp] theorem findTyp?_utf8Env (B : Builtins) (x : IL.Id) :
    (utf8Env B).findTyp? x = (simEnv B).findTyp? x := by
  simp only [utf8Env, utf8BaseEnv, simEnv, Env.findTyp?, Env.bindDef, Env.withBuiltins]

@[simp] theorem findRel?_utf8Env (B : Builtins) (x : IL.Id) :
    (utf8Env B).findRel? x = (simEnv B).findRel? x := by
  simp only [utf8Env, utf8BaseEnv, simEnv, Env.findRel?, Env.bindDef, Env.withBuiltins]

@[simp] theorem findGram?_utf8Env (B : Builtins) (x : IL.Id) :
    (utf8Env B).findGram? x = (simEnv B).findGram? x := by
  simp only [utf8Env, utf8BaseEnv, simEnv, Env.findGram?, Env.bindDef, Env.withBuiltins]

theorem call_utf8Env_of_ne (B : Builtins) {x : IL.Id} (hx : x ≠ "utf8") (ws : List ArgV) :
    (utf8Env B).builtins.call x ws = B.call x ws := by
  simp [utf8Env, withUtf8, hx]

theorem call_utf8Env_utf8 (B : Builtins) (ws : List ArgV) :
    (utf8Env B).builtins.call "utf8" ws = utf8Call ws := by
  simp [utf8Env, withUtf8]

/-! ## The primitive is UTF-8 encoding -/

theorem mapM_charCode (cs : List Char) :
    (cs.map charToValue).mapM charCode? = some (cs.map Char.toNat) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [List.mapM_cons, ih, charToValue, charCode?]

/-- The bytes of a character, as values. -/
def charBytesV (c : Char) : List Value := (String.utf8EncodeChar c).map fun b => pctV b.toNat

/-- **The primitive on a list of characters**: their UTF-8 bytes. -/
theorem utf8Call_chars (cs : List Char) :
    utf8Call [.val (.list (cs.map charToValue))] = some (.list (cs.flatMap charBytesV)) := by
  simp only [utf8Call, mapM_charCode, Option.map_some, Option.some.injEq, Value.list.injEq]
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih, utf8CharV, charBytesV]

theorem flatMap_charBytesV (cs : List Char) :
    cs.flatMap charBytesV = (cs.flatMap String.utf8EncodeChar).map fun b => pctV b.toNat := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih, charBytesV]

/-- The bytes of `String.toUTF8 s` are the UTF-8 encodings of its characters. -/
theorem toUTF8_toList (s : String) :
    s.toUTF8.data.toList = s.toList.flatMap String.utf8EncodeChar := by
  have h := String.utf8Encode_toList (b := s)
  simp only [List.utf8Encode_eq_toByteArray] at h
  rw [String.toUTF8, ← h]
  simp

theorem utf8ByteSize_eq (s : String) :
    s.utf8ByteSize = (s.toList.flatMap String.utf8EncodeChar).length := by
  have h := String.utf8Encode_toList (b := s)
  simp only [List.utf8Encode_eq_toByteArray] at h
  simp [String.utf8ByteSize, ← h]

/-- **The primitive is `String.toUTF8`** on the characters of a string. -/
theorem utf8Call_string (s : String) :
    utf8Call [.val (.list (s.toList.map charToValue))] =
      some (.list (s.toUTF8.data.toList.map fun b => pctV b.toNat)) := by
  rw [utf8Call_chars, flatMap_charBytesV, toUTF8_toList]

/-- **In `utf8Env B`, `$utf8` of a string's characters is its UTF-8 encoding.** -/
theorem applies_utf8 (B : Builtins) (s : String) :
    Applies (utf8Env B) "utf8" [.val (.list (s.toList.map charToValue))]
      (.list (s.toUTF8.data.toList.map fun b => pctV b.toNat)) :=
  Prims.applies_of_noClause ⟨_, _, findDef?_utf8Env B⟩
    ((call_utf8Env_utf8 B _).trans (utf8Call_string s))

end Silmaril.Wasm.SpecTec.Sim.Round7
