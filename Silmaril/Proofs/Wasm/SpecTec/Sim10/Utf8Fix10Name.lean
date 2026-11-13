module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Env
public import Silmaril.Wasm.SpecTec.Sim10.Round7Host.Thms

/-!
# The 1.0 `$utf8` erratum: export names are `name`s

In `utf8Env10T B` (the fixed script `fixedU10`):

* `applies_utf8_10U`: `$utf8` of a string's characters is its UTF-8 encoding;
* `evalExp_namePrem10U`: `name`'s premise `|$utf8(char*)| < 2 ^ 32` holds of every string with
  fewer than `2 ^ 32` UTF-8 bytes;
* **`hasTyp_name10U`**, `typedV_name10U`: every such string is a `name`, in every term-only
  scope; `typedV_name_single10U`: every one-character string is;
* **`typedV_name10U_not_10T`**: the contrast with the script without the erratum. For a
  non-empty string within the bound, the name is typed in `utf8Env10T B` and not in
  `simEnv10T B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Fix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.ExecNumeric (applies_iff_callDef Applies)
open Silmaril.SpecTec.Equiv.RuntimeBridge (charToValue nameToValue)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)
open Silmaril.Wasm.SpecTec.Sim.Round7 (utf8Params utf8Res charPrem nameScope)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

set_option maxRecDepth 100000

variable (B : Builtins)

/-- **In `utf8Env10T B`, `$utf8` of a string's characters is its UTF-8 encoding.** -/
theorem applies_utf8_10U (s : String) :
    Applies (utf8Env10T B) "utf8" [.val (.list (s.toList.map charToValue))]
      (.list (s.toUTF8.data.toList.map fun b => pctV b.toNat)) :=
  Sim.Prims.applies_of_noClause ⟨_, _, findDef?_utf8Env10T B⟩
    ((call_utf8Env10T_utf8 B _).trans (Sim.Round7.utf8Call_string s))

set_option maxRecDepth 8000000 in
theorem findTyp_char10U : (utf8Env10T B).findTyp? "char" = some ([], [.instD [] []
    (.variantT [.mk "%" (.tupT [.mk "i" (.numT .natT)]) [] [.ifPr charPrem]])]) :=
  (findTyp?_utf8Env10T B "char").trans rfl

set_option maxRecDepth 8000000 in
theorem findTyp_name10U : (utf8Env10T B).findTyp? "name" = some ([], [.instD [] []
    (.variantT [.mk "%" (.tupT [.mk "char*" (.iterT (.varT "char" []) .list)]) []
      [.ifPr Sim.Round5.Pos.namePrem]])]) :=
  (findTyp?_utf8Env10T B "name").trans rfl

/-- **Every character is a `char`** of `utf8Env10T B`. -/
theorem hasTyp_char10U {ρ : VarEnv} (hρ : ValsOnly ρ) (c : Char) :
    HasTyp (utf8Env10T B) ρ (.varT "char" []) (charToValue c) := by
  have hl : localTyp? ρ "char" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  have hv : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := c.valid
  refine hasTyp_varT_case hl (findTyp_char10U B) evalArgs_nil matchArgs_nil
    ((hasTypCase_cons_hit_iff rfl).2 ⟨?_, Sim.IntNumeric.premsOk_if
      (Sim.Round7.evalExp_charPrem hv)⟩)
  exact hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    hasTyp_numT_iff.2 ⟨_, rfl, by simp [Num.subTyp, Num.toTyp]⟩, hasTypTup_nil_iff.2 rfl⟩⟩

/-- `|$utf8(char*)|` is the UTF-8 size, in `utf8Env10T B`. -/
theorem evalExp_namePremLhs10U (s : String) :
    EvalExp (utf8Env10T B) (nameScope s) Sim.Round5.Pos.namePremLhs
      (.num (.natN s.utf8ByteSize)) := by
  have hi : EvalExp (utf8Env10T B) (nameScope s)
      (.iterE (.varE "char") Sim.Round5.Pos.charDom) (.list (s.toList.map charToValue)) :=
    Silmaril.SpecTec.Equiv.Execution.evalExp_iterPat (by decide) (by simp)
  have hc := evalExp_callE_iff.2 ((applies_iff_callDef (ρ := nameScope s) (args := [.expA
    (.iterE (.varE "char") Sim.Round5.Pos.charDom)]) rfl (evalArgs_cons hi evalArgs_nil)).1
      (applies_utf8_10U B s))
  have hlen := Sim.RefsGC.evalExp_len hc
  rwa [List.length_map, Sim.Round7.toUTF8_toList, ← Sim.Round7.utf8ByteSize_eq] at hlen

/-- **`name`'s premise holds** of a string with fewer than `2 ^ 32` UTF-8 bytes. -/
theorem evalExp_namePrem10U {s : String} (hs : s.utf8ByteSize < 2 ^ 32) :
    EvalExp (utf8Env10T B) (nameScope s) Sim.Round5.Pos.namePrem (.bool true) :=
  Sim.RefsGC.evalExp_ltNat (evalExp_namePremLhs10U B s) Sim.Round7.evalExp_pow32 hs

/-- **With the 1.0 erratum, a string within SpecTec's bound is a `name`**, in every term-only
scope. -/
theorem hasTyp_name10U {ρ : VarEnv} (hρ : ValsOnly ρ) {s : String}
    (hs : s.utf8ByteSize < 2 ^ 32) :
    HasTyp (utf8Env10T B) ρ (.varT "name" []) (nameToValue s) := by
  have hl : localTyp? ρ "name" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  refine hasTyp_varT_case hl (findTyp_name10U B) evalArgs_nil matchArgs_nil
    ((hasTypCase_cons_hit_iff rfl).2 ⟨?_, Sim.IntNumeric.premsOk_if
      (evalExp_namePrem10U B hs)⟩)
  refine hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, ?_, hasTypTup_nil_iff.2 rfl⟩⟩
  refine hasTyp_iterT_list_iff.2 ⟨_, rfl, hasTypList_iff.2 fun w hw => ?_⟩
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hw
  exact hasTyp_char10U B ⟨rfl, rfl, rfl⟩ c

/-- `hasTyp_name10U`, as a `TypedV`. -/
theorem typedV_name10U {s : String} (hs : s.utf8ByteSize < 2 ^ 32) :
    TypedV (utf8Env10T B) (.varT "name" []) (Sim20.nameV s) := fun _ hρ => hasTyp_name10U B hρ hs

/-- **Every one-character string is a `name`** of `utf8Env10T B`. -/
theorem typedV_name_single10U (c : Char) :
    TypedV (utf8Env10T B) (.varT "name" []) (Sim20.nameV (String.singleton c)) := by
  refine typedV_name10U B ?_
  rw [Sim.Round7.utf8ByteSize_eq]
  have : (String.utf8EncodeChar c).length ≤ 4 := by
    rw [String.length_utf8EncodeChar]; exact c.utf8Size_le_four
  simp only [String.toList_singleton, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  omega

/-- **The erratum repairs the 1.0 `name`**: a non-empty string within the bound is a `name` of
`utf8Env10T B` and not of `simEnv10T B`. -/
theorem typedV_name10U_not_10T {s : String} (hs : s.utf8ByteSize < 2 ^ 32) (hne : s ≠ "") :
    TypedV (utf8Env10T B) (.varT "name" []) (Sim20.nameV s) ∧
      ¬ TypedV (simEnv10T B) (.varT "name" []) (Sim20.nameV s) :=
  ⟨typedV_name10U B hs, fun h =>
    Name10.not_hasTyp_nameV_ne10 (Name10.nameEnv10T B) hne (h VarEnv.empty ⟨rfl, rfl, rfl⟩)⟩

end Silmaril.Wasm.SpecTec.Sim10.Utf8Fix
