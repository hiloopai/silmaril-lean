module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkFT
public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Thms

/-!
# The 2.0 `$utf8` erratum: export names and module instances

SpecTec's `name` is `% char*` with the premise `|$utf8(char*)| < 2 ^ 32`. In the 2.0 script,
`$utf8` has five clauses: four on a one-character list `[ch]`, whose byte variables `b`, `b_1`, …
occur only in their `if` premises, and a last one, `$utf8(ch*) = $concat_(byte, $utf8([ch])*)`.
The evaluator does not solve premises for unbound variables, and round 3's executable check
(`EncodeCheck`) finds no evaluation of `$utf8` on a non-empty name. The empty name is a `name`
(`typedV_name_nil20`, by evaluation).

This file states the **erratum**, as round 7 does for the 3.0 script (`Round7.utf8Env`), and what
it gives:

* `utf8BaseEnv20`: `baseEnv20` with `$utf8` rebound to a declaration with the same parameters and
  result type (`findDef_utf8_base20`) and **no clauses**, as a `hint(builtin)` declaration is.
  Every type, relation and other definition is unchanged (`types20_utf8Env20`,
  `findDef?_utf8Env20_of_ne`, `findRel?_utf8Env20`).
* `utf8Env20 B`: that environment with the primitives `Round6.MemSimd.withUtf8 B`, which answer
  `$utf8` by the UTF-8 encoding of the characters (`applies_utf8_20`).
* **`hasTyp_name20U`**: every string with fewer than `2 ^ 32` UTF-8 bytes is a `name` in
  `utf8Env20 B`.
* **`typedV_moduleInst_utf8Env20`**: a module instance with bounded function types
  (`TypesSmall`) and export names (`ModNamesBnd20`) is a `moduleinst` in `utf8Env20 B`.

Not done here: the forward invariant (`Good20B`, read in `simEnv20` and `simEnv20T`) is not moved
to the erratum, and the failure of `$utf8` on a one-character name in `simEnv20 B` is not proved
(it is round 3's executable observation). See `docs/projects/spectec/README.md`, "fwd20".
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreBulk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.ExecNumeric (applies_iff_callDef Applies)
open Silmaril.SpecTec.Equiv.RuntimeBridge (charToValue nameToValue)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)
open Silmaril.Wasm.SpecTec.Sim.Round7 (utf8Params utf8Res charPrem nameScope)
open Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd (withUtf8 utf8Call)

set_option maxRecDepth 100000

variable {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## The erratum -/

/-- **The 2.0 erratum**: `$utf8` keeps its signature and loses its clauses. -/
noncomputable def utf8BaseEnv20 : Env := baseEnv20.bindDef "utf8" (utf8Params, utf8Res, [])

/-- **The 2.0 environment with the erratum**: `$utf8` answered by the UTF-8 encoding of its
characters, every other primitive by `B`. -/
noncomputable def utf8Env20 (B : Builtins) : Env := utf8BaseEnv20.withBuiltins (withUtf8 B)

/-- `$utf8` in the 2.0 script has the erratum's signature. -/
theorem findDef_utf8_base20 :
    ∃ rest, baseEnv20.findDef? "utf8" = some (utf8Params, utf8Res, rest) :=
  ⟨_, rfl⟩

theorem types20_utf8Env20 (B : Builtins) : Types20 (utf8Env20 B) := rfl

@[simp] theorem findDef?_utf8Env20 (B : Builtins) :
    (utf8Env20 B).findDef? "utf8" = some (utf8Params, utf8Res, []) := by
  simp [utf8Env20, utf8BaseEnv20]

theorem findDef?_utf8Env20_of_ne (B : Builtins) {x : IL.Id} (hx : x ≠ "utf8") :
    (utf8Env20 B).findDef? x = (E20 B).findDef? x := by
  simp [utf8Env20, utf8BaseEnv20, simEnv20, Ne.symm hx]

theorem findRel?_utf8Env20 (B : Builtins) (x : IL.Id) :
    (utf8Env20 B).findRel? x = (E20 B).findRel? x := by
  simp only [utf8Env20, utf8BaseEnv20, simEnv20, Env.findRel?, Env.bindDef, Env.withBuiltins]

theorem call_utf8Env20_of_ne (B : Builtins) {x : IL.Id} (hx : x ≠ "utf8") (ws : List ArgV) :
    (utf8Env20 B).builtins.call x ws = B.call x ws := by
  simp [utf8Env20, withUtf8, hx]

theorem call_utf8Env20_utf8 (B : Builtins) (ws : List ArgV) :
    (utf8Env20 B).builtins.call "utf8" ws = utf8Call ws := by
  simp [utf8Env20, withUtf8]

/-- **In `utf8Env20 B`, `$utf8` of a string's characters is its UTF-8 encoding.** -/
theorem applies_utf8_20 (B : Builtins) (s : String) :
    Applies (utf8Env20 B) "utf8" [.val (.list (s.toList.map charToValue))]
      (.list (s.toUTF8.data.toList.map fun b => pctV b.toNat)) :=
  Sim.Prims.applies_of_noClause ⟨_, _, findDef?_utf8Env20 B⟩
    ((call_utf8Env20_utf8 B _).trans (Sim.Round7.utf8Call_string s))

/-! ## `char` and `name` -/

theorem findTyp_char20 : (E20 B).findTyp? "char" = some ([], [.instD [] []
    (.variantT [.mk "%" (.tupT [.mk "i" (.numT .natT)]) [] [.ifPr charPrem]])]) := rfl

theorem findTyp_name20 : (E20 B).findTyp? "name" = some ([], [.instD [] []
    (.variantT [.mk "%" (.tupT [.mk "char*" (.iterT (.varT "char" []) .list)]) []
      [.ifPr Sim.Round5.Pos.namePrem]])]) := rfl

/-- **Every character is a `char`**, in every environment with the 2.0 types. -/
theorem hasTyp_charE {e : Env} (hE : Types20 e) {ρ : VarEnv} (hρ : ValsOnly ρ) (c : Char) :
    HasTyp e ρ (.varT "char" []) (charToValue c) := by
  have hl : localTyp? ρ "char" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  have hv : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := c.valid
  refine hasTyp_varT_case hl (hE.find (findTyp_char20 (B := noBuiltins))) evalArgs_nil
    matchArgs_nil
    ((hasTypCase_cons_hit_iff rfl).2 ⟨?_, Sim.IntNumeric.premsOk_if
      (Sim.Round7.evalExp_charPrem hv)⟩)
  exact hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    hasTyp_numT_iff.2 ⟨_, rfl, by simp [Num.subTyp, Num.toTyp]⟩, hasTypTup_nil_iff.2 rfl⟩⟩

/-- `|$utf8(char*)|` is the UTF-8 size, in `utf8Env20 B`. -/
theorem evalExp_namePremLhs20U (B : Builtins) (s : String) :
    EvalExp (utf8Env20 B) (nameScope s) Sim.Round5.Pos.namePremLhs
      (.num (.natN s.utf8ByteSize)) := by
  have hi : EvalExp (utf8Env20 B) (nameScope s)
      (.iterE (.varE "char") Sim.Round5.Pos.charDom) (.list (s.toList.map charToValue)) :=
    Silmaril.SpecTec.Equiv.Execution.evalExp_iterPat (by decide) (by simp)
  have hc := evalExp_callE_iff.2 ((applies_iff_callDef (ρ := nameScope s) (args := [.expA
    (.iterE (.varE "char") Sim.Round5.Pos.charDom)]) rfl (evalArgs_cons hi evalArgs_nil)).1
      (applies_utf8_20 B s))
  have hlen := Sim.RefsGC.evalExp_len hc
  rwa [List.length_map, Sim.Round7.toUTF8_toList, ← Sim.Round7.utf8ByteSize_eq] at hlen

/-- **`name`'s premise holds** of a string with fewer than `2 ^ 32` UTF-8 bytes, in
`utf8Env20 B`. -/
theorem evalExp_namePrem20U (B : Builtins) {s : String} (hs : s.utf8ByteSize < 2 ^ 32) :
    EvalExp (utf8Env20 B) (nameScope s) Sim.Round5.Pos.namePrem (.bool true) :=
  Sim.RefsGC.evalExp_ltNat (evalExp_namePremLhs20U B s) Sim.Round7.evalExp_pow32 hs

/-- **With the erratum, a string within SpecTec's bound is a `name`** of `utf8Env20 B`, in
every term-only scope. -/
theorem hasTyp_name20U (B : Builtins) {ρ : VarEnv} (hρ : ValsOnly ρ) {s : String}
    (hs : s.utf8ByteSize < 2 ^ 32) :
    HasTyp (utf8Env20 B) ρ (.varT "name" []) (nameToValue s) := by
  have hl : localTyp? ρ "name" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  refine hasTyp_varT_case hl ((types20_utf8Env20 B).find (findTyp_name20 (B := B))) evalArgs_nil
    matchArgs_nil ((hasTypCase_cons_hit_iff rfl).2 ⟨?_, Sim.IntNumeric.premsOk_if
      (evalExp_namePrem20U B hs)⟩)
  refine hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, ?_, hasTypTup_nil_iff.2 rfl⟩⟩
  refine hasTyp_iterT_list_iff.2 ⟨_, rfl, hasTypList_iff.2 fun w hw => ?_⟩
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hw
  exact hasTyp_charE (types20_utf8Env20 B) ⟨rfl, rfl, rfl⟩ c

theorem nameV_eq (s : String) : nameV s = nameToValue s := rfl

/-- `hasTyp_name20U`, as a `TypedV`. -/
theorem typedV_name20U (B : Builtins) {s : String} (hs : s.utf8ByteSize < 2 ^ 32) :
    TypedV (utf8Env20 B) (.varT "name" []) (nameV s) := fun _ hρ => hasTyp_name20U B hρ hs

/-! ## Module instances -/

/-- Every export name of a module instance has fewer than `2 ^ 32` UTF-8 bytes. -/
def ModNamesBnd20 (m : ModuleInst) : Prop := ∀ x ∈ m.exports, x.name.utf8ByteSize < 2 ^ 32

/-- **With the erratum, a module instance with bounded function types and export names is a
`moduleinst`.** -/
theorem typedV_moduleInst_utf8Env20 (B : Builtins) {m : ModuleInst} (ht : TypesSmall m)
    (hb : ModNamesBnd20 m) : TypedV (utf8Env20 B) (.varT "moduleinst" []) (moduleInstV m) :=
  typedV_moduleInstE (types20_utf8Env20 B) ht fun x hx => typedV_name20U B (hb x hx)

/-- **The erratum at a one-character name**: a `name` of `utf8Env20 B`. -/
theorem typedV_name_single20U (B : Builtins) (c : Char) :
    TypedV (utf8Env20 B) (.varT "name" []) (nameV (String.singleton c)) := by
  refine typedV_name20U B ?_
  rw [Sim.Round7.utf8ByteSize_eq]
  have : (String.utf8EncodeChar c).length ≤ 4 := by
    rw [String.length_utf8EncodeChar]; exact c.utf8Size_le_four
  simp only [String.toList_singleton, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  omega

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
