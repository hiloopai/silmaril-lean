module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8SwapGood

/-!
# Typing the export lists that the involution exchanges

The leaf `Task.swapStep20` asks the involution to keep `exportinst*` typing in
`utf8Env20T (storeB P)`. The involution `swapS S` exchanges two kinds of export lists:

* re-encodings, whose names are all empty: `typedV_expV_rep20`, `typedV_expV_repU20T` type them in
  `simEnv20 B` and in `utf8Env20T B`;
* the export lists of the module instances of a `Good20BU` configuration. Those are typed in
  `utf8Env20 B`. `name_bnd_of_typed20U` reads the bound `|$utf8(s)| < 2 ^ 32` off a typed name,
  and `hasTyp_name20UT` types every such name in `utf8Env20T B`, so `hasTyp_expV_20T` types the
  list there.

`utf8Env20T B` finds the same type declarations as `simEnv20 B` away from `instr` and
`admininstr` (`findTypU_off`), which is all these types reach.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Swap

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
open Silmaril.Wasm.SpecTec.Sim.Round7 (charPrem nameScope)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (utf8Env20T)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (utf8Env20 findTyp_name20 findTyp_char20
  findTyp_exportinst20 findTyp_externaddr20)

set_option maxRecDepth 100000

variable {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## Type declarations of `utf8Env20T` -/

/-- **Off `instr` and `admininstr`, `utf8Env20T` finds what `simEnv20` finds.** -/
theorem findTypU_off (y : IL.Id) (ha : y ≠ "admininstr") (hi : y ≠ "instr") :
    (utf8Env20T B).findTyp? y = (E20 B).findTyp? y :=
  (Utf8Mono.findTyp?_utf8Env20T B y).trans (StoreFn.findTypT_off y ha hi)

/-- A declaration of `simEnv20 B'`, found in `utf8Env20T B`. -/
theorem findTypU {B' : Builtins} {y : IL.Id} {r : Option TypDef} (ha : y ≠ "admininstr")
    (hi : y ≠ "instr") (h : (E20 B').findTyp? y = r) : (utf8Env20T B).findTyp? y = r :=
  (findTypU_off y ha hi).trans h

/-! ## `name` in `utf8Env20T` -/

/-- **Every character is a `char`** of `utf8Env20T B`. -/
theorem hasTyp_charU {ρ : VarEnv} (hρ : ValsOnly ρ) (c : Char) :
    HasTyp (utf8Env20T B) ρ (.varT "char" []) (charToValue c) := by
  have hl : localTyp? ρ "char" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  have hv : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := c.valid
  refine hasTyp_varT_case hl (findTypU (by decide) (by decide) (findTyp_char20 (B := B)))
    evalArgs_nil matchArgs_nil
    ((hasTypCase_cons_hit_iff rfl).2 ⟨?_, Sim.IntNumeric.premsOk_if
      (Sim.Round7.evalExp_charPrem hv)⟩)
  exact hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    hasTyp_numT_iff.2 ⟨_, rfl, by simp [Num.subTyp, Num.toTyp]⟩, hasTypTup_nil_iff.2 rfl⟩⟩

/-- In `utf8Env20T B`, `$utf8` of a string's characters is its UTF-8 encoding. -/
theorem applies_utf8_20T (s : String) :
    Applies (utf8Env20T B) "utf8" [.val (.list (s.toList.map charToValue))]
      (.list (s.toUTF8.data.toList.map fun b => pctV b.toNat)) :=
  Sim.Prims.applies_of_noClause ⟨_, _, Utf8Mono.findDef?_utf8Env20T B⟩
    ((Utf8Mono.call_utf8Env20T_utf8 B _).trans (Sim.Round7.utf8Call_string s))

/-- `|$utf8(char*)|` is the UTF-8 size, in `utf8Env20T B`. -/
theorem evalExp_namePremLhs20T (s : String) :
    EvalExp (utf8Env20T B) (nameScope s) Sim.Round5.Pos.namePremLhs
      (.num (.natN s.utf8ByteSize)) := by
  have hi : EvalExp (utf8Env20T B) (nameScope s)
      (.iterE (.varE "char") Sim.Round5.Pos.charDom) (.list (s.toList.map charToValue)) :=
    Silmaril.SpecTec.Equiv.Execution.evalExp_iterPat (by decide) (by simp)
  have hc := evalExp_callE_iff.2 ((applies_iff_callDef (ρ := nameScope s) (args := [.expA
    (.iterE (.varE "char") Sim.Round5.Pos.charDom)]) rfl (evalArgs_cons hi evalArgs_nil)).1
      (applies_utf8_20T s))
  have hlen := Sim.RefsGC.evalExp_len hc
  rwa [List.length_map, Sim.Round7.toUTF8_toList, ← Sim.Round7.utf8ByteSize_eq] at hlen

/-- **A string within SpecTec's bound is a `name`** of `utf8Env20T B`. -/
theorem hasTyp_name20UT {ρ : VarEnv} (hρ : ValsOnly ρ) {s : String}
    (hs : s.utf8ByteSize < 2 ^ 32) :
    HasTyp (utf8Env20T B) ρ (.varT "name" []) (nameToValue s) := by
  have hl : localTyp? ρ "name" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  refine hasTyp_varT_case hl (findTypU (by decide) (by decide) (findTyp_name20 (B := B)))
    evalArgs_nil matchArgs_nil ((hasTypCase_cons_hit_iff rfl).2 ⟨?_, Sim.IntNumeric.premsOk_if
      (Sim.RefsGC.evalExp_ltNat (evalExp_namePremLhs20T s) Sim.Round7.evalExp_pow32 hs)⟩)
  refine hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, ?_, hasTypTup_nil_iff.2 rfl⟩⟩
  refine hasTyp_iterT_list_iff.2 ⟨_, rfl, hasTypList_iff.2 fun w hw => ?_⟩
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hw
  exact hasTyp_charU ⟨rfl, rfl, rfl⟩ c

/-- The premise of `name` holds, read off a typed name of `utf8Env20 B`. -/
theorem namePrem_of_typed20U {s : String}
    (h : TypedV (utf8Env20 B) (.varT "name" []) (nameV s)) :
    EvalExp (utf8Env20 B) (nameScope s) Sim.Round5.Pos.namePrem (.bool true) := by
  have hl : localTyp? VarEnv.empty "name" [] = none := rfl
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 (h VarEnv.empty ⟨rfl, rfl, rfl⟩)
  rw [(StoreBulk.types20_utf8Env20 B).find (findTyp_name20 (B := B))] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
  · obtain rfl := Sim.IntNumeric.matchArgs_nil_scope hm
    obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 hd
    simp only [Sim20.nameV, Value.case.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact Sim.ConfigOk.evalExp_of_premsOk_if ((hasTypCase_cons_hit_iff rfl).1 hc).2
  · exact absurd hrest not_hasTypInsts_nil

/-- **The bound on a `name` of `utf8Env20 B`**: its UTF-8 encoding has fewer than `2 ^ 32`
bytes. -/
theorem name_bnd_of_typed20U {s : String}
    (h : TypedV (utf8Env20 B) (.varT "name" []) (nameV s)) : s.utf8ByteSize < 2 ^ 32 := by
  obtain ⟨v₁, v₂, h₁, h₂, hcmp⟩ := evalExp_cmpE_iff.1 (namePrem_of_typed20U h)
  have e₁ := EvalExp.unique h₁ (StoreBulk.evalExp_namePremLhs20U B s)
  have e₂ := EvalExp.unique h₂ (Sim.Round7.evalExp_pow32 (env := utf8Env20 B))
  subst e₁ e₂
  simp only [cmpValues, Res.ofOption] at hcmp
  revert hcmp
  simp [Num.cmp]

/-! ## Export lists -/

/-- An export, from its typed name and address. -/
theorem typedV_export_of {e : Env} (hx : e.findTyp? "exportinst" = (E20 B).findTyp? "exportinst")
    {x : ExportInst} (hn : TypedV e (.varT "name" []) (nameV x.name))
    (hd : TypedV e (.varT "externaddr" []) (externAddrV x.addr)) :
    TypedV e (.varT "exportinst" [])
      (.struct [("NAME", nameV x.name), ("ADDR", externAddrV x.addr)]) :=
  Whole.typedV_structG (hx.trans findTyp_exportinst20)
    (Whole.hasTypFields_consG hn (Whole.hasTypFields_oneG hd))

/-- An export list whose exports are typed. -/
theorem typedV_expV_of {e : Env} {l : List ExportInst}
    (h : ∀ x ∈ l, TypedV e (.varT "exportinst" [])
      (.struct [("NAME", nameV x.name), ("ADDR", externAddrV x.addr)])) :
    TypedV e exportsT (expV l) :=
  Sim.typedV_list_iff.2 fun u hu => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
    exact h x hx

end Silmaril.Wasm.SpecTec.Sim20.Utf8Swap
