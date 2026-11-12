module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Utf8.Env

/-!
# Round 7: with the erratum, export names are `name`s

Round 5 showed that no one-character string is a `name` in any `simEnv B`
(`Round5.Pos.not_hasTyp_name_single`), because `$utf8([ch])` never returns. Under the erratum the
premise `|$utf8(char*)| < 2^32` of `name` is evaluated by the primitive, so:

* `hasTyp_char`: every Lean character is a SpecTec `char`, since its code point is a Unicode
  scalar value;
* `evalExp_namePrem`: `name`'s premise holds of a string with fewer than `2 ^ 32` UTF-8 bytes;
* `hasTyp_name`: **such a string is a `name` in `utf8Env B`**, for every `B` and term-only scope;
* `name_erratum`: the contrast at a one-character string. It is not a `name` in `simEnv B`, and it
  is one in `utf8Env B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.SpecTec.Equiv.ExecNumeric (applies_iff_callDef)
open Silmaril.SpecTec.Equiv.RuntimeBridge (charToValue nameToValue)
open Silmaril.SpecTec.Equiv.Execution (pctV)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## `char` -/

/-- The premise of `char`: a Unicode scalar value. -/
def charPrem : Exp :=
  .binE .orOp .boolT
    (.binE .andOp .boolT (.cmpE .geOp (.numT .natT) (.varE "i") (.numE (.natN 0)))
      (.cmpE .leOp (.numT .natT) (.varE "i") (.numE (.natN 55295))))
    (.binE .andOp .boolT (.cmpE .geOp (.numT .natT) (.varE "i") (.numE (.natN 57344)))
      (.cmpE .leOp (.numT .natT) (.varE "i") (.numE (.natN 1114111))))

set_option maxRecDepth 100000 in
theorem findTyp_char (B : Builtins) : (utf8Env B).findTyp? "char" = some ([], [.instD [] []
    (.variantT [.mk "%" (.tupT [.mk "i" (.numT .natT)]) [] [.ifPr charPrem]])]) := by
  rw [findTyp?_utf8Env]; rfl

/-- `p ∨ q` on booleans, when `p` holds. -/
theorem evalExp_or_left {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {t : OpTyp}
    (h₁ : EvalExp env ρ e₁ (.bool true)) : EvalExp env ρ (.binE .orOp t e₁ e₂) (.bool true) :=
  evalExp_binE_iff.2 ⟨_, h₁, .inl (by simp [boolShort])⟩

/-- `p ∨ q` on booleans, when `p` fails and `q` holds. -/
theorem evalExp_or_right {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {t : OpTyp}
    (h₁ : EvalExp env ρ e₁ (.bool false)) (h₂ : EvalExp env ρ e₂ (.bool true)) :
    EvalExp env ρ (.binE .orOp t e₁ e₂) (.bool true) :=
  evalExp_binE_iff.2 ⟨_, h₁, .inr ⟨by simp [boolShort], _, h₂, by simp [binValues, boolBin]⟩⟩

/-- A comparison of naturals with a literal, in a scope binding `i`. -/
theorem evalExp_cmpI {env : Env} (op : CmpOp) (n k : Nat) (c : Bool)
    (hc : Num.cmp op (.natN n) (.natN k) = some c) :
    EvalExp env (VarEnv.empty.bindVal "i" (.num (.natN n)))
      (.cmpE op (.numT .natT) (.varE "i") (.numE (.natN k))) (.bool c) :=
  RefsGC.evalExp_cmpNat (Sim.evalExp_var (by simp)) (evalExp_numE_iff.2 rfl) hc

/-- The premise of `char` holds of a Unicode scalar value. -/
theorem evalExp_charPrem {env : Env} {n : Nat} (hn : n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000)) :
    EvalExp env (VarEnv.empty.bindVal "i" (.num (.natN n))) charPrem (.bool true) := by
  have h0 := evalExp_cmpI (env := env) .geOp n 0 true (by simp [Num.cmp])
  rcases hn with hn | hn
  · exact evalExp_or_left (IntNumeric.evalExp_and h0
      (evalExp_cmpI .leOp n 55295 true (by simp [Num.cmp]; omega)))
  · refine evalExp_or_right ?_ (IntNumeric.evalExp_and
      (evalExp_cmpI .geOp n 57344 true (by simp [Num.cmp]; omega))
      (evalExp_cmpI .leOp n 1114111 true (by simp [Num.cmp]; omega)))
    exact IntNumeric.evalExp_and h0
      (evalExp_cmpI .leOp n 55295 false (by simp [Num.cmp]; omega))

/-- **Every character is a `char`**, in `utf8Env B` and every term-only scope. -/
theorem hasTyp_char (B : Builtins) {ρ : VarEnv} (hρ : ValsOnly ρ) (c : Char) :
    HasTyp (utf8Env B) ρ (.varT "char" []) (charToValue c) := by
  have hl : localTyp? ρ "char" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  have hv : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := c.valid
  refine hasTyp_varT_case hl (findTyp_char B) evalArgs_nil matchArgs_nil
    ((hasTypCase_cons_hit_iff rfl).2 ⟨?_, IntNumeric.premsOk_if (evalExp_charPrem hv)⟩)
  exact hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl,
    hasTyp_numT_iff.2 ⟨_, rfl, by simp [Num.subTyp, Num.toTyp]⟩, hasTypTup_nil_iff.2 rfl⟩⟩

/-! ## `name` -/

/-- `2 ^ 32`, as `name`'s premise writes it. -/
theorem evalExp_pow32 {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.numE (.natN 32)))
      (.num (.natN (2 ^ 32))) :=
  evalExp_binE_iff.2 ⟨_, evalExp_numE_iff.2 rfl,
    .inr ⟨by simp [boolShort], _, evalExp_numE_iff.2 rfl, by rfl⟩⟩

/-- The scope `name`'s premise is read in. -/
abbrev nameScope (s : String) : VarEnv :=
  VarEnv.empty.bindVal "char*" (.list (s.toList.map charToValue))

/-- `|$utf8(char*)|` is the UTF-8 size, in `utf8Env B`. -/
theorem evalExp_namePremLhs (B : Builtins) (s : String) :
    EvalExp (utf8Env B) (nameScope s) Round5.Pos.namePremLhs (.num (.natN s.utf8ByteSize)) := by
  have hi : EvalExp (utf8Env B) (nameScope s) (.iterE (.varE "char") Round5.Pos.charDom)
      (.list (s.toList.map charToValue)) :=
    Silmaril.SpecTec.Equiv.Execution.evalExp_iterPat (by decide) (by simp)
  have hc := evalExp_callE_iff.2 ((applies_iff_callDef (ρ := nameScope s) (args := [.expA (.iterE
    (.varE "char") Round5.Pos.charDom)]) rfl (evalArgs_cons hi evalArgs_nil)).1 (applies_utf8 B s))
  have hlen := RefsGC.evalExp_len hc
  rwa [List.length_map, toUTF8_toList, ← utf8ByteSize_eq] at hlen

/-- **`name`'s premise holds** of a string with fewer than `2 ^ 32` UTF-8 bytes, in
`utf8Env B`. -/
theorem evalExp_namePrem (B : Builtins) {s : String} (hs : s.utf8ByteSize < 2 ^ 32) :
    EvalExp (utf8Env B) (nameScope s) Round5.Pos.namePrem (.bool true) :=
  RefsGC.evalExp_ltNat (evalExp_namePremLhs B s) evalExp_pow32 hs

theorem findTyp_name (B : Builtins) : (utf8Env B).findTyp? "name" = some ([], [.instD [] []
    (.variantT [.mk "%" (.tupT [.mk "char*" (.iterT (.varT "char" []) .list)]) []
      [.ifPr Round5.Pos.namePrem]])]) := by
  rw [findTyp?_utf8Env]; exact Round5.Pos.findTyp_name B

/-- **With the erratum, a string within SpecTec's bound is a `name`**, in every term-only
scope. -/
theorem hasTyp_name (B : Builtins) {ρ : VarEnv} (hρ : ValsOnly ρ) {s : String}
    (hs : s.utf8ByteSize < 2 ^ 32) :
    HasTyp (utf8Env B) ρ (.varT "name" []) (nameToValue s) := by
  have hl : localTyp? ρ "name" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  refine hasTyp_varT_case hl (findTyp_name B) evalArgs_nil matchArgs_nil
    ((hasTypCase_cons_hit_iff rfl).2 ⟨?_, IntNumeric.premsOk_if (evalExp_namePrem B hs)⟩)
  refine hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, ?_, hasTypTup_nil_iff.2 rfl⟩⟩
  refine hasTyp_iterT_list_iff.2 ⟨_, rfl, hasTypList_iff.2 fun w hw => ?_⟩
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hw
  exact hasTyp_char B ⟨rfl, rfl, rfl⟩ c

/-- **The erratum at a one-character name**: not a `name` in `simEnv B`, a `name` in
`utf8Env B`. -/
theorem name_erratum (B : Builtins) (c : Char) :
    ¬ HasTyp (simEnv B) VarEnv.empty (.varT "name" []) (nameToValue (String.singleton c)) ∧
      HasTyp (utf8Env B) VarEnv.empty (.varT "name" []) (nameToValue (String.singleton c)) := by
  have hs : (String.singleton c).utf8ByteSize < 2 ^ 32 := by
    rw [utf8ByteSize_eq]
    have : (String.utf8EncodeChar c).length ≤ 4 := by
      rw [String.length_utf8EncodeChar]; exact c.utf8Size_le_four
    simp only [String.toList_singleton, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    omega
  refine ⟨fun h => ?_, hasTyp_name B ⟨rfl, rfl, rfl⟩ hs⟩
  exact Round5.Pos.not_hasTyp_name_single B ⟨rfl, rfl, rfl⟩ (charToValue c)
    (by simpa [nameToValue] using h)

end Silmaril.Wasm.SpecTec.Sim.Round7
