module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Dead
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Text

/-!
# The remaining text-format errata in the byte grammar institution

`Separate.lean` separates the pinned and the text-patched wasm-3.0 grammar theories at #662 and
#663. This module takes the other five patched issues of `#677`, one at a time,
in the byte semantics (`gramRelSup`, the least model of `scriptAxioms`):

* **#661, `Tstringchar`: separated.** The patched theory entails
  `Tstringchar ⊢ \u{E000} ↦ %(57344)` and the pinned one does not (`tstringchar_E000_*`). The
  escape production reads only ASCII, so the byte semantics reaches it; the other productions
  are `Tchar` (empty over bytes) or two-byte escapes.
* **#665, `Tblockcomment`/`Tblockchar`: not separable.** Both targets denote nothing over bytes,
  before and after the patch (`tblockcomment_*_dead`, `tblockchar_*_dead`): `Tblockcomment`'s
  body is an attribute over a sequence of five or six values (arity), and `Tblockchar` either
  reaches `Tchar` or `Tblockcomment`, or is dead by arity. The separation lives in the character
  semantics `Derives` of `Equiv/Text.lean` (`not_derives_blockcomment_semis_wasm30`,
  `derives_blockcomment_semis_text6x`), which is not the grammar institution.
* **#692, `Texporttabledots_`: not separable.** Every production, before and after the patch,
  is dead by arity (`texporttabledots_*_dead`).
* **#694, `Treserved`: not separable.** See `TextReserved.lean`.
* **#664, `Ttypeuse_`: not separable.** See `TextTypeuse.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts
open Silmaril.SpecTec.Equiv.Text (envPinned envCorrected tcharProds tblockcommentProds
  tblockcommentProdsC tblockcharProds tblockcharProdsC shortProd shortProdC neTwo implicitId
  unitResult gramRelSup_tchar_wasm30_eq_bot gramRelSup_tchar_text6x_eq_bot)

/-! ## The two environments -/

/-- The pinned wasm-3.0 environment of `Equiv/Text.lean` is the `Scripts` one. -/
theorem envOriginal_eq_pinned : Wasm30.envOriginal = envPinned := by
  show envOfScript Wasm30.original = envOfScript Specs.wasm30
  rw [wasm30_original_eq]

/-- A nonterminal that derives nothing, read as non-entailment. -/
theorem not_entails_of_dead {env : Env} {x : IL.Id} {args : List IL.Arg}
    (h : ∀ {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value},
      ¬ SymDerives env ρ (.varG x args) bs l ρ')
    (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    ¬ Entails (scriptAxioms env) (derivesNT x args ρ bs v) := fun he => by
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp ((gramRelSup_varG_iff_entails ..).mpr he)
  exact h hd

/-- `Tchar` derives nothing over bytes, as a statement about `SymDerives`. -/
theorem not_symDerives_tchar {env : Env}
    (hb : ∀ ρ, gramRelSup env ρ (.varG "Tchar" []) = ⊥) {ρ ρ' : VarEnv} {bs : Grammar.Bytes}
    {l : List Value} : ¬ SymDerives env ρ (.varG "Tchar" []) bs l ρ' := by
  intro h
  obtain ⟨hl, -⟩ := symDerives_varG_elim h
  match l, hl, h with
  | [v], _, h =>
      have hg : gramRelSup env ρ (.varG "Tchar" []) bs v := gramRelSup_iff.mpr ⟨ρ', h⟩
      rw [hb ρ] at hg
      exact hg

/-- `Tchar` is empty over bytes in the pinned script. -/
theorem tchar_bot_pinned (ρ : VarEnv) : gramRelSup envPinned ρ (.varG "Tchar" []) = ⊥ :=
  gramRelSup_tchar_wasm30_eq_bot ρ

/-- `Tchar` is empty over bytes in the text-patched script. -/
theorem tchar_bot_text6x (ρ : VarEnv) : gramRelSup envText6x ρ (.varG "Tchar" []) = ⊥ :=
  gramRelSup_tchar_text6x_eq_bot ρ

/-! ## #665: `Tblockcomment` and `Tblockchar` are empty over bytes, before and after -/

/-- A grammar without parameters substitutes nothing. -/
theorem gramArgSubst_nil (args : List IL.Arg) : gramArgSubst [] args = [] := by
  cases args <;> rfl

/-- **`Tblockcomment` is dead by arity**, pinned or patched: its one production is an
attribute over a sequence of five (pinned) or six (patched) values. -/
theorem tblockcomment_dead {env : Env} {prods : List IL.Prod}
    (hg : env.findGram? "Tblockcomment" = some ([], .tupT [], prods))
    (hp : prods = tblockcommentProds ∨ prods = tblockcommentProdsC) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    ¬ SymDerives env ρ (.varG "Tblockcomment" []) bs l ρ' := by
  have hd : prods.all (deadByArity []) = true := by rcases hp with rfl | rfl <;> decide
  exact not_symDerives_of_deadByArity hg hd (gramArgSubst_nil [])

/-- A production `x:y` whose inner symbol `y` derives nothing is dead. -/
theorem not_prodDerives_attr_of_dead {env : Env} {ρ : VarEnv} {q : List Param} {e ev : Exp}
    {g : IL.Sym} {prems : List Prem}
    (hg : ∀ {σ σ' : VarEnv} {bs : Grammar.Bytes} {l : List Value},
      ¬ SymDerives env σ (substSym [] g) bs l σ') {bs : Grammar.Bytes} {l : List Value} :
    ¬ ProdDerives env ρ [] [] (.prodD q (.attrG e g) ev prems) bs l := by
  rintro ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, -, -, hs, -, -, -⟩
  obtain ⟨w, σ, hd, -, -⟩ := symDerives_attrG.mp hs
  exact hg hd

/-- **`Tblockchar` is empty over bytes**, pinned or patched: its first production reads a
`Tchar`, the second and third are dead by arity, and the fourth is (pinned) a `Tblockcomment`
or (patched) dead by arity. -/
theorem tblockchar_dead {env : Env} {prods : List IL.Prod}
    (hb : ∀ ρ, gramRelSup env ρ (.varG "Tchar" []) = ⊥)
    (hc : ∀ {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value},
      ¬ SymDerives env ρ (.varG "Tblockcomment" []) bs l ρ')
    (hg : env.findGram? "Tblockchar" = some ([], .tupT [], prods))
    (hp : prods = tblockcharProds ∨ prods = tblockcharProdsC) {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    ¬ SymDerives env ρ (.varG "Tblockchar" []) bs l ρ' := by
  intro h
  obtain ⟨-, p, hmem, hpd⟩ := (symDerives_varG hg).mp h
  have hchar : ∀ {σ σ' : VarEnv} {bs : Grammar.Bytes} {l : List Value},
      ¬ SymDerives env σ (substSym [] (.attrG (.varE "c") (.varG "Tchar" []))) bs l σ' :=
    fun hd => by
      obtain ⟨w, σ₁, hd, -, -⟩ := symDerives_attrG.mp hd
      exact not_symDerives_tchar hb hd
  rcases hp with rfl | rfl <;>
    simp only [tblockcharProds, tblockcharProdsC, shortProdC, shortProd, List.mem_cons,
      List.not_mem_nil, or_false] at hmem <;>
    rcases hmem with rfl | rfl | rfl | rfl
  · exact not_prodDerives_attr_of_dead hchar hpd
  · exact not_prodDerives_attr_of_arity (by decide) hpd
  · exact not_prodDerives_attr_of_arity (by decide) hpd
  · exact not_prodDerives_attr_of_dead hc hpd
  · exact not_prodDerives_attr_of_dead hchar hpd
  · exact not_prodDerives_attr_of_arity (by decide) hpd
  · exact not_prodDerives_attr_of_arity (by decide) hpd
  · exact not_prodDerives_attr_of_arity (by decide) hpd

set_option maxRecDepth 100000 in
theorem findGram_tblockcomment_pinned :
    envPinned.findGram? "Tblockcomment" = some ([], .tupT [], tblockcommentProds) := by
  rfl

set_option maxRecDepth 100000 in
theorem findGram_tblockcomment_text6x :
    envText6x.findGram? "Tblockcomment" = some ([], .tupT [], tblockcommentProdsC) := by
  rfl

set_option maxRecDepth 100000 in
theorem findGram_tblockchar_pinned :
    envPinned.findGram? "Tblockchar" = some ([], .tupT [], tblockcharProds) := by
  rfl

set_option maxRecDepth 100000 in
theorem findGram_tblockchar_text6x :
    envText6x.findGram? "Tblockchar" = some ([], .tupT [], tblockcharProdsC) := by
  rfl

/-- **#665 over bytes, pinned**: neither target derives anything. -/
theorem blockcomment_dead_pinned {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    ¬ SymDerives envPinned ρ (.varG "Tblockcomment" []) bs l ρ' ∧
      ¬ SymDerives envPinned ρ (.varG "Tblockchar" []) bs l ρ' :=
  ⟨tblockcomment_dead findGram_tblockcomment_pinned (.inl rfl),
    tblockchar_dead tchar_bot_pinned (tblockcomment_dead findGram_tblockcomment_pinned (.inl rfl))
      findGram_tblockchar_pinned (.inl rfl)⟩

/-- **#665 over bytes, patched**: neither target derives anything. -/
theorem blockcomment_dead_text6x {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {l : List Value} :
    ¬ SymDerives envText6x ρ (.varG "Tblockcomment" []) bs l ρ' ∧
      ¬ SymDerives envText6x ρ (.varG "Tblockchar" []) bs l ρ' :=
  ⟨tblockcomment_dead findGram_tblockcomment_text6x (.inr rfl),
    tblockchar_dead tchar_bot_text6x
      (tblockcomment_dead findGram_tblockcomment_text6x (.inr rfl))
      findGram_tblockchar_text6x (.inr rfl)⟩

/-! ## #692: `Texporttabledots_` is dead by arity, before and after -/

/-- The parameter list of `Texporttabledots_`. -/
def iParams : List Param := [.expP "I" (.varT "I" [])]

set_option maxRecDepth 100000 in
/-- The pinned `Texporttabledots_`: every production is dead by arity. -/
theorem texporttabledots_shape_pinned : ∃ t prods,
    envPinned.findGram? "Texporttabledots_" = some (iParams, t, prods) ∧
      prods.all (deadByArity []) = true :=
  ⟨_, _, rfl, by decide⟩

set_option maxRecDepth 100000 in
/-- The patched `Texporttabledots_`: every production, including the two #692 adds, is dead by
arity. -/
theorem texporttabledots_shape_text6x : ∃ t prods,
    envText6x.findGram? "Texporttabledots_" = some (iParams, t, prods) ∧
      prods.all (deadByArity []) = true :=
  ⟨_, _, rfl, by decide⟩

/-- **#692 over bytes**: `Texporttabledots_` derives nothing, pinned or patched, at any
argument. -/
theorem texporttabledots_dead {args : List IL.Arg} {ρ ρ' : VarEnv} {bs : Grammar.Bytes}
    {l : List Value} :
    ¬ SymDerives envPinned ρ (.varG "Texporttabledots_" args) bs l ρ' ∧
      ¬ SymDerives envText6x ρ (.varG "Texporttabledots_" args) bs l ρ' := by
  obtain ⟨t, prods, hg, hd⟩ := texporttabledots_shape_pinned
  obtain ⟨t', prods', hg', hd'⟩ := texporttabledots_shape_text6x
  exact ⟨not_symDerives_of_deadByArity hg hd (gramArgSubst_expP "I" _ args),
    not_symDerives_of_deadByArity hg' hd' (gramArgSubst_expP "I" _ args)⟩

end Silmaril.Wasm.SpecTec.GrammarInst
