module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.TextErrata
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x

/-!
# #664 in the byte grammar institution: `Ttypeuse_` is empty before and after

#664 corrects the second premise of the two `Ttypeuse_/base` productions
(`6.2-text.types.spectec:164`, `:169`) from `st*[i] = SUB FINAL (FUNC …)` to
`st*[i] = SUB FINAL? tu* (FUNC …)`. Both productions carry, before it, the premise

```
-- if I.TYPEDEFS[x] = ?(_DEF (REC st*) i)
```

which is meant to *bind* `st*` and `i`. The IL evaluator checks an `IfPr`, it does not solve
it (`Sem/Eval.lean`, `premHolds`), and nothing in either production's symbol binds `i`
(`symFrames "i"`, decided by `rfl`). So evaluating the right-hand side reads an unbound `i`, the
first premise never holds, and neither production derives anything — pinned or patched, at any
argument (`ttypeuse_dead_pinned`, `ttypeuse_dead_text6x`). The pinned stream has no third
(`abbrev`) production. The corrected premise is never reached, so no sentence of the byte
grammar institution separates #664.

The same argument applies to the character semantics `Derives` of `Equiv/Text.lean`, which
uses the same premise evaluation; that is not proved here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts
open Silmaril.SpecTec.Equiv.Text (envPinned envCorrected)

/-- The shape of the first premise, `lhs = ?(_DEF r i)`. -/
def typedefPrem (lhs r : Exp) : Prem :=
  .ifPr (.cmpE .eqOp .boolT lhs (.optE (some (.caseE "_DEF" (.tupE [r, .varE "i"])))))

/-- Its right-hand side cannot be evaluated while `i` is unbound. -/
theorem not_evalExp_typedefRhs {env : Env} {ρ : VarEnv} {r : Exp} {v : Value}
    (hi : ρ.findVal? "i" = none) :
    ¬ EvalExp env ρ (.optE (some (.caseE "_DEF" (.tupE [r, .varE "i"])))) v := by
  intro h
  obtain ⟨w, hw, -⟩ := evalExp_optE_some_iff.mp h
  obtain ⟨u, hu, -⟩ := evalExp_caseE_iff.mp hw
  obtain ⟨vs, hvs, -⟩ := evalExp_tupE_iff.mp hu
  obtain ⟨a, as₁, -, has, -⟩ := evalExps_cons_iff.mp hvs
  obtain ⟨b, bs, hb, -, -⟩ := evalExps_cons_iff.mp has
  exact not_evalExp_varE_none hi hb

/-- A premise list starting with the `typedefPrem` does not hold while `i` is unbound. -/
theorem not_premsHold_typedef {env : Env} {ρ ρ' : VarEnv} {lhs r : Exp} {rest : List Prem}
    (hi : ρ.findVal? "i" = none) : ¬ PremsHold env ρ (typedefPrem lhs r :: rest) ρ' := by
  rintro ⟨n, h⟩
  match n, h with
  | 0, h => simp [premsHold] at h
  | 1, h => simp [premsHold, premHolds] at h
  | m + 2, h =>
      rw [premsHold, List.foldlM_cons, Res.bind_eq_ok] at h
      obtain ⟨ρ₁, h₁, -⟩ := h
      rw [typedefPrem, premHolds, Res.bind_eq_ok] at h₁
      obtain ⟨v, hv, -⟩ := h₁
      obtain ⟨v₁, v₂, -, h₂, -⟩ := evalExp_cmpE_iff.mp ⟨m, hv⟩
      exact not_evalExp_typedefRhs hi h₂

/-- Binding one expression parameter `x ≠ "i"` leaves `i` unbound. -/
theorem bindParams_expP_i {x : IL.Id} (hx : x ≠ "i") {t : Typ} {ws : List ArgV} {ρ₀ : VarEnv}
    (h : bindParams VarEnv.empty [.expP x t] ws = some ρ₀) : ρ₀.findVal? "i" = none := by
  match ws, h with
  | [.val w], h =>
      simp only [bindParams, Option.some.injEq] at h
      rw [← h, findVal?_bindVal_ne hx]
      rfl

/-- **A production whose first premise is `typedefPrem` and whose symbol binds no `i` is
dead**, in a grammar with one expression parameter other than `i`. -/
theorem not_prodDerives_typedef {env : Env} {ρ : VarEnv} {x : IL.Id} (hx : x ≠ "i") {t : Typ}
    {args : List IL.Arg} {q : List Param} {g : IL.Sym} {e lhs r : Exp} {rest : List Prem}
    (hg : symFrames "i" (substSym [] g) = true) {bs : Grammar.Bytes} {l : List Value} :
    ¬ ProdDerives env ρ [.expP x t] args (.prodD q g e (typedefPrem lhs r :: rest)) bs l := by
  rintro ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, -, hb, hs, hpr, -, -⟩
  rw [gramArgSubst_expP] at hs
  have h₀ : ρ₀.findVal? "i" = none := bindParams_expP_i hx hb
  have h₁ : ρ₁.findVal? "i" = none := (symDerives_frame _ hg hs).trans h₀
  exact not_premsHold_typedef h₁ hpr

/-- The shape of `Ttypeuse_`, pinned or patched: two productions, each starting its premises
with `typedefPrem`, and neither symbol binding `i`. -/
def TtypeuseShape (env : Env) : Prop :=
  ∃ (t : Typ) (q₁ : List Param) (g₁ : IL.Sym) (e₁ l₁ r₁ : Exp) (rest₁ : List Prem)
    (q₂ : List Param) (g₂ : IL.Sym) (e₂ l₂ r₂ : Exp) (rest₂ : List Prem),
    env.findGram? "Ttypeuse_" = some ([.expP "I" (.varT "I" [])], t,
      [.prodD q₁ g₁ e₁ (typedefPrem l₁ r₁ :: rest₁), .prodD q₂ g₂ e₂ (typedefPrem l₂ r₂ :: rest₂)]) ∧
    symFrames "i" (substSym [] g₁) = true ∧ symFrames "i" (substSym [] g₂) = true

/-- **`Ttypeuse_` derives nothing** in a script of that shape. -/
theorem ttypeuse_dead {env : Env} (hs : TtypeuseShape env) {args : List IL.Arg} {ρ ρ' : VarEnv}
    {bs : Grammar.Bytes} {l : List Value} :
    ¬ SymDerives env ρ (.varG "Ttypeuse_" args) bs l ρ' := by
  obtain ⟨t, q₁, g₁, e₁, l₁, r₁, rest₁, q₂, g₂, e₂, l₂, r₂, rest₂, hg, hf₁, hf₂⟩ := hs
  intro h
  obtain ⟨-, p, hp, hd⟩ := (symDerives_varG hg).mp h
  rcases List.mem_pair.mp hp with rfl | rfl
  · exact not_prodDerives_typedef (by decide) hf₁ hd
  · exact not_prodDerives_typedef (by decide) hf₂ hd

set_option maxRecDepth 100000 in
theorem ttypeuseShape_pinned : TtypeuseShape envPinned :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, by rfl, by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem ttypeuseShape_text6x : TtypeuseShape envText6x :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, by rfl, by decide, by decide⟩

/-- **#664 over bytes, pinned**: `Ttypeuse_` derives nothing. -/
theorem ttypeuse_dead_pinned {args : List IL.Arg} {ρ ρ' : VarEnv} {bs : Grammar.Bytes}
    {l : List Value} : ¬ SymDerives envPinned ρ (.varG "Ttypeuse_" args) bs l ρ' :=
  ttypeuse_dead ttypeuseShape_pinned

/-- **#664 over bytes, patched**: `Ttypeuse_` derives nothing. -/
theorem ttypeuse_dead_text6x {args : List IL.Arg} {ρ ρ' : VarEnv} {bs : Grammar.Bytes}
    {l : List Value} : ¬ SymDerives envText6x ρ (.varG "Ttypeuse_" args) bs l ρ' :=
  ttypeuse_dead ttypeuseShape_text6x

end Silmaril.Wasm.SpecTec.GrammarInst
