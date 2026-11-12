module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Dead
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm20

/-!
# `Bmodule` of wasm-1.0 and wasm-2.0 is empty, before and after #687/#672

The 1.0 and 2.0 `Bmodule` productions (`A-binary.spectec:526-527`, `:923-924`) return
`MODULE type* import* func* …`, where `func*` is a production *quantifier*: no factor of the
body binds it, and the premise meant to define it is the iterated check
`-- (if func = FUNC typeidx local* expr)*` over the domains `expr*`, `func*`, `local**`,
`typeidx*`. `premIter` evaluates every domain of a `list` iteration first, and the body leaves
`func*` unbound (`symFrames "func*"`, decided by `rfl`), so that premise never holds and the
production derives nothing. In wasm-2.0 the iterated premise comes third, after an optional
iteration and an `if`, both of which keep the scope (`premHolds_keepsScope`).

This holds for the pinned and for the corrected scripts alike (`bmodule_dead_*`): the version
field #687 and #672 correct is never reached. Hence no sentence about `Bmodule` separates those
errata in the byte grammar institution, and the "positive derivation of a whole module" the
pass-3 notes asked for does not exist. `Equiv/BinaryModule.lean` records the same obstacle for
wasm-3.0's `Bmodule` without proving it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts

/-! ## Premises that keep the scope -/

/-- Premises the evaluator checks without binding: `if`, and `opt`/`list` iterations. -/
def keepsScope : Prem → Bool
  | .ifPr _ => true
  | .iterPr _ (.mk .opt _) => true
  | .iterPr _ (.mk .list _) => true
  | _ => false

/-- `premRounds` returns the scope it was given. -/
theorem premRounds_scope {n : Nat} {env : Env} {ρ ρ' : VarEnv} {pr : Prem}
    {xvs : List (IL.Id × Value)} {ido : Option IL.Id} {k : Nat}
    (h : premRounds n env ρ pr xvs ido k = .ok ρ') : ρ' = ρ := by
  match n, h with
  | 0, h => simp [premRounds] at h
  | m + 1, h =>
      simp only [premRounds, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨-, -, -, -, -, h⟩ := h
      exact (Except.ok.inj h).symm

/-- `premIter` of an `opt` iteration returns the scope it was given. -/
theorem premIter_opt_scope {n : Nat} {env : Env} {ρ ρ' : VarEnv} {pr : Prem} {ds : List Dom}
    (h : premIter n env ρ pr .opt ds = .ok ρ') : ρ' = ρ := by
  match n, h with
  | 0, h => simp [premIter] at h
  | m + 1, h =>
      simp only [premIter, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨xvs, -, -, os, -, h⟩ := h
      split at h
      · exact (Except.ok.inj h).symm
      · split at h
        · obtain ⟨-, -, h⟩ := Res.bind_eq_ok.mp h
          exact (Except.ok.inj h).symm
        · simp at h

/-- `premIter` of a `list` iteration returns the scope it was given. -/
theorem premIter_list_scope {n : Nat} {env : Env} {ρ ρ' : VarEnv} {pr : Prem} {ds : List Dom}
    (h : premIter n env ρ pr .list ds = .ok ρ') : ρ' = ρ := by
  match n, h with
  | 0, h => simp [premIter] at h
  | m + 1, h =>
      simp only [premIter, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨xvs, -, -, k, -, h⟩ := h
      exact premRounds_scope h

/-- **A scope-keeping premise returns the scope it was given.** -/
theorem premHolds_keepsScope {n : Nat} {env : Env} {ρ ρ' : VarEnv} {p : Prem}
    (hp : keepsScope p = true) (h : premHolds n env ρ p = .ok ρ') : ρ' = ρ := by
  match n, p, hp, h with
  | 0, _, _, h => simp [premHolds] at h
  | m + 1, .ifPr e, _, h =>
      simp only [premHolds, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨-, -, -, h⟩ := h
      exact (Except.ok.inj h).symm
  | m + 1, .iterPr pr (.mk .opt ds), _, h =>
      rw [premHolds] at h
      exact premIter_opt_scope h
  | m + 1, .iterPr pr (.mk .list ds), _, h =>
      rw [premHolds] at h
      exact premIter_list_scope h

/-- **Scope-keeping premises before a failing one**: if the premises `pre` keep the scope and
are followed by a `list` iteration over a domain unbound in it, the list does not hold. -/
theorem not_premsHold_after_keeping {env : Env} {pr : Prem} {ds : List Dom} {rest : List Prem}
    {x y : IL.Id} (hd : Dom.mk x (.varE y) ∈ ds) :
    ∀ (pre : List Prem) {ρ ρ' : VarEnv}, pre.all keepsScope = true → ρ.findVal? y = none →
      ¬ PremsHold env ρ (pre ++ .iterPr pr (.mk .list ds) :: rest) ρ'
  | [], _, _, _, hy => not_premsHold_iterPr_of_unbound hd hy
  | p :: pre, ρ, ρ', hk, hy => by
      rintro ⟨n, h⟩
      have hk' : keepsScope p = true ∧ pre.all keepsScope = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using hk
      match n, h with
      | 0, h => simp [premsHold] at h
      | m + 1, h =>
          rw [premsHold, List.cons_append, List.foldlM_cons, Res.bind_eq_ok] at h
          obtain ⟨ρ₁, h₁, h₂⟩ := h
          obtain rfl := premHolds_keepsScope hk'.1 h₁
          exact not_premsHold_after_keeping hd pre hk'.2 hy ⟨m + 1, by rw [premsHold]; exact h₂⟩

/-! ## `Bmodule` -/

/-- The shape of a 1.0/2.0 `Bmodule`: one production, whose symbol leaves `func*` alone and
whose premises are scope-keeping ones followed by a `list` iteration over a domain `func*`. -/
def BmoduleShape (env : Env) : Prop :=
  ∃ (t : Typ) (q : List Param) (g : IL.Sym) (e : Exp) (pre : List Prem) (pr : Prem)
    (ds : List Dom) (rest : List Prem),
    env.findGram? "Bmodule" = some ([], t, [.prodD q g e (pre ++ .iterPr pr (.mk .list ds) :: rest)]) ∧
    symFrames "func*" (substSym [] g) = true ∧ pre.all keepsScope = true ∧
    Dom.mk "func" (.varE "func*") ∈ ds

/-- **`Bmodule` derives nothing** in a script of that shape. -/
theorem bmodule_dead {env : Env} (hs : BmoduleShape env) {ρ ρ' : VarEnv} {bs : Grammar.Bytes}
    {l : List Value} : ¬ SymDerives env ρ (.varG "Bmodule" []) bs l ρ' := by
  obtain ⟨t, q, g, e, pre, pr, ds, rest, hg, hf, hk, hd⟩ := hs
  intro h
  obtain ⟨-, p, hp, hpd⟩ := (symDerives_varG hg).mp h
  rw [List.mem_singleton] at hp
  subst hp
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, hws, hb, hsd, hpr, -, -⟩ := hpd
  obtain rfl := evalArgs_nil_iff.mp hws
  obtain rfl : ρ₀ = VarEnv.empty := (Option.some.inj hb).symm
  have h₁ : ρ₁.findVal? "func*" = none := (symDerives_frame _ hf hsd).trans rfl
  exact not_premsHold_after_keeping hd pre hk h₁ hpr

set_option maxRecDepth 100000 in
theorem bmoduleShape_wasm10_original : BmoduleShape Wasm10.envOriginal :=
  ⟨_, _, _, _, [], _, _, [], by rfl, by decide, rfl, by simp⟩

set_option maxRecDepth 100000 in
theorem bmoduleShape_wasm10_fixed : BmoduleShape Wasm10.envFixed :=
  ⟨_, _, _, _, [], _, _, [], by rfl, by decide, rfl, by simp⟩

set_option maxRecDepth 100000 in
theorem bmoduleShape_wasm20_original : BmoduleShape Wasm20.envOriginal :=
  ⟨_, _, _, _, [_, _], _, _, [], by rfl, by decide, rfl, by simp⟩

set_option maxRecDepth 100000 in
theorem bmoduleShape_wasm20_fixed : BmoduleShape Wasm20.envFixed :=
  ⟨_, _, _, _, [_, _], _, _, [], by rfl, by decide, rfl, by simp⟩

/-- **#687 and #672 cannot be separated over bytes**: in the pinned and the corrected wasm-1.0
and wasm-2.0 grammar theories, nothing about `Bmodule` is entailed. -/
theorem bmodule_not_entailed (ρ : VarEnv) (bs : Grammar.Bytes) (v : Value) :
    ¬ Entails (scriptAxioms Wasm10.envOriginal) (derivesNT "Bmodule" [] ρ bs v) ∧
      ¬ Entails (scriptAxioms Wasm10.envFixed) (derivesNT "Bmodule" [] ρ bs v) ∧
      ¬ Entails (scriptAxioms Wasm20.envOriginal) (derivesNT "Bmodule" [] ρ bs v) ∧
      ¬ Entails (scriptAxioms Wasm20.envFixed) (derivesNT "Bmodule" [] ρ bs v) := by
  have k : ∀ {env : Env}, BmoduleShape env →
      ¬ Entails (scriptAxioms env) (derivesNT "Bmodule" [] ρ bs v) := fun hs he => by
    obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp ((gramRelSup_varG_iff_entails ..).mpr he)
    exact bmodule_dead hs hd
  exact ⟨k bmoduleShape_wasm10_original, k bmoduleShape_wasm10_fixed,
    k bmoduleShape_wasm20_original, k bmoduleShape_wasm20_fixed⟩

end Silmaril.Wasm.SpecTec.GrammarInst
