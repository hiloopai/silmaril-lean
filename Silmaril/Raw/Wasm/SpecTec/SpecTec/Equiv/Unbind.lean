module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecReadControl
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `matchExp` binds only in pattern position

To say that a rule's conclusion leaves a variable unbound one has to know
which variables a pattern binds.  `Unbinds env e y` says `y` is not one of
them, and the closure lemmas below let it be read off a conclusion's shape
without unfolding `matchExp`: each is a one-liner from the corresponding
inversion.

`CallE` — and every other form `matchDefault` handles — binds nothing at all,
which is the whole point: that is where the variables the unfireable rules
need would have had to come from.  See
`Equiv/ExecStepRules.lean`'s `not_ruleFires_tableGrowSucceed_pinned` and
`Equiv/ExecReadAggregate.lean`'s `not_ruleFires_structGetStruct` for the two
shapes this settles, and `scripts/spectec_unbound_vars.py` for the census.

This module exists so that `Equiv/ExecReadAggregate.lean` and
`Equiv/ExecStepRules.lean` can share it: the latter imports the former, so
neither could host it.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.Unbind

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (MatchExps)
open Silmaril.SpecTec.Equiv.Execution

attribute [local simp] Execution.findVal?_empty Execution.findVal?_bindVal_lit

/-- Matching `e` never binds `y`. -/
def Unbinds (env : Env) (e : Exp) (y : IL.Id) : Prop :=
  ∀ ρ σ v, ρ.findVal? y = none → MatchExp env ρ e v σ → σ.findVal? y = none

/-- The same, for a list of patterns matched pointwise. -/
def UnbindsAll (env : Env) (es : List Exp) (y : IL.Id) : Prop :=
  ∀ ρ σ vs, ρ.findVal? y = none → MatchExps env ρ es vs σ → σ.findVal? y = none

theorem unbindsAll_nil {env : Env} {y : IL.Id} : UnbindsAll env [] y := by
  rintro ρ σ vs hy hm
  obtain ⟨-, rfl⟩ := Validation.matchExps_nil_iff.1 hm
  exact hy

theorem unbindsAll_cons {env : Env} {e : Exp} {es : List Exp} {y : IL.Id}
    (h : Unbinds env e y) (hs : UnbindsAll env es y) : UnbindsAll env (e :: es) y := by
  rintro ρ σ vs hy hm
  obtain ⟨w, ws, τ, rfl, hw, hws⟩ := Validation.matchExps_cons_iff.1 hm
  exact hs _ _ _ (h _ _ _ hy hw) hws

/-- A variable pattern binds only itself. -/
theorem unbinds_varE {env : Env} {x y : IL.Id} (hx : x ≠ "_") (h : x ≠ y) :
    Unbinds env (.varE x) y := by
  rintro ρ σ v hy hm
  rcases Validation.matchExp_var_iff.1 hm with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · simpa [Execution.findVal?_bindVal_lit hx, h] using hy
  · exact hy

theorem unbinds_caseE {env : Env} {op : MixopS} {e : Exp} {y : IL.Id}
    (h : Unbinds env e y) : Unbinds env (.caseE op e) y := by
  rintro ρ σ v hy hm
  obtain ⟨w, rfl, hw⟩ := Validation.matchExp_case_iff.1 hm
  exact h _ _ _ hy hw

theorem unbinds_tupE {env : Env} {es : List Exp} {y : IL.Id}
    (h : UnbindsAll env es y) : Unbinds env (.tupE es) y := by
  rintro ρ σ v hy hm
  obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hm
  exact h _ _ _ hy hws

theorem unbinds_listE {env : Env} {es : List Exp} {y : IL.Id}
    (h : UnbindsAll env es y) : Unbinds env (.listE es) y := by
  rintro ρ σ v hy hm
  obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_list_iff.1 hm
  exact h _ _ _ hy hws

theorem unbinds_subE {env : Env} {e : Exp} {t₁ t₂ : Typ} {y : IL.Id}
    (h : Unbinds env e y) : Unbinds env (.subE e t₁ t₂) y := by
  rintro ρ σ v hy hm
  exact h _ _ _ hy (Validation.matchExp_sub_iff.1 hm)

/-- A concatenation binds what its two operands bind, in sequence. -/
theorem unbinds_catE {env : Env} {e₁ e₂ : Exp} {y : IL.Id}
    (h₁ : Unbinds env e₁ y) (h₂ : Unbinds env e₂ y) :
    Unbinds env (.catE e₁ e₂) y := by
  rintro ρ σ v hy hm
  obtain ⟨vs, k, τ, rfl, ha, hb⟩ := ExecReadControl.matchExp_catE_dest hm
  exact h₂ _ _ _ (h₁ _ _ _ hy ha) hb

theorem unbinds_optNone {env : Env} {y : IL.Id} : Unbinds env (.optE none) y := by
  rintro ρ σ v hy hm
  obtain ⟨-, rfl⟩ := Validation.matchExp_optNone_iff.1 hm
  exact hy

theorem unbinds_optSome {env : Env} {e : Exp} {y : IL.Id}
    (h : Unbinds env e y) : Unbinds env (.optE (some e)) y := by
  rintro ρ σ v hy hm
  obtain ⟨w, rfl, hw⟩ := Validation.matchExp_optSome_iff.1 hm
  exact h _ _ _ hy hw

/-- Discharge `Unbinds` for a conclusion built from the pattern formers.  Every
rule below uses it; the point is that there is no case for `CallE`, so a
variable reachable only through one is never bound. -/
macro "unbinds" : tactic => `(tactic|
  repeat' first
    | exact unbindsAll_nil
    | exact unbinds_varE (by decide) (by decide)
    | exact unbinds_optNone
    | apply unbinds_optSome
    | apply unbinds_caseE
    | apply unbinds_tupE
    | apply unbinds_listE
    | apply unbinds_subE
    | apply unbindsAll_cons)

end Silmaril.SpecTec.Equiv.Unbind
