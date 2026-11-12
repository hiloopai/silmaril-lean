module

public import Silmaril.Wasm.SpecTec.Surface.Elab.Defs

/-!
# Soundness of the SpecTec surface elaborator

Each elaboration function is sound for its relation. The headline
`elab?_sound` is in `Silmaril.Wasm.SpecTec.Surface.Elab.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Surface.Elab

open Silmaril.Wasm.SpecTec.Surface.Syntax
open Silmaril.SpecTec

theorem optMap_sound {α β : Type} {f : α → Option β} {R : α → β → Prop}
    (hf : ∀ {a b}, f a = some b → R a b) :
    ∀ {as : List α} {bs : List β}, optMap f as = some bs → List.Forall₂ R as bs := by
  intro as
  induction as with
  | nil => intro bs h; cases h; exact .nil
  | cons a as ih =>
    intro bs h
    unfold optMap at h
    split at h
    next b bs' ha has => cases h; exact .cons (hf ha) (ih has)
    next => cases h

theorem elabTyp?_sound {Γ : Ctx} {t : Typ} {t' : IL.Typ} (h : elabTyp? Γ t = some t') :
    ElabTyp Γ t t' := by
  induction t generalizing t' with
  | var x as =>
    cases as with
    | nil =>
      unfold elabTyp? at h
      split at h
      next hx => cases h; exact .var hx
      next => cases h
    | cons _ _ => cases h
  | bool => cases h; exact .bool
  | num t => cases h; exact .num
  | text => cases h; exact .text
  | iter t it ih =>
    obtain ⟨t0, ht, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact .iter (ih ht)

mutual

theorem elabExp?_sound (Γ : Ctx) (vs : Vars) :
    (e : Exp) → ∀ {e' : IL.Exp}, elabExp? Γ vs e = some e' → ElabExp Γ vs e e'
  | .var x [], e', h => by
    unfold elabExp? at h
    split at h
    next hx => cases h; exact .var hx
    next => cases h
  | .var _ (_ :: _), _, h => by simp [elabExp?] at h
  | .nat s, e', h => by cases h; exact .nat
  | .paren e, e', h => .paren (elabExp?_sound Γ vs e h)
  | .call f as, e', h => by
    obtain ⟨as', ha, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact .call (elabExps?_sound Γ vs as ha)
  | .cmp op e₁ e₂, e', h => by
    unfold elabExp? at h
    split at h
    next t e₁' e₂' ht h₁ h₂ =>
      cases h
      exact .cmp ht (elabExp?_sound Γ vs e₁ h₁) (elabExp?_sound Γ vs e₂ h₂)
    next => cases h
  | .bin op e₁ e₂, e', h => by
    unfold elabExp? at h
    split at h
    next t e₁' e₂' ht h₁ h₂ =>
      cases h
      exact .bin ht (elabExp?_sound Γ vs e₁ h₁) (elabExp?_sound Γ vs e₂ h₂)
    next => cases h
  | .eps, _, h => by simp [elabExp?] at h
  | .iter _ _, _, h => by simp [elabExp?] at h
  | .seq _, _, h => by simp [elabExp?] at h

theorem elabExps?_sound (Γ : Ctx) (vs : Vars) :
    (es : List Exp) → ∀ {es' : List IL.Exp}, elabExp?.elabExps? Γ vs es = some es' →
      List.Forall₂ (ElabExp Γ vs) es es'
  | [], es', h => by cases h; exact .nil
  | e :: es, es', h => by
    unfold elabExp?.elabExps? at h
    split at h
    next e' es'' h₁ h₂ => cases h; exact .cons (elabExp?_sound Γ vs e h₁) (elabExps?_sound Γ vs es h₂)
    next => cases h

end

theorem elabPrem?_sound {Γ : Ctx} {vs : Vars} {p : Prem} {p' : IL.Prem}
    (h : elabPrem? Γ vs p = some p') : ElabPrem Γ vs p p' := by
  cases p with
  | ifP e =>
    obtain ⟨e', he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .ifP (elabExp?_sound Γ vs e he)
  | otherwise => cases h; exact .otherwise

theorem elabParam?_sound {Γ : Ctx} {e : Exp} {p : IL.Param} (h : elabParam? Γ e = some p) :
    ElabParam Γ e p := by
  unfold elabParam? at h
  split at h
  next t ht =>
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
    exact .mk ht (elabTyp?_sound ht')
  next => cases h

theorem argQuants?_sound (Γ : Ctx) (as : List Exp) (ps : List IL.Param) :
    ∀ {vs : Vars}, argQuants? Γ as ps = some vs → ArgQuants Γ as ps vs := by
  fun_induction argQuants? Γ as ps with
  | case1 => intro vs h; cases h; exact .nil
  | case2 x as p t ps ih =>
    intro vs h
    obtain ⟨vs', hv, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .var (ih hv)
  | case3 s as p ps ih => intro vs h; exact .nat (ih h)
  | case4 => intro vs h; cases h

theorem elabClause?_sound {Γ : Ctx} {ps : List IL.Param} {f : Exp}
    {c : List Exp × Exp × List Prem} {c' : IL.Clause} (h : elabClause? Γ ps c = some c') :
    ElabClause Γ ps f c.1 c.2.1 c.2.2 c' := by
  unfold elabClause? at h
  split at h
  next => cases h
  next vs hv =>
    split at h
    next as' e' prems' ha he hp =>
      cases h
      exact .mk (argQuants?_sound Γ _ _ hv) (optMap_sound (elabExp?_sound Γ vs _) ha)
        (elabExp?_sound Γ vs _ he) (optMap_sound elabPrem?_sound hp)
    next => cases h

theorem decSig_clauses {Γ : Ctx} {f : List Char} {ps : List IL.Param} {all : List Def}
    {cs : List IL.Clause} (h : optMap (elabClause? Γ ps) (clausesOf f all) = some cs) :
    List.Forall₂ (fun (c : List Exp × Exp × List Prem) c' =>
      ElabClause Γ ps (.call f []) c.1 c.2.1 c.2.2 c') (clausesOf f all) cs :=
  optMap_sound elabClause?_sound h

theorem noCalls {f : List Char} {cs : List IL.Clause}
    (h : (cs.all fun c => !(clauseCalls c).contains (String.ofList f)) = true) :
    ∀ c ∈ cs, String.ofList f ∉ clauseCalls c := by
  intro c hc hm
  have hc' := List.all_eq_true.mp h c hc
  simp_all

theorem elabDecls?_sound (all : List Def) (Γ : Ctx) (ds : List Def) :
    ∀ {s : IL.Script}, elabDecls? all Γ ds = some s → ElabDecls all Γ ds s := by
  fun_induction elabDecls? all Γ ds with
  | case1 => intro s h; cases h; exact .nil
  | case2 Γ x hs t ds t' ht ih =>
    intro s h
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp h
    exact .syntaxAlias (elabTyp?_sound ht) (ih hs')
  | case4 Γ f pas t hs ds ps t' ht hp cs hc hall ih =>
    intro s h
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp h
    exact .decSig (optMap_sound elabParam?_sound hp) (elabTyp?_sound ht) (decSig_clauses hc)
      (noCalls hall) (ih hs')
  | case8 Γ x t hs g a ds t' p τ a' ha hg ht ih =>
    intro s h
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp h
    exact .gramAlias (elabTyp?_sound ht) hg (elabExp?_sound Γ [] a ha) (ih hs')
  | case11 Γ x as e ps ds ih => intro s h; exact .decClause (ih h)
  | case12 Γ ds ih => intro s h; exact .sep (ih h)
  | _ => intro s h; cases h

end Silmaril.Wasm.SpecTec.Surface.Elab
