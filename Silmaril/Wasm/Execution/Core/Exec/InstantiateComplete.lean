module

public import Silmaril.Wasm.Execution.Core.Exec.Instantiate
public import Silmaril.Wasm.Execution.Core.Soundness.ConstEvalStep

@[expose] public section

/-! # Completeness of `instantiate?`

Relative to an evaluator-completeness hypothesis `EvalComplete` on constant
expressions, `instantiate?` computes every configuration related by `Instantiate`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- An expression made only of constant instructions. -/
def ConstExpr (e : Expr) : Prop := ∀ i ∈ e, i.IsConstI

/-- Completeness of an initializer evaluator on constant expressions. -/
def EvalComplete (P : Profile) (host : HostSemantics H)
    (ev : Store H → Frame → Expr → Option (Store H × Val)) : Prop :=
  ∀ s f e s' f' v, ConstExpr e → EvalExpr P host s f e s' f' [v] → f' = f ∧ ev s f e = some (s', v)

variable {P : Profile} {host : HostSemantics H}
  {ev : Store H → Frame → Expr → Option (Store H × Val)}

theorem evalGlobals?_complete (hev : EvalComplete P host ev)
    {s : Store H} {f : Frame} {gs : List CGlobalType} {es : List Expr}
    {s' : Store H} {f' : Frame} {vs : List Val}
    (h : EvalGlobals P host s f gs es s' f' vs) (hc : ∀ e ∈ es, ConstExpr e) :
    evalGlobals? ev s f gs es = some (s', f', vs) := by
  induction h with
  | nil => simp [evalGlobals?]
  | cons he _ ih =>
    obtain ⟨rfl, he'⟩ := hev _ _ _ _ _ _ (hc _ (List.mem_cons_self ..)) he
    simp only [evalGlobals?, he', ih (fun e h => hc e (List.mem_cons_of_mem _ h))]

theorem evalExprs?_complete (hev : EvalComplete P host ev)
    {s : Store H} {f : Frame} {es : List Expr} {s' : Store H} {f' : Frame} {rs : List Ref}
    (h : EvalExprs P host s f es s' f' rs) (hc : ∀ e ∈ es, ConstExpr e) :
    evalExprs? ev s f es = some (s', f', rs) := by
  induction h with
  | nil => simp [evalExprs?]
  | cons he _ ih =>
    obtain ⟨rfl, he'⟩ := hev _ _ _ _ _ _ (hc _ (List.mem_cons_self ..)) he
    rw [evalExprs?, he']
    simp only [ih (fun e h => hc e (List.mem_cons_of_mem _ h))]

theorem evalExprss?_complete (hev : EvalComplete P host ev)
    {s : Store H} {f : Frame} {ess : List (List Expr)} {s' : Store H} {f' : Frame}
    {rss : List (List Ref)}
    (h : EvalExprss P host s f ess s' f' rss) (hc : ∀ es ∈ ess, ∀ e ∈ es, ConstExpr e) :
    evalExprss? ev s f ess = some (s', f', rss) := by
  induction h with
  | nil => simp [evalExprss?]
  | cons he _ ih =>
    simp only [evalExprss?, evalExprs?_complete hev he (hc _ (List.mem_cons_self ..)),
      ih (fun es h => hc es (List.mem_cons_of_mem _ h))]

theorem _root_.Silmaril.Wasm.Validation.ExprConst.constExpr {C : Context} {e : Expr} (h : ExprConst C e) : ConstExpr e :=
  fun i hi => (h i hi).isConstI

theorem _root_.Silmaril.Wasm.Validation.ExprOkConst.constExpr {C : Context} {e : Expr} {t : CValType}
    (h : ExprOkConst C e t) : ConstExpr e := ExprConst.constExpr h.const

theorem _root_.Silmaril.Wasm.Validation.GlobalsOk.constExpr {C : Context} {gs : List Global} {gts : List CGlobalType}
    (h : GlobalsOk C gs gts) : ∀ g ∈ gs, ConstExpr g.init := by
  induction h with
  | nil => simp
  | cons hg _ ih =>
    intro g hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hg.2.2.constExpr
    · exact ih g hm

theorem forall₂_left_of {α β : Type} {R : α → β → Prop} {p : α → Prop}
    (hR : ∀ a b, R a b → p a) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, p a
  | _, _, .nil => by simp
  | _, _, .cons hab hs => by
    intro a hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hR _ _ hab
    · exact forall₂_left_of hR hs a hm

/-- Every initializer (global, table, element) of a valid module is constant. -/
theorem _root_.Silmaril.Wasm.Validation.ModuleOk.initConst {m : Module} {mt : CModuleType} (h : ModuleOk m mt) :
    (∀ e ∈ m.globals.map Global.init, ConstExpr e) ∧
    (∀ e ∈ m.tables.map Table.init, ConstExpr e) ∧
    (∀ es ∈ m.elems.map Elem.init, ∀ e ∈ es, ConstExpr e) := by
  cases h with
  | mk _ _ _ _ _ hglobals _ htables _ _ helems =>
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.mem_map]
      rintro _ ⟨g, hg, rfl⟩
      exact hglobals.constExpr g hg
    · simp only [List.mem_map]
      rintro _ ⟨t, ht, rfl⟩
      exact forall₂_left_of (p := fun t : Table => ConstExpr t.init)
        (fun _ _ h => h.2.2.constExpr) htables t ht
    · simp only [List.mem_map]
      rintro _ ⟨el, hel, rfl⟩
      exact forall₂_left_of (p := fun el : Elem => ∀ e ∈ el.init, ConstExpr e)
        (fun _ _ h e he => (h.2.2.1 e he).constExpr) helems el hel

theorem instantiate?_complete (hev : EvalComplete P host ev) {s : Store H} {m : Module}
    {xas : List ExternAddr} {c : Config H} (h : Instantiate P host s m xas c) :
    instantiate? ev s m xas = some c := by
  obtain ⟨_, _, hmod, _⟩ := h.valid
  obtain ⟨hcG, hcT, hcE⟩ := hmod.initConst
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi, hG, hT, hE, hM, rfl⟩ := h.run
  unfold instantiate?
  rw [ite_eq_left_of_eq_true _ _ (eq_true h.bounded)]
  simp only [evalGlobals?_complete hev hG hcG,
    evalExprs?_complete hev hT hcT, evalExprss?_complete hev hE hcE, hM]
  rfl

end Silmaril.Wasm.Execution.Core

