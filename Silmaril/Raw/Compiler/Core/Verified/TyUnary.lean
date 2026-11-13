module

public import Silmaril.Compiler.Core.Verified.TyGuard.Defs
public import Silmaril.Compiler.Core.Verified.Unary.Defs
/-! # Unary minus and casts at every supported integer type

Cerberus elaborates `-e` and the cast `(T) e` to `let weak a = e in pure(g)`, with

* `-e` at a signed type `T`: `case a of Specified(x) => Specified(catch_exceptional_condition(T,
  -, 0, conv_int(T, x))) | …`, undefined when `T` does not hold `-x`;
* `-e` at an unsigned type `T`: `… Specified(wrapI(T, -, 0, conv_int(T, x))) …`;
* `(T) e`: `conv_loaded_int(T, a)`.

`uguard file a g = some u` recognises `g` syntactically; `u` is a binary guard (`TyGuard.G`) whose
first operand is `0`: `0 - x` at `T` for the minus, and `0 + x` wrapped at `T`, the conversion
`cv T x`, for the cast. `uguard_eval` evaluates a defined guard to `Specified (u.val 0 n)`,
`uguard_fails` runs an undefined one to undefined behaviour; `runs` and `fails` lift both to the
whole expression, from a run of its operand.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyUnary

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (tagsOf)
open Silmaril.Cerberus.Core.PureEvalExt (Ev)
open Silmaril.Cerberus.Core.Interleave (LocalReaches)
open Silmaril.Cerberus.Core.ArenaFail (Fails)
open ConvInt (Pure)
open Cond (OneAnn)
open TyActions (supported width signed Fits)
open TyConv (cv)
open TyGuard (G convTy)
open IntExpr (spec overflow)
open LoadTask (Touched)

/-- The unary guards over the operand `a`. -/
def uguard (file : File Codec.wireModel Unit Unit) (a : Sym) : Pure → Option G
  | .mk _ () (.case_ (.mk _ () (.sym a'))
      ((.mk _ (.ctor .specified [.mk _ (.base (some x, _))]),
        .mk _ () (.ctor .specified [.mk _ () (.catchExceptionalCondition ity .sub
          (.mk _ () (.val (.object (.integer 0)))) q)])) :: _)) =>
      if a'.key = a.key ∧ convTy file x q = some ity ∧ supported ity = true ∧ signed ity = true then
        some (.arith ity .sub)
      else none
  | .mk _ () (.case_ (.mk _ () (.sym a'))
      ((.mk _ (.ctor .specified [.mk _ (.base (some x, _))]),
        .mk _ () (.ctor .specified [.mk _ () (.wrapI ity .sub
          (.mk _ () (.val (.object (.integer 0)))) q)])) :: _)) =>
      if a'.key = a.key ∧ convTy file x q = some ity ∧ supported ity = true then
        some (.wrap ity .sub)
      else none
  | .mk _ () (.call (.sym s) [.mk _ () (.val (.ctype (.mk _ (.basic (.integer ity))))),
      .mk _ () (.sym a')]) =>
      if a'.key = a.key ∧ TyConv.isConvLoaded file s = true ∧ supported ity = true then
        some (.wrap ity .add)
      else none
  | _ => none

variable {file : Program} {tags : Mem.Concrete.Tags}

/-- The operand value bound to `a`. -/
abbrev operand (a : Sym) (n : Int) (env : Env) : Env :=
  extendEnv [(a, .loaded (.specified (.integer n)))] env

theorem cv_zero {ity : IntegerType} (hs : supported ity = true) : cv ity 0 = 0 :=
  TyConv.cv_of_fits hs (TyConv.fits_zero hs)

/-- **A defined unary guard** evaluates to `Specified (u.val 0 n)`. -/
theorem uguard_eval {a : Sym} {p : Pure} {u : G} (h : uguard file a p = some u) (env : Env) {n : Int}
    (ok : u.Ok 0 n) :
    Ev file tags (operand a n env) (.inl p) (.inl (spec (u.val 0 n))) := by
  unfold uguard at h
  split at h
  · rename_i _ _ a' _ _ x _ _ _ ity _ q _
    split at h
    · rename_i hc
      cases h
      obtain ⟨e1, hq, hs, -⟩ := hc
      refine .case_ (.sym (ConvInt.lookup_one e1)) (by simp [selectCase, matchPattern]; exact ⟨rfl, rfl⟩) ?_
      have ok' : Fits ity (Guard.apply .sub 0 (cv ity n)) := by
        simpa [TyGuard.G.Ok, cv_zero hs] using ok
      refine .ctor (.cons (.catchInt (.cons (Ev.val (v := .object (.integer 0)))
        (.cons (TyGuard.convTy_ev hq hs (ConvInt.lookup_one rfl)) .nil))
        (TyGuard.catch_ok hs rfl ok' tags)) .nil) ?_
      simp [primitive, TyGuard.G.val, cv_zero hs]; rfl
    · cases h
  · rename_i _ _ a' _ _ x _ _ _ ity _ q _
    split at h
    · rename_i hc
      cases h
      obtain ⟨e1, hq, hs⟩ := hc
      refine .case_ (.sym (ConvInt.lookup_one e1)) (by simp [selectCase, matchPattern]; exact ⟨rfl, rfl⟩) ?_
      refine .ctor (.cons (.wrapInt (.cons (Ev.val (v := .object (.integer 0)))
        (.cons (TyGuard.convTy_ev hq hs (ConvInt.lookup_one rfl)) .nil))
        (TyGuard.wrap_prim hs rfl _ _ tags)) .nil) ?_
      simp [primitive, TyGuard.G.val, cv_zero hs]; rfl
    · cases h
  · rename_i _ s _ c ity _ a'
    split at h
    · rename_i hc
      cases h
      obtain ⟨e1, hcv, hs⟩ := hc
      have e : TyGuard.G.val (.wrap ity .add) 0 n = cv ity n := by
        simp only [TyGuard.G.val, Guard.apply, cv_zero hs, Int.zero_add]
        exact TyConv.cv_of_fits hs (TyConv.cv_fits hs n)
      rw [e]
      exact TyConv.convLoaded_ev (ann := c) hcv hs (.cons .val (.cons (.sym (ConvInt.lookup_one e1)) .nil))
    · cases h
  · cases h

/-- **An undefined unary guard** runs to undefined behaviour. -/
theorem uguard_fails {labels : Labels} {a : Sym} {p : Pure} {u : G} (h : uguard file a p = some u)
    (env : Env) {n : Int} (bad : ¬ u.Ok 0 n) (wc : Bool) (k : List Frame) (m : Mem.Concrete.State) :
    Fails file labels wc ⟨.pureExpr p (operand a n env), k, m⟩ overflow := by
  unfold uguard at h
  split at h
  · rename_i ann ann₁ a' pann pann' x tx q₁ q₂ ity q₀ q rest
    split at h
    · rename_i hc
      cases h
      obtain ⟨e1, hq, hs, -⟩ := hc
      let env₁ := operand a n env
      let env₂ := extendEnv [(x, .object (.integer n))] env₁
      let k₁ : List Frame := .arguments (.ctor .specified) [] [] env₂ :: k
      let CATCH : Pure := .mk q₂ () (.catchExceptionalCondition ity .sub
        (.mk q₀ () (.val (.object (.integer 0)))) q)
      have args : Ev file (tagsOf file m) env₂ (.inr [.mk q₀ () (.val (.object (.integer 0))), q])
          (.inr [.object (.integer 0), .object (.integer (cv ity n))]) :=
        .cons (Ev.val (v := .object (.integer 0))) (.cons (TyGuard.convTy_ev hq hs (ConvInt.lookup_one rfl)) .nil)
      have bad' : ¬ Fits ity (Guard.apply .sub 0 (cv ity n)) := by
        simpa [TyGuard.G.Ok, cv_zero hs] using bad
      let BS : List (Pattern Sym × Pure) :=
        (.mk pann (.ctor .specified [.mk pann' (.base (some x, tx))]), .mk q₁ () (.ctor .specified [CATCH]))
          :: rest
      refine ⟨⟨.apply (.catchInt ity .sub) [.object (.integer 0), .object (.integer (cv ity n))], k₁, m⟩,
        ?_, (fun v hv => by cases hv), .inl ?_⟩
      · refine .head (.next (c' := .pureExpr (.mk ann₁ () (.sym a')) env₁)
          (k' := .pureCase BS env₁ :: k)
          (by simp [requestAux, awaitsScheduling, env₁, BS, CATCH]) (PureLocal.plain_pureExpr _ _)) ?_
        refine (PureLocal.eval_local file _ (.sym (ConvInt.lookup_one e1)) _ m rfl).trans ?_
        refine .head (.next (c' := .pureExpr (.mk q₁ () (.ctor .specified [CATCH])) env₂) (k' := k)
          (by simp [requestAux, awaitsScheduling, selectCase, matchPattern, BS, CATCH, env₂])
          (PureLocal.plain_pureExpr _ _)) ?_
        refine .head (.next (c' := .pureExpr CATCH env₂) (k' := k₁)
          (by simp [requestAux, awaitsScheduling, arguments, k₁, CATCH]) (PureLocal.plain_pureExpr _ _)) ?_
        refine (PureLocal.arguments_local file (.catchInt ity .sub)
          [.mk q₀ () (.val (.object (.integer 0))), q] env₂ k₁ m wc
          (by simp [requestAux, awaitsScheduling, CATCH])).trans ?_
        simpa using PureEvalExt.args_local file _ args (.catchInt ity .sub) [] k₁ m rfl (wc := wc)
          (labels := labels)
      · rw [PureLocal.requestAux_apply file (op := .catchInt ity .sub) trivial, TyGuard.catch_ub hs rfl bad']
    · cases h
  · split at h
    · cases h; exact absurd trivial bad
    · cases h
  · split at h
    · cases h; exact absurd trivial bad
    · cases h
  · cases h

/-- **In range**: from a run of the operand to `Specified n`, `let weak a = e in pure(g)` runs
to `Specified (u.val 0 n)`, over the operand's annotation frame. -/
theorem runs {labels : Labels} {an pa ag : List Annot} {a : Sym} {ta : BaseType} {e : EE} {g : Pure}
    {u : G} (hg : uguard file a g = some u) {env : Env} {n : Int} (ok : u.Ok 0 n)
    {k : List Frame} {m m₁ : Mem.Concrete.State} {fr : List Frame}
    {xs : List Access} (hfr : OneAnn fr xs)
    (run : LocalReaches file labels false
      ⟨.effectExpr e env, .effectBind (.mk pa (.base (some a, ta))) (.mk ag (.pure g)) env :: k, m⟩
      ⟨.value (spec n), fr ++ .effectBind (.mk pa (.base (some a, ta))) (.mk ag (.pure g)) env :: k, m₁⟩) :
    ∃ m₂, Touched m₁ m₂ ∧ LocalReaches file labels false
      ⟨.effectExpr (.mk an (.wseq (.mk pa (.base (some a, ta))) e (.mk ag (.pure g)))) env, k, m⟩
      ⟨.value (spec (u.val 0 n)), fr ++ k, m₂⟩ := by
  have s₁ : LocalReaches file labels false
      ⟨.effectExpr (.mk an (.wseq (.mk pa (.base (some a, ta))) e (.mk ag (.pure g)))) env, k, m⟩
      ⟨.effectExpr e env, .effectBind (.mk pa (.base (some a, ta))) (.mk ag (.pure g)) env :: k, m⟩ :=
    .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
  have s₂ := Unary.value_effectBind (file := file) (labels := labels) hfr (spec n) pa a ta
    (.mk ag (.pure g)) env k m₁
  obtain ⟨l', s₃⟩ := IntExpr.guard_local (file := file) (labels := labels) ag g (operand a n env)
    (fr ++ k) m₁
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l'}
  have s₄ := PureEvalExt.ev_local file (PureEval.tagsOf file m₂) (wc := false) (labels := labels)
    (uguard_eval hg env ok) (.diagnosticLocation m₁.currentLocation :: (fr ++ k)) m₂ rfl
  refine ⟨m₂, ⟨l', m₁.lastUsed, rfl⟩, s₁.trans (run.trans (s₂.trans (s₃.trans (s₄.tail ?_))))⟩
  exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
    (LoadTask.plain_value _)

/-- **Out of range**: the expression reaches undefined behaviour. -/
theorem fails {labels : Labels} {an pa ag : List Annot} {a : Sym} {ta : BaseType} {e : EE}
    {g : Pure} {u : G} (hg : uguard file a g = some u) {env : Env} {n : Int} (bad : ¬ u.Ok 0 n)
    {k : List Frame} {m m₁ : Mem.Concrete.State} {fr : List Frame}
    {xs : List Access} (hfr : OneAnn fr xs)
    (run : LocalReaches file labels false
      ⟨.effectExpr e env, .effectBind (.mk pa (.base (some a, ta))) (.mk ag (.pure g)) env :: k, m⟩
      ⟨.value (spec n), fr ++ .effectBind (.mk pa (.base (some a, ta))) (.mk ag (.pure g)) env :: k, m₁⟩) :
    Fails file labels false
      ⟨.effectExpr (.mk an (.wseq (.mk pa (.base (some a, ta))) e (.mk ag (.pure g)))) env, k, m⟩
      overflow := by
  have s₁ : LocalReaches file labels false
      ⟨.effectExpr (.mk an (.wseq (.mk pa (.base (some a, ta))) e (.mk ag (.pure g)))) env, k, m⟩
      ⟨.effectExpr e env, .effectBind (.mk pa (.base (some a, ta))) (.mk ag (.pure g)) env :: k, m⟩ :=
    .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
  have s₂ := Unary.value_effectBind (file := file) (labels := labels) hfr (spec n) pa a ta
    (.mk ag (.pure g)) env k m₁
  obtain ⟨l', s₃⟩ := IntExpr.guard_local (file := file) (labels := labels) ag g (operand a n env)
    (fr ++ k) m₁
  exact ArenaFail.Fails.pre file labels (s₁.trans (run.trans (s₂.trans s₃)))
    (uguard_fails (labels := labels) hg env bad false
      (.diagnosticLocation m₁.currentLocation :: (fr ++ k)) {m₁ with currentLocation := l'})

end Silmaril.Compile.Core.Verified.TyUnary
