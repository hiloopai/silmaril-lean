module

public import Silmaril.Compiler.Core.Verified.IntExpr.Defs

/-! # Cerberus's unary `int` operators `-` and `~`

Cerberus elaborates `-e` and `~e` on an `int` operand to the operand bound to `a`, followed by
the pure guard

```
case a of
| Specified(x) => Specified(catch_exceptional_condition(int, sub, 0, conv_int(int, x)))   -- -e
| Specified(x) => Specified(ivcompl(int, conv_int(int, x)))                               -- ~e
| Unspecified(_) => Unspecified(int)
```

`guard file a p = some u` recognises the guard syntactically. With an `int` operand
`Specified n` bound to `a`:

* `guard_eval`: when `u.apply n` is an `int`, the guard evaluates to `Specified (u.apply n)`:
  `-n` is `0 - n` and `~n` is `-1 - n` (Cerberus's `ivcompl` is `-n - 1`, unbounded two's
  complement);
* `guard_fails`: otherwise (only `-` of the least `int`) its local run reaches the
  `catch_exceptional_condition` whose request is undefined behaviour
  `UB036_exceptional_condition`.

Both are `u.base - n`, so the Lir side computes them with the existing 64-bit subtraction.

`runs` and `fails` lift these to the whole expression `let weak a = e in pure(guard)`, from a
run of the operand `e` to `Specified n`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Unary

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf argState)
open Silmaril.Cerberus.Core.Interleave (LocalReaches)
open ConvInt (Pure IsInt)
open Silmaril.Cerberus.Core.ArenaFail (Fails)
open LoadTask (Touched)
open Cond (OneAnn)
open IntExpr (spec overflow)

/-- The unary operators. -/
inductive Unop where
  | neg
  | compl
  deriving DecidableEq

/-- `u n = u.base - n`. -/
def Unop.base : Unop → Int
  | .neg => 0
  | .compl => -1

/-- The value of a unary operator. -/
def Unop.apply (u : Unop) (n : Int) : Int := u.base - n

theorem Unop.base_int (u : Unop) : IsInt u.base := by
  cases u <;> exact ⟨by decide, by decide⟩

theorem Unop.compl_int {n : Int} (hn : IsInt n) : IsInt (Unop.compl.apply n) := by
  obtain ⟨lo, hi⟩ := hn
  exact ⟨by simp [Unop.apply, Unop.base]; omega, by simp [Unop.apply, Unop.base]; omega⟩

/-- The guard of a unary `int` operator over the operand `a`. -/
def guard (file : File Codec.wireModel Unit Unit) (a : Sym) : Pure → Option Unop
  | .mk _ () (.case_ (.mk _ () (.sym a'))
      ((.mk _ (.ctor .specified [.mk _ (.base (some x, _))]),
        .mk _ () (.ctor .specified [.mk _ () (.catchExceptionalCondition (.signed .int) .sub
          (.mk _ () (.val (.object (.integer 0)))) q)])) :: _)) =>
      if decide (a'.key = a.key) && Guard.convOf file x q then some .neg else none
  | .mk _ () (.case_ (.mk _ () (.sym a'))
      ((.mk _ (.ctor .specified [.mk _ (.base (some x, _))]),
        .mk _ () (.ctor .specified [.mk _ () (.ctor .ivCompl
          [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), q])])) :: _)) =>
      if decide (a'.key = a.key) && Guard.convOf file x q then some .compl else none
  | _ => none

variable {file : Program} {tags : Mem.Concrete.Tags}

/-- The operand value bound to `a`. -/
abbrev operand (a : Sym) (n : Int) (env : Env) : Env :=
  extendEnv [(a, .loaded (.specified (.integer n)))] env

/-- The pieces of a recognised guard. -/
theorem guard_parts {a : Sym} {p : Pure} {u : Unop} (h : guard file a p = some u) :
    ∃ (ann ann₁ : List Annot) (a' : Sym) (bs : List (Pattern Sym × Pure)),
      p = .mk ann () (.case_ (.mk ann₁ () (.sym a')) bs) ∧ a'.key = a.key ∧
      ∀ (env : Env) (n : Int), IsInt n → ∃ (body : Pure) (q₁ : List Annot) (x : Sym),
        selectCase (.loaded (.specified (.integer n))) bs = some ([(x, .object (.integer n))], body) ∧
        ((u = .neg ∧ ∃ (q₂ : List Annot) (pp pq : Pure),
            body = .mk q₁ () (.ctor .specified [.mk q₂ () (.catchExceptionalCondition (.signed .int)
              .sub pp pq)]) ∧
            ∀ tags, Eval file tags (extendEnv [(x, .object (.integer n))] env) (.inr [pp, pq])
              (.inr [.object (.integer 0), .object (.integer n)])) ∨
         (u = .compl ∧ ∀ tags, Eval file tags (extendEnv [(x, .object (.integer n))] env) (.inl body)
              (.inl (.loaded (.specified (.integer (Unop.compl.apply n))))))) := by
  unfold guard at h
  split at h
  · rename_i ann ann₁ a' pann pann' x tx q₁ q₂ q₀ q rest
    split at h
    · rename_i cond
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
      obtain ⟨e1, cq⟩ := cond
      refine ⟨ann, ann₁, a', _, rfl, e1, ?_⟩
      intro env n hn
      refine ⟨_, q₁, x, by simp [selectCase, matchPattern]; rfl, .inl ⟨rfl, q₂, _, q,
        rfl, ?_⟩⟩
      intro tags
      exact .cons .val (.cons (Guard.convOf_eval cq hn (ConvInt.lookup_one rfl)) .nil)
    · cases h
  · rename_i ann ann₁ a' pann pann' x tx q₁ q₂ c₁ cty q rest
    split at h
    · rename_i cond
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
      obtain ⟨e1, cq⟩ := cond
      refine ⟨ann, ann₁, a', _, rfl, e1, ?_⟩
      intro env n hn
      refine ⟨_, q₁, x, by simp [selectCase, matchPattern]; rfl, .inr ⟨rfl, ?_⟩⟩
      intro tags
      have e : Unop.compl.apply n = -n - 1 := by simp only [Unop.apply, Unop.base]; omega
      have hc : primitive (.ctor .ivCompl) [runtimeValue (.ctype (.mk cty (.basic (.integer
          (.signed .int))))), .object (.integer n)] tags = .ok (integer (Unop.compl.apply n)) := by
        rw [e]; simp [primitive, runtimeValue, intType]; rfl
      exact .ctor (.cons (.ctor (.cons .val (.cons (Guard.convOf_eval cq hn (ConvInt.lookup_one rfl))
        .nil)) hc) .nil) (by simp [primitive, integer]; rfl)
    · cases h
  · cases h

/-- **A guard in range** evaluates to `Specified (u.apply n)`. -/
theorem guard_eval {a : Sym} {p : Pure} {u : Unop} (h : guard file a p = some u)
    (env : Env) {n : Int} (hn : IsInt n) (hr : IsInt (u.apply n)) :
    Eval file tags (operand a n env) (.inl p)
      (.inl (.loaded (.specified (.integer (u.apply n))))) := by
  obtain ⟨ann, ann₁, a', bs, rfl, e1, rest⟩ := guard_parts h
  obtain ⟨body, q₁, x, hsel, hb⟩ := rest (operand a n env) n hn
  refine .case_ (.sym (ConvInt.lookup_one e1)) hsel ?_
  rcases hb with ⟨rfl, q₂, pp, pq, rfl, hargs⟩ | ⟨rfl, hbody⟩
  · refine .ctor (.cons (.catchInt (hargs tags) (Guard.catchInt_ok (op := .sub) rfl
      (by simpa [Unop.apply, Unop.base, Guard.apply] using hr) tags)) .nil) ?_
    simp [primitive, Unop.apply, Unop.base, Guard.apply]; rfl
  · exact hbody tags

/-- **A guard out of range** runs, by local steps from any continuation, to the
`catch_exceptional_condition` whose request is undefined behaviour. -/
theorem guard_fails {labels : Labels} {a : Sym} {p : Pure} {u : Unop}
    (h : guard file a p = some u) (env : Env) {n : Int} (hn : IsInt n)
    (hr : ¬ IsInt (u.apply n)) (wc : Bool) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ k', LocalReaches file labels wc ⟨.pureExpr p (operand a n env), k, m⟩
        ⟨.apply (.catchInt (.signed .int) .sub) [.object (.integer 0), .object (.integer n)], k', m⟩ ∧
      requestAux file labels m
        (.apply (.catchInt (.signed .int) .sub) [.object (.integer 0), .object (.integer n)]) k' wc =
        .end_ (.ub .unknown .UB036_exceptional_condition) := by
  obtain ⟨ann, ann₁, a', bs, rfl, e1, rest⟩ := guard_parts h
  let env₁ := operand a n env
  obtain ⟨body, q₁, x, hsel, hb⟩ := rest env₁ n hn
  rcases hb with ⟨rfl, q₂, pp, pq, rfl, hargs⟩ | ⟨rfl, -⟩
  · let env₂ := extendEnv [(x, .object (.integer n))] env₁
    let k₁ : List Frame := .arguments (.ctor .specified) [] [] env₂ :: k
    let CATCH : Pure := .mk q₂ () (.catchExceptionalCondition (.signed .int) .sub pp pq)
    refine ⟨k₁, ?_, ?_⟩
    · refine .head (.next (c' := .pureExpr (.mk ann₁ () (.sym a')) env₁) (k' := .pureCase bs env₁ :: k)
        (by simp [requestAux, awaitsScheduling, env₁]) (PureLocal.plain_pureExpr _ _)) ?_
      refine (PureLocal.eval_local file _ (.sym (ConvInt.lookup_one e1)) _ m rfl).trans ?_
      refine .head (.next (c' := .pureExpr (.mk q₁ () (.ctor .specified [CATCH])) env₂) (k' := k)
        (by simp [requestAux, awaitsScheduling, hsel, CATCH, env₂]) (PureLocal.plain_pureExpr _ _)) ?_
      refine .head (.next (c' := .pureExpr CATCH env₂) (k' := k₁)
        (by simp [requestAux, awaitsScheduling, arguments, k₁]) (PureLocal.plain_pureExpr _ _)) ?_
      refine (PureLocal.arguments_local file (.catchInt (.signed .int) .sub) [pp, pq] env₂ k₁ m wc
        (by simp [requestAux, awaitsScheduling, CATCH])).trans ?_
      simpa using PureLocal.args_local file _ (hargs (tagsOf file m)) (.catchInt (.signed .int) .sub)
        [] k₁ m rfl (wc := wc) (labels := labels)
    · rw [PureLocal.requestAux_apply file (op := .catchInt (.signed .int) .sub) trivial,
        Guard.catchInt_ub (op := .sub) rfl (by simpa [Unop.apply, Unop.base, Guard.apply] using hr)]
  · exact absurd (Unop.compl_int hn) hr

/-! ## The whole expression -/

/-- A finished operand binds the weak pattern. -/
theorem value_effectBind {labels : Labels} {fr : List Frame} {xs : List Access} (hfr : OneAnn fr xs)
    (v : Val) (ann : List Annot) (u : Sym) (ty : BaseType) (b : EE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    LocalReaches file labels false
      ⟨.value v, fr ++ .effectBind (.mk ann (.base (some u, ty))) b env :: k, m⟩
      ⟨.effectExpr b (extendEnv [(u, v)] env), fr ++ k, m⟩ := by
  rcases hfr with ⟨rfl, rfl⟩ | rfl
  · exact .single (.next (LoadTask.requestAux_bind m ann u ty v b env k false)
      (LoadTask.plain_effectExpr _ _))
  · refine .single (.next ?_ (LoadTask.plain_effectExpr _ _))
    rw [requestAux.eq_def]; simp [awaitsScheduling, LoadTask.requestAux_bind]

/-- **In range**: from a run of the operand to `Specified n`, `let weak a = e in pure(g)` runs
to `Specified (u.apply n)`, over the operand's annotation frame. -/
theorem runs {labels : Labels} {an pa ag : List Annot} {a : Sym} {ta : BaseType} {e : EE} {g : Pure}
    {u : Unop} (hg : guard file a g = some u) {env : Env} {n : Int} (hn : IsInt n)
    (hr : IsInt (u.apply n)) {k : List Frame} {m m₁ : Mem.Concrete.State} {fr : List Frame}
    {xs : List Access} (hfr : OneAnn fr xs)
    (run : LocalReaches file labels false
      ⟨.effectExpr e env, .effectBind (.mk pa (.base (some a, ta))) (.mk ag (.pure g)) env :: k, m⟩
      ⟨.value (spec n), fr ++ .effectBind (.mk pa (.base (some a, ta))) (.mk ag (.pure g)) env :: k, m₁⟩) :
    ∃ m₂, Touched m₁ m₂ ∧ LocalReaches file labels false
      ⟨.effectExpr (.mk an (.wseq (.mk pa (.base (some a, ta))) e (.mk ag (.pure g)))) env, k, m⟩
      ⟨.value (spec (u.apply n)), fr ++ k, m₂⟩ := by
  have s₁ : LocalReaches file labels false
      ⟨.effectExpr (.mk an (.wseq (.mk pa (.base (some a, ta))) e (.mk ag (.pure g)))) env, k, m⟩
      ⟨.effectExpr e env, .effectBind (.mk pa (.base (some a, ta))) (.mk ag (.pure g)) env :: k, m⟩ :=
    .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
  have s₂ := value_effectBind (file := file) (labels := labels) hfr (spec n) pa a ta
    (.mk ag (.pure g)) env k m₁
  obtain ⟨l', s₃⟩ := IntExpr.guard_local (file := file) (labels := labels) ag g (operand a n env)
    (fr ++ k) m₁
  let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l'}
  have s₄ := PureLocal.eval_local file (PureEval.tagsOf file m₂) (wc := false) (labels := labels)
    (guard_eval hg env hn hr) (.diagnosticLocation m₁.currentLocation :: (fr ++ k)) m₂ rfl
  refine ⟨m₂, ⟨l', m₁.lastUsed, rfl⟩, s₁.trans (run.trans (s₂.trans (s₃.trans (s₄.tail ?_))))⟩
  exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
    (LoadTask.plain_value _)

/-- **Out of range**: from a run of the operand to `Specified n` with `u.apply n` outside `int`,
`let weak a = e in pure(g)` reaches undefined behaviour. -/
theorem fails {labels : Labels} {an pa ag : List Annot} {a : Sym} {ta : BaseType} {e : EE}
    {g : Pure} {u : Unop} (hg : guard file a g = some u) {env : Env} {n : Int} (hn : IsInt n)
    (hr : ¬ IsInt (u.apply n)) {k : List Frame} {m m₁ : Mem.Concrete.State} {fr : List Frame}
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
  have s₂ := value_effectBind (file := file) (labels := labels) hfr (spec n) pa a ta
    (.mk ag (.pure g)) env k m₁
  obtain ⟨l', s₃⟩ := IntExpr.guard_local (file := file) (labels := labels) ag g (operand a n env)
    (fr ++ k) m₁
  obtain ⟨k', s₄, hend⟩ := guard_fails (labels := labels) hg env hn hr false
    (.diagnosticLocation m₁.currentLocation :: (fr ++ k)) {m₁ with currentLocation := l'}
  refine ⟨_, s₁.trans (run.trans (s₂.trans (s₃.trans s₄))), ?_, Or.inl hend⟩
  intro v h
  cases h

end Silmaril.Compile.Core.Verified.Unary
