module

public import Silmaril.Compiler.Core.Verified.ClosedEff.Defs
public import Silmaril.Compiler.Core.Verified.FoldLocal.Defs
public import Silmaril.Compiler.Core.Verified.ExitCall.Defs
public import Silmaril.Compiler.Core.Verified.IntExpr.Defs

/-! # Closed effectful expressions run to their folded value

`value_local`: when `ClosedEff.value` folds `e` to `w`, local steps of the Core dynamics reduce
`e`, in any environment that agrees with the folder's on the symbols it binds (`Fold.EnvSub`),
above any continuation, to `runtimeValue w`, over at most one annotation frame with no access,
changing only the current location of the memory. `value_noCall`: such an expression holds no
procedure call, so it is a task of any enclosing `unseq`. `lit_local` is the case the
expression fragments use: `ClosedEff.lit` in the empty folder environment.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ClosedEff

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave (LocalStep LocalReaches TaskRuns Plain)
open Fold
open Cond (OneAnn)

local notation "rv" => runtimeValue

/-! ## Inversions -/

section Inversions
variable {file : Program}

theorem value_inv {env : WEnv} {e : EExp} {w : WVal} (h : value file env e = some w) :
    (∃ a p, e = .mk a (.pure p) ∧ eval file Return.fuel env p = some w) ∨
    (∃ a pat x y v xs, (e = .mk a (.wseq pat x y) ∨ e = .mk a (.sseq pat x y)) ∧
      value file env x = some v ∧ matchP pat v = some xs ∧ value file (extend xs env) y = some w) ∨
    (∃ a es ws, e = .mk a (.unseq es) ∧ values file env es = some ws ∧ w = .tuple ws) ∨
    (∃ a p bs v, e = .mk a (.case_ p bs) ∧ hasCCall e = false ∧
      eval file Return.fuel env p = some v ∧ branch file env v bs = some w) := by
  unfold value at h
  split at h
  · exact .inl ⟨_, _, rfl, h⟩
  · split at h
    · split at h
      · exact .inr (.inl ⟨_, _, _, _, _, _, .inl rfl, by assumption, by assumption, h⟩)
      · cases h
    · cases h
  · split at h
    · split at h
      · exact .inr (.inl ⟨_, _, _, _, _, _, .inr rfl, by assumption, by assumption, h⟩)
      · cases h
    · cases h
  · obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inr (.inr (.inl ⟨_, _, _, rfl, hws, rfl⟩))
  · split at h
    · cases h
    · rename_i hc
      split at h
      · exact .inr (.inr (.inr ⟨_, _, _, _, rfl, by simpa [calls_eq] using hc, by assumption, h⟩))
      · cases h
  · cases h

theorem values_cons {env : WEnv} {e : EExp} {es : List EExp} {ws : List WVal}
    (h : values file env (e :: es) = some ws) :
    ∃ w ws', value file env e = some w ∧ values file env es = some ws' ∧ ws = w :: ws' := by
  unfold values at h
  split at h
  · rename_i w ws' hw hws
    cases h
    exact ⟨w, ws', hw, hws, rfl⟩
  · cases h

theorem values_mem {env : WEnv} : ∀ {es : List EExp} {ws : List WVal},
    values file env es = some ws → ∀ e ∈ es, ∃ w, value file env e = some w
  | [], _, _, e, he => by cases he
  | e :: es, ws, h, e', he' => by
    obtain ⟨w, ws', hw, hes, rfl⟩ := values_cons h
    rcases List.mem_cons.mp he' with rfl | he'
    · exact ⟨w, hw⟩
    · exact values_mem hes e' he'

theorem branch_inv {env : WEnv} {v w : WVal} : ∀ {bs : List (Pattern Sym × EExp)},
    branch file env v bs = some w →
    ∃ p body xs, (p, body) ∈ bs ∧ selectCase (rv v) bs = some (bmap xs, body) ∧
      value file (extend xs env) body = some w
  | [], h => by simp [branch] at h
  | (p, body) :: rest, h => by
    unfold branch at h
    cases hm : matchP p v with
    | some xs =>
      rw [hm] at h
      exact ⟨p, body, xs, List.mem_cons_self, by simp [selectCase, matchP_rv, hm], h⟩
    | none =>
      rw [hm] at h
      obtain ⟨p', body', xs, hmem, hsel, hv⟩ := branch_inv h
      exact ⟨p', body', xs, List.mem_cons_of_mem _ hmem,
        by simp [selectCase, matchP_rv, hm, hsel], hv⟩

end Inversions

/-! ## No calls -/

section NoCall
variable {file : Program}

theorem sizeOf_unseq_lt {a : List Annot} {es : List EExp} {e' : EExp} (h : e' ∈ es) :
    sizeOf e' < sizeOf (Expr.mk a (.unseq es) : EExp) := by
  have := List.sizeOf_lt_of_mem h
  simp only [Expr.mk.sizeOf_spec, ExprNode.unseq.sizeOf_spec]
  omega

theorem sizeOf_case_lt {a : List Annot} {p : PExp} {bs : List (Pattern Sym × EExp)}
    {q : Pattern Sym} {body : EExp} (h : (q, body) ∈ bs) :
    sizeOf body < sizeOf (Expr.mk a (.case_ p bs) : EExp) := by
  have := List.sizeOf_lt_of_mem h
  simp only [Expr.mk.sizeOf_spec, ExprNode.case_.sizeOf_spec, Prod.mk.sizeOf_spec] at this ⊢
  omega

theorem sizeOf_wseq_lt {a : List Annot} {pat : Pattern Sym} {x y : EExp} :
    sizeOf x < sizeOf (Expr.mk a (.wseq pat x y) : EExp) ∧
      sizeOf y < sizeOf (Expr.mk a (.wseq pat x y) : EExp) := by
  simp only [Expr.mk.sizeOf_spec, ExprNode.wseq.sizeOf_spec]
  omega

theorem sizeOf_sseq_lt {a : List Annot} {pat : Pattern Sym} {x y : EExp} :
    sizeOf x < sizeOf (Expr.mk a (.sseq pat x y) : EExp) ∧
      sizeOf y < sizeOf (Expr.mk a (.sseq pat x y) : EExp) := by
  simp only [Expr.mk.sizeOf_spec, ExprNode.sseq.sizeOf_spec]
  omega

/-- Closed expressions hold no call. -/
theorem value_noCall : (e : EExp) → ∀ {env : WEnv} {w : WVal}, value file env e = some w →
    hasCCall e = false
  | e, env, w, h => by
    rcases value_inv h with ⟨a, p, he, -⟩ | ⟨a, pat, x, y, v, xs, hxy, hx, -, hy⟩ |
      ⟨a, es, ws, he, hws, -⟩ | ⟨a, p, bs, v, -, hb, -, -⟩
    · rw [he, hasCCall.eq_def]
    · have hlt : sizeOf x < sizeOf e ∧ sizeOf y < sizeOf e := by
        rcases hxy with rfl | rfl
        · exact sizeOf_wseq_lt
        · exact sizeOf_sseq_lt
      have hx' := value_noCall x hx
      have hy' := value_noCall y hy
      rcases hxy with rfl | rfl <;> (rw [hasCCall.eq_def]; simp [hx', hy'])
    · have hall : ∀ e' ∈ es, hasCCall e' = false := fun e' he' => by
        have hlt : sizeOf e' < sizeOf e := he ▸ sizeOf_unseq_lt he'
        obtain ⟨w', hw'⟩ := values_mem hws e' he'
        exact value_noCall e' hw'
      rw [he, hasCCall.eq_def]
      simp only [List.any_eq_false]
      intro e' he'
      simpa using hall e'.1 e'.2
    · exact hb
termination_by e => sizeOf e
decreasing_by all_goals first | assumption | exact hlt.1 | exact hlt.2

end NoCall

/-! ## Runs -/

section Runs
variable (file : Program) (labels : Labels)

/-- `pure(p)` with `p` folding runs to its value above any continuation. -/
theorem pure_run {fenv : WEnv} {denv : Env} (hr : EnvSub fenv denv) {a : List Annot} {p : PExp}
    {w : WVal} (hp : eval file Return.fuel fenv p = some w) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ l, LocalReaches file labels false ⟨.effectExpr (.mk a (.pure p)) denv, k, m⟩
      ⟨.value (rv w), k, {m with currentLocation := l}⟩ := by
  obtain ⟨l, s₁⟩ := IntExpr.guard_local (file := file) (labels := labels) a p denv k m
  have s₂ := eval_local file labels false Return.fuel fenv p w hp denv hr
    (.diagnosticLocation m.currentLocation :: k) {m with currentLocation := l}
  exact ⟨l, s₁.trans (s₂.tail (.next (ExitCall.ra_diagnostic file labels _ _) (Fold.plain_value _)))⟩

/-- A value over at most one empty annotation frame enters the body of a weak or strong bind. -/
theorem value_bind {fr : List Frame} (hfr : OneAnn fr []) {v : Val} {pat : Pattern Sym}
    {xs : Bindings} (hm : matchPattern pat v = some xs) {f : Frame} {b : EE} {env : Env}
    (hf : f = .effectBind pat b env ∨ f = .strongBind pat b env) (k : List Frame)
    (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.value v, fr ++ f :: k, m⟩
      ⟨.effectExpr b (extendEnv xs env), fr ++ k, m⟩ := by
  have step : ∀ wc', requestAux file labels m (.value v) (f :: k) wc' =
      .next (.effectExpr b (extendEnv xs env)) k := by
    intro wc'
    rcases hf with rfl | rfl
    · exact ExitCall.ra_effectBind file labels hm b env
    · exact ExitCall.ra_strongBind file labels hm b env
  rcases hfr with ⟨rfl, -⟩ | rfl
  · exact .single (.next (step false) (ExitCall.plain_effectExpr _ _))
  · refine .single (.next (ExitCall.ra_annotations file labels ?_ ?_ step)
      (ExitCall.plain_effectExpr _ _))
    · rcases hf with rfl | rfl <;> intro ys h <;> cases h
    · rcases hf with rfl | rfl <;> intro h <;> cases h

/-- Two runs' empty annotation frames merge into at most one empty frame. -/
theorem merge_empty {fr fr' : List Frame} (h : OneAnn fr []) (h' : OneAnn fr' []) (v : Val)
    (k : List Frame) (m : Mem.Concrete.State) :
    ∃ fr'', OneAnn fr'' [] ∧
      LocalReaches file labels false ⟨.value v, fr' ++ (fr ++ k), m⟩ ⟨.value v, fr'' ++ k, m⟩ := by
  obtain ⟨zs, fr'', h'', hz, run⟩ := Cond.merge (file := file) (labels := labels) h h' v k m
  have : zs = [] := List.eq_nil_iff_forall_not_mem.mpr fun a ha => by simpa using hz a ha
  subst this
  exact ⟨fr'', h'', run⟩

/-- The value of a task, for `unseq_tasks_local`. -/
def taskVal (fenv : WEnv) (e : EE) : Val := ((value file fenv e).map rv).getD .unit

theorem taskVal_values {fenv : WEnv} : ∀ {es : List EExp} {ws : List WVal},
    values file fenv es = some ws → es.map (taskVal file fenv) = ws.map rv
  | [], ws, h => by cases h; rfl
  | e :: es, ws, h => by
    obtain ⟨w, ws', hw, hes, rfl⟩ := values_cons h
    simp [taskVal, hw, taskVal_values hes]

/-- **A closed expression runs** to its folded value, changing only the current location. -/
theorem value_local : (e : EExp) → ∀ {fenv : WEnv} {denv : Env} {w : WVal}, EnvSub fenv denv →
    value file fenv e = some w → ∀ (k : List Frame) (m : Mem.Concrete.State),
    ∃ l fr, OneAnn fr [] ∧ LocalReaches file labels false ⟨.effectExpr e denv, k, m⟩
      ⟨.value (rv w), fr ++ k, {m with currentLocation := l}⟩
  | e, fenv, denv, w, hr, h, k, m => by
    rcases value_inv h with ⟨a, p, he, hp⟩ | ⟨a, pat, x, y, v, xs, hxy, hx, hxs, hy⟩ |
      ⟨a, es, ws, he, hws, rfl⟩ | ⟨a, p, bs, v, he, hc, hp, hb⟩
    · obtain ⟨l, r⟩ := pure_run file labels hr hp k m
      exact ⟨l, [], .inl ⟨rfl, rfl⟩, by rw [he]; simpa using r⟩
    · have hm : matchPattern pat (rv v) = some (bmap xs) := by rw [matchP_rv, hxs]; rfl
      have hlt : sizeOf x < sizeOf e ∧ sizeOf y < sizeOf e := by
        rcases hxy with rfl | rfl
        · exact sizeOf_wseq_lt
        · exact sizeOf_sseq_lt
      rcases hxy with he | he
      · obtain ⟨l₁, fr₁, h₁, r₁⟩ := value_local x hr hx (.effectBind pat y denv :: k) m
        have r₂ := value_bind file labels h₁ hm (f := .effectBind pat y denv) (.inl rfl) k
          {m with currentLocation := l₁}
        obtain ⟨l₂, fr₂, h₂, r₃⟩ := value_local y (hr.extend xs) hy (fr₁ ++ k)
          {m with currentLocation := l₁}
        obtain ⟨fr₃, h₃, r₄⟩ := merge_empty file labels h₁ h₂ (rv w) k
          {m with currentLocation := l₂}
        rw [he]
        exact ⟨l₂, fr₃, h₃, .head (.next (ExitCall.ra_wseq file labels _ _ _ _)
          (ExitCall.plain_effectExpr _ _)) (r₁.trans (r₂.trans (r₃.trans r₄)))⟩
      · obtain ⟨l₁, fr₁, h₁, r₁⟩ := value_local x hr hx (.strongBind pat y denv :: k) m
        have r₂ := value_bind file labels h₁ hm (f := .strongBind pat y denv) (.inr rfl) k
          {m with currentLocation := l₁}
        obtain ⟨l₂, fr₂, h₂, r₃⟩ := value_local y (hr.extend xs) hy (fr₁ ++ k)
          {m with currentLocation := l₁}
        obtain ⟨fr₃, h₃, r₄⟩ := merge_empty file labels h₁ h₂ (rv w) k
          {m with currentLocation := l₂}
        rw [he]
        exact ⟨l₂, fr₃, h₃, .head (.next (ExitCall.ra_sseq file labels _ _ _ _)
          (ExitCall.plain_effectExpr _ _)) (r₁.trans (r₂.trans (r₃.trans r₄)))⟩
    · have hrun : ∀ e' ∈ es, ∀ m : Mem.Concrete.State, ∃ l, TaskRuns file labels false
          ⟨.effectExpr e' denv, [], m⟩ (taskVal file fenv e') [] {m with currentLocation := l} := by
        intro e' he' m
        have hlt : sizeOf e' < sizeOf e := he ▸ sizeOf_unseq_lt he'
        obtain ⟨w', hw'⟩ := values_mem hws e' he'
        obtain ⟨l, fr, hfr, r⟩ := value_local e' hr hw' [] m
        refine ⟨l, fr, by simpa [taskVal, hw'] using r, ?_⟩
        rcases hfr with ⟨rfl, -⟩ | rfl <;> rfl
      obtain ⟨l, ru⟩ := ExitCall.unseq_tasks_local file labels (taskVal file fenv) hrun
        (fun e' he' => by
          obtain ⟨w', hw'⟩ := values_mem hws e' he'
          exact value_noCall e' hw') a k m
      rw [taskVal_values file hws] at ru
      refine ⟨l, [.annotations []], .inr rfl, ?_⟩
      rw [show rv (.tuple ws) = (.tuple (ws.map rv) : Val) by
        rw [← runtimeValues_eq]; rfl, he]
      exact ru
    · obtain ⟨q, body, xs, hmem, hsel, hv⟩ := branch_inv hb
      have hlt : sizeOf body < sizeOf e := he ▸ sizeOf_case_lt hmem
      obtain ⟨l₀, hreq⟩ := Cond.requestAux_case (file := file) (labels := labels) m a p bs denv k false
      obtain ⟨l₁, s₁⟩ := LoadTask.focus_local (LoadTask.plain_pureExpr p denv) (by simpa using hreq)
      have s₂ := eval_local file labels false Return.fuel fenv p v hp denv hr
        (.effectCase bs denv :: k) {m with currentLocation := l₁}
      have s₃ : LocalReaches file labels false
          ⟨.value (rv v), .effectCase bs denv :: k, {m with currentLocation := l₁}⟩
          ⟨.effectExpr body (extendEnv (bmap xs) denv), k, {m with currentLocation := l₁}⟩ :=
        .single (.next (Cond.requestAux_effectCase (file := file) (labels := labels) _ (rv v) bs denv k
          false hsel) (ExitCall.plain_effectExpr _ _))
      obtain ⟨l₂, fr, hfr, s₄⟩ := value_local body (hr.extend xs) hv k {m with currentLocation := l₁}
      rw [he]
      exact ⟨l₂, fr, hfr, s₁.trans (s₂.trans (s₃.trans s₄))⟩
termination_by e => sizeOf e
decreasing_by all_goals first | assumption | exact hlt.1 | exact hlt.2

theorem lit_inv {e : EExp} {n : Int} (h : lit file e = some n) :
    value file ∅ e = some (.loaded (.specified (.integer n))) ∧
      -2147483648 ≤ n ∧ n ≤ 2147483647 := by
  unfold lit at h
  split at h
  · rename_i n' hv
    split at h
    · rename_i hn
      cases h
      exact ⟨hv, hn⟩
    · cases h
  · cases h

/-- **A closed `int` expression runs to its literal**, in any environment, above any
continuation. -/
theorem lit_local {e : EExp} {n : Int} (h : lit file e = some n) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) :
    ∃ l fr, OneAnn fr [] ∧ LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
      ⟨.value (.loaded (.specified (.integer n))), fr ++ k, {m with currentLocation := l}⟩ :=
  value_local file labels e (EnvSub.empty env) (lit_inv file h).1 k m

theorem lit_noCall {e : EExp} {n : Int} (h : lit file e = some n) : hasCCall e = false :=
  value_noCall e (lit_inv file h).1

end Runs

end Silmaril.Compile.Core.Verified.ClosedEff
