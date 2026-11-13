module

public import Silmaril.Compiler.Core.Verified.ClosedEffSound.Defs
/-! # Closed expressions without `unseq` run under either call flag

`ClosedEff.value_local` runs a closed expression under the call flag `false`. An operand that an
arena runs while a sibling call is pending runs under the flag `true`, which only delays memory
actions and calls; closed expressions hold neither. `flat_local` runs closed expressions without
an inner `unseq` (`flat`, e.g. Cerberus's `-1`) under any flag, and `flatLit_task` packages a
closed `int` operand as an arena task.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ClosedEff

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave (LocalStep LocalReaches TaskRuns Plain)
open Fold
open Cond (OneAnn)

local notation "rv" => runtimeValue

/-- Closed-expression glue without `unseq`: `pure`, weak and strong sequences, effectful `case`. -/
def flat : EExp → Bool
  | .mk _ e => match e with
    | .pure _ => true
    | .wseq _ a b | .sseq _ a b => flat a && flat b
    | .case_ _ bs => bs.attach.all fun b => flat b.val.2
    | _ => false
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | (rcases b with ⟨⟨p, e⟩, member⟩; have h := List.sizeOf_lt_of_mem member; simp_all; omega)
    | (simp_all; omega)

theorem flat_wseq {a : List Annot} {pat : Pattern Sym} {x y : EExp}
    (h : flat (.mk a (.wseq pat x y)) = true) : flat x = true ∧ flat y = true := by
  rw [flat.eq_def] at h; simpa using h

theorem flat_sseq {a : List Annot} {pat : Pattern Sym} {x y : EExp}
    (h : flat (.mk a (.sseq pat x y)) = true) : flat x = true ∧ flat y = true := by
  rw [flat.eq_def] at h; simpa using h

theorem flat_unseq {a : List Annot} {es : List EExp} : flat (.mk a (.unseq es)) = false := by
  rw [flat.eq_def]

theorem flat_case {a : List Annot} {p : PExp} {bs : List (Pattern Sym × EExp)} {q : Pattern Sym}
    {body : EExp} (h : flat (.mk a (.case_ p bs)) = true) (hm : (q, body) ∈ bs) :
    flat body = true := by
  rw [flat.eq_def] at h
  simp only [List.all_eq_true] at h
  exact h ⟨(q, body), hm⟩ (List.mem_attach _ _)

section Runs
variable (file : Program) (labels : Labels) (wc : Bool)

theorem pure_run_any {fenv : WEnv} {denv : Env} (hr : EnvSub fenv denv) {a : List Annot} {p : PExp}
    {w : WVal} (hp : eval file Return.fuel fenv p = some w) (k : List Frame) (m : Mem.Concrete.State) :
    ∃ l, LocalReaches file labels wc ⟨.effectExpr (.mk a (.pure p)) denv, k, m⟩
      ⟨.value (rv w), k, {m with currentLocation := l}⟩ := by
  obtain ⟨l₀, hreq⟩ := LoadTask.requestAux_pure (file := file) (labels := labels) m a p denv k wc
  obtain ⟨l, s₁⟩ := LoadTask.focus_local (LoadTask.plain_pureExpr p denv) (by simpa using hreq)
  have s₂ := eval_local file labels wc Return.fuel fenv p w hp denv hr
    (.diagnosticLocation m.currentLocation :: k) {m with currentLocation := l}
  exact ⟨l, s₁.trans (s₂.tail (.next (ExitCall.ra_diagnostic file labels _ _) (Fold.plain_value _)))⟩

theorem value_bind_any {fr : List Frame} (hfr : OneAnn fr []) {v : Val} {pat : Pattern Sym}
    {xs : Bindings} (hm : matchPattern pat v = some xs) {f : Frame} {b : EE} {env : Env}
    (hf : f = .effectBind pat b env ∨ f = .strongBind pat b env) (k : List Frame)
    (m : Mem.Concrete.State) :
    LocalReaches file labels wc ⟨.value v, fr ++ f :: k, m⟩
      ⟨.effectExpr b (extendEnv xs env), fr ++ k, m⟩ := by
  have step : ∀ wc', requestAux file labels m (.value v) (f :: k) wc' =
      .next (.effectExpr b (extendEnv xs env)) k := by
    intro wc'
    rcases hf with rfl | rfl
    · exact ExitCall.ra_effectBind file labels hm b env
    · exact ExitCall.ra_strongBind file labels hm b env
  rcases hfr with ⟨rfl, -⟩ | rfl
  · exact .single (.next (step wc) (ExitCall.plain_effectExpr _ _))
  · refine .single (.next (ExitCall.ra_annotations file labels ?_ ?_ step)
      (ExitCall.plain_effectExpr _ _))
    · rcases hf with rfl | rfl <;> intro ys h <;> cases h
    · rcases hf with rfl | rfl <;> intro h <;> cases h

theorem merge_empty_any {fr fr' : List Frame} (h : OneAnn fr []) (h' : OneAnn fr' []) (v : Val)
    (k : List Frame) (m : Mem.Concrete.State) :
    ∃ fr'', OneAnn fr'' [] ∧
      LocalReaches file labels wc ⟨.value v, fr' ++ (fr ++ k), m⟩ ⟨.value v, fr'' ++ k, m⟩ := by
  rcases h' with ⟨rfl, -⟩ | rfl
  · exact ⟨fr, h, .refl⟩
  · rcases h with ⟨rfl, -⟩ | rfl
    · exact ⟨[.annotations []], .inr rfl, .refl⟩
    · refine ⟨[.annotations []], .inr rfl, ?_⟩
      exact .single (.next (by simpa using Interleave.requestAux_value_merge file labels m v [] [] k wc)
        (LoadTask.plain_value v))

/-- **A closed expression without `unseq` runs** to its folded value under any call flag,
changing only the current location. -/
theorem flat_local : (e : EExp) → flat e = true → ∀ {fenv : WEnv} {denv : Env} {w : WVal},
    EnvSub fenv denv → value file fenv e = some w → ∀ (k : List Frame) (m : Mem.Concrete.State),
    ∃ l fr, OneAnn fr [] ∧ LocalReaches file labels wc ⟨.effectExpr e denv, k, m⟩
      ⟨.value (rv w), fr ++ k, {m with currentLocation := l}⟩
  | e, hflat, fenv, denv, w, hr, h, k, m => by
    rcases value_inv h with ⟨a, p, he, hp⟩ | ⟨a, pat, x, y, v, xs, hxy, hx, hxs, hy⟩ |
      ⟨a, es, ws, he, hws, rfl⟩ | ⟨a, p, bs, v, he, hc, hp, hb⟩
    · obtain ⟨l, r⟩ := pure_run_any file labels wc hr hp k m
      exact ⟨l, [], .inl ⟨rfl, rfl⟩, by rw [he]; simpa using r⟩
    · have hm : matchPattern pat (rv v) = some (bmap xs) := by rw [matchP_rv, hxs]; rfl
      have hlt : sizeOf x < sizeOf e ∧ sizeOf y < sizeOf e := by
        rcases hxy with rfl | rfl
        · exact sizeOf_wseq_lt
        · exact sizeOf_sseq_lt
      rcases hxy with he | he
      · obtain ⟨fx, fy⟩ := flat_wseq (he ▸ hflat)
        obtain ⟨l₁, fr₁, h₁, r₁⟩ := flat_local x fx hr hx (.effectBind pat y denv :: k) m
        have r₂ := value_bind_any file labels wc h₁ hm (f := .effectBind pat y denv) (.inl rfl) k
          {m with currentLocation := l₁}
        obtain ⟨l₂, fr₂, h₂, r₃⟩ := flat_local y fy (hr.extend xs) hy (fr₁ ++ k)
          {m with currentLocation := l₁}
        obtain ⟨fr₃, h₃, r₄⟩ := merge_empty_any file labels wc h₁ h₂ (rv w) k
          {m with currentLocation := l₂}
        rw [he]
        exact ⟨l₂, fr₃, h₃, .head (.next (ExitCall.ra_wseq file labels _ _ _ _)
          (ExitCall.plain_effectExpr _ _)) (r₁.trans (r₂.trans (r₃.trans r₄)))⟩
      · obtain ⟨fx, fy⟩ := flat_sseq (he ▸ hflat)
        obtain ⟨l₁, fr₁, h₁, r₁⟩ := flat_local x fx hr hx (.strongBind pat y denv :: k) m
        have r₂ := value_bind_any file labels wc h₁ hm (f := .strongBind pat y denv) (.inr rfl) k
          {m with currentLocation := l₁}
        obtain ⟨l₂, fr₂, h₂, r₃⟩ := flat_local y fy (hr.extend xs) hy (fr₁ ++ k)
          {m with currentLocation := l₁}
        obtain ⟨fr₃, h₃, r₄⟩ := merge_empty_any file labels wc h₁ h₂ (rv w) k
          {m with currentLocation := l₂}
        rw [he]
        exact ⟨l₂, fr₃, h₃, .head (.next (ExitCall.ra_sseq file labels _ _ _ _)
          (ExitCall.plain_effectExpr _ _)) (r₁.trans (r₂.trans (r₃.trans r₄)))⟩
    · rw [he, flat_unseq] at hflat
      cases hflat
    · obtain ⟨q, body, xs, hmem, hsel, hv⟩ := branch_inv hb
      have hlt : sizeOf body < sizeOf e := he ▸ sizeOf_case_lt hmem
      have fb := flat_case (he ▸ hflat) hmem
      obtain ⟨l₀, hreq⟩ := Cond.requestAux_case (file := file) (labels := labels) m a p bs denv k wc
      obtain ⟨l₁, s₁⟩ := LoadTask.focus_local (LoadTask.plain_pureExpr p denv) (by simpa using hreq)
      have s₂ := eval_local file labels wc Return.fuel fenv p v hp denv hr
        (.effectCase bs denv :: k) {m with currentLocation := l₁}
      have s₃ : LocalReaches file labels wc
          ⟨.value (rv v), .effectCase bs denv :: k, {m with currentLocation := l₁}⟩
          ⟨.effectExpr body (extendEnv (bmap xs) denv), k, {m with currentLocation := l₁}⟩ :=
        .single (.next (Cond.requestAux_effectCase (file := file) (labels := labels) _ (rv v) bs denv k
          wc hsel) (ExitCall.plain_effectExpr _ _))
      obtain ⟨l₂, fr, hfr, s₄⟩ := flat_local body fb (hr.extend xs) hv k {m with currentLocation := l₁}
      rw [he]
      exact ⟨l₂, fr, hfr, s₁.trans (s₂.trans (s₃.trans s₄))⟩
termination_by e => sizeOf e
decreasing_by all_goals first | assumption | exact hlt.1 | exact hlt.2

/-- A closed `int` operand without `unseq`. -/
def flatLit (file : Doc) (e : EExp) : Option Int := if flat e then lit file e else none

theorem flatLit_range {e : EExp} {n : Int} (h : flatLit file e = some n) :
    -2147483648 ≤ n ∧ n ≤ 2147483647 := by
  unfold flatLit at h
  split at h
  · exact (lit_inv file h).2
  · cases h

/-- **A closed `int` operand runs as an arena task** under any call flag. -/
theorem flatLit_task {e : EExp} {n : Int} (h : flatLit file e = some n) (env : Env)
    (m : Mem.Concrete.State) :
    ∃ l, TaskRuns file labels wc ⟨.effectExpr e env, [], m⟩ (.loaded (.specified (.integer n))) []
      {m with currentLocation := l} := by
  unfold flatLit at h
  split at h
  · rename_i hf
    obtain ⟨l, fr, hfr, r⟩ := flat_local file labels wc e hf (EnvSub.empty env) (lit_inv file h).1 [] m
    refine ⟨l, fr ++ [], r, ?_⟩
    rcases hfr with ⟨rfl, -⟩ | rfl <;> rfl
  · cases h

end Runs

end Silmaril.Compile.Core.Verified.ClosedEff
