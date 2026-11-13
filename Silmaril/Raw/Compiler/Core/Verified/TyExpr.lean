module

public import Silmaril.Compiler.Core.Verified.TyUnary.Defs
public import Silmaril.Compiler.Core.Verified.TyECmp.Defs
public import Silmaril.Compiler.Core.Verified.ClosedEffSound.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false
/-! # Integer expressions of every supported type over several locals

`StateExpr` for locals and operators of every supported integer type (`TyActions.supported`).
`term file e = some t` recognises Cerberus's elaboration of an integer expression:

* a closed expression that folds to an integer (`fold`, `ClosedEff.value`: constants of any
  integer type, casts, shifts, `/`, `%`, comparisons) or a literal `pure(Specified(n))`
  (`.lit n`);
* a read `let weak p = pure(x) in load(T, p)` of the local `x` of type `T` (`.var x.key T`);
* `e₁ op e₂`, `let weak (a, b) = unseq(e₁, e₂) in pure(guard)` with a guard of `TyGuard`
  (`.bin g t₁ t₂`): `+`, `-`, `*` at a signed type (undefined out of range), at an unsigned
  type (wrapping), and the comparisons, each operand converted to the operator's type.

`t.val σ` is the value with each local `q` holding `σ q`, computed exactly; `t.Ok σ` says no
signed operator leaves its type. From a memory where every read local `q` of type `T` points to
the `T` object holding `σ q` (`Locs`):

* `term_runs`: if `t.Ok σ`, local steps reach `Specified (t.val σ)` with read accesses only,
  over any continuation;
* `term_fails`: otherwise they reach undefined behaviour `UB036_exceptional_condition`.

`close ds t` replaces each read of `q` by the closed term `ds q`:
`(close ds t).val zero = t.val (values ds)`. The statement fragment (`TyState`) compiles a
sequence of assignments to one closed term that the Lir code (`TyLir`) computes at run time.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyExpr

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (tagsOf)
open Silmaril.Cerberus.Core.Interleave (LocalStep LocalReaches TaskRuns taskFlag unseqTasks)
open Silmaril.Cerberus.Core.ArenaFail (Fails)
open ReturnLit (Eff lookup_key)
open LoadTask (Touched ReadTask)
open ConvInt (Pure)
open Cond (OneAnn)
open IntExpr (spec overflow unseq_pair guard_local requestAux_tuple_bind)
open TyActions (supported width signed Fits TSlot)
open TyGuard (G tguard)

/-- The name of a local: its symbol's key. -/
abbrev Key := Digest × Nat

/-- Integer expressions over several typed locals. -/
inductive Term where
  | lit (n : Int)
  | var (q : Key) (ity : IntegerType)
  | bin (g : G) (a b : Term)
  /-- A relational comparison (an effect-level case). -/
  | ebin (g : G) (a b : Term)
  /-- A unary minus or a cast: the guard with first operand `0`. -/
  | un (g : G) (a : Term)

/-- The locals `t` reads, with the types it reads them at. -/
def Term.vars : Term → List (Key × IntegerType)
  | .lit _ => []
  | .var q ity => [(q, ity)]
  | .bin _ a b => a.vars ++ b.vars
  | .ebin _ a b => a.vars ++ b.vars
  | .un _ a => a.vars

/-- A closed expression that folds to the integer `n` (constant folding, `ClosedEff.value`). -/
def fold (file : File Codec.wireModel Unit Unit) (e : Eff) : Option Int :=
  match ClosedEff.value file ∅ e with
  | some (.loaded (.specified (.integer n))) => some n
  | _ => none

theorem fold_inv {file : File Codec.wireModel Unit Unit} {e : Eff} {n : Int} (h : fold file e = some n) :
    ClosedEff.value file ∅ e = some (.loaded (.specified (.integer n))) := by
  unfold fold at h
  split at h
  · cases h; assumption
  · cases h

/-- The recogniser. -/
def term (file : File Codec.wireModel Unit Unit) (e : Eff) : Option Term :=
  match fold file e with
  | some n => some (.lit n)
  | none => match e with
  | .mk _ (.pure (.mk _ () (.val (.loaded (.specified (.integer n)))))) => some (.lit n)
  | .mk _ (.wseq (.mk _ (.base (some p, _))) (.mk _ (.pure (.mk _ () (.sym x'))))
      (.mk _ (.action (.mk .pos (.mk _ _ (.load
        (.mk _ () (.val (.ctype (.mk _ (.basic (.integer ity))))))
        (.mk _ () (.sym p')) .na)))))) =>
      if p'.key = p.key ∧ supported ity = true then some (.var x'.key ity) else none
  | .mk _ (.wseq (.mk _ (.ctor .tuple [.mk _ (.base (some a, _)), .mk _ (.base (some b, _))]))
      (.mk _ (.unseq [e₁, e₂])) (.mk _ (.pure g))) =>
      match term file e₁, term file e₂, tguard file a b g with
      | some t₁, some t₂, some gd => some (.bin gd t₁ t₂)
      | _, _, _ => none
  | .mk _ (.wseq (.mk _ (.ctor .tuple [.mk _ (.base (some a, _)), .mk _ (.base (some b, _))]))
      (.mk _ (.unseq [e₁, e₂])) (.mk ag (.case_ scr bs))) =>
      match term file e₁, term file e₂, TyECmp.eguard file a b (.mk ag (.case_ scr bs)) with
      | some t₁, some t₂, some gd => some (.ebin gd t₁ t₂)
      | _, _, _ => none
  | .mk _ (.wseq (.mk _ (.base (some a, _))) e₁ (.mk _ (.pure g))) =>
      match term file e₁, TyUnary.uguard file a g with
      | some t, some u => some (.un u t)
      | _, _ => none
  | _ => none
termination_by sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- The value with each local `q` holding `σ q`. -/
def Term.val (σ : Key → Int) : Term → Int
  | .lit c => c
  | .var q _ => σ q
  | .bin g a b => g.val (a.val σ) (b.val σ)
  | .ebin g a b => g.val (a.val σ) (b.val σ)
  | .un g a => g.val 0 (a.val σ)

/-- No signed operator leaves its type. -/
def Term.Ok (σ : Key → Int) : Term → Prop
  | .lit _ => True
  | .var _ _ => True
  | .bin g a b => a.Ok σ ∧ b.Ok σ ∧ g.Ok (a.val σ) (b.val σ)
  | .ebin g a b => a.Ok σ ∧ b.Ok σ ∧ g.Ok (a.val σ) (b.val σ)
  | .un g a => a.Ok σ ∧ g.Ok 0 (a.val σ)

/-! ## Closing over the assigned expressions -/

/-- The valuation of closed terms. -/
def zero : Key → Int := fun _ => 0

/-- Each read of `q` replaced by the closed term `ds q`. -/
def close (ds : Key → Term) : Term → Term
  | .lit c => .lit c
  | .var q _ => ds q
  | .bin g a b => .bin g (close ds a) (close ds b)
  | .ebin g a b => .ebin g (close ds a) (close ds b)
  | .un g a => .un g (close ds a)

/-- The values of the closed terms. -/
def values (ds : Key → Term) : Key → Int := fun q => (ds q).val zero

theorem close_val (ds : Key → Term) : (t : Term) → (close ds t).val zero = t.val (values ds)
  | .lit _ => rfl
  | .var _ _ => rfl
  | .bin g a b => by simp [close, Term.val, close_val ds a, close_val ds b]
  | .ebin g a b => by simp [close, Term.val, close_val ds a, close_val ds b]
  | .un g a => by simp [close, Term.val, close_val ds a]

theorem close_ok (ds : Key → Term) : (t : Term) →
    (∀ q ∈ t.vars, (ds q.1).Ok zero) → t.Ok (values ds) → (close ds t).Ok zero
  | .lit _, _, h => h
  | .var q ity, hd, _ => hd (q, ity) (by simp [Term.vars])
  | .bin g a b, hd, ⟨ha, hb, hr⟩ => by
    refine ⟨close_ok ds a (fun q hq => hd q (by simp [Term.vars, hq])) ha,
      close_ok ds b (fun q hq => hd q (by simp [Term.vars, hq])) hb, ?_⟩
    rw [close_val, close_val]; exact hr
  | .ebin g a b, hd, ⟨ha, hb, hr⟩ => by
    refine ⟨close_ok ds a (fun q hq => hd q (by simp [Term.vars, hq])) ha,
      close_ok ds b (fun q hq => hd q (by simp [Term.vars, hq])) hb, ?_⟩
    rw [close_val, close_val]; exact hr
  | .un g a, hd, ⟨ha, hr⟩ => by
    refine ⟨close_ok ds a (fun q hq => hd q (by simpa [Term.vars] using hq)) ha, ?_⟩
    rw [close_val]; exact hr

theorem ok_of_close (ds : Key → Term) : (t : Term) → (close ds t).Ok zero → t.Ok (values ds)
  | .lit _, h => h
  | .var _ _, _ => trivial
  | .bin g a b, ⟨ha, hb, hr⟩ => by
    refine ⟨ok_of_close ds a ha, ok_of_close ds b hb, ?_⟩
    rw [← close_val, ← close_val]; exact hr
  | .ebin g a b, ⟨ha, hb, hr⟩ => by
    refine ⟨ok_of_close ds a ha, ok_of_close ds b hb, ?_⟩
    rw [← close_val, ← close_val]; exact hr
  | .un g a, ⟨ha, hr⟩ => by
    refine ⟨ok_of_close ds a ha, ?_⟩
    rw [← close_val]; exact hr

/-! ## Inversion -/

theorem term_lit {file : File Codec.wireModel Unit Unit} {e : Eff} {c : Int}
    (h : term file e = some (.lit c)) : fold file e = some c ∨
    ∃ an pa, e = .mk an (.pure (.mk pa () (.val (.loaded (.specified (.integer c)))))) := by
  unfold term at h
  split at h
  · rename_i n hn; cases h; exact .inl hn
  · split at h
    · cases h; exact .inr ⟨_, _, rfl⟩
    all_goals (repeat' split at h)
    all_goals cases h

theorem term_var {file : File Codec.wireModel Unit Unit} {e : Eff} {q : Key} {ity : IntegerType}
    (h : term file e = some (.var q ity)) :
    ∃ (a0 pa a1 a2 la a3 c1 a4 : List Annot) (pt : BaseType) (p p' x' : Sym) (l : Loc) (u : Unit),
      e = TyGuard.loadExpr a0 pa a1 a2 la a3 c1 a4 pt p p' x' l u ity ∧ x'.key = q ∧
        p'.key = p.key ∧ supported ity = true := by
  unfold term at h
  split at h
  · cases h
  split at h
  · cases h
  · split at h
    · rename_i hc
      cases h; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, hc.1, hc.2⟩
    · cases h
  all_goals (repeat' split at h)
  all_goals cases h

theorem term_bin {file : File Codec.wireModel Unit Unit} {e : Eff} {g : G}
    {t₁ t₂ : Term} (h : term file e = some (.bin g t₁ t₂)) :
    ∃ (an pp p1 p2 au ag : List Annot) (a b : Sym) (ta tb : BaseType) (e₁ e₂ : Eff) (gp : Pure),
      e = .mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))]))
        (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure gp))) ∧
      tguard file a b gp = some g ∧ term file e₁ = some t₁ ∧ term file e₂ = some t₂ := by
  unfold term at h
  split at h
  · cases h
  split at h
  · cases h
  · split at h <;> cases h
  · split at h
    · cases h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by assumption, by assumption, by assumption⟩
    · cases h
  all_goals (repeat' split at h)
  all_goals cases h

theorem term_ebin {file : File Codec.wireModel Unit Unit} {e : Eff} {g : G}
    {t₁ t₂ : Term} (h : term file e = some (.ebin g t₁ t₂)) :
    ∃ (an pp p1 p2 au : List Annot) (a b : Sym) (ta tb : BaseType) (e₁ e₂ ge : Eff),
      e = .mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))]))
        (.mk au (.unseq [e₁, e₂])) ge) ∧
      TyECmp.eguard file a b ge = some g ∧ term file e₁ = some t₁ ∧ term file e₂ = some t₂ := by
  unfold term at h
  split at h
  · cases h
  split at h
  · cases h
  · split at h <;> cases h
  · split at h <;> cases h
  · split at h
    · cases h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, by assumption, by assumption, by assumption⟩
    · cases h
  all_goals (repeat' split at h)
  all_goals cases h

theorem term_un {file : File Codec.wireModel Unit Unit} {e : Eff} {g : G} {t : Term}
    (h : term file e = some (.un g t)) :
    ∃ (an pa ag : List Annot) (a : Sym) (ta : BaseType) (e₁ : Eff) (gp : Pure),
      e = .mk an (.wseq (.mk pa (.base (some a, ta))) e₁ (.mk ag (.pure gp))) ∧
      TyUnary.uguard file a gp = some g ∧ term file e₁ = some t := by
  unfold term at h
  split at h
  · cases h
  split at h
  · cases h
  · split at h <;> cases h
  · split at h <;> cases h
  · split at h <;> cases h
  · split at h
    · cases h
      exact ⟨_, _, _, _, _, _, _, rfl, by assumption, by assumption⟩
    · cases h
  all_goals cases h

/-- Recognised expressions make no procedure call. -/
theorem term_calls {file : File Codec.wireModel Unit Unit} :
    (t : Term) → {e : Eff} → term file e = some t → hasCCall e = false
  | .lit _, _, h => by
    rcases term_lit h with hf | ⟨an, pa, rfl⟩
    · exact ClosedEff.value_noCall _ (fold_inv hf)
    · rw [hasCCall.eq_def]
  | .var _ _, _, h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := term_var h
    simp [TyGuard.loadExpr, hasCCall]
  | .bin _ t₁ t₂, _, h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, e₁, e₂, _, rfl, _, h₁, h₂⟩ := term_bin h
    simp [hasCCall, term_calls t₁ h₁, term_calls t₂ h₂]
  | .ebin _ t₁ t₂, _, h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, e₁, e₂, ge, rfl, hg, h₁, h₂⟩ := term_ebin h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, -⟩ := TyECmp.eguard_parts hg
    simp [hasCCall, term_calls t₁ h₁, term_calls t₂ h₂]
  | .un _ t₁, _, h => by
    obtain ⟨_, _, _, _, _, e₁, _, rfl, _, h₁⟩ := term_un h
    simp [hasCCall, term_calls t₁ h₁]

/-! ## Runs -/

variable {file : Program} {labels : Labels}

/-- Every symbol with key `q` points, in `env`, to the `ity` object holding `n`. -/
def Loc (env : Env) (m : Mem.Concrete.State) (q : Key) (ity : IntegerType) (n : Int) : Prop :=
  supported ity = true ∧ Fits ity n ∧ ∃ id addr, (∀ y : Sym, y.key = q → env.lookup y =
    some (.object (.pointer (.allocated id addr)))) ∧ TSlot m id addr (width ity) n

theorem Loc.touched {env : Env} {m m' : Mem.Concrete.State} {q : Key} {ity : IntegerType} {n : Int}
    (h : Loc env m q ity n) (t : Touched m m') : Loc env m' q ity n := by
  obtain ⟨hs, hn, id, addr, hx, slot⟩ := h
  exact ⟨hs, hn, id, addr, hx, TyActions.Touched.slot t slot⟩

theorem Loc.env {env env' : Env} {m : Mem.Concrete.State} {q : Key} {ity : IntegerType} {n : Int}
    (h : Loc env m q ity n) (he : ∀ y : Sym, y.key = q → env'.lookup y = env.lookup y) :
    Loc env' m q ity n := by
  obtain ⟨hs, hn, id, addr, hx, slot⟩ := h
  exact ⟨hs, hn, id, addr, fun y hy => (he y hy).trans (hx y hy), slot⟩

/-- `Loc` for every local `t` reads. -/
def Locs (env : Env) (m : Mem.Concrete.State) (σ : Key → Int) (t : Term) : Prop :=
  ∀ q ∈ t.vars, Loc env m q.1 q.2 (σ q.1)

theorem Locs.touched {env : Env} {m m' : Mem.Concrete.State} {σ : Key → Int} {t : Term}
    (h : Locs env m σ t) (tch : Touched m m') : Locs env m' σ t :=
  fun q hq => (h q hq).touched tch

theorem Locs.sub {env : Env} {m : Mem.Concrete.State} {σ : Key → Int} {t t' : Term}
    (h : Locs env m σ t) (hs : ∀ q ∈ t'.vars, q ∈ t.vars) : Locs env m σ t' :=
  fun q hq => h q (hs q hq)

theorem Locs.env {env env' : Env} {m : Mem.Concrete.State} {σ : Key → Int} {t : Term}
    {bk : List Key} (h : Locs env m σ t) (fresh : ∀ q ∈ bk, ∀ ity, (q, ity) ∉ t.vars)
    (he : ∀ y : Sym, y.key ∉ bk → env'.lookup y = env.lookup y) : Locs env' m σ t := by
  intro q hq
  refine (h q hq).env fun y hy => he y fun hb => fresh _ hb q.2 (by rw [hy]; exact hq)

/-- The read-only task of an operand. -/
theorem task_of_runs {env : Env} {σ : Key → Int} (t : Term) {e : Eff}
    (he : term file e = some t) (I : Mem.Concrete.State → Prop)
    (runs : ∀ m, I m → ∃ xs m' fr, OneAnn fr xs ∧ (∀ a ∈ xs, a.write = false) ∧ Touched m m' ∧
      LocalReaches file labels false ⟨.effectExpr e env, [], m⟩ ⟨.value (spec (t.val σ)), fr ++ [], m'⟩) :
    ReadTask (file := file) (labels := labels) I env e (spec (t.val σ)) := by
  refine ⟨term_calls t he, fun m hm => ?_⟩
  obtain ⟨xs, m', fr, hfr, rd, tch, run⟩ := runs m hm
  refine ⟨xs, m', rd, tch, fr, by simpa using run, ?_⟩
  rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]

/-- **Value arm.** -/
theorem term_runs : (t : Term) → {e : Eff} → term file e = some t →
    {env : Env} → {σ : Key → Int} → t.Ok σ → ∀ (k : List Frame) (m : Mem.Concrete.State),
      Locs env m σ t →
      ∃ xs m' fr, OneAnn fr xs ∧ (∀ a ∈ xs, a.write = false) ∧
        Touched m m' ∧ LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
          ⟨.value (spec (t.val σ)), fr ++ k, m'⟩
  | .lit c, e, h, env, σ, ok, k, m, _ => by
    rcases term_lit h with hf | ⟨an, pa, rfl⟩
    · obtain ⟨l, fr, hfr, run⟩ := ClosedEff.value_local file labels e (Fold.EnvSub.empty env)
        (fold_inv hf) k m
      exact ⟨[], _, fr, hfr, by simp, ⟨l, m.lastUsed, rfl⟩, run⟩
    · obtain ⟨l', run⟩ := LoadTask.pure_val_local (file := file) (labels := labels) (wc := false) an pa
        (.loaded (.specified (.integer c))) env k m
      exact ⟨[], _, [], .inl ⟨rfl, rfl⟩, by simp, ⟨l', m.lastUsed, rfl⟩, run⟩
  | .var q ity, e, h, env, σ, ok, k, m, locs => by
    obtain ⟨a0, pa, a1, a2, la, a3, c1, a4, pt, p, p', x', l, u, rfl, hx', hp', hs⟩ := term_var h
    obtain ⟨-, hn, id, addr, hx, slot⟩ := locs (q, ity) (by simp [Term.vars])
    obtain ⟨a, m', ha, t, run⟩ := TyGuard.load_local (file := file) (labels := labels) a0 pa a1 a2
      la a3 c1 a4 pt p p' x' l u hs hp' env k m (hx x' hx') hn slot
    exact ⟨[a], m', [.annotations [a]], .inr rfl, by simpa using ha, t, run⟩
  | .bin g t₁ t₂, e, h, env, σ, ok, k, m, locs => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, gp, rfl, hg, h₁, h₂⟩ := term_bin h
    obtain ⟨ok₁, ok₂, okr⟩ := ok
    let I : Mem.Concrete.State → Prop := fun m => Locs env m σ (.bin g t₁ t₂)
    have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t => s.touched t
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.bin g t₁ t₂).vars := fun q hq => by simp [Term.vars, hq]
    have sub₂ : ∀ q ∈ t₂.vars, q ∈ (Term.bin g t₁ t₂).vars := fun q hq => by simp [Term.vars, hq]
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure gp)))) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, .effectBind PAT (.mk ag (.pure gp)) env :: k, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    obtain ⟨xs, m₁, rd, tch, s₂⟩ := unseq_pair (file := file) (labels := labels)
      (k := .effectBind PAT (.mk ag (.pure gp)) env :: k) (annots := au) I hI
      (task_of_runs t₁ h₁ I fun m hm => term_runs t₁ h₁ ok₁ [] m (hm.sub sub₁))
      (task_of_runs t₂ h₂ I fun m hm => term_runs t₂ h₂ ok₂ [] m (hm.sub sub₂))
      (by rintro rfl; rw [h₁] at h₂; cases h₂; rfl) m locs
    have s₃ : LocalReaches file labels false
        ⟨.value (.tuple [spec (t₁.val σ), spec (t₂.val σ)]),
          .annotations xs :: .effectBind PAT (.mk ag (.pure gp)) env :: k, m₁⟩
        ⟨.effectExpr (.mk ag (.pure gp)) (Guard.operands a b (t₁.val σ) (t₂.val σ) env),
          .annotations xs :: k, m₁⟩ :=
      .single (.next (requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
        (LoadTask.plain_effectExpr _ _))
    obtain ⟨l', s₄⟩ := guard_local (file := file) (labels := labels) ag gp
      (Guard.operands a b (t₁.val σ) (t₂.val σ) env) (.annotations xs :: k) m₁
    let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l'}
    have s₅ := PureEvalExt.ev_local file (PureEval.tagsOf file m₂) (wc := false) (labels := labels)
      (TyGuard.tguard_eval hg env okr) (.diagnosticLocation m₁.currentLocation :: .annotations xs :: k)
      m₂ rfl
    refine ⟨xs, m₂, [.annotations xs], .inr rfl, rd, tch.trans ⟨l', m₁.lastUsed, rfl⟩,
      s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.tail ?_))))⟩
    exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
      (LoadTask.plain_value _)

  | .ebin g t₁ t₂, e, h, env, σ, ok, k, m, locs => by
    obtain ⟨an, pp, p1, p2, au, a, b, ta, tb, e₁, e₂, ge, rfl, hg, h₁, h₂⟩ := term_ebin h
    obtain ⟨ok₁, ok₂, -⟩ := ok
    let I : Mem.Concrete.State → Prop := fun m => Locs env m σ (.ebin g t₁ t₂)
    have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t => s.touched t
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.ebin g t₁ t₂).vars := fun q hq => by simp [Term.vars, hq]
    have sub₂ : ∀ q ∈ t₂.vars, q ∈ (Term.ebin g t₁ t₂).vars := fun q hq => by simp [Term.vars, hq]
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) ge)) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, .effectBind PAT ge env :: k, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    obtain ⟨xs, m₁, rd, tch, s₂⟩ := unseq_pair (file := file) (labels := labels)
      (k := .effectBind PAT ge env :: k) (annots := au) I hI
      (task_of_runs t₁ h₁ I fun m hm => term_runs t₁ h₁ ok₁ [] m (hm.sub sub₁))
      (task_of_runs t₂ h₂ I fun m hm => term_runs t₂ h₂ ok₂ [] m (hm.sub sub₂))
      (by rintro rfl; rw [h₁] at h₂; cases h₂; rfl) m locs
    have s₃ : LocalReaches file labels false
        ⟨.value (.tuple [spec (t₁.val σ), spec (t₂.val σ)]),
          .annotations xs :: .effectBind PAT ge env :: k, m₁⟩
        ⟨.effectExpr ge (Guard.operands a b (t₁.val σ) (t₂.val σ) env), .annotations xs :: k, m₁⟩ :=
      .single (.next (requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
        (LoadTask.plain_effectExpr _ _))
    obtain ⟨m₂, tch₂, s₄⟩ := TyECmp.eguard_runs (file := file) (labels := labels) hg env
      (t₁.val σ) (t₂.val σ) (.annotations xs :: k) m₁
    exact ⟨xs, m₂, [.annotations xs], .inr rfl, rd, tch.trans tch₂, s₁.trans (s₂.trans (s₃.trans s₄))⟩
  | .un u t₁, e, h, env, σ, ok, k, m, locs => by
    obtain ⟨an, pa, ag, a, ta, e₁, g, rfl, hg, h₁⟩ := term_un h
    obtain ⟨ok₁, okr⟩ := ok
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.un u t₁).vars := fun q hq => by simpa [Term.vars] using hq
    obtain ⟨xs, m₁, fr, hfr, rd, tch, run⟩ := term_runs t₁ h₁ ok₁
      (.effectBind (.mk pa (.base (some a, ta))) (.mk ag (.pure g)) env :: k) m (locs.sub sub₁)
    obtain ⟨m₂, tch₂, run₂⟩ := TyUnary.runs (an := an) hg okr hfr run
    exact ⟨xs, m₂, fr, hfr, rd, tch.trans tch₂, run₂⟩

/-- A recognised expression in range is a read-only task. -/
theorem term_task (t : Term) {e : Eff} (h : term file e = some t) {env : Env} {σ : Key → Int}
    (ok : t.Ok σ) (I : Mem.Concrete.State → Prop) (hs : ∀ m, I m → Locs env m σ t) :
    ReadTask (file := file) (labels := labels) I env e (spec (t.val σ)) :=
  task_of_runs t h I fun m hm => term_runs t h ok [] m (hs m hm)

/-- **Undefined-behaviour arm.** -/
theorem term_fails : (t : Term) → {e : Eff} → term file e = some t →
    {env : Env} → {σ : Key → Int} → ¬ t.Ok σ → ∀ (k : List Frame) (m : Mem.Concrete.State),
      Locs env m σ t → Fails file labels false ⟨.effectExpr e env, k, m⟩ overflow
  | .lit c, e, h, env, σ, bad, k, m, _ => absurd trivial bad
  | .var q _, _, _, _, _, bad, _, _, _ => absurd trivial bad
  | .bin g t₁ t₂, e, h, env, σ, bad, k, m, locs => by
    obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, e₁, e₂, gp, rfl, hg, h₁, h₂⟩ := term_bin h
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.bin g t₁ t₂).vars := fun q hq => by simp [Term.vars, hq]
    have sub₂ : ∀ q ∈ t₂.vars, q ∈ (Term.bin g t₁ t₂).vars := fun q hq => by simp [Term.vars, hq]
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    let K : List Frame := .effectBind PAT (.mk ag (.pure gp)) env :: k
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure gp)))) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, K, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    refine ArenaFail.Fails.pre file labels s₁ ?_
    have flag₁ : taskFlag false K [(0, .effectExpr e₁ env, [])] = false := by
      simp [taskFlag, Interleave.controlHasCCall_effectExpr, term_calls t₁ h₁]
    have flag₀ : taskFlag false K [] = false := by simp [taskFlag]
    by_cases ok₂ : t₂.Ok σ
    · by_cases ok₁ : t₁.Ok σ
      · have okr : ¬ g.Ok (t₁.val σ) (t₂.val σ) := fun hr => bad ⟨ok₁, ok₂, hr⟩
        let I : Mem.Concrete.State → Prop := fun m => Locs env m σ (.bin g t₁ t₂)
        have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t => s.touched t
        obtain ⟨xs, m₁, -, -, s₂⟩ := unseq_pair (file := file) (labels := labels) (k := K)
          (annots := au) I hI
          (term_task t₁ h₁ ok₁ I (fun _ hm => hm.sub sub₁))
          (term_task t₂ h₂ ok₂ I (fun _ hm => hm.sub sub₂))
          (by rintro rfl; rw [h₁] at h₂; cases h₂; rfl) m locs
        have s₃ : LocalReaches file labels false
            ⟨.value (.tuple [spec (t₁.val σ), spec (t₂.val σ)]), .annotations xs :: K, m₁⟩
            ⟨.effectExpr (.mk ag (.pure gp)) (Guard.operands a b (t₁.val σ) (t₂.val σ) env),
              .annotations xs :: k, m₁⟩ :=
          .single (.next (requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
            (LoadTask.plain_effectExpr _ _))
        obtain ⟨l', s₄⟩ := guard_local (file := file) (labels := labels) ag gp
          (Guard.operands a b (t₁.val σ) (t₂.val σ) env) (.annotations xs :: k) m₁
        exact ArenaFail.Fails.pre file labels (s₂.trans (s₃.trans s₄))
          (TyGuard.tguard_fails (labels := labels) hg env okr false
            (.diagnosticLocation m₁.currentLocation :: .annotations xs :: k)
            {m₁ with currentLocation := l'})
      · obtain ⟨xs, m', fr, hfr, -, tch, run⟩ := term_runs (file := file) (labels := labels) t₂ h₂
          ok₂ [] m (locs.sub sub₂)
        refine ArenaFail.fail_pair file labels (.inr ⟨spec (t₂.val σ), xs, m', ?_, ?_⟩)
        · rw [flag₁]
          refine ⟨fr, by simpa using run, ?_⟩
          rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]
        · rw [flag₀]
          exact term_fails t₁ h₁ ok₁ [] m' ((locs.sub sub₁).touched tch)
    · refine ArenaFail.fail_pair file labels (.inl ?_)
      rw [flag₁]
      exact term_fails t₂ h₂ ok₂ [] m (locs.sub sub₂)

  | .ebin g t₁ t₂, e, h, env, σ, bad, k, m, locs => by
    obtain ⟨an, pp, p1, p2, au, a, b, ta, tb, e₁, e₂, ge, rfl, hg, h₁, h₂⟩ := term_ebin h
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.ebin g t₁ t₂).vars := fun q hq => by simp [Term.vars, hq]
    have sub₂ : ∀ q ∈ t₂.vars, q ∈ (Term.ebin g t₁ t₂).vars := fun q hq => by simp [Term.vars, hq]
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    let K : List Frame := .effectBind PAT ge env :: k
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) ge)) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, K, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    refine ArenaFail.Fails.pre file labels s₁ ?_
    have flag₁ : taskFlag false K [(0, .effectExpr e₁ env, [])] = false := by
      simp [taskFlag, Interleave.controlHasCCall_effectExpr, term_calls t₁ h₁]
    have flag₀ : taskFlag false K [] = false := by simp [taskFlag]
    by_cases ok₂ : t₂.Ok σ
    · by_cases ok₁ : t₁.Ok σ
      · exact absurd ⟨ok₁, ok₂, TyECmp.eguard_ok hg _ _⟩ bad
      · obtain ⟨xs, m', fr, hfr, -, tch, run⟩ := term_runs (file := file) (labels := labels) t₂ h₂
          ok₂ [] m (locs.sub sub₂)
        refine ArenaFail.fail_pair file labels (.inr ⟨spec (t₂.val σ), xs, m', ?_, ?_⟩)
        · rw [flag₁]
          refine ⟨fr, by simpa using run, ?_⟩
          rcases hfr with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]
        · rw [flag₀]
          exact term_fails t₁ h₁ ok₁ [] m' ((locs.sub sub₁).touched tch)
    · refine ArenaFail.fail_pair file labels (.inl ?_)
      rw [flag₁]
      exact term_fails t₂ h₂ ok₂ [] m (locs.sub sub₂)
  | .un u t₁, e, h, env, σ, bad, k, m, locs => by
    obtain ⟨an, pa, ag, a, ta, e₁, g, rfl, hg, h₁⟩ := term_un h
    have sub₁ : ∀ q ∈ t₁.vars, q ∈ (Term.un u t₁).vars := fun q hq => by simpa [Term.vars] using hq
    by_cases ok₁ : t₁.Ok σ
    · have okr : ¬ u.Ok 0 (t₁.val σ) := fun hr => bad ⟨ok₁, hr⟩
      obtain ⟨xs, m₁, fr, hfr, -, -, run⟩ := term_runs (file := file) (labels := labels) t₁ h₁ ok₁
        (.effectBind (.mk pa (.base (some a, ta))) (.mk ag (.pure g)) env :: k) m (locs.sub sub₁)
      exact TyUnary.fails (an := an) hg okr hfr run
    · refine ArenaFail.Fails.pre file labels
        (.single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false)
          (LoadTask.plain_effectExpr _ _))) ?_
      exact term_fails t₁ h₁ ok₁ _ m (locs.sub sub₁)

end Silmaril.Compile.Core.Verified.TyExpr
