module

public import Silmaril.Compiler.Core.Verified.StateExitMem.Defs
public import Silmaril.Compiler.Core.Verified.ExitCallSub.Defs

/-! # A runtime termination result for the State statement machine -/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.StateExit

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open ReturnLit (Eff)
open IntExpr (Term spec)
open StateStmt (Overflows)

/-- The runtime flag is one for an ordinary exit, zero for abort. -/
structure Result where
  test : Term
  ret : Term

def Result.returning (t : Term) : Result := ⟨.lit 1, t⟩
def Result.aborting : Result := ⟨.lit 0, .lit 0⟩
def Result.choose (c : Term) (a b : Result) : Result :=
  ⟨StmtIf.choose c a.test b.test, StmtIf.choose c a.ret b.ret⟩

def Result.Ok (r : Result) : Prop := r.test.Ok 0 ∧ (r.test.val 0 = 1 → r.ret.Ok 0)
def Result.outcome (r : Result) : Outcome :=
  if r.test.val 0 = 1 then .defined (spec (r.ret.val 0)) else .aborted

variable {file : Program} {labels : Labels}

def Shows (s : State) (r : Result) (out : String) : Prop :=
  (r.Ok ∧ ∃ m', m'.stdout = out ∧ Reaches file labels s ⟨.halt r.outcome, [], m'⟩) ∨
  Overflows (file := file) (labels := labels) s

variable {file : Program} {labels : Labels}

theorem Shows.pre {s s' : State} {r : Result} {out : String}
    (h : Reaches file labels s s') (o : Shows (file := file) (labels := labels) s' r out) :
    Shows (file := file) (labels := labels) s r out := by
  rcases o with ⟨ok, m', hout, run⟩ | ub
  · exact .inl ⟨ok, m', hout, h.trans run⟩
  · exact .inr (Overflows.pre h ub)

theorem Shows.of_return {s : State} {t : Term} {out : String}
    (h : LocalExpr.Shows (file := file) (labels := labels) s 0 t out) :
    Shows (file := file) (labels := labels) s (.returning t) out := by
  rcases h with ⟨ok, m', hout, run⟩ | ub
  · refine .inl ⟨?_, m', hout, ?_⟩
    · simpa [Result.Ok, Result.returning, Term.Ok, Term.val, ConvInt.IsInt] using ok
    · simpa [Result.outcome, Result.returning, Term.val] using run
  · exact .inr ub

theorem shows_choose_left {s : State} {C : Term} {A B : Result} {out : String}
    (okC : C.Ok 0) (h1 : C.val 0 ≠ 1)
    (o : Shows (file := file) (labels := labels) s A out) :
    Shows (file := file) (labels := labels) s (.choose C A B) out := by
  rcases o with ⟨ok, m', hout, run⟩ | ub
  · refine .inl ⟨?_, m', hout, ?_⟩
    · simpa [Result.Ok, Result.choose, h1, okC] using ok
    · simpa [Result.outcome, Result.choose, h1] using run
  · exact .inr ub

theorem shows_choose_right {s : State} {C : Term} {A B : Result} {out : String}
    (okC : C.Ok 0) (h1 : C.val 0 = 1)
    (o : Shows (file := file) (labels := labels) s B out) :
    Shows (file := file) (labels := labels) s (.choose C A B) out := by
  rcases o with ⟨ok, m', hout, run⟩ | ub
  · refine .inl ⟨?_, m', hout, ?_⟩
    · simpa [Result.Ok, Result.choose, h1, okC] using ok
    · simpa [Result.outcome, Result.choose, h1] using run
  · exact .inr ub

open ExitCall (Budget exitCall_reaches_sub lift ra_sseq ra_wseq ra_bound plain_effectExpr)

theorem exit_reaches {n : Int} : (e : Eff) → ExitCall.recognizeBody file e = some n →
    ∀ (env : Env) (k : List Frame) (m : Mem.Concrete.State), Budget m →
    ∃ m', Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.halt (.defined (.loaded (.specified (.integer n)))), [], m'⟩ ∧ m'.stdout = m.stdout
  | e, h, env, k, m, hb => by
    rw [ExitCall.recognizeBody.eq_def] at h
    split at h
    · rename_i n' he
      cases h
      exact exitCall_reaches_sub file labels (Fold.EnvSub.empty env) he k m hb
    · split at h
      · rename_i pat a b _
        obtain ⟨m', r, o⟩ := exit_reaches a h env (.strongBind pat b env :: k) m hb
        exact ⟨m', (lift file labels (ra_sseq file labels _ _ _ _) (plain_effectExpr _ _)).trans r, o⟩
      · rename_i pat a b _
        obtain ⟨m', r, o⟩ := exit_reaches a h env (.effectBind pat b env :: k) m hb
        exact ⟨m', (lift file labels (ra_wseq file labels _ _ _ _) (plain_effectExpr _ _)).trans r, o⟩
      · rename_i a _
        obtain ⟨m', r, o⟩ := exit_reaches a h env (.bound :: k) m hb
        exact ⟨m', (lift file labels (ra_bound file labels _ _) (plain_effectExpr _ _)).trans r, o⟩
      · cases h

end Silmaril.Compile.Core.Verified.StateExit
