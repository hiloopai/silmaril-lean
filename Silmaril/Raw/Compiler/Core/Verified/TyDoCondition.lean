module

public import Silmaril.Compiler.Core.Verified.DoCondition.Defs
public import Silmaril.Compiler.Core.Verified.TyRun.Defs
/-! # The direct loaded condition of a `do` loop over typed slots

`DoCondition` with the typed terms of `TyExpr`: the bound condition, then Cerberus's direct
`z ≠ 0` test of the specified result (`DoCondition.branch`). The successors remain effectful
syntax; the test keeps the slots and enters the selected successor.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyDoCondition

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Dynamics
open TyExpr (Key Term term values)
open TyMem (Local Inv Defined defsOf)
open TyStmt (Vars Keys isFresh typedIn)
open StateStmt (Overflows)
open PureEval (Reaches)

/-- The bound condition and its direct conditional continuation; both temporaries are fresh
for every slot. -/
def recognize (file : File Codec.wireModel Unit Unit) (xs : Vars) :
    EE → Option (Term × EE × EE)
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec)) rest) => do
      let (z, yes, no) ← DoCondition.branch c rest
      if isFresh xs c = true ∧ isFresh xs z = true then
        return (← term file ec, yes, no)
      else none
  | _ => none

variable {file : Program} {labels : Labels}

/-- A direct condition runs to precisely one successor, or its loaded test reaches integer
undefined behaviour. -/
theorem runs {xs : Vars} {e yes no : EE} {t : Term}
    (shape : recognize file xs e = some (t, yes, no))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (inv : Inv env m ls ds) (keys : Keys ls xs) (defined : Defined ds t = true)
    (typed : typedIn xs t = true) (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      ∃ env' m', LoadTask.Touched m m' ∧ Inv env' m' ls ds ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (if t.val (values (defsOf ds)) = 0 then no else yes) env', k, m'⟩ := by
  unfold recognize at shape
  split at shape
  · rename_i ann pann c ty bann ec rest
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at shape
    obtain ⟨⟨z, yes', no'⟩, hb, hs⟩ := shape
    split at hs
    · rename_i fresh
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hs
      obtain ⟨t', ht, ht', hy, hn⟩ := hs
      subst t' yes' no'
      let K := Frame.strongBind (.mk pann (.base (some c, ty))) rest env :: k
      have pre := (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
        (ReturnLit.bound_reaches bann ec env K m)
      have locs := inv.locs defined (keys.typed typed)
      by_cases ok : t.Ok (values (defsOf ds))
      · obtain ⟨as, m₁, fr, hfr, _, touch, run⟩ := TyExpr.term_runs
          (file := file) (labels := labels) t ht ok (.bound :: K) m locs
        have next := (Interleave.reaches_of_local file labels run).trans
          ((StateStmt.bound_pop hfr _ K m₁).trans (ReturnLit.bind_reaches pann c ty _ rest env k m₁))
        obtain ⟨m₂, touch₂, select⟩ := DoCondition.branch_runs hb
          (extendEnv [(c, IntExpr.spec (t.val (values (defsOf ds))))] env) k m₁ _
          (ConvInt.lookup_one rfl)
        have touched := touch.trans touch₂
        exact .inr ⟨_, m₂, touched,
          ((inv.touched touched).extend (keys.fresh fresh.1)).extend (keys.fresh fresh.2),
          pre.trans (next.trans select)⟩
      · exact .inl (Overflows.pre pre (StateStmt.fails_overflows (TyExpr.term_fails
          (file := file) (labels := labels) t ht ok (.bound :: K) m locs)))
    · cases hs
  · cases shape

end Silmaril.Compile.Core.Verified.TyDoCondition
