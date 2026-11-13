module

public import Silmaril.Compiler.Core.Verified.ParamCallReserve.Defs
/-! # A parameter call under two operand arenas -/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ParamCallNested

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Reaches Eval)
open ReturnConst (focusMemory)
open LoadTask (plain_effectExpr plain_value)
open CallParamAlloc (Reserve)

variable {file : Program} {labels : Labels} {r : Nat}

/-- Lift a non-value-ending local trace into a sole outer task. -/
theorem wrap_local (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame)
    {c c' : Control} {fr fr' : List Frame} {m m' : Mem.Concrete.State}
    (h : LocalReaches file labels false ⟨c, fr, m⟩ ⟨c', fr', m'⟩)
    (hv : ∀ v, c' ≠ .value v) :
    LocalReaches file labels false ⟨.interleave done [(i, c, fr)], k, m⟩
      ⟨.interleave done [(i, c', fr')], k, m'⟩ := by
  have hp : Pending [] i := ⟨by simp, by simp⟩
  exact ArenaFail.drive_run file labels hp (done := done) (k := k) (wc := false)
    (s := ⟨c, fr, m⟩) (t := ⟨c', fr', m'⟩) (by simpa [taskFlag] using h) hv

/-- A call in an inner comparison stays within its outer comparison operand.
The only scheduled transition is procedure entry; all other phases are local. -/
theorem call_nested {e : EE} {g x : Sym} {n : Int} {t : IntExpr.Term}
    (hs : CallArg.argSite file e = some (g, n)) (hc : CallParam.calleeArg file g ParamRun.maxLocals = some (x, t))
    (env : Env) (m : Mem.Concrete.State) (hb : Reserve (r + ParamRun.maxLocals + 1) m)
    (done outer : List (Nat × (Val × List Access))) (i j : Nat) (fr k : List Frame) :
    StateStmt.Overflows (file := file) (labels := labels)
      ⟨.interleave outer [(j, .interleave done [(i, .effectExpr e env, [])], fr)], k, m⟩ ∨
    t.Ok n ∧ ∃ m' xs, m'.stdout = m.stdout ∧ Reserve r m' ∧ Reaches file labels
      ⟨.interleave outer [(j, .interleave done [(i, .effectExpr e env, [])], fr)], k, m⟩
      ⟨.interleave outer [(j, .interleave ((i, IntExpr.spec (t.val n), xs) :: done) [], fr)], k, m'⟩ := by
  obtain ⟨body, hbody, env', m₁, frames, id, addr, out₁, slot, reserve₁, hid, haddr, ordinary, resolved, pre,
    cleanup⟩ := CallParamAlloc.argSite_prepared (fuel := r + ParamRun.maxLocals) (labels := labels) hs hc env [] m
      hb.budget.room hb.budget.fresh hb
  have pi : Pending [] i := ⟨by simp, by simp⟩
  have pj : Pending [] j := ⟨by simp, by simp⟩
  have preRun : Reaches file labels
      ⟨.interleave outer [(j, .interleave done [(i, .effectExpr e env, [])], fr)], k, m⟩
      ⟨.interleave outer [(j, .interleave done [(i, .apply (.procedure env')
        [.loaded (.specified (.pointer (.function g))), .object (.pointer (.allocated id addr))], frames)], fr)], k, m₁⟩ := by
    apply reaches_of_local file labels
    apply wrap_local outer j k
    · exact wrap_local done i fr pre (fun v h => by cases h)
    · intro v h; cases h
  have enter : Reaches file labels
      ⟨.interleave outer [(j, .interleave done [(i, .apply (.procedure env')
        [.loaded (.specified (.pointer (.function g))), .object (.pointer (.allocated id addr))], frames)], fr)], k, m₁⟩
      ⟨.interleave outer [(j, .interleave done [(i, .effectExpr body
        (extendEnv [(x, .object (.pointer (.allocated id addr)))] env'),
        .procedureReturn (CallReach.bodyLabels body) :: frames)], fr)], k, m₁⟩ := by
    apply ArenaCall.scheduled_reaches file labels
    · intro v h; cases h
    · apply ArenaLift.requestAux_sole_scheduled file labels
      · intro v h; cases h
      · rw [requestAux.eq_def]
        simp [awaitsScheduling, ordinary, resolved, scheduledRequest, CallReach.bodyLabels]
      · exact plain_effectExpr _ _
    · exact plain_interleave _ _
  have entry := preRun.trans enter
  rcases ParamRun.body_returns (labels := labels) hbody
      (extendEnv [(x, .object (.pointer (.allocated id addr)))] env') frames m₁
      (ConvInt.lookup_one rfl) (CallArg.argSite_range hs) slot hid haddr reserve₁.aligned
      (by have := reserve₁.room; push_cast at this ⊢; omega) reserve₁.dead with
      ⟨ok, m₂, out₂, uses, live, run⟩ | fail
  · right
    let v := IntExpr.spec (t.val n)
    obtain ⟨m₃, fs, xs, out₃, reserve₃, hfs, finish⟩ := cleanup r v m₂ live (reserve₁.uses uses)
      (by have := uses.next; omega)
    have pop : LocalReaches file labels false
        ⟨.value v, .procedureReturn (CallReach.bodyLabels body) :: frames, m₂⟩ ⟨.value v, frames, m₂⟩ :=
      .single (.next (by simp [requestAux, awaitsScheduling]) (plain_value _))
    have complete := run.trans (pop.trans finish)
    refine ⟨ok, m₃, xs, out₃.trans (out₂.trans out₁), reserve₃, entry.trans ?_⟩
    apply reaches_of_local file labels
    apply wrap_local outer j k
    · have localInner : LocalReaches file labels false
          ⟨.interleave done [(i, .effectExpr body
            (extendEnv [(x, .object (.pointer (.allocated id addr)))] env'),
            .procedureReturn (CallReach.bodyLabels body) :: frames)], fr, m₁⟩
          ⟨.interleave ((i, v, xs) :: done) [], fr, m₃⟩ := by
        apply drive_task file labels pi
        refine ⟨fs, ?_, ?_⟩
        · simpa [taskFlag, CallReach.bodyLabels, v] using complete
        · rcases hfs with ⟨rfl, rfl⟩ | rfl <;> simp [annotationsOnly]
      simpa [taskFlag] using localInner
    · intro w h; cases h
  · left
    refine StateStmt.Overflows.pre entry ?_
    apply ArenaFail.fail_reaches file labels
    apply ArenaFail.fail_task file labels pj (done := outer) (k := k) (wc := false)
    simpa [taskFlag] using ArenaFail.fail_task file labels pi (done := done) (k := fr) (wc := false)
      (by simpa [taskFlag, CallReach.bodyLabels] using fail)

/-- Evaluate a complete call comparison as the sole remaining outer operand. -/
theorem comparison_task {e : EE} {p : ParamCallCompare.Plan}
    (h : ParamCallCompare.expr file e ParamRun.maxLocals = some p) (env : Env)
    (outer : List (Nat × (Val × List Access))) (j : Nat) (k : List Frame)
    (m : Mem.Concrete.State) (hb : Reserve (r + ParamRun.maxLocals + 1) m) :
    StateStmt.Overflows (file := file) (labels := labels)
      ⟨.interleave outer [(j, .effectExpr e env, [])], k, m⟩ ∨
    p.result.Ok 0 ∧ ∃ m' xs, m'.stdout = m.stdout ∧ Reserve r m' ∧ Reaches file labels
      ⟨.interleave outer [(j, .effectExpr e env, [])], k, m⟩
      ⟨.interleave ((j, IntExpr.spec (p.result.val 0), xs) :: outer) [], k, m'⟩ := by
  obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, ec, rhs, guard,
    rfl, hrhs, hs, hc, hlit, hg⟩ := ParamCallCompare.expr_parts h
  let pat : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
  let K := [Frame.effectBind pat (.mk ag (.pure guard)) env]
  have start : LocalReaches file labels false
      ⟨.effectExpr (.mk an (.wseq pat (.mk au (.unseq [ec,
        rhs]))
          (.mk ag (.pure guard)))) env, [], m⟩
      ⟨.interleave [] [(0, .effectExpr ec env, []),
        (1, .effectExpr (rhs) env, [])], K, m⟩ := by
    refine .head (.next (LoadTask.requestAux_wseq m an pat _ _ env [] false)
      (LoadTask.plain_effectExpr _ _)) ?_
    exact .single (.next (requestAux_unseq file labels m au _ env K false)
      (plain_interleave _ _))
  have pending : Pending [(0, .effectExpr ec env, [])] 1 :=
    ⟨by simp, by intro q hq; simp only [List.mem_singleton] at hq; subst q; exact activeCall_effectExpr ec env⟩
  obtain ⟨l, literal⟩ := ClosedEff.flatLit_task file labels (taskFlag false K [(0, .effectExpr ec env, [])]) hrhs env m
  have first := start.trans (drive_task file labels pending (done := []) (k := K) (wc := false) literal)
  have pj : Pending [] j := ⟨by simp, by simp⟩
  have pre : Reaches file labels
      ⟨.interleave outer [(j, .effectExpr (.mk an (.wseq pat (.mk au (.unseq [ec,
        rhs]))
          (.mk ag (.pure guard)))) env, [])], k, m⟩
      ⟨.interleave outer [(j, .interleave [(1, IntExpr.spec p.literal, [])]
        [(0, .effectExpr ec env, [])], K)], k, {m with currentLocation := l}⟩ := by
    apply reaches_of_local file labels
    apply wrap_local outer j k
    · exact first
    · intro v h; cases h
  rcases call_nested (labels := labels) hs hc env {m with currentLocation := l}
      (hb.same ⟨rfl, rfl, rfl⟩) [(1, IntExpr.spec p.literal, [])] outer 0 j K k with
    ub | ⟨okt, m₁, xs, out₁, reserve₁, run⟩
  · exact .inl (StateStmt.Overflows.pre pre ub)
  right
  have harg := CallArg.argSite_range hs
  have okt' : p.inst.Ok 0 := (StateSubst.subst_ok (.lit p.argument) p.term 0 harg).mpr okt
  have value : p.inst.val 0 = p.term.val p.argument := StateSubst.subst_val _ _ _
  have hn := IntExpr.Term.ok_int harg p.term okt
  have hok : p.result.Ok 0 := ⟨okt', hlit, StateExpr.cmpGuard'_int hg⟩
  have finish : LocalReaches file labels false
      ⟨.interleave [(0, IntExpr.spec (p.term.val p.argument), xs), (1, IntExpr.spec p.literal, [])] [], K, m₁⟩
      ⟨.value (.tuple [IntExpr.spec (p.term.val p.argument), IntExpr.spec p.literal]), .annotations xs :: K, m₁⟩ := by
    exact .single (.next (by
      simpa using requestAux_end file labels m₁
        [(0, IntExpr.spec (p.term.val p.argument), xs), (1, IntExpr.spec p.literal, [])] K false (by simp [NoRace])
        (by simp)) (LoadTask.plain_value _))
  have bind : LocalReaches file labels false
      ⟨.value (.tuple [IntExpr.spec (p.term.val p.argument), IntExpr.spec p.literal]), .annotations xs :: K, m₁⟩
      ⟨.effectExpr (.mk ag (.pure guard)) (Guard.operands a b (p.term.val p.argument) p.literal env),
        [.annotations xs], m₁⟩ := by
    exact .single (.next (IntExpr.requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env [])
      (LoadTask.plain_effectExpr _ _))
  refine ⟨hok, focusMemory ag m₁, xs, by simp [out₁], reserve₁.focus ag, pre.trans (run.trans ?_)⟩
  apply reaches_of_local file labels
  apply drive_task file labels pj
  refine ⟨[.annotations xs], ?_, by simp [annotationsOnly]⟩
  have final := finish.trans (bind.trans (CallLocal.pure ag
    (fun _ => StateExpr.cmpGuard'_eval hg env hn hlit) _ _))
  simpa [taskFlag, ParamCallCompare.Plan.result, IntExpr.Term.val, value] using final

end Silmaril.Compile.Core.Verified.ParamCallNested
