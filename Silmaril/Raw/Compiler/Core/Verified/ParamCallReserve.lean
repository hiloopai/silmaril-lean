module

public import Silmaril.Compiler.Core.Verified.ParamCallCompare.Defs
public import Silmaril.Compiler.Core.Verified.CallParamAlloc.Defs
public import Silmaril.Compiler.Core.Verified.LoopCondition.Defs
/-! # Parameter-call comparisons retain a reserve for the selected successor -/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ParamCallReserve

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Reaches Eval tagsOf)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons saveFree)
open ConvInt (IsInt isConvLoadedInt)
open IntExpr (Term spec)
open LocalExpr (Shows)
open ParamCallCompare (Plan expr expr_parts)
open StateStmt (Overflows boolSource_touched bound_pop seqFocus_touched)

variable {file : Program} {labels : Labels} {r : Nat}

/-- The pure right operand finishes first; the full State callee then runs
inside the sole remaining operand, with overflow propagated out of the arena. -/
theorem operands {ec : EE} {g x : Sym} {t : Term} {n c : Int}
    (hs : CallArg.argSite file ec = some (g, n))
    (hc : CallParam.calleeArg file g ParamRun.maxLocals = some (x, t))
    (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    (hpos : 0 < Mem.Concrete.nextIntAddress m) (hdead : m.nextId ∉ m.dead)
    {rhs : EE} (hrhs : ClosedEff.flatLit file rhs = some c) (hb : CallParamAlloc.Reserve (r + ParamRun.maxLocals + 1) m) :
    StateStmt.Overflows (file := file) (labels := labels)
      ⟨.interleave [] [(0, .effectExpr ec env, []),
        (1, .effectExpr rhs env, [])], k, m⟩ ∨
    t.Ok n ∧ ∃ m' xs, m'.stdout = m.stdout ∧ CallParamAlloc.Reserve r m' ∧ CoreReaches file labels
      ⟨.interleave [] [(0, .effectExpr ec env, []),
        (1, .effectExpr rhs env, [])], k, m⟩
      ⟨.interleave [(0, spec (t.val n), xs), (1, spec c, [])] [], k, m'⟩ := by
  have pending : Pending [(0, .effectExpr ec env, [])] 1 :=
    ⟨by simp, by intro q hq; simp only [List.mem_singleton] at hq; subst q; exact activeCall_effectExpr ec env⟩
  obtain ⟨l, literal⟩ := ClosedEff.flatLit_task file labels (taskFlag false k [(0, .effectExpr ec env, [])]) hrhs env m
  have first := reaches_of_local file labels
    (drive_task file labels pending (done := []) (k := k) (wc := false) literal)
  rcases CallParamAlloc.call_in_arena (labels := labels) hs hc env
      {m with currentLocation := l} (by simpa [Mem.Concrete.nextIntAddress] using hpos)
      hdead [(1, spec c, [])] 0 k (by exact hb.same ⟨rfl, rfl, rfl⟩) with ub | ⟨ok, m', xs, out, reserve, call⟩
  · exact .inl (StateStmt.Overflows.pre first ub)
  · exact .inr ⟨ok, m', xs, out, reserve, first.trans call⟩

/-- A comparison consumes the real result of its operand call. -/
theorem expr_runs {e : EE} {p : Plan} (h : expr file e ParamRun.maxLocals = some p)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    (hpos : 0 < Mem.Concrete.nextIntAddress m) (hdead : m.nextId ∉ m.dead)
    (hb : CallParamAlloc.Reserve (r + ParamRun.maxLocals + 1) m) :
    StateStmt.Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    p.result.Ok 0 ∧ ∃ m' xs, m'.stdout = m.stdout ∧ CallParamAlloc.Reserve r m' ∧ Reaches file labels
      ⟨.effectExpr e env, k, m⟩
      ⟨.value (spec (p.result.val 0)), .annotations xs :: k, m'⟩ := by
  obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, ec, rhs, guard,
    rfl, hrhs, hs, hc, hlit, hg⟩ := expr_parts h
  let pat : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
  let K := Frame.effectBind pat (.mk ag (.pure guard)) env :: k
  have start : Reaches file labels
      ⟨.effectExpr (.mk an (.wseq pat (.mk au (.unseq [ec,
        rhs]))
          (.mk ag (.pure guard)))) env, k, m⟩
      ⟨.interleave [] [(0, .effectExpr ec env, []),
        (1, .effectExpr (rhs) env, [])], K, m⟩ := by
    apply reaches_of_local file labels
    refine .head (.next (LoadTask.requestAux_wseq m an pat _ _ env k false)
      (LoadTask.plain_effectExpr _ _)) ?_
    exact .single (.next (requestAux_unseq file labels m au _ env K false)
      (plain_interleave _ _))
  rcases operands (labels := labels) hs hc env K m hpos hdead hrhs hb with ub | ⟨okt, m₁, xs, out₁, reserve₁, run⟩
  · exact .inl (StateStmt.Overflows.pre start ub)
  right
  have harg := CallArg.argSite_range hs
  have okt' : p.inst.Ok 0 := (StateSubst.subst_ok (.lit p.argument) p.term 0 harg).mpr okt
  have value : p.inst.val 0 = p.term.val p.argument := StateSubst.subst_val _ _ _
  have hn := IntExpr.Term.ok_int harg p.term okt
  have hok : p.result.Ok 0 := ⟨okt', hlit, StateExpr.cmpGuard'_int hg⟩
  refine ⟨hok, ?_⟩
  have finish : Reaches file labels
      ⟨.interleave [(0, spec (p.term.val p.argument), xs), (1, spec p.literal, [])] [], K, m₁⟩
      ⟨.value (.tuple [spec (p.term.val p.argument), spec p.literal]), .annotations xs :: K, m₁⟩ := by
    apply reaches_of_local file labels
    exact .single (.next (by
      simpa using requestAux_end file labels m₁
        [(0, spec (p.term.val p.argument), xs), (1, spec p.literal, [])] K false (by simp [NoRace])
        (by simp))
      (LoadTask.plain_value _))
  have bind : Reaches file labels
      ⟨.value (.tuple [spec (p.term.val p.argument), spec p.literal]), .annotations xs :: K, m₁⟩
      ⟨.effectExpr (.mk ag (.pure guard)) (Guard.operands a b (p.term.val p.argument) p.literal env),
        .annotations xs :: k, m₁⟩ := by
    apply reaches_of_local file labels
    exact .single (.next (IntExpr.requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
      (LoadTask.plain_effectExpr _ _))
  refine ⟨ReturnConst.focusMemory ag m₁, xs, by simp [out₁], reserve₁.focus ag, ?_⟩
  have final := start.trans (run.trans (finish.trans (bind.trans (reaches_of_local file labels
    (CallLocal.pure ag (fun _ => StateExpr.cmpGuard'_eval hg env hn hlit) _ _)))))
  simpa [Plan.result, IntExpr.Term.val, value] using final

/-- Both successors remain syntax; neither is evaluated by the recognizer. -/
def condition (file : File Codec.wireModel Unit Unit)  :
    EE → Option (Plan × EE × EE)
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec))
      (.mk _ (.sseq (.mk _ (.base (some b, _))) cb
        (.mk _ (.if_ (.mk _ () (.sym b')) yes no))))) =>
      if b'.key = b.key ∧ StmtIf.boolSource c cb = true then
        (ParamCallCompare.expr file ec ParamRun.maxLocals).map fun t => (t, yes, no)
      else none
  | _ => none

theorem condition_inv {file : File Codec.wireModel Unit Unit}
    {e yes no : EE} {t : Plan} (h : condition file e = some (t, yes, no)) :
    ∃ (a0 a1 : List Annot) (c : Sym) (cty : BaseType) (a2 : List Annot) (ec : EE)
      (a3 a4 : List Annot) (b : Sym) (bty : BaseType) (cb : EE)
      (a5 a6 : List Annot) (b' : Sym),
      e = .mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec))
        (.mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb
          (.mk a5 (.if_ (.mk a6 () (.sym b')) yes no))))) ∧
      b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ ParamCallCompare.expr file ec ParamRun.maxLocals = some t := by
  unfold condition at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨t', ht, rfl, rfl, rfl⟩ := h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
        hc.1, hc.2, ht⟩
    · cases h
  · cases h


/-- Enter the selected effectful branch, preserving stdout and the remaining
allocation reserve after argument cleanup. -/
theorem condition_runs {e yes no : EE} {t : Plan}
    (shape : condition file e = some (t, yes, no))
    (env : Env) (m : Mem.Concrete.State) (k : List Frame) (hb : CallParamAlloc.Reserve (r + ParamRun.maxLocals + 1) m) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.result.Ok 0 ∧ ∃ env' m',
        m'.stdout = m.stdout ∧ CallParamAlloc.Reserve r m' ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (if t.result.val 0 = 1 then no else yes) env', k, m'⟩ := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', rfl,
    hb', hcb, htc⟩ := condition_inv shape
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) yes no)
  let REST : EE := .mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb IF)
  let K := Frame.strongBind (.mk a1 (.base (some c, cty))) REST env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec)) REST)) env, k, m⟩
      ⟨.effectExpr ec env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
  rcases expr_runs (labels := labels) htc env (.bound :: K) m hb.budget.room hb.budget.fresh hb with
    ub | ⟨ok, m₁, xs', out₁, reserve₁, run⟩
  · exact .inl (Overflows.pre pre ub)
  · right
    let cv := t.result.val 0
    let env₁ := extendEnv [(c, IntExpr.spec cv)] env
    let KB := Frame.strongBind (.mk a4 (.base (some b, bty))) IF env₁ :: k
    obtain ⟨m₂, tch₂, conv⟩ := boolSource_touched (file := file) (labels := labels) hcb env₁ KB m₁ cv
      (ConvInt.lookup_one rfl)
    let flag := decide (cv ≠ 1)
    let env₂ := extendEnv [(b, boolean flag)] env₁
    have hp : SeqReach.PureEval file labels (.mk a6 () (.sym b')) env₂ (boolean flag) :=
      SeqReach.pure_symbol a6 b' env₂ _ (ConvInt.lookup_one hb')
    have enter : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
        ⟨.effectExpr (if flag then yes else no) env₂, k, SeqReach.focusMemory a5 m₂⟩ :=
      run.trans ((Locals.annotations_bound_reaches xs' _ K m₁).trans
        ((ReturnLit.bind_reaches a1 c cty _ REST env k m₁).trans
          ((ReturnConst.sequence_reaches file labels a3 _ cb IF env₁ k m₁).trans
            (conv.trans ((ReturnLit.bind_reaches a4 b bty _ IF env₁ k m₂).trans
              (SeqReach.effect_if_reaches a5 flag hp k m₂))))))
    have reserve := (reserve₁.touched tch₂).touched (seqFocus_touched a5 m₂)
    refine ⟨ok, env₂, _, (seqFocus_touched a5 m₂).stdout.trans (tch₂.stdout.trans out₁), reserve, ?_⟩
    have select : (if flag then yes else no) =
        (if t.result.val 0 = 1 then no else yes) := by
      change (if flag then yes else no) = (if cv = 1 then no else yes)
      by_cases h : cv = 1 <;> simp [flag, h]
    rw [select] at enter
    exact pre.trans enter

end Silmaril.Compile.Core.Verified.ParamCallReserve
