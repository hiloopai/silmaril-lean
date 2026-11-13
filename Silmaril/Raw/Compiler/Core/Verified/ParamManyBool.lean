module

public import Silmaril.Compiler.Core.Verified.ParamMany.Defs
public import Silmaril.Compiler.Core.Verified.ParamCallBool.Defs
/-! # Cerberus's zero test around a comparison of a call with several arguments

`if (g(n₁, …, nₖ) != c)` elaborates to the comparison inside a second comparison with zero, so
the call runs in an inner operand arena inside an outer one: `ParamCallNested` and
`ParamCallBool` for the calls of `ParamMany`.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ParamManyBool

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Reaches Eval)
open ReturnConst (focusMemory)
open ReturnLit (Eff)
open ConvInt (IsInt)
open IntExpr (Term spec)
open LoadTask (plain_effectExpr plain_value)
open StateStmt (Overflows boolSource_touched seqFocus_touched)
open CallParamAlloc (Reserve)
open CallMany (ptrOf fp)
open ParamMany (callee callee_spec body_returns reserve_mono cost)
open ParamCallNested (wrap_local)

variable {file : Program} {labels : Labels} {r : Nat}

/-- A call `g(n₁, …, nₖ)` in an inner comparison stays within its outer comparison operand. -/
theorem call_nested {e : EE} {g : Sym} {ns : List Int} {t : IntExpr.Term}
    (hs : CallMany.argSite file e = some (g, ns)) (hc : callee file g ns = some t)
    (env : Env) (m : Mem.Concrete.State) (hb : Reserve (r + ParamRun.maxLocals + ns.length) m)
    (done outer : List (Nat × (Val × List Access))) (i j : Nat) (fr k : List Frame) :
    StateStmt.Overflows (file := file) (labels := labels)
      ⟨.interleave outer [(j, .interleave done [(i, .effectExpr e env, [])], fr)], k, m⟩ ∨
    t.Ok 0 ∧ ∃ m' xs, m'.stdout = m.stdout ∧ Reserve r m' ∧ Reaches file labels
      ⟨.interleave outer [(j, .interleave done [(i, .effectExpr e env, [])], fr)], k, m⟩
      ⟨.interleave outer [(j, .interleave ((i, IntExpr.spec (t.val 0), xs) :: done) [], fr)], k, m'⟩ := by
  obtain ⟨loc, attrs, rty, pts, proto, dloc, marker, bt, params, body', hstd, hinfo, hdecl, hr, hpts,
    hlp, hlq, hnd, hbody⟩ := callee_spec hc
  obtain ⟨env', m₁, frames, objs, out₁, mem, reserve₁, pre, cleanup⟩ :=
    CallMany.argSite_prepared (fuel := r + ParamRun.maxLocals) (file := file) (labels := labels)
      hs hinfo hr hpts hlp env [] m hb
  have hlen : objs.length = ns.length := mem.slots.length_eq
  have hns : ∀ n ∈ ns, IsInt n := CallMany.argSite_range hs
  have pi : Pending [] i := ⟨by simp, by simp⟩
  have pj : Pending [] j := ⟨by simp, by simp⟩
  have preRun : Reaches file labels
      ⟨.interleave outer [(j, .interleave done [(i, .effectExpr e env, [])], fr)], k, m⟩
      ⟨.interleave outer [(j, .interleave done [(i, .apply (.procedure env')
        (fp g :: objs.map ptrOf), frames)], fr)], k, m₁⟩ := by
    apply reaches_of_local file labels
    apply wrap_local outer j k
    · exact wrap_local done i fr pre (fun v h => by cases h)
    · intro v h; cases h
  have resolved := CallReach.procedure_body (file := file) (values := objs.map ptrOf) hstd hdecl
    (by simp [hlq, hlen])
  have ordinary := CallReach.procedure_not_builtin hdecl
  have enter : Reaches file labels
      ⟨.interleave outer [(j, .interleave done [(i, .apply (.procedure env')
        (fp g :: objs.map ptrOf), frames)], fr)], k, m₁⟩
      ⟨.interleave outer [(j, .interleave done [(i, .effectExpr body'
        (extendEnv ((params.map Prod.fst).zip (objs.map ptrOf)) env'),
        .procedureReturn (CallReach.bodyLabels body') :: frames)], fr)], k, m₁⟩ := by
    apply ArenaCall.scheduled_reaches file labels
    · intro v h; cases h
    · apply ArenaLift.requestAux_sole_scheduled file labels
      · intro v h; cases h
      · rw [requestAux.eq_def]
        simp [awaitsScheduling, ordinary, resolved, scheduledRequest, CallReach.bodyLabels]
      · exact plain_effectExpr _ _
    · exact plain_interleave _ _
  have entry := preRun.trans enter
  rcases body_returns (labels := labels) hbody env' frames m₁ (by rw [List.map_map]; exact hnd)
      (by simp [hlq, hlen]) mem hns reserve₁.aligned
      (by have := reserve₁.room; push_cast at this ⊢; omega) reserve₁.dead with
    ⟨ok, m₂, out₂, uses, live, run⟩ | fail
  · right
    let v := IntExpr.spec (t.val 0)
    obtain ⟨m₃, fs, xs, out₃, reserve₃, hfs, finish⟩ := cleanup r v m₂ live (reserve₁.uses uses)
      (fun o ho => by have := mem.below o ho; have := uses.next; omega)
    have pop : LocalReaches file labels false
        ⟨.value v, .procedureReturn (CallReach.bodyLabels body') :: frames, m₂⟩ ⟨.value v, frames, m₂⟩ :=
      .single (.next (by simp [requestAux, awaitsScheduling]) (plain_value _))
    have complete := run.trans (pop.trans finish)
    refine ⟨ok, m₃, xs, out₃.trans (out₂.trans out₁), reserve₃, entry.trans ?_⟩
    apply reaches_of_local file labels
    apply wrap_local outer j k
    · have localInner : LocalReaches file labels false
          ⟨.interleave done [(i, .effectExpr body'
            (extendEnv ((params.map Prod.fst).zip (objs.map ptrOf)) env'),
            .procedureReturn (CallReach.bodyLabels body') :: frames)], fr, m₁⟩
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
theorem comparison_task {e : EE} {p : ParamMany.Plan} (h : ParamMany.expr file e = some p)
    (env : Env) (outer : List (Nat × (Val × List Access))) (j : Nat) (k : List Frame)
    (m : Mem.Concrete.State) (hb : Reserve (r + cost) m) :
    StateStmt.Overflows (file := file) (labels := labels)
      ⟨.interleave outer [(j, .effectExpr e env, [])], k, m⟩ ∨
    p.result.Ok 0 ∧ ∃ m' xs, m'.stdout = m.stdout ∧ Reserve r m' ∧ Reaches file labels
      ⟨.interleave outer [(j, .effectExpr e env, [])], k, m⟩
      ⟨.interleave ((j, IntExpr.spec (p.result.val 0), xs) :: outer) [], k, m'⟩ := by
  obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, ec, rhs, guard,
    rfl, hrhs, hs, hc, hlit, hg⟩ := ParamMany.expr_parts h
  let pat : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
  let K := [Frame.effectBind pat (.mk ag (.pure guard)) env]
  have start : LocalReaches file labels false
      ⟨.effectExpr (.mk an (.wseq pat (.mk au (.unseq [ec, rhs])) (.mk ag (.pure guard)))) env, [], m⟩
      ⟨.interleave [] [(0, .effectExpr ec env, []), (1, .effectExpr rhs env, [])], K, m⟩ := by
    refine .head (.next (LoadTask.requestAux_wseq m an pat _ _ env [] false)
      (LoadTask.plain_effectExpr _ _)) ?_
    exact .single (.next (requestAux_unseq file labels m au _ env K false) (plain_interleave _ _))
  have pending : Pending [(0, .effectExpr ec env, [])] 1 :=
    ⟨by simp, by intro q hq; simp only [List.mem_singleton] at hq; subst q; exact activeCall_effectExpr ec env⟩
  obtain ⟨l, literal⟩ := ClosedEff.flatLit_task file labels (taskFlag false K [(0, .effectExpr ec env, [])])
    hrhs env m
  have first := start.trans (drive_task file labels pending (done := []) (k := K) (wc := false) literal)
  have pj : Pending [] j := ⟨by simp, by simp⟩
  have pre : Reaches file labels
      ⟨.interleave outer [(j, .effectExpr (.mk an (.wseq pat (.mk au (.unseq [ec, rhs]))
          (.mk ag (.pure guard)))) env, [])], k, m⟩
      ⟨.interleave outer [(j, .interleave [(1, IntExpr.spec p.literal, [])]
        [(0, .effectExpr ec env, [])], K)], k, {m with currentLocation := l}⟩ := by
    apply reaches_of_local file labels
    apply wrap_local outer j k
    · exact first
    · intro v h; cases h
  have hlen := CallMany.argSite_len hs
  rcases call_nested (r := r) (labels := labels) hs hc env {m with currentLocation := l}
      (reserve_mono (hb.same ⟨rfl, rfl, rfl⟩) (by unfold cost; omega)) [(1, IntExpr.spec p.literal, [])]
      outer 0 j K k with
    ub | ⟨okt, m₁, xs, out₁, reserve₁, run⟩
  · exact .inl (StateStmt.Overflows.pre pre ub)
  right
  have hn := IntExpr.Term.ok_int (n := 0) (by unfold IsInt; decide) p.term okt
  have hok : p.result.Ok 0 := ⟨okt, hlit, StateExpr.cmpGuard'_int hg⟩
  have finish : LocalReaches file labels false
      ⟨.interleave [(0, IntExpr.spec (p.term.val 0), xs), (1, IntExpr.spec p.literal, [])] [], K, m₁⟩
      ⟨.value (.tuple [IntExpr.spec (p.term.val 0), IntExpr.spec p.literal]), .annotations xs :: K, m₁⟩ := by
    exact .single (.next (by
      simpa using requestAux_end file labels m₁
        [(0, IntExpr.spec (p.term.val 0), xs), (1, IntExpr.spec p.literal, [])] K false (by simp [NoRace])
        (by simp)) (LoadTask.plain_value _))
  have bind : LocalReaches file labels false
      ⟨.value (.tuple [IntExpr.spec (p.term.val 0), IntExpr.spec p.literal]), .annotations xs :: K, m₁⟩
      ⟨.effectExpr (.mk ag (.pure guard)) (Guard.operands a b (p.term.val 0) p.literal env),
        [.annotations xs], m₁⟩ := by
    exact .single (.next (IntExpr.requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env [])
      (LoadTask.plain_effectExpr _ _))
  refine ⟨hok, focusMemory ag m₁, xs, by simp [out₁], reserve₁.focus ag, pre.trans (run.trans ?_)⟩
  apply reaches_of_local file labels
  apply drive_task file labels pj
  refine ⟨[.annotations xs], ?_, by simp [annotationsOnly]⟩
  have final := finish.trans (bind.trans (CallLocal.pure ag
    (fun _ => StateExpr.cmpGuard'_eval hg env hn hlit) _ _))
  simpa [taskFlag, ParamMany.Plan.result, IntExpr.Term.val] using final

structure Plan where
  inner : ParamMany.Plan
  literal : Int
  rel : BinOp
  yes : Int
  no : Int

def Plan.result (p : Plan) : Term := .cmp p.rel p.yes p.no p.inner.result (.lit p.literal)

def expr (file : File Codec.wireModel Unit Unit) : EE → Option Plan
  | .mk _ (.wseq (.mk _ (.ctor .tuple [.mk _ (.base (some a, _)), .mk _ (.base (some b, _))]))
      (.mk _ (.unseq [ec, .mk _ (.pure (.mk _ () (.val (.loaded (.specified (.integer n))))))]))
      (.mk _ (.pure guard))) => do
      if -2147483648 ≤ n ∧ n ≤ 2147483647 then
        let p ← ParamMany.expr file ec
        let (r, y, z) ← StateExpr.cmpGuard' file a b guard
        pure ⟨p, n, r, y, z⟩
      else none
  | _ => none

theorem expr_parts {e : EE} {p : Plan} (h : expr file e = some p) :
    ∃ an pp p1 p2 au ag a b ta tb ec ln lv guard,
      e = .mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)),
        .mk p2 (.base (some b, tb))]))
        (.mk au (.unseq [ec, .mk ln (.pure (.mk lv () (.val (.loaded (.specified (.integer p.literal))))))]))
        (.mk ag (.pure guard))) ∧
      ParamMany.expr file ec = some p.inner ∧ IsInt p.literal ∧
      StateExpr.cmpGuard' file a b guard = some (p.rel, p.yes, p.no) := by
  unfold expr at h
  split at h
  · rename_i an pp p1 a ta p2 b tb au ec ln lv n ag guard
    split at h
    · rename_i hn
      cases hp : ParamMany.expr file ec with
      | none => simp [hp] at h
      | some inner =>
        cases hg : StateExpr.cmpGuard' file a b guard with
        | none => simp [hp, hg] at h
        | some triple =>
          obtain ⟨r, y, z⟩ := triple
          simp only [hp, hg, bind, Option.bind, pure, Option.some.injEq] at h
          subst p
          exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hp, hn, hg⟩
    · cases h
  · cases h

theorem operands {ec : EE} {p : ParamMany.Plan} {c : Int} (hs : ParamMany.expr file ec = some p)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    (an av : List Annot) (hb : Reserve (r + cost) m) :
    Overflows (file := file) (labels := labels)
      ⟨.interleave [] [(0, .effectExpr ec env, []),
        (1, .effectExpr (.mk an (.pure (.mk av () (.val (.loaded (.specified (.integer c))))))) env, [])], k, m⟩ ∨
    p.result.Ok 0 ∧ ∃ m' xs, m'.stdout = m.stdout ∧ Reserve r m' ∧ Reaches file labels
      ⟨.interleave [] [(0, .effectExpr ec env, []),
        (1, .effectExpr (.mk an (.pure (.mk av () (.val (.loaded (.specified (.integer c))))))) env, [])], k, m⟩
      ⟨.interleave [(0, spec (p.result.val 0), xs), (1, spec c, [])] [], k, m'⟩ := by
  have pending : Pending [(0, .effectExpr ec env, [])] 1 :=
    ⟨by simp, by intro q hq; simp only [List.mem_singleton] at hq; subst q; exact activeCall_effectExpr ec env⟩
  obtain ⟨l, literal⟩ := literal_task (file := file) (labels := labels)
    (wc := taskFlag false k [(0, .effectExpr ec env, [])])
    (annots := an) (ann := av) (w := .loaded (.specified (.integer c))) (env := env) (m := m)
  have first := reaches_of_local file labels
    (drive_task file labels pending (done := []) (k := k) (wc := false) literal)
  rcases comparison_task (labels := labels) hs env [(1, spec c, [])] 0 k
      {m with currentLocation := l} (hb.same ⟨rfl, rfl, rfl⟩) with ub | ⟨ok, m', xs, out, reserve, call⟩
  · exact .inl (Overflows.pre first ub)
  · exact .inr ⟨ok, m', xs, out, reserve, first.trans call⟩

theorem expr_runs {e : EE} {p : Plan} (h : expr file e = some p)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (hb : Reserve (r + cost) m) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    p.result.Ok 0 ∧ ∃ m' xs, m'.stdout = m.stdout ∧ Reserve r m' ∧ Reaches file labels
      ⟨.effectExpr e env, k, m⟩
      ⟨.value (spec (p.result.val 0)), .annotations xs :: k, m'⟩ := by
  obtain ⟨an, pp, p1, p2, au, ag, a, b, ta, tb, ec, ln, lv, guard,
    rfl, hs, hlit, hg⟩ := expr_parts h
  let pat : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
  let K := Frame.effectBind pat (.mk ag (.pure guard)) env :: k
  have start : Reaches file labels
      ⟨.effectExpr (.mk an (.wseq pat (.mk au (.unseq [ec,
        .mk ln (.pure (.mk lv () (.val (.loaded (.specified (.integer p.literal))))))]))
          (.mk ag (.pure guard)))) env, k, m⟩
      ⟨.interleave [] [(0, .effectExpr ec env, []),
        (1, .effectExpr (.mk ln (.pure (.mk lv () (.val (.loaded (.specified (.integer p.literal))))))) env, [])], K, m⟩ := by
    apply reaches_of_local file labels
    refine .head (.next (LoadTask.requestAux_wseq m an pat _ _ env k false)
      (LoadTask.plain_effectExpr _ _)) ?_
    exact .single (.next (requestAux_unseq file labels m au _ env K false) (plain_interleave _ _))
  rcases operands (labels := labels) hs env K m ln lv hb with ub | ⟨okt, m₁, xs, out₁, reserve₁, run⟩
  · exact .inl (Overflows.pre start ub)
  right
  have hn := IntExpr.Term.ok_int (n := 0) (by constructor <;> omega) p.inner.result okt
  have hok : p.result.Ok 0 := ⟨okt, hlit, StateExpr.cmpGuard'_int hg⟩
  have finish : Reaches file labels
      ⟨.interleave [(0, spec (p.inner.result.val 0), xs), (1, spec p.literal, [])] [], K, m₁⟩
      ⟨.value (.tuple [spec (p.inner.result.val 0), spec p.literal]), .annotations xs :: K, m₁⟩ := by
    apply reaches_of_local file labels
    exact .single (.next (by
      simpa using requestAux_end file labels m₁
        [(0, spec (p.inner.result.val 0), xs), (1, spec p.literal, [])] K false (by simp [NoRace])
        (by simp)) (LoadTask.plain_value _))
  have bind : Reaches file labels
      ⟨.value (.tuple [spec (p.inner.result.val 0), spec p.literal]), .annotations xs :: K, m₁⟩
      ⟨.effectExpr (.mk ag (.pure guard)) (Guard.operands a b (p.inner.result.val 0) p.literal env),
        .annotations xs :: k, m₁⟩ := by
    apply reaches_of_local file labels
    exact .single (.next (IntExpr.requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
      (LoadTask.plain_effectExpr _ _))
  refine ⟨hok, ReturnConst.focusMemory ag m₁, xs, by simp [out₁], reserve₁.focus ag, ?_⟩
  have final := start.trans (run.trans (finish.trans (bind.trans (reaches_of_local file labels
    (CallLocal.pure ag (fun _ => StateExpr.cmpGuard'_eval hg env hn hlit) _ _)))))
  simpa [Plan.result, IntExpr.Term.val] using final

/-- `if (g(n₁, …, nₖ) != c)`: both successors remain syntax. -/
def condition (file : File Codec.wireModel Unit Unit) : EE → Option (Plan × EE × EE)
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec))
      (.mk _ (.sseq (.mk _ (.base (some b, _))) cb
        (.mk _ (.if_ (.mk _ () (.sym b')) yes no))))) =>
      if b'.key = b.key ∧ StmtIf.boolSource c cb = true then
        (expr file ec).map fun t => (t, yes, no)
      else none
  | _ => none

theorem condition_inv {e yes no : EE} {t : Plan} (h : condition file e = some (t, yes, no)) :
    ∃ (a0 a1 : List Annot) (c : Sym) (cty : BaseType) (a2 : List Annot) (ec : EE)
      (a3 a4 : List Annot) (b : Sym) (bty : BaseType) (cb : EE)
      (a5 a6 : List Annot) (b' : Sym),
      e = .mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec))
        (.mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb
          (.mk a5 (.if_ (.mk a6 () (.sym b')) yes no))))) ∧
      b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ expr file ec = some t := by
  unfold condition at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨t', ht, rfl, rfl, rfl⟩ := h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2, ht⟩
    · cases h
  · cases h

/-- Enter the selected branch, preserving stdout and the rest of the allocation reserve. -/
theorem condition_runs {e yes no : EE} {t : Plan} (shape : condition file e = some (t, yes, no))
    (env : Env) (m : Mem.Concrete.State) (k : List Frame) (hb : Reserve (r + cost) m) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.result.Ok 0 ∧ ∃ env' m', m'.stdout = m.stdout ∧ Reserve r m' ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (if t.result.val 0 = 1 then no else yes) env', k, m'⟩ := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', rfl, hb', hcb, htc⟩ :=
    condition_inv shape
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) yes no)
  let REST : EE := .mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb IF)
  let K := Frame.strongBind (.mk a1 (.base (some c, cty))) REST env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec)) REST)) env, k, m⟩
      ⟨.effectExpr ec env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
  rcases expr_runs (labels := labels) htc env (.bound :: K) m hb with
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
    have select : (if flag then yes else no) = (if t.result.val 0 = 1 then no else yes) := by
      change (if flag then yes else no) = (if cv = 1 then no else yes)
      by_cases h : cv = 1 <;> simp [flag, h]
    rw [select] at enter
    exact pre.trans enter

end Silmaril.Compile.Core.Verified.ParamManyBool
