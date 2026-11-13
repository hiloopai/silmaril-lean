module

public import Silmaril.Compiler.Core.Verified.ExitCall.Defs
public import Silmaril.Compiler.Core.Verified.FoldSub.Defs

/-! # Closed exit calls in environments containing live State objects

Only the folder's bound symbols must agree. Unrelated runtime bindings may remain.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ExitCall

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Fold
open Silmaril.Cerberus.Core.PureEval (Reaches)
open ReturnConst (focusMemory)
open Mem.Concrete (LiveInt IntRange nextIntAddress)
open Interleave (LocalStep LocalReaches TaskRuns TasksRun Plain)

local notation "rv" => runtimeValue

variable (file : Program) (labels : Labels)

theorem opValue_runs_sub {fenv : WEnv} {env : Env} (hr : EnvSub fenv env) : (e : EExp) → ∀ {w : WVal},
    opValue file fenv e = some w → ∀ m : Mem.Concrete.State,
    ∃ l, TaskRuns file labels false ⟨.effectExpr e env, [], m⟩ (rv w) [] {m with currentLocation := l}
  | e, w, h, m => by
    rcases opValue_inv h with ⟨a, p, rfl, hp⟩ | ⟨a, pat, a1, es, a2, p, ws, xs, he, hws, hxs, hp⟩
    · exact Interleave.pure_task_of_reaches file labels
        (fun k m' => eval_reaches_sub file labels Return.fuel fenv p _ hp env hr k m')
    have hrun : ∀ e' ∈ es, ∀ m : Mem.Concrete.State, ∃ l, TaskRuns file labels false
        ⟨.effectExpr e' env, [], m⟩ (opVal file fenv e') [] {m with currentLocation := l} := by
      intro e' he' m
      have hlt : sizeOf e' < sizeOf e := by
        have := List.sizeOf_lt_of_mem he'
        rw [he]; simp only [Expr.mk.sizeOf_spec, ExprNode.wseq.sizeOf_spec, ExprNode.unseq.sizeOf_spec]; omega
      obtain ⟨w', hw'⟩ := opValues_mem hws e' he'
      obtain ⟨l, r⟩ := opValue_runs_sub hr e' hw' m
      exact ⟨l, by simpa [opVal, hw'] using r⟩
    rw [he]
    obtain ⟨l1, ru⟩ := unseq_tasks_local file labels (opVal file fenv) hrun
      (fun e' he' => by
        obtain ⟨w', hw'⟩ := opValues_mem hws e' he'; exact opValue_noCall file e' hw')
      a1 [.effectBind pat (.mk a2 (.pure p)) env] m
    rw [opValues_values file hws] at ru
    have hm : matchPattern pat (.tuple (ws.map rv)) = some (bmap xs) := by
      rw [← runtimeValues_eq, show (Value.tuple (runtimeValues ws) : Val) = rv (.tuple ws) from rfl,
        matchP_rv, hxs]; rfl
    have hr' : EnvSub (extend xs fenv) (extendEnv (bmap xs) env) := hr.extend xs
    obtain ⟨l2, rp⟩ := pure_local file labels (wc := false) (env := extendEnv (bmap xs) env)
      (k := [.annotations []]) (m := {m with currentLocation := l1}) a2 p
    refine ⟨l2, [.annotations []], ?_, rfl⟩
    refine .head (.next (ra_wseq file labels _ _ _ _) (plain_effectExpr _ _)) ?_
    refine ru.trans ?_
    refine .head (.next (ra_annotations file labels (by intro _ h; cases h) (by intro h; cases h)
      (fun _ => ra_effectBind file labels hm _ _)) (plain_effectExpr _ _)) ?_
    refine rp.trans ?_
    refine (pure_bridge2 file labels rfl .base
      (eval_reaches_sub file labels Return.fuel _ p _ hp _ hr' _ _)).trans ?_
    exact .single (.next (ra_diagnostic file labels _ _) (plain_value _))
termination_by e => sizeOf e
decreasing_by omega

theorem argTask_runs_sub {fenv : WEnv} {env : Env} (hr : EnvSub fenv env) {t : EExp} {n : Int}
    (h : argTask file fenv t = some n) (m : Mem.Concrete.State) :
    ∃ l, TaskRuns file labels false ⟨.effectExpr t env, [], m⟩ (.loaded (.specified (.integer n))) []
      {m with currentLocation := l} :=
  opValue_runs_sub file labels hr t (argTask_eq h) m

theorem call_unseq_sub {fenv : WEnv} {env : Env} (hr : EnvSub fenv env) {t0 t1 : EExp} {w0 : WVal}
    {n : Int} (h0 : calleeTask file t0 = some w0) (h1 : argTask file fenv t1 = some n) (a : List Annot)
    (k : List Frame) (m : Mem.Concrete.State) :
    ∃ l, Reaches file labels ⟨.effectExpr (.mk a (.unseq [t0, t1])) env, k, m⟩
      ⟨.value (.tuple [rv w0, .loaded (.specified (.integer n))]), .annotations [] :: k,
        {m with currentLocation := l}⟩ := by
  obtain ⟨l1, r1⟩ := argTask_runs_sub file labels hr h1 m
  obtain ⟨l0, r0⟩ := calleeTask_runs file labels h0 env {m with currentLocation := l1}
  have flag1 : Interleave.taskFlag false k ([] ++ [(0, .effectExpr t0 env, [])]) = false := by
    simp [Interleave.taskFlag, Interleave.controlHasCCall_effectExpr, calleeTask_noCall file h0]
  have flag0 : Interleave.taskFlag false k [] = false := by simp [Interleave.taskFlag]
  have run : TasksRun file labels false k (([] ++ [(0, .effectExpr t0 env, [])]) ++ [(1, .effectExpr t1 env, [])])
      m (([] ++ [(0, rv w0, [])]) ++ [(1, .loaded (.specified (.integer n)), [])])
      {m with currentLocation := l0} :=
    .snoc (flag1 ▸ r1) (.snoc (flag0 ▸ r0) .nil)
  have hl := Interleave.unseq_runs file labels (annots := a) (es := [t0, t1]) (env := env) run
    (by intro x hx b hb; simp at hx; rcases hx with rfl | rfl <;> simp at hb)
  exact ⟨l0, Interleave.reaches_of_local file labels (by simpa using hl)⟩

theorem if_false_reaches_sub {fenv : WEnv} {env : Env} (hr : EnvSub fenv env) {ann : List Annot}
    {c : PExp} {yes no : EE} (hc : foldsFalse file fenv c = true) (k : List Frame)
    (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.if_ c yes no)) env, k, m⟩
      ⟨.effectExpr no env, k, focusMemory ann m⟩ :=
  (Straight.focus_reaches (request_if file labels)).trans
    ((eval_reaches_sub file labels Return.fuel fenv c _ (foldsFalse_eval hc) env hr _ _).trans
      (lift file labels (ra_if_false file labels _ _ _) (plain_effectExpr _ _)))

theorem argObject_reaches_sub {fenv : WEnv} {env : Env} (hr : EnvSub fenv env) {e : EExp} {n : Int}
    (h : argObject file fenv e = some n) (k : List Frame) (m : Mem.Concrete.State) (hb : Budget m) :
    ∃ id addr xs m', Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value (.object (.pointer (.allocated id addr))), .annotations xs :: k, m'⟩ ∧
      Locals.Slot m' id addr n ∧ IntRange n ∧ m'.stdout = m.stdout := by
  obtain ⟨a0, pt, nth, a1, c, u, a2, px, x, bx, cr, a3, pn, bn, st, a4, a5, u5, x', w, ys, x3, t,
    rfl, hw, hys, hc, hcr, hx', hst, hx3, hlt, hlook, hrange⟩ := argObject_inv h
  obtain ⟨ann, l, uu, b1, b2, cc1, b3, cc2, pref, rfl⟩ := isIntCreate_inv hcr
  obtain ⟨sann, sl, su, s1, sc1, s2, s3, s, s4, sc3, s5, rfl, hs⟩ := intStore_inv hst
  let env2 : Env := extendEnv (bmap ys) env
  have hr2 : EnvSub (extend ys fenv) env2 := hr.extend ys
  have hm : matchPattern pt (rv w) = some (bmap ys) := by rw [matchP_rv, hys]; rfl
  let m2 := focusMemory a1 (focusMemory a0 m)
  have hb2 : Budget m2 := (hb.focus a0).focus a1
  let mc := focusMemory ann m2
  let ptr : Val := .object (.pointer (.allocated mc.nextId (nextIntAddress m2)))
  let m3 := Actions.created pref cc2 mc
  let env3 : Env := env2.insert x ptr
  have hlive : LiveInt m3 mc.nextId (nextIntAddress m2) := by
    have := Locals.created_live pref cc2 mc (hb2.focus ann).fresh
    rwa [Locals.nextIntAddress_focus] at this
  have hxl : env3.lookup x3 = some ptr := lookup_bind ptr hx3
  have htl : env3.lookup t = some (.loaded (.specified (.integer n))) := by
    rw [Map.lookup_insert_of_key_ne _ _ hlt]
    exact hr2 t _ hlook
  obtain ⟨xs, rst⟩ := Locals.store_reaches (file := file) (labels := labels) sann s1 s2 s3 s4 s5 sc1
    sc3 sl su x3 s t hs env3
    (.effectBind (.mk pn (.base (none, bn))) (.mk a4 (.pure (.mk a5 u5 (.sym x')))) env3 :: k) m3
    hxl htl hrange hlive
  let m4 := Locals.stored (focusMemory sann m3) mc.nextId (nextIntAddress m2) n
  have hslot : Locals.Slot m4 mc.nextId (nextIntAddress m2) n :=
    Locals.stored_slot (Locals.liveInt_focus sann hlive) n
  refine ⟨mc.nextId, nextIntAddress m2, xs, focusMemory a4 m4, ?_, Locals.slot_focus a4 hslot, hrange,
    by simp [m4, m3, mc, m2, Locals.stored_stdout, Actions.created_stdout]⟩
  refine (Straight.focus_reaches (request_let file labels)).trans ?_
  refine (eval_reaches_sub file labels Return.fuel fenv nth w hw env hr _ _).trans ?_
  refine (lift file labels (ra_effectBind file labels hm _ _) (plain_effectExpr _ _)).trans ?_
  refine (if_false_reaches_sub file labels hr2 hc _ _).trans ?_
  refine (lift file labels (ra_wseq file labels _ _ _ _) (plain_effectExpr _ _)).trans ?_
  refine (Locals.create_reaches ann b1 b2 b3 cc1 cc2 l uu pref env2 _ m2 hb2.room).trans ?_
  refine (lift file labels (ra_effectBind file labels (xs := [(x, ptr)]) rfl _ _)
    (plain_effectExpr _ _)).trans ?_
  refine (lift file labels (ra_wseq file labels _ _ _ _) (plain_effectExpr _ _)).trans ?_
  refine rst.trans ?_
  refine (lift file labels (ra_annotations file labels (by intro _ h; cases h) (by intro h; cases h)
    (fun _ => ra_effectBind file labels (xs := []) rfl _ _)) (plain_effectExpr _ _)).trans ?_
  refine (ReturnConst.effect_pure_reaches file labels a4 _ _ _ _).trans ?_
  refine (lift file labels (ra_sym file labels _ _ (lookup_bind ptr hx')) (plain_value _)).trans ?_
  exact lift file labels (ra_diagnostic file labels _ _) (plain_value _)

theorem exitCall_reaches_sub {fenv : WEnv} {env : Env} (hr0 : EnvSub fenv env) {e : EExp} {n : Int}
    (h : exitCall file fenv e = some n) (k : List Frame) (m : Mem.Concrete.State) (hb : Budget m) :
    ∃ m', Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.halt (.defined (.loaded (.specified (.integer n)))), [], m'⟩ ∧ m'.stdout = m.stdout := by
  obtain ⟨a0, pat, a1, t0, t1, a2, c1, u1, a3, c2, u2, a4, pp, p, bp, args, rest, w0, na, xs, g, q, y,
    rfl, h0, h1, hxs, hc1, hc2, ho, hce, hq, hg, hgl, hy⟩ := exitCall_inv h
  let env' : Env := extendEnv (bmap xs) env
  have hr : EnvSub (extend xs fenv) env' := hr0.extend xs
  have hm : matchPattern pat (.tuple [rv w0, .loaded (.specified (.integer na))]) = some (bmap xs) := by
    rw [show (Value.tuple [rv w0, .loaded (.specified (.integer na))] : Val) =
      rv (.tuple [w0, .loaded (.specified (.integer na))]) from rfl, matchP_rv, hxs]; rfl
  obtain ⟨l1, ru⟩ := call_unseq_sub file labels hr0 h0 h1 a1 (.strongBind pat _ env :: k) m
  let m2 := focusMemory a3 (focusMemory a2 {m with currentLocation := l1})
  obtain ⟨id, addr, ys, m3, ra, slot, hn, out3⟩ := argObject_reaches_sub file labels hr ho
    (.strongBind (.mk pp (.base (some p, bp))) rest env' :: .annotations [] :: k) m2
    (((hb.reloc l1).focus a2).focus a3)
  let pv : Val := .object (.pointer (.allocated id addr))
  have hgl' : (env'.insert p pv).lookup g = some (.loaded (.specified (.pointer (.function y)))) := by
    rw [Map.lookup_insert_of_key_ne _ _ hg]
    exact hr g _ hgl
  obtain ⟨m4, rc, out4⟩ := call_reaches file labels hce hgl' hy (lookup_bind pv hq) hn
    (.annotations ys :: .annotations [] :: k) m3 slot
  refine ⟨m4, ?_, by rw [out4, out3]; simp [m2]⟩
  refine (lift file labels (ra_sseq file labels _ _ _ _) (plain_effectExpr _ _)).trans ?_
  refine ru.trans ?_
  refine (lift file labels (ra_annotations file labels (by intro _ h; cases h) (by intro h; cases h)
    (fun _ => ra_strongBind file labels hm _ _)) (plain_effectExpr _ _)).trans ?_
  refine (if_false_reaches_sub file labels hr hc1 _ _).trans ?_
  refine (if_false_reaches_sub file labels hr hc2 _ _).trans ?_
  refine (lift file labels (ra_sseq file labels _ _ _ _) (plain_effectExpr _ _)).trans ?_
  refine ra.trans ?_
  refine (lift file labels (ra_annotations file labels (by intro _ h; cases h) (by intro h; cases h)
    (fun _ => ra_strongBind file labels (xs := [(p, pv)]) rfl _ _)) (plain_effectExpr _ _)).trans ?_
  exact rc

end Silmaril.Compile.Core.Verified.ExitCall
