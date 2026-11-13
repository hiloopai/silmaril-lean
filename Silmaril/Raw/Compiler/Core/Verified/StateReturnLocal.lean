module

public import Silmaril.Compiler.Core.Verified.StateProc.Defs
public import Silmaril.Compiler.Core.Verified.CallLocal.Defs

/-! # State returns and lifetime cleanup as local procedure traces

The slot list and definitions are arbitrary: these lemmas can return expressions
reading several parameter/local objects. They retain an explicit procedure boundary
until the return is resolved, then finish the sole remaining operand. No compiler
recognizer executes the source program.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StateReturnLocal

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open ReturnLit (Eff NoBoundary ReturnLabel)
open ReturnConst (focusMemory)
open Mem.Concrete (LiveInt)
open ConvInt (IsInt)
open IntExpr (spec)
open StateExpr (Key Term values close)
open StateMem (Local Inv Defined defsOf ptr)
open StateStmt (Keys killsRun retStmt killsRun_nil killsRun_cons)
open LoadTask (plain_effectExpr plain_pureExpr plain_value)

variable {file : Program} {labels : Labels}

/-- Wildcard strong binding, without converting a local trace to the top-level LTS. -/
theorem wildcard (ann : List Annot) (ty : BaseType) (v : Val) (b : EE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels false
      ⟨.value v, .strongBind (.mk ann (.base (none, ty))) b env :: k, m⟩
      ⟨.effectExpr b env, k, m⟩ := by
  exact .single (.next (by simp [requestAux, awaitsScheduling, matchPattern, extendEnv]) (plain_effectExpr _ _))

/-- Discard the read annotations at the expression's sequence boundary. -/
theorem bound_pop {fr : List Frame} {xs : List Access} (hfr : Cond.OneAnn fr xs)
    (v : Val) (k : List Frame) (m : Mem.Concrete.State) :
    LocalReaches file labels false ⟨.value v, fr ++ .bound :: k, m⟩ ⟨.value v, k, m⟩ := by
  rcases hfr with ⟨rfl, -⟩ | rfl
  all_goals exact .single (.next (by simp [requestAux, awaitsScheduling]) (plain_value v))

/-- Killing one live integer object is a local memory transition, with exact memory. -/
theorem kill (ann a2 c1 : List Annot) (l : Loc) (u : Unit) (x : Sym)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {id addr : Int} (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (live : LiveInt m id addr) :
    LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.kill (.static (Mem.Concrete.intType c1)) (.mk a2 () (.sym x))))))) env, k, m⟩
      ⟨.value .unit, k, Locals.killed (focusMemory ann m) id⟩ := by
  refine (CallLocal.focus (c' := .pureExpr (.mk a2 () (.sym x)) env)
    (k' := .arguments (.memory (.kill (Mem.Concrete.intType c1))) [] [] env :: k)
    ann m (plain_pureExpr _ _) ?_).trans ?_
  · simp only [requestAux, awaitsScheduling, arguments]
    rfl
  · refine (PureLocal.args_local file _ (Eval.cons (Eval.sym hx) Eval.nil)
      (.memory (.kill (Mem.Concrete.intType c1))) [] k (focusMemory ann m) rfl).tail ?_
    exact .memory (name := "Kill") (by
      simp [requestAux, awaitsScheduling, memoryRequest,
        Mem.Concrete.kill_int _ c1 (Locals.liveInt_focus ann live),
        bind, Except.bind, pure, Except.pure, Locals.killed])

/-- Killing a live wrapper object (`WrapObj.isWrap`) is a local memory transition. -/
theorem killWrap (ann a2 c1 : List Annot) (l : Loc) (u : Unit) (x : Sym) {T : Sym}
    (hT : WrapObj.isWrap file.tagDefs T = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {id addr : Int} (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (live : LiveInt m id addr) :
    LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.kill (.static (.mk c1 (.struct T))) (.mk a2 () (.sym x))))))) env, k, m⟩
      ⟨.value .unit, k, Locals.killed (focusMemory ann m) id⟩ := by
  refine (CallLocal.focus (c' := .pureExpr (.mk a2 () (.sym x)) env)
    (k' := .arguments (.memory (.kill (.mk c1 (.struct T)))) [] [] env :: k)
    ann m (plain_pureExpr _ _) ?_).trans ?_
  · simp only [requestAux, awaitsScheduling, arguments]
    rfl
  · refine (PureLocal.args_local file _ (Eval.cons (Eval.sym hx) Eval.nil)
      (.memory (.kill (.mk c1 (.struct T)))) [] k (focusMemory ann m) rfl).tail ?_
    exact .memory (name := "Kill") (by
      simp [requestAux, awaitsScheduling, memoryRequest,
        WrapObj.kill (tags := ⟨file.tagDefs, (focusMemory ann m).enumTypes⟩) hT c1
          (Locals.liveInt_focus ann live),
        bind, Except.bind, pure, Except.pure, Locals.killed])

/-- `kill` or `killWrap`, as recognised by `WrapObj.killAny`. -/
theorem killAny {x : Sym} {e : Eff} (h : WrapObj.killAny file x e = true) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) {id addr : Int}
    (hx : ∀ y : Sym, y.key = x.key → env.lookup y = some (.object (.pointer (.allocated id addr))))
    (live : LiveInt m id addr) :
    ∃ ann, LocalReaches file labels false ⟨.effectExpr e env, k, m⟩
      ⟨.value .unit, k, Locals.killed (focusMemory ann m) id⟩ := by
  unfold WrapObj.killAny at h
  have h' := Bool.or_eq_true_iff.mp h
  clear h
  rcases h' with h | h
  · unfold Locals.killInt at h
    split at h
    · rename_i ann l u c1 a2 x'
      exact ⟨ann, kill ann a2 c1 l u x' env k m (hx x' (of_decide_eq_true h)) live⟩
    · cases h
  · unfold WrapObj.killWrap at h
    split at h
    · rename_i ann l u c1 T a2 x'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨ann, killWrap ann a2 c1 l u x' h.2 env k m (hx x' h.1) live⟩
    · cases h

/-- Local cleanup for any number of disjoint live slots, followed by the callee's
own return label. The caller's frames are retained verbatim. -/
theorem killsRun_returns {ret u : Sym} {L : Labels} (hret : ReturnLabel L ret) :
    (xs : List Sym) → (ls : List Local) → Keys ls xs → (xs.map (·.key)).Nodup →
    {e : Eff} → killsRun file ret u xs e = true → (env : Env) →
    (loc : List Frame) → NoBoundary loc → (caller : List Frame) →
    (m : Mem.Concrete.State) →
    (∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)) →
    (∀ l ∈ ls, LiveInt m l.id l.addr) →
    (∀ a ∈ ls, ∀ b ∈ ls, a.sym.key ≠ b.sym.key → a.id ≠ b.id) →
    {v : Int} → IsInt v → env.lookup u = some (spec v) →
    ∃ m', m'.stdout = m.stdout ∧ LocalReaches file labels false
      ⟨.effectExpr e env, loc ++ .procedureReturn L :: caller, m⟩
      ⟨.value (spec v), .procedureReturn L :: caller, m'⟩
  | [], ls, hls, _, e, h, env, loc, hk, caller, m, _, _, _, v, hv, hu => by
    obtain ⟨rann, l, cann, a3, c3, a4, s, u', rfl, hl, hu', hs⟩ := killsRun_nil h
    have heval : ∀ tags, Eval file tags env
        (.inl (.mk cann () (.call (.sym s) [Locals.intVal a3 c3, .mk a4 () (.sym u')])) )
        (.inl (spec v)) := fun _ =>
      ConvInt.convLoadedInt_eval (ann := c3) hs hv
        (.cons .val (.cons (.sym (by rw [ReturnLit.lookup_key hu']; exact hu)) .nil))
    obtain ⟨m', out, back⟩ := CallLocal.jump_return (file := file) (labels := labels)
      hl hret (spec v) env hk caller (focusMemory rann m)
    refine ⟨m', by simp [out], ?_⟩
    refine (CallLocal.focus (c' := .pureExpr
        (.mk cann () (.call (.sym s) [Locals.intVal a3 c3, .mk a4 () (.sym u')])) env)
      (k' := .runLabel l [] [] env :: (loc ++ .procedureReturn L :: caller))
      rann m (plain_pureExpr _ _) ?_).trans ?_
    · simp [requestAux, awaitsScheduling, focusMemory]; rfl
    · exact (PureLocal.eval_local file _ (heval _) _ _ rfl).trans back
  | x :: xs, ls, hls, nodup, e, h, env, loc, hk, caller, m, henv, hlive, hids, v, hv, hu => by
    cases ls with
    | nil => cases hls
    | cons l ls =>
      simp only [Keys, List.map_cons, List.cons.injEq] at hls
      obtain ⟨hxl, hls⟩ := hls
      obtain ⟨hxs, nodup⟩ := List.nodup_cons.mp nodup
      obtain ⟨ann, pann, ty, kl, rest, rfl, hkl, hrest⟩ := killsRun_cons h
      let K := loc ++ .procedureReturn L :: caller
      obtain ⟨kann, kr⟩ := killAny (file := file) (labels := labels) hkl env
        (.strongBind (.mk pann (.base (none, ty))) rest env :: K) m
        (fun y hy => henv l (by simp) y (hy.trans hxl.symm)) (hlive l (by simp))
      let m₁ := Locals.killed (focusMemory kann m) l.id
      have ne : ∀ l' ∈ ls, l'.id ≠ l.id := by
        intro l' hl'
        refine (hids l' (by simp [hl']) l (by simp) ?_)
        intro e
        apply hxs
        have hm : l'.sym.key ∈ ls.map (·.sym.key) := List.mem_map_of_mem hl'
        rw [hls, e, hxl] at hm
        exact hm
      obtain ⟨m', out, reach⟩ := killsRun_returns hret xs ls hls nodup hrest env loc hk caller m₁
        (fun l' hl' => henv l' (by simp [hl']))
        (fun l' hl' => StateMem.live_killed (Locals.liveInt_focus kann (hlive l' (by simp [hl'])))
          l.id (ne l' hl'))
        (fun a ha b hb => hids a (by simp [ha]) b (by simp [hb])) hv hu
      refine ⟨m', by rw [out]; simp [m₁, Locals.killed], ?_⟩
      exact (CallLocal.sequence ann _ _ rest env K m).trans (kr.trans
        ((wildcard pann ty .unit rest env K m₁).trans reach))

/-- An arbitrary recognised State return, including overflow. The local failure
arm can be propagated through an enclosing arena using `ArenaFail.fail_task`. -/
theorem ret_returns {ret : Sym} {L : Labels} (hret : ReturnLabel L ret)
    {xs : List Sym} {e : Eff} {t : Term}
    (h : retStmt file ret xs e = some t) {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (hls : Keys ls xs)
    (nodup : (xs.map (·.key)).Nodup) (hd : Defined ds t = true)
    (loc : List Frame) (hk : NoBoundary loc) (caller : List Frame) :
    ((close (defsOf ds) t).Ok 0 ∧ ∃ m', m'.stdout = m.stdout ∧ LocalReaches file labels false
      ⟨.effectExpr e env, loc ++ .procedureReturn L :: caller, m⟩
      ⟨.value (spec ((close (defsOf ds) t).val 0)), .procedureReturn L :: caller, m'⟩) ∨
    ArenaFail.Fails file labels false
      ⟨.effectExpr e env, loc ++ .procedureReturn L :: caller, m⟩ IntExpr.overflow := by
  unfold retStmt at h
  split at h
  · rename_i ann pann u ty bann e' kr
    split at h
    · rename_i cond
      obtain ⟨hfresh, hkr⟩ := cond
      let σ := values (defsOf ds)
      let k := loc ++ .procedureReturn L :: caller
      let K := Frame.strongBind (.mk pann (.base (some u, ty))) kr env :: k
      have pre : LocalReaches file labels false
          ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) kr)) env, k, m⟩
          ⟨.effectExpr e' env, .bound :: K, m⟩ :=
        (CallLocal.sequence ann _ _ _ env k m).trans (CallLocal.bound bann _ env K m)
      by_cases ok : t.Ok σ
      · left
        refine ⟨StateExpr.close_ok _ t (inv.defs_ok hd) ok, ?_⟩
        obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
          t h ok (.bound :: K) m (inv.locs hd)
        let v := spec (t.val σ)
        have inv₁ := (inv.touched tch).extend (x := u) (v := v) (hls.fresh hfresh)
        obtain ⟨m', out, reach⟩ := killsRun_returns hret xs ls hls nodup hkr (extendEnv [(u, v)] env)
          loc hk caller m₁ inv₁.env inv₁.live (fun a ha b hb ne => (inv₁.apart a ha b hb ne).1)
          (StateExpr.Term.int_of_ok t ok) (ConvInt.lookup_one rfl)
        refine ⟨m', by rw [out, tch.stdout], ?_⟩
        rw [StateExpr.close_val]
        exact pre.trans (run.trans ((bound_pop hfr v K m₁).trans
          ((CallLocal.bind pann u ty v kr env k m₁).trans reach)))
      · exact .inr (ArenaFail.Fails.pre file labels pre
          (StateExpr.term_fails (file := file) (labels := labels) t h ok (.bound :: K) m (inv.locs hd)))
    · cases h
  · cases h

/-- A recognised State return is a complete operand computation, or raises the
same source overflow out of the arena. All lifetime/read frames stay inside it. -/
theorem ret_in_arena {ret : Sym} {L : Labels} (hret : ReturnLabel L ret)
    {xs : List Sym} {e : Eff} {t : Term}
    (h : retStmt file ret xs e = some t) {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (hls : Keys ls xs)
    (nodup : (xs.map (·.key)).Nodup) (hd : Defined ds t = true)
    (loc : List Frame) (hk : NoBoundary loc)
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame) :
    ((close (defsOf ds) t).Ok 0 ∧ ∃ m', m'.stdout = m.stdout ∧ CoreReaches file labels
      ⟨.interleave done [(i, .effectExpr e env, loc ++ [.procedureReturn L])], k, m⟩
      ⟨.interleave ((i, spec ((close (defsOf ds) t).val 0), []) :: done) [], k, m'⟩) ∨
    ArenaFail.Fails file labels false
      ⟨.interleave done [(i, .effectExpr e env, loc ++ [.procedureReturn L])], k, m⟩
      IntExpr.overflow := by
  have pending : Pending [] i := ⟨by simp, by simp⟩
  rcases ret_returns (labels := labels) hret h inv hls nodup hd loc hk [] with
    ⟨ok, m', out, run⟩ | fail
  · left
    refine ⟨ok, m', out, reaches_of_local file labels ?_⟩
    apply drive_task file labels pending
    refine ⟨[], ?_, rfl⟩
    have pop : LocalReaches file labels false
        ⟨.value (spec ((close (defsOf ds) t).val 0)), [.procedureReturn L], m'⟩
        ⟨.value (spec ((close (defsOf ds) t).val 0)), [], m'⟩ :=
      .single (.next (by simp [requestAux, awaitsScheduling]) (plain_value _))
    simpa [taskFlag] using run.trans pop
  · right
    apply ArenaFail.fail_task file labels pending
    simpa [taskFlag] using fail

end Silmaril.Compile.Core.Verified.StateReturnLocal
