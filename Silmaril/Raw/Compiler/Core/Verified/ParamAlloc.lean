module

public import Silmaril.Compiler.Core.Verified.StateParam.Defs
public import Silmaril.Compiler.Core.Verified.StateStmtLocal.Defs
public import Silmaril.Compiler.Core.Verified.RmwSound.Defs
/-! # Allocation metadata through mutable parameter bodies

The local traces retain the next allocation id, dead-id list and last allocation
address. A caller may use these facts after the parameter object is cleaned up.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ParamAlloc

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open Mem.Concrete (LiveInt IntRange)
open Locals (stored Slot)
open ReturnLit (Eff NoBoundary ReturnLabel)
open ReturnConst (focusMemory)
open ConvInt (isConvLoadedInt IsInt)
open StateExpr (Key Term term values close)
open StateMem (Local Inv Defined defsOf update ptr)
open StateStmt
open StateReturnLocal (bound_pop)
open StateStmtLocal (lifted_store_ann)
open IntExpr (spec overflow)
open LoadTask (Touched)
open StateParam (stmts body paramDefs param_at jump_return stmts_subst)

variable {file : Program} {labels L : Labels} {caller : List Frame}

theorem assign_runs_same {e : Eff} {x : Sym} {t : Term} (h : assignStmt file e = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (k : List Frame) :
    ArenaFail.Fails file labels false ⟨.effectExpr e env, k, m⟩ overflow ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m', m'.stdout = m.stdout ∧ Rmw.Same m m' ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ∧
        LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  obtain ⟨a0, a1, ty0, a2, a3, a4, a5, p, tp, a6, t₀, tt, a7, PX, e', b0, b1, ty1, sann, lc, u,
    b2, c1, b3, p', b4, s, b5, c2, b6, t', b7, b8, s', b9, c3, d0, t'', d1, d2, rfl, hp', ht', ht'',
    htp, hann, hs, hs', he, hdx, hnx⟩ := assignStmt_inv h
  have hdx : IntWrap.desig file PX = some x := by
    rcases StateStmt.desigP_inv hdx with hdx | ⟨r, _, hr⟩
    · exact hdx
    · cases hr
  let σ := values (defsOf ds)
  let PU : EE := .mk d1 (.pure (.mk d2 () (.val .unit)))
  let K0 := Frame.strongBind (.mk a1 (.base (none, ty0))) PU env :: k
  let PAT : Pattern Sym := .mk a4 (.ctor .tuple [.mk a5 (.base (some p, tp)), .mk a6 (.base (some t₀, tt))])
  let CONV : PE := .mk b8 () (.call (.sym s') [Locals.intVal b9 c3, .mk d0 () (.sym t'')])
  let NEG : EE := .mk sann (.action (.mk .neg (.mk lc u (.store false (Locals.intVal b2 c1)
    (.mk b3 () (.sym p')) (.mk b4 () (.call (.sym s) [Locals.intVal b5 c2, .mk b6 () (.sym t')])) .na))))
  let BODY : EE := .mk b0 (.wseq (.mk b1 (.base (none, ty1))) NEG (.mk b7 (.pure CONV)))
  let KB := Frame.effectBind PAT BODY env :: .bound :: K0
  have pre : LocalReaches file labels false ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (none, ty0)))
      (.mk a2 (.bound (.mk a3 (.wseq PAT (.mk a7 (.unseq [PX, e'])) BODY)))) PU)) env, k, m⟩
      ⟨.effectExpr (.mk a7 (.unseq [PX, e'])) env, KB, m⟩ :=
    (CallLocal.sequence a0 _ _ _ env k m).trans
      ((CallLocal.bound a2 _ env _ m).trans (StateActionsLocal.wseq a3 PAT _ BODY env _ m))
  have locs := inv.locs hd
  have hpx : env.lookup x = some (ptr l) := inv.lookup hl hx
  by_cases ok : t.Ok σ
  · right
    refine ⟨ok, ?_⟩
    let I : Mem.Concrete.State → Prop := fun m => StateExpr.Locs env m σ t
    have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t => s.touched t
    obtain ⟨xs, m₁, -, tch, s₂⟩ := IntExpr.unseq_pair (file := file) (labels := labels) (k := KB)
      (annots := a7) I hI (IntWrap.desig_readTask I hdx hpx)
      (StateExpr.term_task t he ok I fun _ hm => hm)
      (by intro eq; rw [← eq, hnx] at he; cases he) m locs
    let v := t.val σ
    have hv : IsInt v := StateExpr.Term.int_of_ok t ok
    let env₁ := extendEnv [(p, ptr l), (t₀, spec v)] env
    have s₃ : LocalReaches file labels false ⟨.value (.tuple [ptr l, spec v]), .annotations xs :: KB, m₁⟩
        ⟨.effectExpr BODY env₁, .annotations xs :: .bound :: K0, m₁⟩ :=
      .single (.next
        (IntExpr.requestAux_tuple_bind m₁ xs a4 a5 a6 p t₀ tp tt _ _ _ env _)
        (LoadTask.plain_effectExpr _ _))
    let inner := [Frame.effectBind (.mk b1 (.base (none, ty1))) (.mk b7 (.pure CONV)) env₁,
      .annotations xs]
    have s₄ : LocalReaches file labels false ⟨.effectExpr BODY env₁, .annotations xs :: .bound :: K0, m₁⟩
        ⟨.effectExpr NEG env₁, inner ++ .bound :: K0, m₁⟩ :=
      StateActionsLocal.wseq b0 _ NEG _ env₁ _ m₁
    have ht₁ : env₁.lookup t'' = some (spec v) := lookup_two_snd ht'' htp
    obtain ⟨m₂, tch₂, resume⟩ := assign_resume (file := file) (labels := labels) b1 ty1 b7 b8 b9 c3 d0
      s' t'' env₁ xs m₁.nextExcluded {m₁ with nextExcluded := m₁.nextExcluded + 1} hv hs' ht₁
    have inv₁ : Inv env m₁ ls ds := inv.touched tch
    have live₁ : LiveInt m₁ l.id l.addr := inv₁.live l hl
    have s₅ := StateStmtLocal.lifted_store_ann (file := file) (labels := labels) sann hann lc u (Locals.intVal b2 c1)
      (.mk b3 () (.sym p')) (.mk b4 () (.call (.sym s) [Locals.intVal b5 c2, .mk b6 () (.sym t')]))
      env₁ inner K0 m₁ c1 live₁ hv
      (fun m' => .cons (Locals.eval_intVal _ env₁ b2 c1) (.cons (.sym (lookup_two_fst hp'))
        (.cons (ConvInt.convLoadedInt_eval (ann := c2) hs hv
          (.cons (Locals.eval_intVal _ env₁ b5 c2) (.cons (.sym (lookup_two_snd ht' htp)) .nil))) .nil)))
      (by simp [inner, List.span, List.span.loop]) resume tch₂
      (by intro a ha; obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha; simp)
      (by simp [activeCall, excludeFrames, inner])
    let m₃ := stored m₂ l.id l.addr v
    have inv₃ : Inv env m₃ ls (update ds l.sym.key (some (close (defsOf ds) t))) := by
      have i₂ : Inv env m₂ ls ds := (inv₁.nextExcluded _).touched tch₂
      have := i₂.store hl (StateExpr.close_ok _ t (inv.defs_ok hd) ok)
      rwa [StateExpr.close_val] at this
    refine ⟨focusMemory d1 m₃, ?_, ?_, inv₃.focus d1, ?_⟩
    · simp [m₃, Locals.stored_stdout, tch₂.stdout, tch.stdout]
    · have st := Rmw.same_stored m₂ l.id l.addr v
      have t₁ : Rmw.Same m m₁ := by obtain ⟨l, u, rfl⟩ := tch; exact ⟨rfl, rfl, rfl⟩
      have t₂ : Rmw.Same m₁ m₂ := by obtain ⟨l, u, rfl⟩ := tch₂; exact ⟨rfl, rfl, rfl⟩
      exact t₁.trans (t₂.trans (st.trans (Rmw.same_focus d1 m₃)))
    · exact pre.trans (s₂.trans (s₃.trans (s₄.trans
        (s₅.trans ((StateReturnLocal.wildcard a1 ty0 _ PU env k m₃).trans
          (StateActionsLocal.pure_unit d1 d2 env k m₃))))))
  · left
    refine ArenaFail.Fails.pre file labels pre (ArenaFail.fail_pair file labels (.inl ?_))
    have flag : taskFlag false KB [(0, .effectExpr PX env, [])] = false := by
      simp [taskFlag, Interleave.controlHasCCall_effectExpr, IntWrap.desig_noCall hdx]
    rw [flag]
    exact StateExpr.term_fails t he ok [] m locs

/-- Successful local return, preserving all caller-owned parameter lifetimes. -/
def Returns (ls : List Local) (s : State) (t : IntExpr.Term) (out : String) : Prop :=
  (t.Ok 0 ∧ ∃ m', m'.stdout = out ∧ Rmw.Same s.memory m' ∧ (∀ l ∈ ls, Mem.Concrete.LiveInt m' l.id l.addr) ∧
    LocalReaches file labels false s
      ⟨.value (spec (t.val 0)), .procedureReturn L :: caller, m'⟩) ∨
  ArenaFail.Fails file labels false s IntExpr.overflow

theorem Returns.pre {ls : List Local} {s s' : State} {t : IntExpr.Term} {out : String}
    (h : LocalReaches file labels false s s') (same : Rmw.Same s.memory s'.memory)
    (o : Returns (file := file) (labels := labels) (L := L) (caller := caller) ls s' t out) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) ls s t out := by
  rcases o with ⟨ok, m', hout, allocation, live, r⟩ | ub
  · exact .inl ⟨ok, m', hout, same.trans allocation, live, h.trans r⟩
  · exact .inr (ArenaFail.Fails.pre file labels h ub)

/-- A parameter return reads every initialized slot but kills none of them. -/
theorem ret_returns {ret : Sym} (hret : ReturnLabel L ret) {e : Eff} {t : Term}
    (h : retStmt file ret [] e = some t) {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (hd : Defined ds t = true)
    (loc : List Frame) (hk : NoBoundary loc) (caller : List Frame) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) ls
      ⟨.effectExpr e env, loc ++ .procedureReturn L :: caller, m⟩
      (close (defsOf ds) t) m.stdout := by
  unfold retStmt at h
  split at h
  · rename_i ann pann u ty bann e' kr
    split at h
    · rename_i cond
      obtain ⟨_, hkr⟩ := cond
      obtain ⟨rann, l, cann, a3, c3, a4, s, u', rfl, hl, hu', hs⟩ := StateStmt.killsRun_nil hkr
      let σ := values (defsOf ds)
      let KR : EE := .mk rann (.run () l [.mk cann () (.call (.sym s)
        [Locals.intVal a3 c3, .mk a4 () (.sym u')])])
      let k := loc ++ .procedureReturn L :: caller
      let K := Frame.strongBind (.mk pann (.base (some u, ty))) KR env :: k
      have pre : LocalReaches file labels false
          ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) KR)) env, k, m⟩
          ⟨.effectExpr e' env, .bound :: K, m⟩ :=
        (CallLocal.sequence ann _ _ _ env k m).trans (CallLocal.bound bann _ env K m)
      by_cases ok : t.Ok σ
      · left
        refine ⟨StateExpr.close_ok _ t (inv.defs_ok hd) ok, ?_⟩
        obtain ⟨xs', m₁, fr, hfr, _, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
          t h ok (.bound :: K) m (inv.locs hd)
        let v := spec (t.val σ)
        let env₁ := extendEnv [(u, v)] env
        have heval : ∀ tags, Eval file tags env₁
            (.inl (.mk cann () (.call (.sym s) [Locals.intVal a3 c3, .mk a4 () (.sym u')])) )
            (.inl v) := fun _ =>
          ConvInt.convLoadedInt_eval (ann := c3) hs (StateExpr.Term.int_of_ok t ok)
            (.cons (Locals.eval_intVal _ env₁ a3 c3) (.cons (.sym (ConvInt.lookup_one hu')) .nil))
        obtain ⟨m', touched, back⟩ := jump_return (file := file) (labels := labels) hl hret v env₁ hk caller (focusMemory rann m₁)
        have totalTouch := tch.trans ((LoadTask.focusMemory_touched rann m₁).trans touched)
        refine ⟨m', totalTouch.stdout, ?_, (inv.touched totalTouch).live, ?_⟩
        · obtain ⟨l, u, rfl⟩ := totalTouch; exact ⟨rfl, rfl, rfl⟩
        ·
          rw [StateExpr.close_val]
          refine pre.trans (run.trans ((StateReturnLocal.bound_pop hfr v K m₁).trans
          ((CallLocal.bind pann u ty v KR env k m₁).trans ?_)))
          refine (CallLocal.focus (c' := .pureExpr
            (.mk cann () (.call (.sym s) [Locals.intVal a3 c3, .mk a4 () (.sym u')])) env₁)
          (k' := .runLabel l [] [] env₁ :: k) rann m₁ (LoadTask.plain_pureExpr _ _) ?_).trans ?_
          · simp [KR, env₁, requestAux, awaitsScheduling, focusMemory]; rfl
          · exact (PureLocal.eval_local file _ (heval _) _ _ rfl).trans back
      · exact .inr (ArenaFail.Fails.pre file labels pre
          (StateExpr.term_fails t h ok (.bound :: K) m (inv.locs hd)))
    · cases h
  · cases h

/-- All parameter assignments execute at run time through the existing lifted
negative-store proof. The return keeps their objects live for caller cleanup. -/
theorem stmts_returns {ret : Sym} (hret : ReturnLabel L ret) {ps : List Sym}
    (ds : Key → Option IntExpr.Term) (sz : Key → Nat) (e : Eff) {t : IntExpr.Term}
    (h : stmts file ret ps ds sz e = some t) (env : Env) (m : Mem.Concrete.State)
    (ls : List Local) (inv : Inv env m ls ds) (hls : Keys ls ps) (k : List Frame)
    (hk : StateProc.Context (labels := labels) L caller k) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) ls
      ⟨.effectExpr e env, k, m⟩ t m.stdout := by
  unfold stmts at h
  split at h
  next ann pann ty s rest =>
    let K := Frame.strongBind (.mk pann (.base (none, ty))) rest env :: k
    have hK : StateProc.Context (labels := labels) L caller K :=
      StateProc.context_cons hk (by simp [NoBoundary, hasBoundary])
    refine Returns.pre (CallLocal.sequence ann _ s rest env k m) ⟨rfl, rfl, rfl⟩ ?_
    split at h
    next tr hc =>
      split at h
      next hd =>
        cases h
        obtain ⟨loc, hl, frames⟩ := StateProcLocal.context_frames hK
        simpa only [← frames] using ret_returns (labels := labels) hret hc inv hd.1 loc hl caller
      next => cases h
    next hc =>
      split at h
      next x tr ha =>
        split at h
        next hd =>
          obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
          rw [State.update_key hx] at h
          rcases assign_runs_same ha inv hl hx hd.2.1 K with ub | ⟨_, m', out, allocation, inv', reach⟩
          · exact .inr ub
          · have o := stmts_returns hret _ _ rest h env m' ls inv' hls k hk
            rw [out] at o
            exact Returns.pre (reach.trans (StateReturnLocal.wildcard pann ty .unit rest env k m')) allocation o
        next => cases h
      next => cases h
  next => cases h
termination_by sizeOf e

/-- The whole recognized parameter body, with an actual runtime input. -/
theorem body_returns {x : Sym} {e : EE} {t : IntExpr.Term} (h : body file x e = some t)
    (env : Env) (caller : List Frame) (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : ConvInt.IsInt n) (slot : Locals.Slot m id addr n) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧ Rmw.Same m m' ∧ Mem.Concrete.LiveInt m' id addr ∧
      LocalReaches file labels false
        ⟨.effectExpr e env, .procedureReturn (CallReach.bodyLabels e) :: caller, m⟩
        ⟨.value (spec (t.val n)), .procedureReturn (CallReach.bodyLabels e) :: caller, m'⟩) ∨
    ArenaFail.Fails file labels false
      ⟨.effectExpr e env, .procedureReturn (CallReach.bodyLabels e) :: caller, m⟩ IntExpr.overflow := by
  unfold body at h
  split at h
  · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
    split at h
    · rename_i cond
      obtain ⟨hr, hfree⟩ := cond
      let B : EE := .mk ann (.sseq (.mk pann (.base (none, bt0))) a
        (.mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))))
      have hret : ReturnLabel (CallReach.bodyLabels B) ret := by
        refine ⟨r, bann, pann', r', hr, ?_⟩
        simp [B, CallReach.bodyLabels, saves, StmtIf.labelFree_saves a hfree, Map.ofList]
      have hs : stmts file ret [x] (StateSubst.defs (.lit n) (paramDefs x)) (fun _ => 1) a =
          some (StateSubst.subst (.lit n) t) := by
        rw [stmts_subst, h]; rfl
      let SAVE : EE := .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
      let K := Frame.strongBind (.mk pann (.base (none, bt0))) SAVE env ::
        .procedureReturn (CallReach.bodyLabels B) :: caller
      have result := stmts_returns (labels := labels) hret _ _ a hs env m [⟨x, id, addr⟩]
        ((param_at x env m hx hn slot).instantiate hn) rfl K rfl
      have pre := CallLocal.sequence (file := file) (labels := labels) ann (.mk pann (.base (none, bt0))) a SAVE env
        (.procedureReturn (CallReach.bodyLabels B) :: caller) m
      rcases Returns.pre pre ⟨rfl, rfl, rfl⟩ result with ⟨ok, m', out, allocation, live, run⟩ | fail
      · exact .inl ⟨(StateSubst.subst_ok (.lit n) t 0 hn).mp ok, m', out, allocation,
          live ⟨x, id, addr⟩ (by simp), by simpa only [StateSubst.subst_val, IntExpr.Term.val] using run⟩
      · exact .inr fail
    · cases h
  · cases h


end Silmaril.Compile.Core.Verified.ParamAlloc
