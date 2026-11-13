module

public import Silmaril.Compiler.Core.Verified.StateParam.Defs
public import Silmaril.Compiler.Core.Verified.PrintMem.Defs
/-! # Caller frames through mutable parameter bodies

The complete local and arena traces preserve any memory predicate closed under
parameter-slot stores. In particular, disjoint caller slots retain their values;
preserving only the allocation frontier and parameter lifetime does not imply this.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.StateParamFrame

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open ReturnLit (Eff NoBoundary ReturnLabel)
open ReturnConst (focusMemory)
open StateExpr (Key Term values close)
open StateMem (Local Inv Defined defsOf update ptr)
open StateStmt (retStmt assignStmt isLocal Keys)
open StateParam (stmts body paramDefs param_at jump_return stmts_subst)
open IntExpr (spec)

variable {file : Program} {labels L : Labels} {caller : List Frame}

/-- Creating a fresh disjoint argument object leaves the caller's integer slots
and their definitions intact. -/
theorem inv_created {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds)
    (pref : Prefix) (ann : List Annot)
    (fresh : ∀ l ∈ ls, l.id ≠ m.nextId)
    (apart : ∀ l ∈ ls, Slots.Apart (Mem.Concrete.nextIntAddress m) 4 l.addr 4) :
    Inv env (Actions.created pref ann m) ls ds := by
  refine { env := inv.env, live := ?_, apart := inv.apart, defs := ?_ }
  · intro l hl
    exact StateMem.live_created (inv.live l hl) pref ann (fresh l hl)
  · intro q d hd
    obtain ⟨ok, l, hl, key, slot⟩ := inv.defs q d hd
    exact ⟨ok, l, hl, key, Slots.slot_created slot pref ann (fresh l hl) (apart l hl)⟩

/-- Killing the call-owned argument preserves disjoint caller objects, including
pointer provenance. Distinct allocation identifiers are required explicitly. -/
theorem inv_killed {env : Env} {m : Mem.Concrete.State} {ls ps : List Local}
    {ds : Key → Option IntExpr.Term} {pts : Key → Option StateExpr.PtsTo}
    (inv : Inv env m ls ds ps pts) (id : Int)
    (hi : ∀ l ∈ ls, l.id ≠ id) (hp : ∀ l ∈ ps, l.id ≠ id) :
    Inv env (Locals.killed m id) ls ds ps pts := by
  have := inv.ptrs.frame (StateMem.PFrame.killed ps m id hp)
  refine { env := inv.env, live := ?_, apart := inv.apart, defs := ?_ }
  · intro l hl
    exact StateMem.live_killed (inv.live l hl) id (hi l hl)
  · intro q d hd
    obtain ⟨ok, l, hl, key, slot⟩ := inv.defs q d hd
    exact ⟨ok, l, hl, key, Slots.slot_killed slot id (hi l hl)⟩

/-- A store into a disjoint callee slot preserves the caller's integer definitions
and any tracked pointer objects. The environments of caller and callee may differ. -/
theorem inv_stored {env : Env} {m : Mem.Concrete.State} {ls ps : List Local}
    {ds : Key → Option IntExpr.Term} {pts : Key → Option StateExpr.PtsTo}
    (inv : Inv env m ls ds ps pts) (id addr v : Int)
    (hi : ∀ l ∈ ls, Slots.Apart addr 4 l.addr 4)
    (hp : ∀ l ∈ ps, Slots.Apart l.addr 8 addr 4) :
    Inv env (Locals.stored m id addr v) ls ds ps pts := by
  have pf : StateMem.PFrame ps m (Locals.stored m id addr v) := by
    apply StateMem.PFrame.write
    simpa [Mem.Concrete.plainBytes, Mem.Concrete.encodeInteger_length] using hp
  have := inv.ptrs.frame pf
  refine { env := inv.env, live := ?_, apart := inv.apart, defs := ?_ }
  · intro l hl
    exact Slots.live_stored (inv.live l hl) id addr v
  · intro q d hd
    obtain ⟨ok, l, hl, key, slot⟩ := inv.defs q d hd
    exact ⟨ok, l, hl, key, Slots.slot_stored slot id addr v (hi l hl)⟩

/-- The corresponding frame rule for an unspecified integer store. -/
theorem inv_unstored {env : Env} {m : Mem.Concrete.State} {ls ps : List Local}
    {ds : Key → Option IntExpr.Term} {pts : Key → Option StateExpr.PtsTo}
    (inv : Inv env m ls ds ps pts) (id addr : Int)
    (hi : ∀ l ∈ ls, Slots.Apart addr 4 l.addr 4)
    (hp : ∀ l ∈ ps, Slots.Apart l.addr 8 addr 4) :
    Inv env (Uninitialized.stored m id addr) ls ds ps pts := by
  have pf : StateMem.PFrame ps m (Uninitialized.stored m id addr) := by
    apply StateMem.PFrame.write
    simpa [Mem.Concrete.plainBytes] using hp
  have := inv.ptrs.frame pf
  refine { env := inv.env, live := ?_, apart := inv.apart, defs := ?_ }
  · intro l hl
    exact StateMem.live_uninit (inv.live l hl) id addr
  · intro q d hd
    obtain ⟨ok, l, hl, key, slot⟩ := inv.defs q d hd
    exact ⟨ok, l, hl, key, StateMem.slot_uninit slot id addr (hi l hl)⟩

/-- A caller's complete memory invariant is closed under disjoint callee stores.
No relation between caller and callee symbol keys is needed. -/
theorem caller_closed (env : Env) (ls ps args : List Local)
    (ds : Key → Option IntExpr.Term) (pts : Key → Option StateExpr.PtsTo)
    (hi : ∀ a ∈ args, ∀ l ∈ ls, Slots.Apart a.addr 4 l.addr 4)
    (hp : ∀ a ∈ args, ∀ l ∈ ps, Slots.Apart l.addr 8 a.addr 4) :
    PrintMem.Closed (fun m => Inv env m ls ds ps pts) args where
  touched := fun inv t => inv.touched t
  excluded := fun n inv => inv.nextExcluded n
  stored := fun v ha inv => inv_stored inv _ _ v (hi _ ha) (hp _ ha)
  unstored := fun ha inv => inv_unstored inv _ _ (hi _ ha) (hp _ ha)

/-- Independent caller predicates can be retained by the same trace. -/
theorem closed_and {P Q : Mem.Concrete.State → Prop} {args : List Local}
    (p : PrintMem.Closed P args) (q : PrintMem.Closed Q args) :
    PrintMem.Closed (fun m => P m ∧ Q m) args where
  touched := fun h t => ⟨p.touched h.1 t, q.touched h.2 t⟩
  excluded := fun n h => ⟨p.excluded n h.1, q.excluded n h.2⟩
  stored := fun v ha h => ⟨p.stored v ha h.1, q.stored v ha h.2⟩
  unstored := fun ha h => ⟨p.unstored ha h.1, q.unstored ha h.2⟩

/-- Parameter assignments keep the allocation metadata needed by the reserve
proofs, independently of which caller objects are framed. -/
theorem allocation_closed (initial : Mem.Concrete.State) (args : List Local) :
    PrintMem.Closed (Rmw.Same initial) args where
  touched := by
    intro m m' h t
    obtain ⟨l, u, rfl⟩ := t
    exact h
  excluded := fun _ h => h
  stored := fun v _ h => h.trans (Rmw.same_stored _ _ _ v)
  unstored := by
    intro m l _ h
    apply h.trans
    obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape l.addr
      (Mem.Concrete.plainBytes (List.replicate 4 none)) m
    simp only [Uninitialized.stored, hw]
    exact ⟨rfl, rfl, rfl⟩

/-- Successful local return, preserving all caller-owned parameter lifetimes. -/
def Returns (P : Mem.Concrete.State → Prop) (ls : List Local) (s : State) (t : IntExpr.Term) (out : String) : Prop :=
  (t.Ok 0 ∧ ∃ m', m'.stdout = out ∧ P m' ∧ (∀ l ∈ ls, Mem.Concrete.LiveInt m' l.id l.addr) ∧
    LocalReaches file labels false s
      ⟨.value (spec (t.val 0)), .procedureReturn L :: caller, m'⟩) ∨
  ArenaFail.Fails file labels false s IntExpr.overflow

theorem Returns.pre {P : Mem.Concrete.State → Prop} {ls : List Local} {s s' : State} {t : IntExpr.Term} {out : String}
    (h : LocalReaches file labels false s s')
    (o : Returns (file := file) (labels := labels) (L := L) (caller := caller) P ls s' t out) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) P ls s t out := by
  rcases o with ⟨ok, m', hout, hp, live, r⟩ | ub
  · exact .inl ⟨ok, m', hout, hp, live, h.trans r⟩
  · exact .inr (ArenaFail.Fails.pre file labels h ub)

/-- A parameter return reads every initialized slot but kills none of them. -/
theorem ret_returns {ret : Sym} (hret : ReturnLabel L ret) {e : Eff} {t : Term}
    (h : retStmt file ret [] e = some t) {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (hd : Defined ds t = true)
    (loc : List Frame) (hk : NoBoundary loc) (caller : List Frame)
    (P : Mem.Concrete.State → Prop) (cl : PrintMem.Closed P ls) (hp : P m) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) P ls
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
        refine ⟨m', totalTouch.stdout, cl.touched hp totalTouch, (inv.touched totalTouch).live, ?_⟩
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
    (hk : StateProc.Context (labels := labels) L caller k)
    (P : Mem.Concrete.State → Prop) (cl : PrintMem.Closed P ls) (hp : P m) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) P ls
      ⟨.effectExpr e env, k, m⟩ t m.stdout := by
  unfold stmts at h
  split at h
  next ann pann ty s rest =>
    let K := Frame.strongBind (.mk pann (.base (none, ty))) rest env :: k
    have hK : StateProc.Context (labels := labels) L caller K :=
      StateProc.context_cons hk (by simp [NoBoundary, hasBoundary])
    refine Returns.pre (CallLocal.sequence ann _ s rest env k m) ?_
    split at h
    next tr hc =>
      split at h
      next hd =>
        cases h
        obtain ⟨loc, hl, frames⟩ := StateProcLocal.context_frames hK
        simpa only [← frames] using ret_returns (labels := labels) hret hc inv hd.1 loc hl caller P cl hp
      next => cases h
    next hc =>
      split at h
      next x tr ha =>
        split at h
        next hd =>
          obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
          rw [State.update_key hx] at h
          rcases StateStmtLocal.assign_runs_preserving ha inv hl hx hd.2.1 K P
              cl.touched cl.excluded (fun v hp => cl.stored v hl hp) hp with
            ub | ⟨_, m', out, hp', inv', reach⟩
          · exact .inr ub
          · have o := stmts_returns hret _ _ rest h env m' ls inv' hls k hk P cl hp'
            rw [out] at o
            exact Returns.pre (reach.trans (StateReturnLocal.wildcard pann ty .unit rest env k m')) o
        next => cases h
      next => cases h
  next => cases h
termination_by sizeOf e

/-- The whole recognized parameter body, with an actual runtime input. -/
theorem body_returns {x : Sym} {e : EE} {t : IntExpr.Term} (h : body file x e = some t)
    (env : Env) (caller : List Frame) (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : ConvInt.IsInt n) (slot : Locals.Slot m id addr n)
    (P : Mem.Concrete.State → Prop) (cl : PrintMem.Closed P [⟨x, id, addr⟩]) (hp : P m) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧ P m' ∧ Mem.Concrete.LiveInt m' id addr ∧
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
        ((param_at x env m hx hn slot).instantiate hn) rfl K rfl P cl hp
      have pre := CallLocal.sequence (file := file) (labels := labels) ann (.mk pann (.base (none, bt0))) a SAVE env
        (.procedureReturn (CallReach.bodyLabels B) :: caller) m
      rcases Returns.pre pre result with ⟨ok, m', out, hp', live, run⟩ | fail
      · exact .inl ⟨(StateSubst.subst_ok (.lit n) t 0 hn).mp ok, m', out, hp',
          live ⟨x, id, addr⟩ (by simp), by simpa only [StateSubst.subst_val, IntExpr.Term.val] using run⟩
      · exact .inr fail
    · cases h
  · cases h

/-- A parameter State body also executes as the sole remaining operand task.
The caller retains the same live argument object for its eventual cleanup. -/
theorem body_in_arena {x : Sym} {e : EE} {t : IntExpr.Term} (h : body file x e = some t)
    (env : Env) (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : ConvInt.IsInt n) (slot : Locals.Slot m id addr n)
    (P : Mem.Concrete.State → Prop) (cl : PrintMem.Closed P [⟨x, id, addr⟩]) (hp : P m)
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧ P m' ∧ Mem.Concrete.LiveInt m' id addr ∧
      CoreReaches file labels
        ⟨.interleave done [(i, .effectExpr e env,
          [.procedureReturn (CallReach.bodyLabels e)])], k, m⟩
        ⟨.interleave ((i, spec (t.val n), []) :: done) [], k, m'⟩) ∨
    ArenaFail.Fails file labels false
      ⟨.interleave done [(i, .effectExpr e env,
        [.procedureReturn (CallReach.bodyLabels e)])], k, m⟩ IntExpr.overflow := by
  have pending : Pending [] i := ⟨by simp, by simp⟩
  rcases body_returns (labels := labels) h env [] m hx hn slot P cl hp with ⟨ok, m', out, hp', live, run⟩ | fail
  · left
    refine ⟨ok, m', out, hp', live, reaches_of_local file labels ?_⟩
    apply drive_task file labels pending
    refine ⟨[], ?_, rfl⟩
    have pop : LocalReaches file labels false
        ⟨.value (spec (t.val n)), [.procedureReturn (CallReach.bodyLabels e)], m'⟩
        ⟨.value (spec (t.val n)), [], m'⟩ :=
      .single (.next (by simp [requestAux, awaitsScheduling]) (LoadTask.plain_value _))
    simpa [taskFlag] using run.trans pop
  · right
    apply ArenaFail.fail_task file labels pending
    simpa [taskFlag] using fail

/-- A mutable parameter body returns with every disjoint caller slot unchanged,
including its closed definition and pointer provenance. -/
theorem body_preserves_caller {x : Sym} {e : EE} {t : IntExpr.Term}
    (h : body file x e = some t) (env : Env) (caller : List Frame)
    (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : ConvInt.IsInt n) (slot : Locals.Slot m id addr n)
    {cenv : Env} {ls ps : List Local} {ds : Key → Option IntExpr.Term}
    {pts : Key → Option StateExpr.PtsTo} (inv : Inv cenv m ls ds ps pts)
    (hi : ∀ l ∈ ls, Slots.Apart addr 4 l.addr 4)
    (hp : ∀ l ∈ ps, Slots.Apart l.addr 8 addr 4) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧
      (Inv cenv m' ls ds ps pts ∧ Rmw.Same m m') ∧
      Mem.Concrete.LiveInt m' id addr ∧ LocalReaches file labels false
        ⟨.effectExpr e env, .procedureReturn (CallReach.bodyLabels e) :: caller, m⟩
        ⟨.value (spec (t.val n)), .procedureReturn (CallReach.bodyLabels e) :: caller, m'⟩) ∨
    ArenaFail.Fails file labels false
      ⟨.effectExpr e env, .procedureReturn (CallReach.bodyLabels e) :: caller, m⟩
      IntExpr.overflow := by
  exact body_returns h env caller m hx hn slot _
    (closed_and (caller_closed cenv ls ps [⟨x, id, addr⟩] ds pts
      (by intro a ha; obtain rfl := List.mem_singleton.mp ha; exact hi)
      (by intro a ha; obtain rfl := List.mem_singleton.mp ha; exact hp))
      (allocation_closed m [⟨x, id, addr⟩])) ⟨inv, rfl, rfl, rfl⟩

/-- Scheduled procedure entry and the complete mutable body preserve the same
caller predicate, with completed operands and arbitrary outer frames retained. -/
theorem prepared_in_arena {e : EE} {x g : Sym} {t : IntExpr.Term}
    (hbody : body file x e = some t) (env : Env) (m : Mem.Concrete.State)
    {id addr n : Int} (hn : Mem.Concrete.IntRange n) (slot : Locals.Slot m id addr n)
    (ordinary : libraryCall file g = none)
    (resolved : procedureBody file g [.object (.pointer (.allocated id addr))] =
      .ok (e, [(x, .object (.pointer (.allocated id addr)))]))
    (P : Mem.Concrete.State → Prop) (cl : PrintMem.Closed P [⟨x, id, addr⟩]) (hp : P m)
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame) :
    StateStmt.Overflows (file := file) (labels := labels)
      ⟨.interleave done [(i, .apply (.procedure env)
        [.loaded (.specified (.pointer (.function g))),
         .object (.pointer (.allocated id addr))], [])], k, m⟩ ∨
    t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧ P m' ∧ Mem.Concrete.LiveInt m' id addr ∧
      CoreReaches file labels
      ⟨.interleave done [(i, .apply (.procedure env)
        [.loaded (.specified (.pointer (.function g))),
         .object (.pointer (.allocated id addr))], [])], k, m⟩
      ⟨.interleave ((i, spec (t.val n), []) :: done) [], k, m'⟩ := by
  have entry := ArenaCall.procedure_enter file labels m done i g
    [.object (.pointer (.allocated id addr))] env e
    [(x, .object (.pointer (.allocated id addr)))] [] k ordinary resolved
  rcases body_in_arena (labels := labels) hbody
      (extendEnv [(x, .object (.pointer (.allocated id addr)))] env) m
      (ConvInt.lookup_one rfl) hn slot P cl hp done i k with
    ⟨ok, m', out, hp', live, run⟩ | fail
  · exact .inr ⟨ok, m', out, hp', live,
      entry.trans (by simpa [CallReach.bodyLabels] using run)⟩
  · obtain ⟨s', run, halt⟩ := ArenaFail.fail_reaches file labels fail
    exact .inl ⟨s', entry.trans (by simpa only [CallReach.bodyLabels] using run), halt⟩

end Silmaril.Compile.Core.Verified.StateParamFrame
