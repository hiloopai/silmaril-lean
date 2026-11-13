module

public import Silmaril.Compiler.Core.Verified.StateSubst.Defs
public import Silmaril.Compiler.Core.Verified.CallArg.Defs

/-! # Mutable integer parameters as persistent State slots

Argument objects belong to the caller. A callee reads and assigns its parameter
slots, but returns without killing them; the caller performs that cleanup.
This first recognizer admits straight assignments followed by an integer return.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.StateParam

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open ReturnLit (Eff NoBoundary ReturnLabel)
open ReturnConst (focusMemory)
open StateExpr (Key Term values close)
open StateMem (Local Inv Defined defsOf update ptr)
open StateStmt (retStmt assignStmt isLocal Keys)
open IntExpr (spec)

/-- Parameter objects survive the callee's return. -/
def stmts (file : File Codec.wireModel Unit Unit) (ret : Sym) (ps : List Sym) :
    (Key → Option IntExpr.Term) → (Key → Nat) → Eff → Option IntExpr.Term
  | ds, sz, .mk _ (.sseq (.mk _ (.base (none, _))) s rest) =>
    match retStmt file ret [] s with
    | some t =>
      if Defined ds t = true ∧ State.closeSize sz t ≤ State.maxSize then
        some (close (defsOf ds) t) else none
    | none => match assignStmt file s with
      | some (x, t) =>
        if isLocal ps x = true ∧ Defined ds t = true ∧ State.closeSize sz t ≤ State.maxSize then
          stmts file ret ps (update ds x.key (some (close (defsOf ds) t)))
            (fun q => if q = x.key then State.closeSize sz t else sz q) rest
        else none
      | none => none
  | _, _, _ => none
termination_by _ _ e => sizeOf e

variable {file : Program} {labels L : Labels} {caller : List Frame}

/-- Successful local return, preserving all caller-owned parameter lifetimes. -/
def Returns (ls : List Local) (s : State) (t : IntExpr.Term) (out : String) : Prop :=
  (t.Ok 0 ∧ ∃ m', m'.stdout = out ∧ (∀ l ∈ ls, Mem.Concrete.LiveInt m' l.id l.addr) ∧
    LocalReaches file labels false s
      ⟨.value (spec (t.val 0)), .procedureReturn L :: caller, m'⟩) ∨
  ArenaFail.Fails file labels false s IntExpr.overflow

theorem Returns.pre {ls : List Local} {s s' : State} {t : IntExpr.Term} {out : String}
    (h : LocalReaches file labels false s s')
    (o : Returns (file := file) (labels := labels) (L := L) (caller := caller) ls s' t out) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) ls s t out := by
  rcases o with ⟨ok, m', hout, live, r⟩ | ub
  · exact .inl ⟨ok, m', hout, live, h.trans r⟩
  · exact .inr (ArenaFail.Fails.pre file labels h ub)

/-- A local return-label transfer changes only diagnostic memory. -/
theorem jump_return {ret l : Sym} (hl : l.key = ret.key) (hret : ReturnLabel L ret)
    (v : Val) (env : Env) {loc : List Frame} (hk : NoBoundary loc)
    (caller : List Frame) (m : Mem.Concrete.State) :
    ∃ m', LoadTask.Touched m m' ∧ LocalReaches file labels false
      ⟨.value v, .runLabel l [] [] env :: (loc ++ .procedureReturn L :: caller), m⟩
      ⟨.value v, .procedureReturn L :: caller, m'⟩ := by
  obtain ⟨r, bann, pann, r', hr, hlook⟩ := hret
  have hlook' : L.lookup l = some ([r], .mk bann (.pure (.mk pann () (.sym r')))) := by
    rw [ReturnLit.lookup_key hl]; exact hlook
  have hb : hasBoundary (loc ++ .procedureReturn L :: caller) = true := by
    simp [hasBoundary, List.any_append]
  refine ⟨focusMemory bann m, LoadTask.focusMemory_touched bann m, ?_⟩
  refine .head (.next (c' := .effectExpr (.mk bann (.pure (.mk pann () (.sym r'))))
      (extendEnv [(r, v)] env)) (k' := .procedureReturn L :: caller)
    ?_ (LoadTask.plain_effectExpr _ _)) ?_
  · rw [requestAux.eq_def]
    simp [awaitsScheduling, requestJump, hb, jump, jumpDestination,
      Call.context_local hk L caller, hlook']
  · exact CallLocal.pure bann (fun _ => .sym (ConvInt.lookup_one hr)) _ _

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
        refine ⟨m', totalTouch.stdout, (inv.touched totalTouch).live, ?_⟩
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
    refine Returns.pre (CallLocal.sequence ann _ s rest env k m) ?_
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
          rcases StateStmtLocal.assign_runs ha inv hl hx hd.2.1 K with ub | ⟨_, m', out, inv', reach⟩
          · exact .inr ub
          · have o := stmts_returns hret _ _ rest h env m' ls inv' hls k hk
            rw [out] at o
            exact Returns.pre (reach.trans (StateReturnLocal.wildcard pann ty .unit rest env k m')) o
        next => cases h
      next => cases h
  next => cases h
termination_by sizeOf e

theorem stmts_subst (file : File Codec.wireModel Unit Unit) (ret : Sym) (ps : List Sym)
    (ds : Key → Option IntExpr.Term) (sz : Key → Nat) (e : Eff) (v : IntExpr.Term) :
    stmts file ret ps (StateSubst.defs v ds) sz e =
      (stmts file ret ps ds sz e).map (StateSubst.subst v) := by
  unfold stmts
  split
  next ann pann ty s rest =>
    rename_i sz _ _ _
    split
    next t hc => simp only [StateSubst.defined_defs, StateSubst.close_defs]; split <;> rfl
    next =>
      split
      next x t hc =>
        simp only [StateSubst.defined_defs]
        split
        · simp only [StateSubst.close_defs]
          simpa only [StateSubst.defs_update, Option.map_some] using
            stmts_subst file ret ps (update ds x.key (some (close (defsOf ds) t)))
              (fun q => if q = x.key then State.closeSize sz t else sz q) rest v
        · rfl
      next => rfl
  next => rfl
termination_by sizeOf e

/-- One symbolic parameter, initialized from its argument object. -/
def paramDefs (x : Sym) : Key → Option IntExpr.Term := fun q =>
  if q = x.key then some .var else none

def body (file : File Codec.wireModel Unit Unit) (x : Sym) : Eff → Option IntExpr.Term
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ StmtIf.labelFree a = true then
        stmts file ret [x] (paramDefs x) (fun _ => 1) a else none
  | _ => none

/-- A real parameter pointer supplies the symbolic State invariant. -/
theorem param_at (x : Sym) (env : Env) (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : ConvInt.IsInt n) (slot : Locals.Slot m id addr n) :
    StateSubst.At n env m [⟨x, id, addr⟩] (paramDefs x) where
  env l hl y hy := by
    obtain rfl := List.mem_singleton.mp hl
    exact (ReturnLit.lookup_key hy).trans hx
  live l hl := by obtain rfl := List.mem_singleton.mp hl; exact slot.live
  apart a ha b hb ne := by
    obtain rfl := List.mem_singleton.mp ha
    obtain rfl := List.mem_singleton.mp hb
    exact False.elim (ne rfl)
  defs q d hd := by
    unfold paramDefs at hd
    split at hd
    · rename_i hq
      cases hd
      exact ⟨hn, ⟨x, id, addr⟩, by simp, hq.symm, slot⟩
    · cases hd

/-- The whole recognized parameter body, with an actual runtime input. -/
theorem body_returns {x : Sym} {e : EE} {t : IntExpr.Term} (h : body file x e = some t)
    (env : Env) (caller : List Frame) (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : ConvInt.IsInt n) (slot : Locals.Slot m id addr n) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧ Mem.Concrete.LiveInt m' id addr ∧
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
      rcases Returns.pre pre result with ⟨ok, m', out, live, run⟩ | fail
      · exact .inl ⟨(StateSubst.subst_ok (.lit n) t 0 hn).mp ok, m', out,
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
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧ Mem.Concrete.LiveInt m' id addr ∧
      CoreReaches file labels
        ⟨.interleave done [(i, .effectExpr e env,
          [.procedureReturn (CallReach.bodyLabels e)])], k, m⟩
        ⟨.interleave ((i, spec (t.val n), []) :: done) [], k, m'⟩) ∨
    ArenaFail.Fails file labels false
      ⟨.interleave done [(i, .effectExpr e env,
        [.procedureReturn (CallReach.bodyLabels e)])], k, m⟩ IntExpr.overflow := by
  have pending : Pending [] i := ⟨by simp, by simp⟩
  rcases body_returns (labels := labels) h env [] m hx hn slot with ⟨ok, m', out, live, run⟩ | fail
  · left
    refine ⟨ok, m', out, live, reaches_of_local file labels ?_⟩
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

end Silmaril.Compile.Core.Verified.StateParam
