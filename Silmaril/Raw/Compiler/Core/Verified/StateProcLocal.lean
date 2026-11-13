module

public import Silmaril.Compiler.Core.Verified.StateStmtLocal.Defs

/-! # Complete State-callee traces inside operand arenas

These are local versions of the StateProc source proofs. Caller frames and the
allocation reserve remain arbitrary. Overflow is a local failure that an enclosing
arena can propagate, rather than an already-normalized top-level halt.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StateProcLocal

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open Mem.Concrete (LiveInt nextIntAddress)
open ReturnLit (Eff NoBoundary ReturnLabel)
open ReturnConst (focusMemory)
open ConvInt (IsInt)
open IntExpr (spec)
open StateExpr (Key Term values close)
open StateMem (Local Inv Fresh Defined defsOf update ptr)
open StateStmt
open State (stmts block classify classify_spec closeSize maxSize update_key)
open StateProc (Reserve Context context_cons)
open StateReturnLocal (bound_pop)

variable {file : Program} {labels L : Labels} {caller : List Frame}

/-- The context equality exposes the exact retained suffix and a boundary-free prefix. -/
theorem context_frames {k : List Frame} (hk : Context (labels := labels) L caller k) :
    ∃ loc, NoBoundary loc ∧ k = loc ++ .procedureReturn L :: caller := by
  induction k with
  | nil => cases hk
  | cons f fs ih =>
    cases f <;> simp only [Context, procedureContext] at hk
    case procedureReturn ls =>
      obtain ⟨hL, htail⟩ := Prod.mk.inj hk
      subst ls
      have hfs := (List.cons.inj htail).2
      subst fs
      exact ⟨[], by simp [NoBoundary, hasBoundary], rfl⟩
    all_goals try { cases hk }
    all_goals
      obtain ⟨loc, hl, rfl⟩ := ih hk
      exact ⟨_ :: loc, by simpa [NoBoundary, hasBoundary] using hl, rfl⟩

/-- Successful local return or local source overflow. -/
def Returns (s : State) (t : IntExpr.Term) (out : String) : Prop :=
  (t.Ok 0 ∧ ∃ m', m'.stdout = out ∧ LocalReaches file labels false s
    ⟨.value (spec (t.val 0)), .procedureReturn L :: caller, m'⟩) ∨
  ArenaFail.Fails file labels false s IntExpr.overflow

theorem Returns.pre {s s' : State} {t : IntExpr.Term} {out : String}
    (h : LocalReaches file labels false s s')
    (o : Returns (file := file) (labels := labels) (L := L) (caller := caller) s' t out) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) s t out := by
  rcases o with ⟨ok, m', hout, r⟩ | ub
  · exact .inl ⟨ok, m', hout, h.trans r⟩
  · exact .inr (ArenaFail.Fails.pre file labels h ub)

theorem ret_returns {ret : Sym} (hret : ReturnLabel L ret) {xs : List Sym} {e : Eff} {t : Term}
    (h : retStmt file ret xs e = some t) {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (hls : Keys ls xs)
    (nodup : (xs.map (·.key)).Nodup) (hd : Defined ds t = true) {k : List Frame}
    (hk : Context (labels := labels) L caller k) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) ⟨.effectExpr e env, k, m⟩
      (close (defsOf ds) t) m.stdout := by
  obtain ⟨loc, hl, rfl⟩ := context_frames hk
  exact StateReturnLocal.ret_returns hret h inv hls nodup hd loc hl caller

theorem ifRet_runs {ret : Sym} (hret : ReturnLabel L ret) {xs : List Sym} {e : Eff}
    {tc ta : Term} (h : ifRet file ret xs e = some (tc, ta)) {env : Env} {m : Mem.Concrete.State}
    {ls : List Local} {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (hls : Keys ls xs)
    (nodup : (xs.map (·.key)).Nodup) (hdc : Defined ds tc = true) (hda : Defined ds ta = true)
    {k : List Frame} (hk : Context (labels := labels) L caller k) :
    ArenaFail.Fails file labels false ⟨.effectExpr e env, k, m⟩ IntExpr.overflow ∨
    (tc.Ok (values (defsOf ds)) ∧ tc.val (values (defsOf ds)) ≠ 1 ∧
      Returns (file := file) (labels := labels) (L := L) (caller := caller) ⟨.effectExpr e env, k, m⟩
        (close (defsOf ds) ta) m.stdout) ∨
    (tc.Ok (values (defsOf ds)) ∧ tc.val (values (defsOf ds)) = 1 ∧ ∃ m', m'.stdout = m.stdout ∧
      Inv env m' ls ds ∧ LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩) := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', ea, a7, a8, rfl, hb', hcb, hfc,
    hfb, htc, hta⟩ := ifRet_inv h
  let σ := values (defsOf ds)
  let PU : EE := .mk a7 (.pure (.mk a8 () (.val .unit)))
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) ea PU)
  let REST : EE := .mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb IF)
  let K := Frame.strongBind (.mk a1 (.base (some c, cty))) REST env :: k
  have pre : LocalReaches file labels false
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec)) REST)) env, k, m⟩
      ⟨.effectExpr ec env, .bound :: K, m⟩ :=
    (CallLocal.sequence a0 _ _ _ env k m).trans
      (CallLocal.bound a2 _ env _ m)
  by_cases okc : tc.Ok σ
  · right
    obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
      tc htc okc (.bound :: K) m (inv.locs hdc)
    let cv := tc.val σ
    let env₁ := extendEnv [(c, spec cv)] env
    let KB := Frame.strongBind (.mk a4 (.base (some b, bty))) IF env₁ :: k
    obtain ⟨m₂, tch₂, conv⟩ := StateActionsLocal.boolSource_touched (file := file) (labels := labels) hcb env₁ KB m₁ cv
      (ConvInt.lookup_one rfl)
    let flag := decide (cv ≠ 1)
    let env₂ := extendEnv [(b, boolean flag)] env₁
    have hp : CallArena.LPure (file := file) (labels := labels)
        (.mk a6 () (.sym b')) env₂ (boolean flag) :=
      CallArena.of_eval (fun _ => Eval.sym (ConvInt.lookup_one hb'))
    let m₃ := SeqReach.focusMemory a5 m₂
    have enter : LocalReaches file labels false ⟨.effectExpr ec env, .bound :: K, m⟩
        ⟨.effectExpr (if flag then ea else PU) env₂, k, m₃⟩ :=
      run.trans ((StateReturnLocal.bound_pop hfr _ K m₁).trans
        ((CallLocal.bind a1 c cty _ REST env k m₁).trans
          ((CallLocal.sequence a3 _ cb IF env₁ k m₁).trans
            (conv.trans ((CallLocal.bind a4 b bty _ IF env₁ k m₂).trans
              (CallArena.effect_if a5 flag hp k m₂))))))
    have tch₃ : LoadTask.Touched m m₃ := tch.trans (tch₂.trans (seqFocus_touched a5 m₂))
    have inv₃ : Inv env m₃ ls ds := inv.touched tch₃
    by_cases h1 : cv = 1
    · right
      refine ⟨okc, h1, focusMemory a7 m₃, by simp [tch₃.stdout], inv₃.focus a7, ?_⟩
      have enter' : LocalReaches file labels false ⟨.effectExpr ec env, .bound :: K, m⟩
          ⟨.effectExpr PU env₂, k, m₃⟩ := by simpa [flag, h1] using enter
      exact pre.trans (enter'.trans (StateActionsLocal.pure_unit a7 a8 env₂ k m₃))
    · left
      refine ⟨okc, h1, ?_⟩
      have enter' : LocalReaches file labels false ⟨.effectExpr ec env, .bound :: K, m⟩
          ⟨.effectExpr ea env₂, k, m₃⟩ := by simpa [flag, h1] using enter
      have inv₂ : Inv env₂ m₃ ls ds := (inv₃.extend (hls.fresh hfc)).extend (hls.fresh hfb)
      have o := ret_returns hret hta inv₂ hls nodup hda hk
      rw [tch₃.stdout] at o
      exact Returns.pre (pre.trans enter') o
  · left
    exact ArenaFail.Fails.pre file labels pre (StateExpr.term_fails (file := file) (labels := labels)
      tc htc okc (.bound :: K) m (inv.locs hdc))


theorem shows_choose_left {s : State} {C A B : IntExpr.Term} {out : String} (okC : C.Ok 0)
    (h1 : C.val 0 ≠ 1) (o : Returns (file := file) (labels := labels) (L := L) (caller := caller) s A out) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) s (StmtIf.choose C A B) out := by
  rcases o with ⟨okA, m', hout, r⟩ | ub
  · left
    refine ⟨(StmtIf.choose_ok C A B 0).mpr ⟨okC, by simp [h1, okA]⟩, m', hout, ?_⟩
    rw [StmtIf.choose_val, ite_eq_right h1]; exact r
  · exact .inr ub

/-- The selection shows its second branch when the test is `1`. -/
theorem shows_choose_right {s : State} {C A B : IntExpr.Term} {out : String} (okC : C.Ok 0)
    (h1 : C.val 0 = 1) (o : Returns (file := file) (labels := labels) (L := L) (caller := caller) s B out) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) s (StmtIf.choose C A B) out := by
  rcases o with ⟨okB, m', hout, r⟩ | ub
  · left
    refine ⟨(StmtIf.choose_ok C A B 0).mpr ⟨okC, by simp [h1, okB]⟩, m', hout, ?_⟩
    rw [StmtIf.choose_val, ite_eq_left h1]; exact r
  · exact .inr ub

/-- **The statements** show the value of the closed expression, or undefined behaviour. -/
theorem stmts_returns {ret : Sym} (hret : ReturnLabel L ret) {xs : List Sym}
    (nodup : (xs.map (·.key)).Nodup) (ds : Key → Option IntExpr.Term) (sz : Key → Nat) (e : Eff)
    {T : IntExpr.Term} (h : stmts file ret xs ds sz e = some T) (env : Env) (m : Mem.Concrete.State)
    (ls : List Local) (inv : Inv env m ls ds) (hls : Keys ls xs) (k : List Frame) (hk : Context (labels := labels) L caller k) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) ⟨.effectExpr e env, k, m⟩ T m.stdout := by
  unfold stmts at h
  split at h
  next ann pann ty s rest =>
    let K := Frame.strongBind (.mk pann (.base (none, ty))) rest env :: k
    have hK : Context (labels := labels) L caller K := context_cons hk (by simp [NoBoundary, hasBoundary])
    have pre : LocalReaches file labels false ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (none, ty))) s rest))
        env, k, m⟩ ⟨.effectExpr s env, K, m⟩ :=
      CallLocal.sequence ann _ s rest env k m
    refine Returns.pre pre ?_
    split at h
    next t hc =>
      split at h
      next hd =>
        cases h
        exact ret_returns hret (classify_spec hc) inv hls nodup hd.1 hK
      next => cases h
    next c a hc =>
      split at h
      next hd =>
        cases hr : stmts file ret xs ds sz rest with
        | none => simp [hr] at h
        | some Tr =>
          simp only [hr, Option.map_some, Option.some.injEq] at h
          subst h
          have okC := fun okc => StateExpr.close_ok (defsOf ds) c (inv.defs_ok hd.1) okc
          rcases ifRet_runs hret (classify_spec hc) inv hls nodup hd.1 hd.2.1 hK with
            ub | ⟨okc, h1, o⟩ | ⟨okc, h1, m', out, inv', reach⟩
          · exact .inr ub
          · exact shows_choose_left (okC okc) (by rw [StateExpr.close_val]; exact h1) o
          · have o := stmts_returns hret nodup ds sz rest hr env m' ls inv' hls k hk
            rw [out] at o
            exact shows_choose_right (okC okc) (by rw [StateExpr.close_val]; exact h1)
              (Returns.pre (reach.trans (StateReturnLocal.wildcard pann ty
                .unit rest env k m')) o)
      next => cases h
    next x t hc =>
      split at h
      next hd =>
        obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
        rw [update_key hx] at h
        rcases StateStmtLocal.assign_runs (classify_spec hc) inv hl hx hd.2.1 K with ub | ⟨-, m', out, inv', reach⟩
        · exact .inr ub
        · have o := stmts_returns hret nodup _ _ rest h env m' ls inv' hls k hk
          rw [out] at o
          exact Returns.pre (reach.trans (StateReturnLocal.wildcard pann ty
            .unit rest env k m')) o
      next => cases h
    next x t hc =>
      split at h
      next hd =>
        obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
        rw [update_key hx] at h
        rcases StateStmtLocal.init_runs (classify_spec hc) inv hl hx hd.2.1 K with ub | ⟨-, m', ys, out, inv', reach⟩
        · exact .inr ub
        · have o := stmts_returns hret nodup _ _ rest h env m' ls inv' hls (.annotations ys :: k)
            (context_cons hk (by simp [NoBoundary, hasBoundary]))
          rw [out] at o
          exact Returns.pre (reach.trans (StateActionsLocal.annotations_bind ys pann ty .unit rest env k m'))
            o
      next => cases h
    next x hc =>
      split at h
      next hd =>
        obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd
        rw [update_key hx] at h
        obtain ⟨m', ys, out, inv', reach⟩ := StateStmtLocal.uninit_runs (classify_spec hc) inv hl hx K
        have o := stmts_returns hret nodup _ _ rest h env m' ls inv' hls (.annotations ys :: k)
          (context_cons hk (by simp [NoBoundary, hasBoundary]))
        rw [out] at o
        exact Returns.pre (reach.trans (StateActionsLocal.annotations_bind ys pann ty .unit rest env k m')) o
      next => cases h
    next => cases h
  next => cases h
termination_by sizeOf e


theorem block_returns {base : Int} {ret : Sym} (hret : ReturnLabel L ret) (xs : List Sym) (e : Eff)
    {T : IntExpr.Term} (h : block file ret xs e = some T) (env : Env) (m : Mem.Concrete.State)
    (ls : List Local) (inv : Inv env m ls (fun _ => none)) (hls : Keys ls xs) (fresh : Reserve base m ls)
    (k : List Frame) (hk : Context (labels := labels) L caller k) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) ⟨.effectExpr e env, k, m⟩ T m.stdout := by
  have hlen : ls.length = xs.length := by
    have := congrArg List.length hls; simpa using this
  unfold block at h
  split at h
  next a p x ty cr rest =>
    split at h
    next hc =>
      obtain ⟨hcr, hfx, hlt⟩ := hc
      obtain ⟨ann, lc, u, a1, a2, c1, a3, c2, pref, rfl⟩ := State.createInt_inv hcr
      have hnext : nextIntAddress m = m.lastAddress - 4 := fresh.nextIntAddress
      have hpos : 0 < nextIntAddress m := by
        rw [hnext, fresh.last, hlen]
        have := fresh.room
        omega
      let REST := rest
      let K := Frame.strongBind (.mk p (.base (some x, ty))) REST env :: k
      have create := StateActionsLocal.create (file := file) (labels := labels) ann a1 a2 a3 c1 c2 lc u
        pref env K m hpos
      rw [State.focus_nextId] at create
      let nl : Local := ⟨x, m.nextId, nextIntAddress m⟩
      let m₁ := Actions.created pref c2 (focusMemory ann m)
      let env₁ := extendEnv [(x, ptr nl)] env
      have bind := CallLocal.bind (file := file) (labels := labels) p x ty (ptr nl) REST env k m₁
      have fx : ∀ l ∈ ls, l.sym.key ≠ x.key := hls.fresh hfx
      have ids : ∀ l ∈ ls, l.id < m.nextId := fresh.ids
      have addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr := fresh.addrs
      have inv₁ : Inv env₁ m₁ (ls ++ [nl]) (fun _ => none) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro l hl y hy
          rcases List.mem_append.mp hl with hl | hl
          · rw [ConvInt.lookup_one_other (by rw [hy]; exact fx l hl)]
            exact inv.env l hl y hy
          · obtain rfl := List.mem_singleton.mp hl
            exact ConvInt.lookup_one hy
        · intro l hl
          rcases List.mem_append.mp hl with hl | hl
          · refine StateMem.live_created (Locals.liveInt_focus ann (inv.live l hl)) pref c2 ?_
            rw [State.focus_nextId]; exact Int.ne_of_lt (ids l hl)
          · obtain rfl := List.mem_singleton.mp hl
            have := Locals.created_live pref c2 (focusMemory ann m)
              (by
                rw [State.focus_dead, State.focus_nextId]
                intro hd
                have := fresh.dead m.nextId hd
                omega)
            rwa [Locals.nextIntAddress_focus, State.focus_nextId] at this
        · intro a ha b hb ne
          rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
          · exact inv.apart a ha b hb ne
          · obtain rfl := List.mem_singleton.mp hb
            refine ⟨Int.ne_of_lt (ids a ha), ?_⟩
            have := addrs a ha
            show a.addr + 4 ≤ nextIntAddress m ∨ nextIntAddress m + 4 ≤ a.addr
            omega
          · obtain rfl := List.mem_singleton.mp ha
            refine ⟨Int.ne_of_gt (ids b hb), ?_⟩
            have := addrs b hb
            show nextIntAddress m + 4 ≤ b.addr ∨ b.addr + 4 ≤ nextIntAddress m
            omega
          · obtain rfl := List.mem_singleton.mp ha
            obtain rfl := List.mem_singleton.mp hb
            exact absurd rfl ne
        · intro q d hd; cases hd
      have hls₁ : Keys (ls ++ [nl]) (xs ++ [x]) := by
        simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hls ⊢
        rw [hls]
      have last₁ : m₁.lastAddress = m.lastAddress - 4 := by
        rw [Locals.created_lastAddress, Locals.nextIntAddress_focus, hnext]
      have fresh₁ : Reserve base m₁ (ls ++ [nl]) := by
        refine ⟨?_, ?_, ?_, ?_, fresh.aligned, fresh.room⟩
        · intro id hd
          rw [Locals.created_dead, State.focus_dead] at hd
          have := fresh.dead id hd
          rw [State.created_nextId, State.focus_nextId]
          omega
        · intro l hl
          rw [State.created_nextId, State.focus_nextId]
          rcases List.mem_append.mp hl with hl | hl
          · have := ids l hl; omega
          · obtain rfl := List.mem_singleton.mp hl
            show m.nextId < m.nextId + 1
            omega
        · intro l hl
          rw [last₁]
          rcases List.mem_append.mp hl with hl | hl
          · have := addrs l hl; omega
          · obtain rfl := List.mem_singleton.mp hl
            show m.lastAddress - 4 ≤ nextIntAddress m
            omega
        · rw [last₁, fresh.last, List.length_append, List.length_singleton]
          push_cast
          ring
      have o := block_returns hret (xs ++ [x]) rest h env₁ m₁ (ls ++ [nl]) inv₁ hls₁ fresh₁ k hk
      have out : m₁.stdout = m.stdout := by simp [m₁, Actions.created_stdout]
      rw [out] at o
      exact Returns.pre ((CallLocal.sequence a _ _ REST env k m).trans
        (create.trans bind)) o
    next => cases h
  next =>
    split at h
    next nodup => exact stmts_returns hret nodup _ _ e h env m ls inv hls k hk
    next => cases h
termination_by sizeOf e

/-- A recognised State body returns its value to the procedure's caller. -/
theorem body_returns {base : Int} {body : EE} {t : IntExpr.Term}
    (h : State.recognizeBody file body = some t) (env : Env) (caller : List Frame)
    (m : Mem.Concrete.State) (fresh : Reserve base m []) :
    Returns (file := file) (labels := labels) (L := CallReach.bodyLabels body) (caller := caller)
      ⟨.effectExpr body env, .procedureReturn (CallReach.bodyLabels body) :: caller, m⟩ t m.stdout := by
  unfold State.recognizeBody at h
  split at h
  · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
    split at h
    · rename_i cond
      obtain ⟨hr, hfree⟩ := cond
      refine Returns.pre (CallLocal.sequence ann _ a _ env _ m) ?_
      let body : EE := .mk ann (.sseq (.mk pann (.base (none, bt0))) a
        (.mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))))
      have hret : ReturnLabel (CallReach.bodyLabels body) ret := by
        refine ⟨r, bann, pann', r', hr, ?_⟩
        simp [body, CallReach.bodyLabels, saves, StmtIf.labelFree_saves a hfree, Map.ofList]
      exact block_returns hret [] a h env m []
        ⟨by simp, by simp, by simp, fun _ _ hd => by cases hd⟩ rfl fresh
        (.strongBind (.mk pann (.base (none, bt0))) _ env ::
          .procedureReturn (CallReach.bodyLabels body) :: caller) rfl
    · cases h
  · cases h


/-- Every local State result finishes a sole arena task, or propagates overflow.
This bridge is independent of the recognizer and the number of callee slots. -/
theorem Returns.in_arena {c : Control} {fr : List Frame} {m : Mem.Concrete.State}
    {t : IntExpr.Term} {out : String}
    (h : Returns (file := file) (labels := labels) (L := L) (caller := []) ⟨c, fr, m⟩ t out)
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame) :
    (t.Ok 0 ∧ ∃ m', m'.stdout = out ∧ CoreReaches file labels
      ⟨.interleave done [(i, c, fr)], k, m⟩
      ⟨.interleave ((i, spec (t.val 0), []) :: done) [], k, m'⟩) ∨
    ArenaFail.Fails file labels false ⟨.interleave done [(i, c, fr)], k, m⟩ IntExpr.overflow := by
  have pending : Pending [] i := ⟨by simp, by simp⟩
  rcases h with ⟨ok, m', hout, run⟩ | fail
  · left
    refine ⟨ok, m', hout, reaches_of_local file labels ?_⟩
    apply drive_task file labels pending
    refine ⟨[], ?_, rfl⟩
    have pop : LocalReaches file labels false
        ⟨.value (spec (t.val 0)), [.procedureReturn L], m'⟩
        ⟨.value (spec (t.val 0)), [], m'⟩ :=
      .single (.next (by simp [requestAux, awaitsScheduling]) (LoadTask.plain_value _))
    simpa [taskFlag] using run.trans pop
  · right
    apply ArenaFail.fail_task file labels pending
    simpa [taskFlag] using fail

/-- Any body accepted by StateProc runs inside a sole operand task. The caller
supplies its allocation reserve; it supplies no per-step lifting invariants. -/
theorem body_in_arena {base : Int} {body : EE} {t : IntExpr.Term}
    (h : State.recognizeBody file body = some t) (env : Env) (m : Mem.Concrete.State)
    (fresh : Reserve base m [])
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame) :
    (t.Ok 0 ∧ ∃ m', m'.stdout = m.stdout ∧ CoreReaches file labels
      ⟨.interleave done [(i, .effectExpr body env,
        [.procedureReturn (CallReach.bodyLabels body)])], k, m⟩
      ⟨.interleave ((i, spec (t.val 0), []) :: done) [], k, m'⟩) ∨
    ArenaFail.Fails file labels false
      ⟨.interleave done [(i, .effectExpr body env,
        [.procedureReturn (CallReach.bodyLabels body)])], k, m⟩ IntExpr.overflow :=
  Returns.in_arena (body_returns h env [] m fresh) done i k

end Silmaril.Compile.Core.Verified.StateProcLocal
