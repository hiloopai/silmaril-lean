module

public import Silmaril.Compiler.Core.Verified.ParamRun.Defs
public import Silmaril.Compiler.Core.Verified.StateParamFrame.Defs
/-! # Caller frames through conditional parameter bodies

The same local trace that executes a `ParamRun` body retains a caller predicate
through assignments, initialisation, conditionals and local cleanup. Callee and
caller environments need not share symbol names.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ParamRunFrame

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf)
open Mem.Concrete (LiveInt nextIntAddress)
open ReturnLit (Eff NoBoundary ReturnLabel)
open ReturnConst (focusMemory)
open ConvInt (IsInt)
open StateExpr (Key Term values close)
open StateMem (Local Inv Defined defsOf update ptr)
open StateStmt (retStmt assignStmt initStmt uninitStmt isLocal isFresh Keys seqFocus_touched
  killsRun_nil killsRun_cons)
open StateGlobals (ifParts ifParts_inv seqParts seqParts_inv isUnit isUnit_inv termSize EnvOk
  inv_withEnv)
open StateProc (Context context_cons)
open IntExpr (spec)
open LoadTask (Touched)

open ParamRun (run creation block fuel body Keeps Uses Returns Pend same_touched keeps_same
  keeps_killed if_runs returns_choose_left returns_choose_right same_uninit block_subst)

variable {file : Program} {labels L : Labels} {caller : List Frame}

/-- Closure under stores to all callee slots and kills of its own locals. Parameter
objects remain live for cleanup by the caller. -/
structure Closed (P : Mem.Concrete.State → Prop) (args locals : List Local) : Prop
    extends PrintMem.Closed P args where
  killed : ∀ {m : Mem.Concrete.State} {l : Local}, l ∈ locals → P m → P (Locals.killed m l.id)

theorem Closed.focus {P : Mem.Concrete.State → Prop} {args locals : List Local}
    (cl : Closed P args locals) {m : Mem.Concrete.State} (ann : List Annot) (hp : P m) :
    P (focusMemory ann m) := cl.toClosed.focus ann hp

/-- Allocation metadata and the caller predicate come from one execution witness. -/
abbrev KeepsFrame (P : Mem.Concrete.State → Prop) (m m' : Mem.Concrete.State) : Prop :=
  Keeps m m' ∧ P m'

theorem returns_keep {P : Mem.Concrete.State → Prop} {ps : List Local}
    {s s' : State} {t : IntExpr.Term} {out : String}
    (h : LocalReaches file labels false s s') (k : Keeps s.memory s'.memory)
    (o : Returns (file := file) (labels := labels) (L := L) (caller := caller)
      (KeepsFrame P) ps s' t out) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller)
      (KeepsFrame P) ps s t out :=
  o.pre h fun _ h' => ⟨k.trans h'.1, h'.2⟩

theorem init_keeps {e : Eff} {x : Sym} {t : Term} (h : initStmt file e = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (k : List Frame)
    (P : Mem.Concrete.State → Prop) (cl : PrintMem.Closed P ls) (hp : P m) :
    ArenaFail.Fails file labels false ⟨.effectExpr e env, k, m⟩ IntExpr.overflow ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m' xs, m'.stdout = m.stdout ∧ (Rmw.Same m m' ∧ P m') ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ∧
        LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, a1, t₀, ty, a2, e', a3, lc, u, b1, c1, b2, b3, b4, c3, b5, s, t', rfl, ht', htx, hs,
    he⟩ := StateStmt.initStmt_inv h
  let σ := values (defsOf ds)
  let ST : EE := .mk a3 (.action (.mk .pos (.mk lc u (.store false (Locals.intVal b1 c1)
    (.mk b2 () (.sym x)) (.mk b3 () (.call (.sym s) [Locals.intVal b4 c3, .mk b5 () (.sym t')])) .na))))
  let K := Frame.strongBind (.mk a1 (.base (some t₀, ty))) ST env :: k
  have pre : LocalReaches file labels false ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some t₀, ty)))
      (.mk a2 (.bound e')) ST)) env, k, m⟩ ⟨.effectExpr e' env, .bound :: K, m⟩ :=
    (CallLocal.sequence a0 _ _ _ env k m).trans (CallLocal.bound a2 _ env _ m)
  have locs := inv.locs hd
  by_cases ok : t.Ok σ
  · right
    refine ⟨ok, ?_⟩
    obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
      t he ok (.bound :: K) m locs
    let v := t.val σ
    have hv : IsInt v := StateExpr.Term.int_of_ok t ok
    let env₁ := extendEnv [(t₀, spec v)] env
    have inv₁ : Inv env m₁ ls ds := inv.touched tch
    have hx₁ : env₁.lookup x = some (ptr l) := by
      rw [ConvInt.lookup_one_other (fun e => htx e.symm)]; exact inv.lookup hl hx
    obtain ⟨ys, hst⟩ := StateActionsLocal.store (file := file) (labels := labels) a3 b1 b2 b3 b4 b5 c1 c3
      lc u x s t' hs env₁ k m₁ hx₁ (ConvInt.lookup_one ht') hv (inv₁.live l hl)
    have inv₂ := (inv₁.focus a3).store hl (StateExpr.close_ok _ t (inv.defs_ok hd) ok)
    rw [StateExpr.close_val] at inv₂
    refine ⟨_, ys, ?_, ?_, inv₂, ?_⟩
    · simp [Locals.stored_stdout, tch.stdout]
    · exact ⟨(same_touched tch).trans ((Rmw.same_focus a3 m₁).trans (Rmw.same_stored _ _ _ _)),
        cl.stored _ hl (cl.focus a3 (cl.touched hp tch))⟩
    · exact pre.trans (run.trans ((StateReturnLocal.bound_pop hfr _ K m₁).trans
        ((CallLocal.bind a1 t₀ ty _ ST env k m₁).trans hst)))
  · left
    exact ArenaFail.Fails.pre file labels pre (StateExpr.term_fails (file := file) (labels := labels)
      t he ok (.bound :: K) m locs)

theorem uninit_keeps {e : Eff} {x : Sym} (h : uninitStmt e = some x)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key) (k : List Frame)
    (P : Mem.Concrete.State → Prop) (cl : PrintMem.Closed P ls) (hp : P m) :
    ∃ m' xs, m'.stdout = m.stdout ∧ (Rmw.Same m m' ∧ P m') ∧ Inv env m' ls (update ds l.sym.key none) ∧
      LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, lc, u, b1, c1, b2, b3, c3, rfl⟩ := StateStmt.uninitStmt_inv h
  refine ⟨_, _, ?_, ⟨(Rmw.same_focus a0 m).trans (same_uninit _ _ _), cl.unstored hl (cl.focus a0 hp)⟩, (inv.focus a0).uninit hl,
    StateActionsLocal.uninitialized (file := file) (labels := labels) a0 b1 c1 b2 b3 c3 lc u x env k m
      (inv.lookup hl hx) (inv.live l hl)⟩
  simp [Uninitialized.stored_stdout]

/-- The kills of a return, then the jump to the return label: the parameter objects `ps`
survive, and only the killed locals (older than the fresh id) die. -/
theorem kills_keep {ret u : Sym} (hret : ReturnLabel L ret) :
    (xs : List Sym) → (lk : List Local) → Keys lk xs → (xs.map (·.key)).Nodup →
    {e : Eff} → StateStmt.killsRun file ret u xs e = true → (env : Env) →
    (loc : List Frame) → NoBoundary loc → (caller : List Frame) →
    (m : Mem.Concrete.State) →
    (∀ l ∈ lk, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)) →
    (∀ l ∈ lk, LiveInt m l.id l.addr) →
    (∀ a ∈ lk, ∀ b ∈ lk, a.sym.key ≠ b.sym.key → a.id ≠ b.id) →
    (∀ l ∈ lk, l.id < m.nextId) → (ps : List Local) → (∀ p ∈ ps, LiveInt m p.id p.addr) →
    (∀ p ∈ ps, ∀ l ∈ lk, p.id ≠ l.id) →
    (P : Mem.Concrete.State → Prop) →
    (∀ {m m'}, P m → Touched m m' → P m') →
    (∀ {m} {l : Local}, l ∈ lk → P m → P (Locals.killed m l.id)) → P m →
    {v : Int} → IsInt v → env.lookup u = some (spec v) →
    ∃ m', m'.stdout = m.stdout ∧ KeepsFrame P m m' ∧ (∀ p ∈ ps, LiveInt m' p.id p.addr) ∧
      LocalReaches file labels false
        ⟨.effectExpr e env, loc ++ .procedureReturn L :: caller, m⟩
        ⟨.value (spec v), .procedureReturn L :: caller, m'⟩
  | [], lk, hls, _, e, h, env, loc, hk, caller, m, _, _, _, _, ps, hps, _, P, touch, kill, hp, v, hv, hu => by
    obtain ⟨rann, l, cann, a3, c3, a4, s, u', rfl, hl, hu', hs⟩ := killsRun_nil h
    have heval : ∀ tags, Eval file tags env
        (.inl (.mk cann () (.call (.sym s) [Locals.intVal a3 c3, .mk a4 () (.sym u')])) )
        (.inl (spec v)) := fun _ =>
      ConvInt.convLoadedInt_eval (ann := c3) hs hv
        (.cons .val (.cons (.sym (by rw [ReturnLit.lookup_key hu']; exact hu)) .nil))
    obtain ⟨m', touched, back⟩ := StateParam.jump_return (file := file) (labels := labels)
      hl hret (spec v) env hk caller (focusMemory rann m)
    have T := (LoadTask.focusMemory_touched rann m).trans touched
    refine ⟨m', T.stdout, ⟨keeps_same (same_touched T), touch hp T⟩, fun p hp => CallArg.touched_live T (hps p hp), ?_⟩
    refine (CallLocal.focus (c' := .pureExpr
        (.mk cann () (.call (.sym s) [Locals.intVal a3 c3, .mk a4 () (.sym u')])) env)
      (k' := .runLabel l [] [] env :: (loc ++ .procedureReturn L :: caller))
      rann m (LoadTask.plain_pureExpr _ _) ?_).trans ?_
    · simp [requestAux, awaitsScheduling, focusMemory]; rfl
    · exact (PureLocal.eval_local file _ (heval _) _ _ rfl).trans back
  | x :: xs, lk, hls, nodup, e, h, env, loc, hk, caller, m, henv, hlive, hids, hnext, ps, hps, hpk,
      P, touch, kill, hp, v, hv, hu => by
    cases lk with
    | nil => cases hls
    | cons l lk =>
      simp only [Keys, List.map_cons, List.cons.injEq] at hls
      obtain ⟨hxl, hls⟩ := hls
      obtain ⟨hxs, nodup⟩ := List.nodup_cons.mp nodup
      obtain ⟨ann, pann, ty, kl, rest, rfl, hkl, hrest⟩ := killsRun_cons h
      let K := loc ++ .procedureReturn L :: caller
      obtain ⟨kann, kr⟩ := StateReturnLocal.killAny (file := file) (labels := labels) hkl env
        (.strongBind (.mk pann (.base (none, ty))) rest env :: K) m
        (fun y hy => henv l (by simp) y (hy.trans hxl.symm)) (hlive l (by simp))
      let m₁ := Locals.killed (focusMemory kann m) l.id
      have keep₁ : Keeps m m₁ := keeps_killed m kann (hnext l (by simp))
      have ne : ∀ l' ∈ lk, l'.id ≠ l.id := by
        intro l' hl'
        refine (hids l' (by simp [hl']) l (by simp) ?_)
        intro e
        apply hxs
        have hm : l'.sym.key ∈ lk.map (·.sym.key) := List.mem_map_of_mem hl'
        rw [hls, e, hxl] at hm
        exact hm
      obtain ⟨m', out, keep, live, reach⟩ := kills_keep hret xs lk hls nodup hrest env loc hk caller m₁
        (fun l' hl' => henv l' (by simp [hl']))
        (fun l' hl' => StateMem.live_killed (Locals.liveInt_focus kann (hlive l' (by simp [hl'])))
          l.id (ne l' hl'))
        (fun a ha b hb => hids a (by simp [ha]) b (by simp [hb]))
        (fun l' hl' => by rw [keep₁.next]; exact hnext l' (by simp [hl']))
        ps (fun p hp => StateMem.live_killed (Locals.liveInt_focus kann (hps p hp)) l.id
          (hpk p hp l (by simp)))
        (fun p hp l' hl' => hpk p hp l' (by simp [hl'])) P touch
        (fun hl hp => kill (List.mem_cons_of_mem _ hl) hp)
        (kill (by simp) (touch hp (LoadTask.focusMemory_touched kann m))) hv hu
      refine ⟨m', by rw [out]; simp [m₁, Locals.killed], ⟨keep₁.trans keep.1, keep.2⟩, live, ?_⟩
      exact (CallLocal.sequence ann _ _ rest env K m).trans (kr.trans
        ((StateReturnLocal.wildcard pann ty .unit rest env K m₁).trans reach))

/-- A return kills the locals `lk` and keeps the parameter objects `ps`. -/
theorem ret_keeps {ret : Sym} (hret : ReturnLabel L ret)
    {xs : List Sym} {e : Eff} {t : Term}
    (h : retStmt file ret xs e = some t) {env : Env} {m : Mem.Concrete.State} {ps lk : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m (ps ++ lk) ds) (hlk : Keys lk xs)
    (nodup : (xs.map (·.key)).Nodup) (hd : Defined ds t = true)
    (hnext : ∀ l ∈ lk, l.id < m.nextId) (hpk : ∀ p ∈ ps, ∀ l ∈ lk, p.id ≠ l.id)
    (loc : List Frame) (hk : NoBoundary loc) (caller : List Frame)
    (P : Mem.Concrete.State → Prop) (cl : Closed P (ps ++ lk) lk) (hp : P m) :
    Returns (file := file) (labels := labels) (L := L) (caller := caller) (KeepsFrame P) ps
      ⟨.effectExpr e env, loc ++ .procedureReturn L :: caller, m⟩ (close (defsOf ds) t) m.stdout := by
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
        have inv₁ := inv.touched tch
        have fresh : ∀ l ∈ lk, l.sym.key ≠ u.key := hlk.fresh hfresh
        obtain ⟨m', out, keep, live, reach⟩ := kills_keep hret xs lk hlk nodup hkr (extendEnv [(u, v)] env)
          loc hk caller m₁
          (fun l hl y hy => by
            rw [ConvInt.lookup_one_other (by rw [hy]; exact fresh l hl)]
            exact inv₁.env l (List.mem_append_right _ hl) y hy)
          (fun l hl => inv₁.live l (List.mem_append_right _ hl))
          (fun a ha b hb ne => (inv₁.apart a (List.mem_append_right _ ha) b
            (List.mem_append_right _ hb) ne).1)
          (fun l hl => by rw [(same_touched tch).1]; exact hnext l hl)
          ps (fun p hp => inv₁.live p (List.mem_append_left _ hp)) hpk
          P cl.touched cl.killed (cl.touched hp tch)
          (StateExpr.Term.int_of_ok t ok) (ConvInt.lookup_one rfl)
        refine ⟨m', by rw [out, tch.stdout], ⟨(keeps_same (same_touched tch)).trans keep.1, keep.2⟩, live, ?_⟩
        rw [StateExpr.close_val]
        exact pre.trans (run.trans ((StateReturnLocal.bound_pop hfr v K m₁).trans
          ((CallLocal.bind pann u ty v kr env k m₁).trans reach)))
      · exact .inr (ArenaFail.Fails.pre file labels pre
          (StateExpr.term_fails (file := file) (labels := labels) t h ok (.bound :: K) m (inv.locs hd)))
    · cases h
  · cases h

/-- **The statements of a parameter body** over the parameters `ps` and the locals `lk` return
their term with the parameter objects live, allocating nothing, or reach a local overflow. -/
theorem run_returns {ret : Sym} (hret : ReturnLabel L ret) {ys xs : List Sym} {ps lk : List Local}
    (hls : Keys (ps ++ lk) ys) (hlk : Keys lk xs) (nodup : (xs.map (·.key)).Nodup)
    (hpk : ∀ p ∈ ps, ∀ l ∈ lk, p.id ≠ l.id)
    (P : Mem.Concrete.State → Prop) (cl : Closed P (ps ++ lk) lk) :
    (n : Nat) → (ds : Key → Option IntExpr.Term) → (sz : Key → Nat) →
    (e : Eff) → (todo : List Eff) → {t : IntExpr.Term} → run file ret ys xs n ds sz e todo = some t →
    ∀ (env : Env) (m : Mem.Concrete.State), Inv env m (ps ++ lk) ds → P m → (∀ l ∈ lk, l.id < m.nextId) →
    ∀ (k : List Frame), Pend (labels := labels) (L := L) (caller := caller) (ps ++ lk) todo k →
    Returns (file := file) (labels := labels) (L := L) (caller := caller) (KeepsFrame P) ps
      ⟨.effectExpr e env, k, m⟩ t m.stdout
  | 0, _, _, _, _, _, h => by simp [run] at h
  | n + 1, ds, sz, e, todo, t, h => by
    intro env m inv hp hnext k p
    unfold run at h
    split at h
    next tr hc =>
      split at h
      next hd =>
        cases h
        obtain ⟨loc, hl, frames⟩ := StateProcLocal.context_frames p.context
        subst frames
        exact ret_keeps (labels := labels) hret hc inv hlk nodup hd.1 hnext hpk loc hl caller P cl hp
      next => cases h
    split at h
    next tc ea eb hi =>
      split at h
      next hd =>
        split at h
        next a b ha hb =>
          split at h
          next =>
            cases h
            have okC := fun okc => StateExpr.close_ok (defsOf ds) tc (inv.defs_ok hd.1) okc
            rcases if_runs (labels := labels) hi inv hls hd.1 k with ub | ⟨okc, env', m', tch, inv', reach⟩
            · exact .inr ub
            · have same := same_touched tch
              have hnext' : ∀ l ∈ lk, l.id < m'.nextId := fun l hl => by rw [same.1]; exact hnext l hl
              by_cases h1 : tc.val (values (defsOf ds)) = 1
              · rw [ite_eq_left h1] at reach
                have o := run_returns hret hls hlk nodup hpk P cl n ds sz eb todo hb env' m' inv' (cl.touched hp tch) hnext' k p
                rw [tch.stdout] at o
                exact returns_choose_right (okC okc) (by rw [StateExpr.close_val]; exact h1)
                  (returns_keep reach (keeps_same same) o)
              · rw [ite_eq_right h1] at reach
                have o := run_returns hret hls hlk nodup hpk P cl n ds sz ea todo ha env' m' inv' (cl.touched hp tch) hnext' k p
                rw [tch.stdout] at o
                exact returns_choose_left (okC okc) (by rw [StateExpr.close_val]; exact h1)
                  (returns_keep reach (keeps_same same) o)
          next => cases h
        next => cases h
      next => cases h
    split at h
    next x tr ha =>
      split at h
      next hd =>
        split at h
        next => cases h
        next r todo' =>
          obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
          rw [State.update_key hx] at h
          rcases StateStmtLocal.assign_runs_preserving ha inv hl hx hd.2.1 k
              (fun m' => Rmw.Same m m' ∧ P m')
              (fun h t => ⟨h.1.trans (same_touched t), cl.touched h.2 t⟩)
              (fun n h => ⟨h.1, cl.excluded n h.2⟩)
              (fun v h => ⟨h.1.trans (Rmw.same_stored _ _ _ v), cl.stored v hl h.2⟩)
              ⟨⟨rfl, rfl, rfl⟩, hp⟩ with
            ub | ⟨_, m', out, same, inv', reach⟩
          · exact .inr ub
          · obtain ⟨env', k', henv, p', back⟩ := p.resume .unit none m' r todo' rfl
            have o := run_returns hret hls hlk nodup hpk P cl n _ _ r todo' h env' m' (inv_withEnv inv' henv) same.2
              (fun l hl => by rw [same.1.1]; exact hnext l hl) k' p'
            rw [out] at o
            exact returns_keep (reach.trans back) (keeps_same same.1) o
      next => cases h
    split at h
    next x tr hi =>
      split at h
      next hd =>
        split at h
        next => cases h
        next r todo' =>
          obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd.1
          rw [State.update_key hx] at h
          rcases init_keeps hi inv hl hx hd.2.1 k P cl.toClosed hp with ub | ⟨_, m', ys', out, same, inv', reach⟩
          · exact .inr ub
          · obtain ⟨env', k', henv, p', back⟩ := p.resume .unit (some ys') m' r todo' rfl
            have o := run_returns hret hls hlk nodup hpk P cl n _ _ r todo' h env' m' (inv_withEnv inv' henv) same.2
              (fun l hl => by rw [same.1.1]; exact hnext l hl) k' p'
            rw [out] at o
            exact returns_keep (reach.trans back) (keeps_same same.1) o
      next => cases h
    split at h
    next x hu =>
      split at h
      next hd =>
        split at h
        next => cases h
        next r todo' =>
          obtain ⟨l, hl, hx⟩ := State.Keys.mem_of_local hls hd
          rw [State.update_key hx] at h
          obtain ⟨m', ys', out, same, inv', reach⟩ := uninit_keeps hu inv hl hx k P cl.toClosed hp
          obtain ⟨env', k', henv, p', back⟩ := p.resume .unit (some ys') m' r todo' rfl
          have o := run_returns hret hls hlk nodup hpk P cl n _ _ r todo' h env' m' (inv_withEnv inv' henv) same.2
            (fun l hl => by rw [same.1.1]; exact hnext l hl) k' p'
          rw [out] at o
          exact returns_keep (reach.trans back) (keeps_same same.1) o
      next => cases h
    split at h
    next s rest hs =>
      obtain ⟨ann, pann, ty, rfl⟩ := seqParts_inv hs
      have o := run_returns hret hls hlk nodup hpk P cl n ds sz s (rest :: todo) h env m inv hp hnext _
        (.bind pann ty rest inv.env p)
      exact returns_keep (CallLocal.sequence ann _ s rest env k m) (Keeps.refl m) o
    split at h
    next hu =>
      obtain ⟨ann, pann, rfl⟩ := isUnit_inv hu
      split at h
      next => cases h
      next r todo' =>
        obtain ⟨env', k', henv, p', back⟩ := p.resume .unit none (focusMemory ann m) r todo' rfl
        have same := Rmw.same_focus ann m
        have o := run_returns hret hls hlk nodup hpk P cl n ds sz r todo' h env' (focusMemory ann m)
          (inv_withEnv (inv.focus ann) henv) (cl.focus ann hp) (fun l hl => by rw [same.1]; exact hnext l hl) k' p'
        rw [show (focusMemory ann m).stdout = m.stdout from
          (LoadTask.focusMemory_touched ann m).stdout] at o
        exact returns_keep ((StateActionsLocal.pure_unit ann pann env k m).trans back)
          (keeps_same same) o
    next => cases h

/-- A caller predicate closed under changes to callee-owned objects. `fresh` assigns
ownership to a new object; `created` retains the predicate through its allocation.
The ownership predicate is independent of source symbol keys. -/
structure Region (P : Mem.Concrete.State → Prop) (Own : Local → Prop) : Prop where
  touched : ∀ {m m'}, P m → Touched m m' → P m'
  excluded : ∀ {m} (n : Nat), P m → P {m with nextExcluded := n}
  stored : ∀ {m} {l : Local} (v : Int), Own l → P m → P (Locals.stored m l.id l.addr v)
  unstored : ∀ {m} {l : Local}, Own l → P m → P (Uninitialized.stored m l.id l.addr)
  killed : ∀ {m} {l : Local}, Own l → P m → P (Locals.killed m l.id)
  created : ∀ {m} (pref : Prefix) (ann : List Annot), P m → P (Actions.created pref ann m)
  fresh : ∀ {m} (x : Sym), P m → Own ⟨x, m.nextId, nextIntAddress m⟩

theorem Region.closed {P : Mem.Concrete.State → Prop} {Own : Local → Prop}
    (r : Region P Own) {args locals : List Local}
    (ha : ∀ l ∈ args, Own l) (hl : ∀ l ∈ locals, Own l) : Closed P args locals where
  touched := r.touched
  excluded := r.excluded
  stored := fun v h => r.stored v (ha _ h)
  unstored := fun h => r.unstored (ha _ h)
  killed := fun h => r.killed (hl _ h)

/-- **The block**: the creations of at most `j` more `int` locals, then the statements. The
objects `pl ++ lk` are below the fresh id and at or above the last address; the reserve has room
for `j` more objects. -/
theorem block_returns {ret : Sym} (hret : ReturnLabel L ret) {ps : List Sym} {pl : List Local}
    (hpl : Keys pl ps)
    (P : Mem.Concrete.State → Prop) (Own : Local → Prop) (reg : Region P Own)
    (hpo : ∀ l ∈ pl, Own l) :
    (j : Nat) → (xs : List Sym) → (lk : List Local) → (ds : Key → Option IntExpr.Term) → (e : Eff) →
    {t : IntExpr.Term} → block file ret ps j xs ds e = some t →
    ∀ (env : Env) (m : Mem.Concrete.State), Inv env m (pl ++ lk) ds → P m → (∀ l ∈ lk, Own l) → Keys lk xs →
    (∀ l ∈ pl ++ lk, l.id < m.nextId) → (∀ l ∈ pl ++ lk, m.lastAddress ≤ l.addr) →
    m.lastAddress % 4 = 0 → 4 * ((j : Int) + 1) < m.lastAddress → (∀ d ∈ m.dead, d < m.nextId) →
    ∀ (k : List Frame), Context (labels := labels) L caller k →
    Returns (file := file) (labels := labels) (L := L) (caller := caller) (fun m m' => Uses j m m' ∧ P m') pl
      ⟨.effectExpr e env, k, m⟩ t m.stdout := by
  intro j
  induction j with
  | zero =>
    intro xs lk ds e t h env m inv hp hlo hlk ids addrs aligned room dead k hk
    simp only [block] at h
    split at h
    next => cases h
    next =>
      split at h
      next nodup =>
        have hls : Keys (pl ++ lk) (ps ++ xs) := by
          simp only [Keys, List.map_append] at hpl hlk ⊢; rw [hpl, hlk]
        have nodupx : (xs.map (·.key)).Nodup := (List.nodup_append.mp (by simpa using nodup)).2.1
        have hpk : ∀ p ∈ pl, ∀ l ∈ lk, p.id ≠ l.id := by
          intro p hp l hl
          refine (inv.apart p (List.mem_append_left _ hp) l (List.mem_append_right _ hl) ?_).1
          intro e
          have hp' : p.sym.key ∈ ps.map (·.key) := hpl ▸ List.mem_map_of_mem hp
          have hl' : l.sym.key ∈ xs.map (·.key) := hlk ▸ List.mem_map_of_mem hl
          rw [List.map_append] at nodup
          exact (List.nodup_append.mp nodup).2.2 _ hp' _ hl' e
        have o := run_returns (labels := labels) (L := L) (caller := caller) hret hls hlk nodupx hpk
          P (reg.closed
            (by intro l hl; rcases List.mem_append.mp hl with hl | hl
                · exact hpo l hl
                · exact hlo l hl) hlo)
          fuel ds _ e [] h env m inv hp (fun l hl => ids l (List.mem_append_right _ hl)) k (.base hk)
        exact o.pre .refl (fun _ h => ⟨Uses.of_keeps h.1, h.2⟩)
      next => cases h
  | succ j ih =>
    intro xs lk ds e t h env m inv hp hlo hlk ids addrs aligned room dead k hk
    simp only [block] at h
    split at h
    next x rest hc =>
      split at h
      next hfx =>
        unfold creation at hc
        split at hc
        next a p x' ty cr rest' =>
          split at hc
          next hcr =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨hx', hrest'⟩ := hc
            subst x' rest'
            obtain ⟨ann, lc, u, a1, a2, c1, a3, c2, pref, rfl⟩ := State.createInt_inv hcr
            have hnext : nextIntAddress m = m.lastAddress - 4 := by
              simp only [nextIntAddress]; omega
            have hpos : 0 < nextIntAddress m := by rw [hnext]; push_cast at room; omega
            let K := Frame.strongBind (.mk p (.base (some x, ty))) rest env :: k
            have create := StateActionsLocal.create (file := file) (labels := labels) ann a1 a2 a3 c1 c2 lc u
              pref env K m hpos
            rw [State.focus_nextId] at create
            let nl : Local := ⟨x, m.nextId, nextIntAddress m⟩
            let m₁ := Actions.created pref c2 (focusMemory ann m)
            let env₁ := extendEnv [(x, ptr nl)] env
            have bind := CallLocal.bind (file := file) (labels := labels) p x ty (ptr nl) rest env k m₁
            have hls : Keys (pl ++ lk) (ps ++ xs) := by
              simp only [Keys, List.map_append] at hpl hlk ⊢; rw [hpl, hlk]
            have fx : ∀ l ∈ pl ++ lk, l.sym.key ≠ x.key := hls.fresh hfx
            have inv₁ : Inv env₁ m₁ (pl ++ (lk ++ [nl])) ds := by
              rw [← List.append_assoc]
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
                      have := dead m.nextId hd
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
              · intro q d hd
                obtain ⟨ok, l, hl, hq, slot⟩ := inv.defs q d hd
                refine ⟨ok, l, List.mem_append_left _ hl, hq, ?_⟩
                refine Slots.slot_created ((LoadTask.focusMemory_touched ann m).slot slot) pref c2
                  (by rw [State.focus_nextId]; exact Int.ne_of_lt (ids l hl)) ?_
                rw [Locals.nextIntAddress_focus]
                have := addrs l hl
                show nextIntAddress m + 4 ≤ l.addr ∨ l.addr + 4 ≤ nextIntAddress m
                omega
            have hlk₁ : Keys (lk ++ [nl]) (xs ++ [x]) := by
              simp only [Keys, List.map_append, List.map_cons, List.map_nil] at hlk ⊢
              rw [hlk]
            have last₁ : m₁.lastAddress = m.lastAddress - 4 := by
              rw [Locals.created_lastAddress, Locals.nextIntAddress_focus, hnext]
            have next₁ : m₁.nextId = m.nextId + 1 := by
              rw [State.created_nextId, State.focus_nextId]
            have dead₁ : m₁.dead = m.dead := by rw [Locals.created_dead, State.focus_dead]
            have o := ih (xs ++ [x]) (lk ++ [nl]) ds rest h env₁ m₁ inv₁ (reg.created pref c2
                (reg.touched hp (LoadTask.focusMemory_touched ann m)))
              (by
                intro l hl
                rcases List.mem_append.mp hl with hl | hl
                · exact hlo l hl
                · obtain rfl := List.mem_singleton.mp hl
                  exact reg.fresh x hp) hlk₁
              (by
                intro l hl
                rw [next₁]
                rcases List.mem_append.mp hl with hl | hl
                · have := ids l (List.mem_append_left _ hl); omega
                · rcases List.mem_append.mp hl with hl | hl
                  · have := ids l (List.mem_append_right _ hl); omega
                  · obtain rfl := List.mem_singleton.mp hl
                    show m.nextId < m.nextId + 1
                    omega)
              (by
                intro l hl
                rw [last₁]
                rcases List.mem_append.mp hl with hl | hl
                · have := addrs l (List.mem_append_left _ hl); omega
                · rcases List.mem_append.mp hl with hl | hl
                  · have := addrs l (List.mem_append_right _ hl); omega
                  · obtain rfl := List.mem_singleton.mp hl
                    show m.lastAddress - 4 ≤ nextIntAddress m
                    omega)
              (by rw [last₁]; omega) (by rw [last₁]; push_cast at room ⊢; omega)
              (by intro d hd; rw [dead₁] at hd; rw [next₁]; have := dead d hd; omega) k hk
            have out : m₁.stdout = m.stdout := by simp [m₁, Actions.created_stdout]
            rw [out] at o
            refine o.pre ((CallLocal.sequence a _ _ rest env k m).trans (create.trans bind)) ?_
            intro m' u'
            change Uses j m₁ m' ∧ P m' at u'
            refine ⟨?_, u'.2⟩
            have u' := u'.1
            show Uses (j + 1) m m'
            refine ⟨by have := u'.next; rw [next₁] at this; omega,
              by have := u'.last; rw [last₁] at this; push_cast; omega,
              by rw [u'.aligned, last₁]; omega, fun d hd => ?_⟩
            rcases u'.dead d hd with h' | h'
            · exact .inl (dead₁ ▸ h')
            · exact .inr h'
          next => cases hc
        next => cases hc
      next => cases h
    next =>
      split at h
      next nodup =>
        have hls : Keys (pl ++ lk) (ps ++ xs) := by
          simp only [Keys, List.map_append] at hpl hlk ⊢; rw [hpl, hlk]
        have nodupx : (xs.map (·.key)).Nodup := (List.nodup_append.mp (by simpa using nodup)).2.1
        have hpk : ∀ p ∈ pl, ∀ l ∈ lk, p.id ≠ l.id := by
          intro p hp l hl
          refine (inv.apart p (List.mem_append_left _ hp) l (List.mem_append_right _ hl) ?_).1
          intro e
          have hp' : p.sym.key ∈ ps.map (·.key) := hpl ▸ List.mem_map_of_mem hp
          have hl' : l.sym.key ∈ xs.map (·.key) := hlk ▸ List.mem_map_of_mem hl
          rw [List.map_append] at nodup
          exact (List.nodup_append.mp nodup).2.2 _ hp' _ hl' e
        have o := run_returns (labels := labels) (L := L) (caller := caller) hret hls hlk nodupx hpk
          P (reg.closed
            (by intro l hl; rcases List.mem_append.mp hl with hl | hl
                · exact hpo l hl
                · exact hlo l hl) hlo)
          fuel ds _ e [] h env m inv hp (fun l hl => ids l (List.mem_append_right _ hl)) k (.base hk)
        exact o.pre .refl (fun _ h => ⟨Uses.of_keeps h.1, h.2⟩)
      next => cases h

/-- The whole recognized parameter body, with an actual runtime input and room for `J` locals
below the argument object. -/
theorem body_returns {x : Sym} {e : EE} {t : IntExpr.Term} {J : Nat} (h : body file x e J = some t)
    (env : Env) (caller : List Frame) (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : IsInt n) (slot : Locals.Slot m id addr n)
    (hid : id < m.nextId) (haddr : m.lastAddress ≤ addr) (aligned : m.lastAddress % 4 = 0)
    (room : 4 * ((J : Int) + 1) < m.lastAddress) (dead : ∀ d ∈ m.dead, d < m.nextId)
    (P : Mem.Concrete.State → Prop) (Own : Local → Prop) (reg : Region P Own)
    (hp : P m) (owned : Own ⟨x, id, addr⟩) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧ (Uses J m m' ∧ P m') ∧ LiveInt m' id addr ∧
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
      have hs : block file ret [x] J [] (StateSubst.defs (.lit n) (StateParam.paramDefs x)) a =
          some (StateSubst.subst (.lit n) t) := by
        rw [block_subst, h]; rfl
      let SAVE : EE := .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
      let K := Frame.strongBind (.mk pann (.base (none, bt0))) SAVE env ::
        .procedureReturn (CallReach.bodyLabels B) :: caller
      have hK : Context (labels := labels) (CallReach.bodyLabels B) caller K := rfl
      have inv : Inv env m ([⟨x, id, addr⟩] ++ []) (StateSubst.defs (.lit n) (StateParam.paramDefs x)) := by
        simpa using (StateParam.param_at x env m hx hn slot).instantiate hn
      have result := block_returns (labels := labels) hret (ps := [x]) (pl := [⟨x, id, addr⟩]) rfl
        P Own reg (by intro l hl; obtain rfl := List.mem_singleton.mp hl; exact owned)
        J [] [] _ a hs env m inv hp (by simp) rfl
        (by intro l hl; simp only [List.append_nil, List.mem_singleton] at hl; subst hl; exact hid)
        (by intro l hl; simp only [List.append_nil, List.mem_singleton] at hl; subst hl; exact haddr)
        aligned room dead K hK
      have pre := CallLocal.sequence (file := file) (labels := labels) ann (.mk pann (.base (none, bt0))) a SAVE env
        (.procedureReturn (CallReach.bodyLabels B) :: caller) m
      rcases Returns.pre pre (fun _ h => h) result with ⟨ok, m', out, uses, live, run⟩ | fail
      · exact .inl ⟨(StateSubst.subst_ok (.lit n) t 0 hn).mp ok, m', out, uses,
          live ⟨x, id, addr⟩ (by simp), by simpa only [StateSubst.subst_val, IntExpr.Term.val] using run⟩
      · exact .inr fail
    · cases h
  · cases h

end Silmaril.Compile.Core.Verified.ParamRunFrame
