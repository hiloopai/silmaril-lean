module

public import Silmaril.Compiler.Core.Verified.StateGlobals.Defs
public import Silmaril.Compiler.Core.Verified.AbortCall.Defs

/-! # Allocation budgets through State statements

Stores and reads preserve the room and fresh identifier needed by a later exit argument.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.StateExitMem

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval Reaches tagsOf)
open Mem.Concrete (LiveInt IntRange)
open Locals (stored Slot)
open ReturnLit (Eff NoBoundary ReturnLabel)
open ReturnConst (focusMemory)
open ConvInt (IsInt)
open StateExpr (Key Term term values close)
open StateMem (Local Inv Defined defsOf update ptr)
open StateStmt
open StateGlobals (ifParts ifParts_inv exprStmt)
open IntExpr (spec)
open LoadTask (Touched)
open ExitCall (Budget)

variable {file : Program} {labels : Labels}

theorem budget_touched {m m' : Mem.Concrete.State} (b : Budget m) (h : Touched m m') :
    Budget m' := by
  obtain ⟨l, u, rfl⟩ := h
  exact ⟨b.room, b.fresh⟩

theorem budget_store {m : Mem.Concrete.State} (b : Budget m) (id addr n : Int) :
    Budget (stored m id addr n) := ⟨b.room, b.fresh⟩

theorem budget_nextExcluded {m : Mem.Concrete.State} (b : Budget m) (n : Nat) :
    Budget {m with nextExcluded := n} := ⟨b.room, b.fresh⟩

theorem assign_runs {e : Eff} {x : Sym} {t : Term} (h : assignStmt file e = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (k : List Frame) (hb : Budget m) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m', m'.stdout = m.stdout ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ∧
        Budget m' ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  obtain ⟨a0, a1, ty0, a2, a3, a4, a5, p, tp, a6, t₀, tt, a7, PX, e', b0, b1, ty1, sann, lc, u,
    b2, c1, b3, p', b4, s, b5, c2, b6, t', b7, b8, s', b9, c3, d0, t'', d1, d2, rfl, hp', ht', ht'',
    htp, hann, hs, hs', he, hdx, hnx⟩ := assignStmt_inv h
  replace hdx : IntWrap.desig file PX = some x :=
    (StateStmt.desigP_inv hdx).resolve_right (by rintro ⟨_, _, h⟩; simp at h)
  let σ := values (defsOf ds)
  let PU : EE := .mk d1 (.pure (.mk d2 () (.val .unit)))
  let K0 := Frame.strongBind (.mk a1 (.base (none, ty0))) PU env :: k
  let PAT : Pattern Sym := .mk a4 (.ctor .tuple [.mk a5 (.base (some p, tp)), .mk a6 (.base (some t₀, tt))])
  let CONV : PE := .mk b8 () (.call (.sym s') [Locals.intVal b9 c3, .mk d0 () (.sym t'')])
  let NEG : EE := .mk sann (.action (.mk .neg (.mk lc u (.store false (Locals.intVal b2 c1)
    (.mk b3 () (.sym p')) (.mk b4 () (.call (.sym s) [Locals.intVal b5 c2, .mk b6 () (.sym t')])) .na))))
  let BODY : EE := .mk b0 (.wseq (.mk b1 (.base (none, ty1))) NEG (.mk b7 (.pure CONV)))
  let KB := Frame.effectBind PAT BODY env :: .bound :: K0
  have pre : Reaches file labels ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (none, ty0)))
      (.mk a2 (.bound (.mk a3 (.wseq PAT (.mk a7 (.unseq [PX, e'])) BODY)))) PU)) env, k, m⟩
      ⟨.effectExpr (.mk a7 (.unseq [PX, e'])) env, KB, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      ((ReturnLit.bound_reaches a2 _ env _ m).trans (Locals.wseq_reaches a3 PAT _ BODY env _ m))
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
    have s₃ : Reaches file labels ⟨.value (.tuple [ptr l, spec v]), .annotations xs :: KB, m₁⟩
        ⟨.effectExpr BODY env₁, .annotations xs :: .bound :: K0, m₁⟩ :=
      Interleave.reaches_of_local file labels (.single (.next
        (IntExpr.requestAux_tuple_bind m₁ xs a4 a5 a6 p t₀ tp tt _ _ _ env _)
        (LoadTask.plain_effectExpr _ _)))
    let inner := [Frame.effectBind (.mk b1 (.base (none, ty1))) (.mk b7 (.pure CONV)) env₁,
      .annotations xs]
    have s₄ : Reaches file labels ⟨.effectExpr BODY env₁, .annotations xs :: .bound :: K0, m₁⟩
        ⟨.effectExpr NEG env₁, inner ++ .bound :: K0, m₁⟩ :=
      Locals.wseq_reaches b0 _ NEG _ env₁ _ m₁
    have ht₁ : env₁.lookup t'' = some (spec v) := lookup_two_snd ht'' htp
    obtain ⟨m₂, tch₂, resume⟩ := assign_resume (file := file) (labels := labels) b1 ty1 b7 b8 b9 c3 d0
      s' t'' env₁ xs m₁.nextExcluded {m₁ with nextExcluded := m₁.nextExcluded + 1} hv hs' ht₁
    have inv₁ : Inv env m₁ ls ds := inv.touched tch
    have live₁ : LiveInt m₁ l.id l.addr := inv₁.live l hl
    have s₅ := lifted_store_ann (file := file) (labels := labels) sann hann lc u (Locals.intVal b2 c1)
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
    refine ⟨focusMemory d1 m₃, ?_, inv₃.focus d1, (budget_store (budget_touched (budget_nextExcluded (budget_touched hb tch) _) tch₂) _ _ _).focus d1, ?_⟩
    · simp [m₃, Locals.stored_stdout, tch₂.stdout, tch.stdout]
    · exact pre.trans ((Interleave.reaches_of_local file labels s₂).trans (s₃.trans (s₄.trans
        (s₅.trans ((ReturnConst.wildcard_sequence_reaches file labels a1 ty0 _ PU env k m₃).trans
          (pure_unit_reaches d1 d2 env k m₃))))))
  · left
    refine Overflows.pre pre (fails_overflows (ArenaFail.fail_pair file labels (.inl ?_)))
    have flag : taskFlag false KB [(0, .effectExpr PX env, [])] = false := by
      simp [taskFlag, Interleave.controlHasCCall_effectExpr, IntWrap.desig_noCall hdx]
    rw [flag]
    exact StateExpr.term_fails t he ok [] m locs

/-- The allocation state of `Rmw.Same` is all that the budget reads. -/
theorem budget_same {m m' : Mem.Concrete.State} (b : Budget m) (h : Rmw.Same m m') : Budget m' := by
  obtain ⟨hid, hdead, hlast⟩ := h
  refine ⟨?_, ?_⟩
  · have := b.room
    unfold Mem.Concrete.nextIntAddress at this ⊢
    rw [hlast]; exact this
  · rw [hid, hdead]; exact b.fresh

/-- `StateGlobals.assignOrRmw_runs` with the budget. -/
theorem assignOrRmw_runs {e : Eff} {x : Sym} {t : Term} (h : StateGlobals.assignOrRmw file e = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (k : List Frame) (hb : Budget m) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m', m'.stdout = m.stdout ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ∧
        Budget m' ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  unfold StateGlobals.assignOrRmw at h
  split at h
  next pair ha =>
    cases h
    exact assign_runs ha inv hl hx hd k hb
  next =>
    cases hr : Rmw.rmwStmt file e with
    | none => simp [hr] at h
    | some pair =>
      obtain ⟨y, op⟩ := pair
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hd' : (ds y.key).isSome := by
        simpa [Defined, StateExpr.Term.vars] using hd
      rcases Rmw.rmw_runs_same (labels := labels) hr inv hd' k with ub | ⟨ok, m', out, same, inv', r⟩
      · exact .inl ub
      · refine .inr ⟨ok, m', out, ?_, budget_same hb same, r⟩
        simpa only [hx] using inv'

theorem init_runs {e : Eff} {x : Sym} {t : Term} (h : initStmt file e = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (k : List Frame) (hb : Budget m) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m' xs, m'.stdout = m.stdout ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ∧
        Budget m' ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, a1, t₀, ty, a2, e', a3, lc, u, b1, c1, b2, b3, b4, c3, b5, s, t', rfl, ht', htx, hs,
    he⟩ := initStmt_inv h
  let σ := values (defsOf ds)
  let ST : EE := .mk a3 (.action (.mk .pos (.mk lc u (.store false (Locals.intVal b1 c1)
    (.mk b2 () (.sym x)) (.mk b3 () (.call (.sym s) [Locals.intVal b4 c3, .mk b5 () (.sym t')])) .na))))
  let K := Frame.strongBind (.mk a1 (.base (some t₀, ty))) ST env :: k
  have pre : Reaches file labels ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some t₀, ty)))
      (.mk a2 (.bound e')) ST)) env, k, m⟩ ⟨.effectExpr e' env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
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
    obtain ⟨ys, hst⟩ := Locals.store_reaches (file := file) (labels := labels) a3 b1 b2 b3 b4 b5 c1 c3
      lc u x s t' hs env₁ k m₁ hx₁ (ConvInt.lookup_one ht') hv (inv₁.live l hl)
    have inv₂ := (inv₁.focus a3).store hl (StateExpr.close_ok _ t (inv.defs_ok hd) ok)
    rw [StateExpr.close_val] at inv₂
    refine ⟨_, ys, ?_, inv₂, budget_store ((budget_touched hb tch).focus a3) _ _ _, ?_⟩
    · simp [Locals.stored_stdout, tch.stdout]
    · exact pre.trans ((Interleave.reaches_of_local file labels run).trans ((bound_pop hfr _ K m₁).trans
        ((ReturnLit.bind_reaches a1 t₀ ty _ ST env k m₁).trans hst)))
  · left
    exact Overflows.pre pre (fails_overflows (StateExpr.term_fails (file := file) (labels := labels)
      t he ok (.bound :: K) m locs))

theorem uninit_runs {e : Eff} {x : Sym} (h : uninitStmt e = some x)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key) (k : List Frame) (hb : Budget m) :
    ∃ m' xs, m'.stdout = m.stdout ∧ Inv env m' ls (update ds l.sym.key none) ∧
      Budget m' ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, lc, u, b1, c1, b2, b3, c3, rfl⟩ := uninitStmt_inv h
  refine ⟨_, _, ?_, (inv.focus a0).uninit hl, (show Budget (Uninitialized.stored (focusMemory a0 m) l.id l.addr) from ⟨(hb.focus a0).room, (hb.focus a0).fresh⟩), Uninitialized.store_reaches (file := file)
    (labels := labels) a0 b1 c1 b2 b3 c3 lc u x env k m (inv.lookup hl hx) (inv.live l hl)⟩
  simp [Uninitialized.stored_stdout]

/-- `uninit_runs` for `int x;` or `T x;` (a wrapper `T`, `StateStmt.uninitAny`). -/
theorem uninitAny_runs {e : Eff} {x : Sym} (h : uninitAny file e = some x)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key) (k : List Frame) (hb : Budget m) :
    ∃ m' xs, m'.stdout = m.stdout ∧ Inv env m' ls (update ds l.sym.key none) ∧
      Budget m' ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  unfold uninitAny at h
  split at h
  · rename_i x' hu
    cases h
    exact uninit_runs hu inv hl hx k hb
  · obtain ⟨ann, reach⟩ := WrapObj.uninitWrap_reaches (file := file) (labels := labels) h env k m
      (inv.lookup hl hx) (inv.live l hl)
    exact ⟨_, _, by simp [Uninitialized.stored_stdout], (inv.focus ann).uninit hl,
      (show Budget (Uninitialized.stored (focusMemory ann m) l.id l.addr) from
        ⟨(hb.focus ann).room, (hb.focus ann).fresh⟩), reach⟩

theorem if_runs {ys : List Sym} {e ea eb : Eff} {tc : Term} (h : ifParts file ys e = some (tc, ea, eb))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (hls : Keys ls ys) (hdc : Defined ds tc = true) (k : List Frame) (hb : Budget m) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    (tc.Ok (values (defsOf ds)) ∧ ∃ env' m', m'.stdout = m.stdout ∧ Inv env' m' ls ds ∧ Budget m' ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.effectExpr (if tc.val (values (defsOf ds)) = 1 then eb else ea) env', k, m'⟩) := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', rfl, hb', hcb, hfc, hfb, htc⟩ :=
    ifParts_inv h
  replace htc : StateExpr.term file ec = some tc := htc.2.2
  let σ := values (defsOf ds)
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) ea eb)
  let REST : EE := .mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb IF)
  let K := Frame.strongBind (.mk a1 (.base (some c, cty))) REST env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec)) REST)) env, k, m⟩
      ⟨.effectExpr ec env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
  by_cases okc : tc.Ok σ
  · right
    obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
      tc htc okc (.bound :: K) m (inv.locs hdc)
    let cv := tc.val σ
    let env₁ := extendEnv [(c, spec cv)] env
    let KB := Frame.strongBind (.mk a4 (.base (some b, bty))) IF env₁ :: k
    obtain ⟨m₂, tch₂, conv⟩ := boolSource_touched (file := file) (labels := labels) hcb env₁ KB m₁ cv
      (ConvInt.lookup_one rfl)
    let flag := decide (cv ≠ 1)
    let env₂ := extendEnv [(b, boolean flag)] env₁
    have hp : SeqReach.PureEval file labels (.mk a6 () (.sym b')) env₂ (boolean flag) :=
      SeqReach.pure_symbol a6 b' env₂ _ (ConvInt.lookup_one hb')
    let m₃ := SeqReach.focusMemory a5 m₂
    have enter : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
        ⟨.effectExpr (if flag then ea else eb) env₂, k, m₃⟩ :=
      (Interleave.reaches_of_local file labels run).trans ((bound_pop hfr _ K m₁).trans
        ((ReturnLit.bind_reaches a1 c cty _ REST env k m₁).trans
          ((ReturnConst.sequence_reaches file labels a3 _ cb IF env₁ k m₁).trans
            (conv.trans ((ReturnLit.bind_reaches a4 b bty _ IF env₁ k m₂).trans
              (SeqReach.effect_if_reaches a5 flag hp k m₂))))))
    have tch₃ : Touched m m₃ := tch.trans (tch₂.trans (seqFocus_touched a5 m₂))
    have inv₂ : Inv env₂ m₃ ls ds := ((inv.touched tch₃).extend (hls.fresh hfc)).extend (hls.fresh hfb)
    refine ⟨okc, env₂, m₃, tch₃.stdout, inv₂, budget_touched hb tch₃, pre.trans ?_⟩
    have hsel : (if flag then ea else eb) = (if tc.val σ = 1 then eb else ea) := by
      by_cases h1 : tc.val σ = 1 <;> simp [flag, cv, h1]
    rw [← hsel]
    exact enter
  · left
    exact StateStmt.Overflows.pre pre (fails_overflows (StateExpr.term_fails (file := file)
      (labels := labels) tc htc okc (.bound :: K) m (inv.locs hdc)))

theorem expr_runs {e : Eff} {t : Term} (h : exprStmt file e = some t) {env : Env}
    {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds)
    (hd : Defined ds t = true) (k : List Frame) (hb : Budget m) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    ∃ v m', m'.stdout = m.stdout ∧ Inv env m' ls ds ∧ Budget m' ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value v, k, m'⟩ := by
  unfold exprStmt at h
  split at h
  · rename_i ann e'
    have pre := ReturnLit.bound_reaches (file := file) (labels := labels) ann e' env k m
    by_cases ok : t.Ok (values (defsOf ds))
    · right
      obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
        t h ok (.bound :: k) m (inv.locs hd)
      exact ⟨_, m₁, tch.stdout, inv.touched tch, budget_touched hb tch,
        pre.trans ((Interleave.reaches_of_local file labels run).trans (bound_pop hfr _ k m₁))⟩
    · left
      exact StateStmt.Overflows.pre pre (fails_overflows (StateExpr.term_fails (file := file)
        (labels := labels) t h ok (.bound :: k) m (inv.locs hd)))
  · cases h

/-! ## Falling off the end of `main` -/

end Silmaril.Compile.Core.Verified.StateExitMem
