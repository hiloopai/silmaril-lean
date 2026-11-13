module

public import Silmaril.Compiler.Core.Verified.StateActionsLocal.Defs

/-! # Local traces for State statements, including lifted negative stores -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StateStmtLocal

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
open IntExpr (spec overflow)
open LoadTask (Touched)
open StateStmt
open StateReturnLocal (bound_pop)

variable {file : Program} {labels : Labels}


theorem lifted_store_ann (sann : List Annot) (hann : noLoc sann = true) (l : Loc) (u : Unit)
    (ty p v : PE) (env : Env) (inner k : List Frame) (m : Mem.Concrete.State) (cann : List Annot)
    {id addr n : Int} (live : LiveInt m id addr) (hn : IntRange n)
    (eval : ∀ m', Eval file (tagsOf file m') env (.inr [ty, p, v])
      (.inr [.ctype (Mem.Concrete.intType cann), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))]))
    (boundary : (inner ++ .bound :: k).span (fun f => match f with
      | .strongBind .. | .bound => false | _ => true) = (inner, .bound :: k))
    {result : Val} {xs : List Access} {m₂ : Mem.Concrete.State}
    (resume : TaskRuns file labels false
      ⟨.value .unit, excludeFrames m.nextExcluded inner,
        {m with nextExcluded := m.nextExcluded + 1}⟩ result xs m₂)
    (touched : LoadTask.Touched {m with nextExcluded := m.nextExcluded + 1} m₂)
    (excluded : ∀ a ∈ xs, m.nextExcluded ∈ a.exclusions)
    (idle : activeCall (.value .unit) (excludeFrames m.nextExcluded inner) = false) :
    LocalReaches file labels false
      ⟨.effectExpr (.mk sann (.action (.mk .neg (.mk l u (.store false ty p v .na))))) env,
        inner ++ .bound :: k, m⟩
      ⟨.value result, k, stored m₂ id addr n⟩ := by
  have hno : ∀ a ∈ sann, ∀ l, a ≠ .loc l := by
    intro a ha l e; subst e
    have := List.all_eq_true.mp hann _ ha
    simp at this
  have hfind : (sann.findSome? fun a => match a with | .loc l => some l | _ => none) = none := by
    rw [List.findSome?_eq_none_iff]
    intro a ha
    cases a <;> first | rfl | exact absurd rfl (hno _ ha _)
  let act : EE := .mk [] (.action (.mk .pos (.mk l u (.store false ty p v .na))))
  let m₁ : Mem.Concrete.State := {m with nextExcluded := m.nextExcluded + 1}
  let K := Frame.liftedResult :: .bound :: k
  let a := StoreTask.writeAccess [.excluded m.nextExcluded] addr
  let tasks : List (Nat × (Control × List Frame)) :=
    [(0, .effectExpr act env, [.excluded m.nextExcluded]),
     (1, .value .unit, excludeFrames m.nextExcluded inner)]
  let results : List (Nat × (Val × List Access)) := [(0, .unit, [a]), (1, result, xs)]
  have live₁ : LiveInt m₁ id addr := Locals.liveInt_with live rfl rfl
  have live₂ : LiveInt m₂ id addr := by
    obtain ⟨loc, used, eq⟩ := touched
    rw [eq]
    exact Locals.liveInt_with live₁ rfl rfl
  have store := StoreTask.store_local [] l u ty p v env [.excluded m.nextExcluded] m₂ cann
    live₂ hn (eval m₂) (labels := labels)
  have task0 : TaskRuns file labels false
      ⟨.effectExpr act env, [.excluded m.nextExcluded], m₂⟩ .unit [a]
        (stored m₂ id addr n) := by
    refine ⟨[.annotations [a]], ?_, rfl⟩
    refine store.tail (.next ?_ (LoadTask.plain_value .unit))
    simp [requestAux, awaitsScheduling, a, ReturnConst.focusMemory]
  have flag0 : taskFlag false K [] = false := by simp [taskFlag]
  have flag1 : taskFlag false K [(0, .effectExpr act env, [.excluded m.nextExcluded])] = false := by
    simp [taskFlag, controlHasCCall, hasCCall, act]
  have run : TasksRun file labels false K tasks m₁ results (stored m₂ id addr n) := by
    have r0 : TasksRun file labels false K [(0, .effectExpr act env, [.excluded m.nextExcluded])]
        m₂ [(0, .unit, [a])] (stored m₂ id addr n) :=
      .snoc (by rw [flag0]; exact task0) .nil
    exact .snoc (by rw [flag1]; exact resume) r0
  have norace : NoRace results := by
    intro x hx y hy ne aa haa bb hbb
    simp only [results, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (ne rfl)
    · have eq : aa = a := by simpa using haa
      subst aa
      exact NegativeStore.excluded_noRace (by simp [a, StoreTask.writeAccess]) (excluded bb hbb)
    · have eq : bb = a := by simpa using hbb
      subst bb
      exact NegativeStore.excluded_noRace_rev (by simp [a, StoreTask.writeAccess]) (excluded aa haa)
    · exact False.elim (ne rfl)
  have sorted : results.Pairwise fun a b => a.1 ≤ b.1 := by simp [results]
  have arena := interleave_runs file labels run (by simp [tasks]) (by
    intro t ht
    simp only [tasks, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · simp [activeCall]
    · exact idle) []
  have end_ := LocalStep.next (requestAux_end file labels (stored m₂ id addr n) results K false
    norace sorted) (LoadTask.plain_value _)
  have lift : liftAction m (.effectExpr act env) (Control.value .unit).resuming
      (inner ++ .bound :: k) = .update m₁ (.interleave [] tasks) K := by
    dsimp only [liftAction]
    erw [boundary]
    simp [excludePath, m₁, tasks, K]
  have start : LocalReaches file labels false
      ⟨.effectExpr (.mk sann (.action (.mk .neg (.mk l u (.store false ty p v .na))))) env,
        inner ++ .bound :: k, m⟩
      ⟨.interleave [] tasks, K, m₁⟩ := by
    apply Relation.ReflTransGen.single
    apply LocalStep.update
    simp only [act] at lift
    simp [requestAux, awaitsScheduling]
    erw [hfind]
    simp [lift]
  refine start.trans ?_
  have steps := arena.tail end_
  refine steps.trans ?_
  have selected : LocalReaches file labels false
      ⟨.value (.tuple [.unit, result]), .annotations (a :: xs) :: K, stored m₂ id addr n⟩
      ⟨.value result, .annotations (a :: xs) :: .bound :: k, stored m₂ id addr n⟩ :=
    .single (.next (by simp [requestAux, awaitsScheduling, K]) (LoadTask.plain_value _))
  have finish := selected.trans
    (StateReturnLocal.bound_pop (fr := [.annotations (a :: xs)]) (.inr rfl)
      result k (stored m₂ id addr n))
  simpa [results] using finish

/-- A local assignment preserves any predicate closed under its diagnostic changes,
exclusion reservation and its one concrete store. -/
theorem assign_runs_preserving {e : Eff} {x : Sym} {t : Term} (h : assignStmt file e = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (k : List Frame)
    (P : Mem.Concrete.State → Prop)
    (touch : ∀ {m m'}, P m → Touched m m' → P m')
    (exclude : ∀ {m} (n : Nat), P m → P {m with nextExcluded := n})
    (write : ∀ {m} (v : Int), P m → P (stored m l.id l.addr v))
    (hp : P m) :
    ArenaFail.Fails file labels false ⟨.effectExpr e env, k, m⟩ overflow ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m', m'.stdout = m.stdout ∧ P m' ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ∧
        LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
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
    have hp₂ : P m₂ := touch (exclude _ (touch hp tch)) tch₂
    have hp₃ : P m₃ := write v hp₂
    refine ⟨focusMemory d1 m₃, ?_, touch hp₃ (LoadTask.focusMemory_touched d1 m₃),
      inv₃.focus d1, ?_⟩
    · simp [m₃, Locals.stored_stdout, tch₂.stdout, tch.stdout]
    · exact pre.trans (s₂.trans (s₃.trans (s₄.trans
        (s₅.trans ((StateReturnLocal.wildcard a1 ty0 _ PU env k m₃).trans
          (StateActionsLocal.pure_unit d1 d2 env k m₃))))))
  · left
    refine ArenaFail.Fails.pre file labels pre (ArenaFail.fail_pair file labels (.inl ?_))
    have flag : taskFlag false KB [(0, .effectExpr PX env, [])] = false := by
      simp [taskFlag, Interleave.controlHasCCall_effectExpr, IntWrap.desig_noCall hdx]
    rw [flag]
    exact StateExpr.term_fails t he ok [] m locs

theorem assign_runs {e : Eff} {x : Sym} {t : Term} (h : assignStmt file e = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (k : List Frame) :
    ArenaFail.Fails file labels false ⟨.effectExpr e env, k, m⟩ overflow ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m', m'.stdout = m.stdout ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ∧
        LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  rcases assign_runs_preserving h inv hl hx hd k (fun _ => True)
      (fun {_ _} _ _ => True.intro) (fun {_} _ _ => True.intro)
      (fun {_} _ _ => True.intro) True.intro with
    ub | ⟨ok, m', out, _, inv', run⟩
  · exact .inl ub
  · exact .inr ⟨ok, m', out, inv', run⟩

theorem init_runs {e : Eff} {x : Sym} {t : Term} (h : initStmt file e = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (k : List Frame) :
    ArenaFail.Fails file labels false ⟨.effectExpr e env, k, m⟩ overflow ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m' xs, m'.stdout = m.stdout ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ∧
        LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, a1, t₀, ty, a2, e', a3, lc, u, b1, c1, b2, b3, b4, c3, b5, s, t', rfl, ht', htx, hs,
    he⟩ := initStmt_inv h
  let σ := values (defsOf ds)
  let ST : EE := .mk a3 (.action (.mk .pos (.mk lc u (.store false (Locals.intVal b1 c1)
    (.mk b2 () (.sym x)) (.mk b3 () (.call (.sym s) [Locals.intVal b4 c3, .mk b5 () (.sym t')])) .na))))
  let K := Frame.strongBind (.mk a1 (.base (some t₀, ty))) ST env :: k
  have pre : LocalReaches file labels false ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some t₀, ty)))
      (.mk a2 (.bound e')) ST)) env, k, m⟩ ⟨.effectExpr e' env, .bound :: K, m⟩ :=
    (CallLocal.sequence a0 _ _ _ env k m).trans
      (CallLocal.bound a2 _ env _ m)
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
    refine ⟨_, ys, ?_, inv₂, ?_⟩
    · simp [Locals.stored_stdout, tch.stdout]
    · exact pre.trans (run.trans ((StateReturnLocal.bound_pop hfr _ K m₁).trans
        ((CallLocal.bind a1 t₀ ty _ ST env k m₁).trans hst)))
  · left
    exact ArenaFail.Fails.pre file labels pre (StateExpr.term_fails (file := file) (labels := labels)
      t he ok (.bound :: K) m locs)

theorem uninit_runs {e : Eff} {x : Sym} (h : uninitStmt e = some x)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key) (k : List Frame) :
    ∃ m' xs, m'.stdout = m.stdout ∧ Inv env m' ls (update ds l.sym.key none) ∧
      LocalReaches file labels false ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, lc, u, b1, c1, b2, b3, c3, rfl⟩ := uninitStmt_inv h
  refine ⟨_, _, ?_, (inv.focus a0).uninit hl, StateActionsLocal.uninitialized (file := file)
    (labels := labels) a0 b1 c1 b2 b3 c3 lc u x env k m (inv.lookup hl hx) (inv.live l hl)⟩
  simp [Uninitialized.stored_stdout]

end Silmaril.Compile.Core.Verified.StateStmtLocal
