module

public import Silmaril.Compiler.Core.Verified.ArrStore.Defs
public import Silmaril.Compiler.Core.Verified.ArrMem.Defs
public import Silmaril.Compiler.Core.Verified.StructCell.Defs
/-! # Assigning a runtime scalar expression to an array element

The element index is static; the right-hand side is an open State expression,
computed at runtime. The source invariant retains adjacent elements and the
existing scalar and pointer objects. Bounds are explicit proof obligations.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArrStmt

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches Eval tagsOf)
open Silmaril.Cerberus.Core.Interleave
open StateExpr (Key Term termP values close PtsTo)
open StateMem (Local Defined defsOf ptr)
open ReturnLit (Eff)
open StateStmt (noLoc lookup_two_snd lookup_two_fst assign_resume Overflows fails_overflows)
open ConvInt (isConvLoadedInt IsInt)
open LoadTask (Touched)
open IntExpr (spec)

def assignStmt (file : File Codec.wireModel Unit Unit) (e : Eff)
    (pts : Key → Option PtsTo := fun _ => none) : Option ((Sym × Int) × Term) :=
  match e with
  | .mk _ (.sseq (.mk _ (.base (none, _)))
      (.mk _ (.bound (.mk _ (.wseq
        (.mk _ (.ctor .tuple [.mk _ (.base (some p, _)), .mk _ (.base (some t, _))]))
        (.mk _ (.unseq [d, e]))
        (.mk _ (.wseq (.mk _ (.base (none, _)))
          (.mk sann (.action (.mk .neg (.mk _ _ (.store false
            (.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))))
            (.mk _ () (.sym p'))
            (.mk _ () (.call (.sym s) [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))),
              .mk _ () (.sym t')])) .na)))))
          (.mk _ (.pure (.mk _ () (.call (.sym s') [.mk _ () (.val (.ctype (.mk _
            (.basic (.integer (.signed .int)))))), .mk _ () (.sym t'')]))))))))))
      (.mk _ (.pure (.mk _ () (.val .unit))))) =>
      match StructCell.cellOf file d with
      | some (x, i) =>
        if p'.key = p.key ∧ t'.key = t.key ∧ t''.key = t.key ∧ t.key ≠ p.key ∧ noLoc sann = true ∧
            isConvLoadedInt file s = true ∧ isConvLoadedInt file s' = true ∧ termP file pts d = none then
          (termP file pts e).map fun te => ((x, i), te)
        else none
      | none => none
  | _ => none

theorem assignStmt_inv {f : File Codec.wireModel Unit Unit} {e : Eff} {x : Sym} {i : Int} {t : Term}
    {pts : Key → Option PtsTo} (h : assignStmt f e pts = some ((x, i), t)) :
    ∃ (a0 a1 : List Annot) (ty0 : BaseType) (a2 a3 a4 a5 : List Annot) (p : Sym) (tp : BaseType)
      (a6 : List Annot) (t₀ : Sym) (tt : BaseType) (a7 : List Annot) (dx e' : Eff)
      (b0 b1 : List Annot) (ty1 : BaseType) (sann : List Annot) (l : Loc) (u : Unit)
      (b2 c1 b3 : List Annot) (p' : Sym) (b4 : List Annot) (s : Sym) (b5 c2 b6 : List Annot)
      (t' : Sym) (b7 b8 : List Annot) (s' : Sym) (b9 c3 d0 : List Annot) (t'' : Sym)
      (d1 d2 : List Annot),
      e = .mk a0 (.sseq (.mk a1 (.base (none, ty0)))
        (.mk a2 (.bound (.mk a3 (.wseq
          (.mk a4 (.ctor .tuple [.mk a5 (.base (some p, tp)), .mk a6 (.base (some t₀, tt))]))
          (.mk a7 (.unseq [dx, e']))
          (.mk b0 (.wseq (.mk b1 (.base (none, ty1)))
            (.mk sann (.action (.mk .neg (.mk l u (.store false (Locals.intVal b2 c1)
              (.mk b3 () (.sym p'))
              (.mk b4 () (.call (.sym s) [Locals.intVal b5 c2, .mk b6 () (.sym t')])) .na)))))
            (.mk b7 (.pure (.mk b8 () (.call (.sym s') [Locals.intVal b9 c3, .mk d0 () (.sym t'')]))))))))))
        (.mk d1 (.pure (.mk d2 () (.val .unit))))) ∧
      p'.key = p.key ∧ t'.key = t₀.key ∧ t''.key = t₀.key ∧ t₀.key ≠ p.key ∧ noLoc sann = true ∧
      isConvLoadedInt f s = true ∧ isConvLoadedInt f s' = true ∧ termP f pts e' = some t ∧
      StructCell.cellOf f dx = some (x, i) ∧ termP f pts dx = none := by
  unfold assignStmt at h
  split at h
  · split at h
    · rename_i x' i' hdx
      split at h
      · rename_i hc
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨te, ht, ⟨rfl, rfl⟩, rfl⟩ := h
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
            _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
            hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, ht, hdx, hc.2.2.2.2.2.2.2⟩
      · cases h
    · cases h
  · cases h


/-- A defined, in-bounds element assignment has the usual overflow escape and
preserves every scalar/pointer object and every other array element. -/
theorem assign_runs {file : Program} {labels : Labels} {e : Eff} {x : Sym} {t : Term}
    {pts : Key → Option PtsTo} {i : Nat} (h : assignStmt file e pts = some ((x, (i : Int)), t))
    {env : Env} {m : Mem.Concrete.State} {ls ps : List Local} {ds : Key → Option IntExpr.Term}
    {arrays : List ArrMem.Array} {ads : ArrMem.Defs}
    (inv : StateMem.Inv env m ls ds ps pts) (ai : ArrMem.Inv m arrays ads)
    (ae : ArrMem.EnvOk env arrays) (sep : ArrMem.Separated arrays ls ps)
    {a : ArrMem.Array} (ha : a ∈ arrays) (hx : x.key = a.object.sym.key) (hi : i < a.length)
    (hd : Defined ds t = true) (k : List Frame) (penv : StateMem.PEnv env ps) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m', m'.stdout = m.stdout ∧
        StateMem.Inv env m' ls ds ps pts ∧
        ArrMem.Inv m' arrays (ArrMem.update ads (a.object.sym.key, i)
          (some (close (defsOf ds) t))) ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ ∧
        (m'.lastAddress = m.lastAddress ∧ m'.nextId = m.nextId ∧ m'.dead = m.dead) := by
  obtain ⟨a0, a1, ty0, a2, a3, a4, a5, p, tp, a6, t₀, tt, a7, PX, e', b0, b1, ty1, sann, lc, u,
    b2, c1, b3, p', b4, s, b5, c2, b6, t', b7, b8, s', b9, c3, d0, t'', d1, d2, rfl, hp', ht', ht'',
    htp, hann, hs, hs', he, hdx, hnx⟩ := assignStmt_inv h
  let dest : Val := .object (.pointer (.allocated a.object.id (a.addr i)))
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
  have locs := inv.locsP penv hd
  let D : Mem.Concrete.State → Prop := fun m' => ArrDesig.Arr m' a.object.id a.object.addr a.length
  have hD : ∀ m₁ m₂, D m₁ → Touched m₁ m₂ → D m₂ := fun _ _ h t => h.touched t
  have hDm : D m := ai.live a ha
  have task (I : Mem.Concrete.State → Prop) (hI : ∀ m₁ m₂, I m₁ → Touched m₁ m₂ → I m₂)
      (hID : ∀ m₁, I m₁ → D m₁) :
      LoadTask.ReadTask (file := file) (labels := labels) I env PX dest :=
    (StructCell.cell_runs_arr hdx I hI (ae a ha x hx) hID (by omega)
      (by exact_mod_cast hi) (ai.aligned a ha)).task
  by_cases ok : t.Ok σ
  · right
    refine ⟨ok, ?_⟩
    let I : Mem.Concrete.State → Prop := fun m => StateExpr.LocsP env m σ pts t ∧ D m
    have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ s t => ⟨s.1.touched t, hD _ _ s.2 t⟩
    obtain ⟨xs, m₁, -, tch, s₂⟩ := IntExpr.unseq_pair (file := file) (labels := labels) (k := KB)
      (annots := a7) I hI (task I hI fun _ hm => hm.2)
      (StateExpr.termP_task t he ok I fun _ hm => hm.1)
      (by intro eq; rw [← eq, hnx] at he; cases he) m ⟨locs, hDm⟩
    let v := t.val σ
    have hv : IsInt v := StateExpr.Term.int_of_ok t ok
    let env₁ := extendEnv [(p, dest), (t₀, spec v)] env
    have s₃ : Reaches file labels ⟨.value (.tuple [dest, spec v]), .annotations xs :: KB, m₁⟩
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
    have inv₁ : StateMem.Inv env m₁ ls ds ps pts := inv.touched tch
    have live₁ : IntSubobject.Live m₁ a.object.id (a.addr i) :=
      ((ai.touched tch).live a ha).live (by omega) (by exact_mod_cast hi)
    have s₅ := ArrStore.liftedSub_store_ann (file := file) (labels := labels) sann hann lc u (Locals.intVal b2 c1)
      (.mk b3 () (.sym p')) (.mk b4 () (.call (.sym s) [Locals.intVal b5 c2, .mk b6 () (.sym t')]))
      env₁ inner K0 m₁ c1 live₁ hv
      (fun m' => .cons (Locals.eval_intVal _ env₁ b2 c1) (.cons (.sym (lookup_two_fst hp'))
        (.cons (ConvInt.convLoadedInt_eval (ann := c2) hs hv
          (.cons (Locals.eval_intVal _ env₁ b5 c2) (.cons (.sym (lookup_two_snd ht' htp)) .nil))) .nil)))
      (by simp [inner, List.span, List.span.loop]) resume tch₂
      (by intro a ha; obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha; simp)
      (by simp [activeCall, excludeFrames, inner])
    let m₃ := Locals.stored m₂ a.object.id (a.addr i) v
    have inv₃ : StateMem.Inv env m₃ ls ds ps pts := by
      have i₂ : StateMem.Inv env m₂ ls ds ps pts := (inv₁.nextExcluded _).touched tch₂
      exact ArrMem.scalarInv_storeElem i₂ sep ha hi v
    have ai₃ : ArrMem.Inv m₃ arrays
        (ArrMem.update ads (a.object.sym.key, i) (some (close (defsOf ds) t))) := by
      have a₂ := ((ai.touched tch).nextExcluded _).touched tch₂
      have result := a₂.store ha hi (close (defsOf ds) t)
        (StateExpr.close_ok _ t (inv.defs_ok hd) ok)
      rwa [StateExpr.close_val] at result
    have focus : Touched m₃ (ReturnConst.focusMemory d1 m₃) := by
      obtain ⟨l, eq⟩ := Locals.focusMemory_eq d1 m₃
      exact ⟨l, m₃.lastUsed, eq⟩
    refine ⟨ReturnConst.focusMemory d1 m₃, ?_, inv₃.focus d1, ai₃.touched focus, ?_, ?_⟩
    · simp [m₃, Locals.stored_stdout, tch₂.stdout, tch.stdout]
    · exact pre.trans ((Interleave.reaches_of_local file labels s₂).trans (s₃.trans (s₄.trans
        (s₅.trans ((ReturnConst.wildcard_sequence_reaches file labels a1 ty0 _ PU env k m₃).trans
          (StateStmt.pure_unit_reaches d1 d2 env k m₃))))))
    · obtain ⟨l₁, u₁, e₁⟩ := tch
      obtain ⟨l₂, u₂, e₂⟩ := tch₂
      obtain ⟨l₃, e₃⟩ := Locals.focusMemory_eq d1 m₃
      rw [e₃]
      simp only [m₃, Locals.stored, e₂, e₁]
      exact ⟨rfl, rfl, rfl⟩
  · left
    refine Overflows.pre pre (fails_overflows (ArenaFail.fail_pair file labels (.inl ?_)))
    have flag : taskFlag false KB [(0, .effectExpr PX env, [])] = false := by
      simp [taskFlag, Interleave.controlHasCCall_effectExpr, StructCell.cellOf_noCall hdx]
    rw [flag]
    exact StateExpr.termP_fails t he ok [] m locs


end Silmaril.Compile.Core.Verified.ArrStmt
