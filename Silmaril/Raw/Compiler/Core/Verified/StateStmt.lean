module

public import Silmaril.Compiler.Core.Verified.StateMem.Defs
public import Silmaril.Compiler.Core.Verified.WrapObj.Defs
public import Silmaril.Compiler.Core.Verified.NegativeStore.Defs
public import Silmaril.Compiler.Core.Verified.LocalExpr.Defs
public import Silmaril.Compiler.Core.Verified.StmtIf.Defs

/-! # Statements over several `int` locals

The statements of a block of `int` locals, as Cerberus elaborates them, with their runs from a
memory satisfying `StateMem.Inv`:

* `x = e;` (`assignStmt`): `bound(let weak (p, t) = unseq(pure(x), e) in
  let weak _ = store⁻(int, p, conv_loaded_int(int, t)) in pure(conv_loaded_int(int, t)))`,
  then `pure(unit)`; `pure(x)` may also be a member designator of a struct local wrapping one
  `int` (`IntWrap.desig`), the member being the local's slot. The negative store is lifted to the bound (`lifted_store_ann`, the
  generalisation of `NegativeStore.lifted_store` to location-free action annotations, which is
  what Cerberus emits); `assign_runs`.
* `int x = e;` (`initStmt`): `let strong t = bound(e) in store(int, x, conv_loaded_int(int, t))`;
  `init_runs`.
* `int x;` (`uninitStmt`): `store(int, x, Unspecified(int))`; `uninit_runs`.
* `return e;` (`retStmt`): `let strong u = bound(e) in kill(int, x₁); …; kill(int, xₙ);
  run ret(conv_loaded_int(int, u))`, the block's locals killed in order; `ret_halts`.
* `if (c) return e;` (`ifRet`): the test `c == 0` as a loaded integer, its conversion to a Core
  boolean (`StmtIf.boolSource`), then `if b then <return e;> else pure(unit)`; `ifRet_runs`.

Each run reaches undefined behaviour (an operator leaves `int`) or its normal end. Values are
those of the closed expressions `StateExpr.close (defsOf ds) t`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StateStmt

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval Reaches next_reaches tagsOf)
open Mem.Concrete (LiveInt IntRange)
open Locals (stored Slot)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons)
open ReturnConst (focusMemory)
open ConvInt (isConvLoadedInt IsInt)
open StateExpr (Key Term term termP PtsTo values close)
open StateMem (Local Inv Defined defsOf update ptr)
open IntExpr (spec overflow)
open LoadTask (Touched)

variable {file : Program} {labels : Labels}

/-- No source location among the annotations: focusing on them leaves the memory. -/
def noLoc (ann : List Annot) : Bool :=
  ann.all fun a => match a with | .loc _ => false | _ => true

/-- Undefined behaviour from an operator. -/
def Overflows (s : State) : Prop := ∃ s', Reaches file labels s s' ∧ s'.control = .halt overflow

theorem Overflows.pre {s s' : State} (h : Reaches file labels s s')
    (o : Overflows (file := file) (labels := labels) s') : Overflows (file := file) (labels := labels) s := by
  obtain ⟨t, r, ht⟩ := o
  exact ⟨t, h.trans r, ht⟩

theorem fails_overflows {s : State} (h : ArenaFail.Fails file labels false s overflow) :
    Overflows (file := file) (labels := labels) s :=
  ArenaFail.fail_reaches file labels h

theorem lookup_two_fst {a b s : Sym} {v₁ v₂ : Val} {env : Env} (h : s.key = a.key) :
    (extendEnv [(a, v₁), (b, v₂)] env).lookup s = some v₁ :=
  ConvInt.lookup_one (env := extendEnv [(b, v₂)] env) h

theorem lookup_two_snd {a b s : Sym} {v₁ v₂ : Val} {env : Env} (h : s.key = b.key)
    (ne : b.key ≠ a.key) : (extendEnv [(a, v₁), (b, v₂)] env).lookup s = some v₂ := by
  change (extendEnv [(a, v₁)] (extendEnv [(b, v₂)] env)).lookup s = _
  rw [ConvInt.lookup_one_other (by rw [h]; exact ne), ConvInt.lookup_one h]

/-- `pure(unit)` reaches `unit`. -/
theorem pure_unit_reaches (ann pann : List Annot) (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.pure (.mk pann () (.val .unit)))) env, k, m⟩
      ⟨.value .unit, k, focusMemory ann m⟩ :=
  (ReturnConst.effect_pure_reaches file labels ann _ env k m).trans
    ((ReturnConst.pure_value_reaches file labels pann .unit env _ _).trans
      (ReturnConst.diagnostic_reaches file labels m.currentLocation .unit k _))

/-- A value over at most one annotation frame passes a wildcard strong bind. -/
theorem seq_next {fr : List Frame} {xs : List Access} (hfr : Cond.OneAnn fr xs) (v : Val)
    (ann : List Annot) (ty : BaseType) (b : EE) (env : Env) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, fr ++ .strongBind (.mk ann (.base (none, ty))) b env :: k, m⟩
      ⟨.effectExpr b env, fr ++ k, m⟩ := by
  rcases hfr with ⟨rfl, rfl⟩ | rfl
  · exact ReturnConst.wildcard_sequence_reaches file labels ann ty v b env k m
  · exact Locals.annotations_bind_reaches xs ann ty v b env k m

/-- A value over at most one annotation frame passes a `bound`. -/
theorem bound_pop {fr : List Frame} {xs : List Access} (hfr : Cond.OneAnn fr xs) (v : Val)
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, fr ++ .bound :: k, m⟩ ⟨.value v, k, m⟩ := by
  rcases hfr with ⟨rfl, -⟩ | rfl
  · exact LocalExpr.value_bound_reaches v k m
  · exact Locals.annotations_bound_reaches xs v k m

/-! ## The lifted store -/

/-- `NegativeStore.lifted_store` for an action whose annotations carry no source location
(Cerberus annotates the store of an assignment with its standard reference only). -/
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
    Reaches file labels
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
  have start : Reaches file labels
      ⟨.effectExpr (.mk sann (.action (.mk .neg (.mk l u (.store false ty p v .na))))) env,
        inner ++ .bound :: k, m⟩
      ⟨.interleave [] tasks, K, m₁⟩ := by
    apply ReturnConst.update_reaches
    · intro o h; cases h
    · simp only [act] at lift
      simp [request, requestAux, awaitsScheduling]
      erw [hfind]
      simp [lift]
  refine start.trans ?_
  have steps := arena.tail end_
  refine (reaches_of_local file labels steps).trans ?_
  have selected : Reaches file labels
      ⟨.value (.tuple [.unit, result]), .annotations (a :: xs) :: K, stored m₂ id addr n⟩
      ⟨.value result, .annotations (a :: xs) :: .bound :: k, stored m₂ id addr n⟩ :=
    next_reaches (by intro o h; cases h) (by
      simp [request, requestAux, awaitsScheduling, K])
  have finish := selected.trans
    (Locals.annotations_bound_reaches (a :: xs) result k (stored m₂ id addr n))
  unfold PureEval.Reaches Spec.coreStep at finish
  simpa [results] using finish

/-- The resumption of an assignment: its weak bind, then `pure(conv_loaded_int(int, t))`. -/
theorem assign_resume (b1 : List Annot) (ty1 : BaseType) (an an₁ a1 c1 a3 : List Annot)
    (s t' : Sym) (env₁ : Env) (xs : List Access) (n : Nat) (m : Mem.Concrete.State) {v : Int}
    (hv : IsInt v) (hs : isConvLoadedInt file s = true) (ht : env₁.lookup t' = some (spec v)) :
    ∃ m', Touched m m' ∧ TaskRuns file labels false
      ⟨.value .unit, excludeFrames n [.effectBind (.mk b1 (.base (none, ty1)))
        (.mk an (.pure (.mk an₁ () (.call (.sym s) [.mk a1 () (.val (.ctype (.mk c1
          (.basic (.integer (.signed .int)))))), .mk a3 () (.sym t')])))) env₁,
        .annotations xs], m⟩
      (spec v) (xs.map fun x => {x with exclusions := n :: x.exclusions}) m' := by
  let CALL : PE := .mk an₁ () (.call (.sym s) [.mk a1 () (.val (.ctype (.mk c1
    (.basic (.integer (.signed .int)))))), .mk a3 () (.sym t')])
  let ys := xs.map fun x => {x with exclusions := n :: x.exclusions}
  have hex : excludeFrames n [.effectBind (.mk b1 (.base (none, ty1))) (.mk an (.pure CALL)) env₁,
      .annotations xs] = [.effectBind (.mk b1 (.base (none, ty1))) (.mk an (.pure CALL)) env₁,
      .annotations ys] := rfl
  rw [hex]
  have s₁ : LocalReaches file labels false
      ⟨.value .unit, [.effectBind (.mk b1 (.base (none, ty1))) (.mk an (.pure CALL)) env₁,
        .annotations ys], m⟩
      ⟨.effectExpr (.mk an (.pure CALL)) env₁, [.annotations ys], m⟩ :=
    .single (.next (by simp [requestAux, awaitsScheduling, matchPattern, extendEnv])
      (LoadTask.plain_effectExpr _ _))
  obtain ⟨l, hr⟩ := LoadTask.requestAux_pure (file := file) (labels := labels) m an CALL env₁
    [.annotations ys] false
  obtain ⟨l', s₂⟩ := LoadTask.focus_local (LoadTask.plain_pureExpr CALL env₁) (by simpa using hr)
  let m₄ : Mem.Concrete.State := {m with currentLocation := l'}
  have heval : Eval file (tagsOf file m₄) env₁ (.inl CALL) (.inl (spec v)) :=
    ConvInt.convLoadedInt_eval (ann := c1) hs hv (.cons .val (.cons (.sym ht) .nil))
  have s₃ := PureLocal.eval_local file (tagsOf file m₄) (wc := false) (labels := labels) heval
    (.diagnosticLocation m.currentLocation :: [.annotations ys]) m₄ rfl
  refine ⟨m₄, ⟨l', m.lastUsed, rfl⟩, [.annotations ys], s₁.trans (s₂.trans (s₃.tail ?_)),
    by simp [annotationsOnly, ys]⟩
  exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
    (LoadTask.plain_value _)

/-! ## Recognisers -/

/-- The key of a symbol is the key of a local. -/
def isLocal (xs : List Sym) (x : Sym) : Bool := xs.any fun y => y.key == x.key

/-- The key of a symbol is no local's. -/
def isFresh (xs : List Sym) (x : Sym) : Bool := xs.all fun y => y.key != x.key

/-- The `int` slot an assignment designator names: a local (or a member of a struct wrapping one
`int`, `IntWrap.desig`), or the target `x` of a pointer local `r` dereferenced as `*r` or `r[0]`
when `pts r = some (.addr x)`. -/
def desigP (file : File Codec.wireModel Unit Unit) (pts : Key → Option PtsTo) (d : Eff) :
    Option Sym :=
  match IntWrap.desig file d with
  | some x => some x
  | none => match PtrDeref.derefOf d with
    | some r => match pts r.key with
      | some (.addr x) => some x
      | _ => none
    | none => none

theorem desigP_inv {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} {d : Eff}
    {x : Sym} (h : desigP file pts d = some x) :
    IntWrap.desig file d = some x ∨ ∃ r, PtrDeref.derefOf d = some r ∧ pts r.key = some (.addr x) := by
  unfold desigP at h
  split at h
  · rename_i x' hx; cases h; exact .inl hx
  · split at h
    · rename_i r hr
      split at h
      · rename_i x' hq; cases h; exact .inr ⟨r, hr, hq⟩
      · cases h
    · cases h

theorem desigP_noCall {file : File Codec.wireModel Unit Unit} {pts : Key → Option PtsTo} {d : Eff}
    {x : Sym} (h : desigP file pts d = some x) : hasCCall d = false := by
  rcases desigP_inv h with h | ⟨r, hr, -⟩
  · exact IntWrap.desig_noCall h
  · exact PtrDeref.derefOf_noCall hr

/-- `x = e;` (also `*p = e;` for a pointer local `p` with a target, `pts`) -/
def assignStmt (file : File Codec.wireModel Unit Unit) (e : Eff)
    (pts : Key → Option PtsTo := fun _ => none) : Option (Sym × Term) :=
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
      match desigP file pts d with
      | some x =>
        if p'.key = p.key ∧ t'.key = t.key ∧ t''.key = t.key ∧ t.key ≠ p.key ∧ noLoc sann = true ∧
            isConvLoadedInt file s = true ∧ isConvLoadedInt file s' = true ∧ termP file pts d = none then
          (termP file pts e).map fun te => (x, te)
        else none
      | none => none
  | _ => none

/-- `int x = e;` -/
def initStmt (file : File Codec.wireModel Unit Unit) (e : Eff)
    (pts : Key → Option PtsTo := fun _ => none) : Option (Sym × Term) :=
  match e with
  | .mk _ (.sseq (.mk _ (.base (some t, _))) (.mk _ (.bound e))
      (.mk _ (.action (.mk .pos (.mk _ _ (.store false
        (.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))))
        (.mk _ () (.sym x))
        (.mk _ () (.call (.sym s) [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))),
          .mk _ () (.sym t')])) .na)))))) =>
      if t'.key = t.key ∧ t.key ≠ x.key ∧ isConvLoadedInt file s = true then
        (termP file pts e).map fun te => (x, te)
      else none
  | _ => none

/-- `int x;`: the store of `Unspecified(int)`. -/
def uninitStmt : Eff → Option Sym
  | .mk _ (.action (.mk .pos (.mk _ _ (.store false
      (.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))))
      (.mk _ () (.sym x))
      (.mk _ () (.val (.loaded (.unspecified (.mk _ (.basic (.integer (.signed .int)))))))) .na)))) =>
      some x
  | _ => none

/-- `run ret(conv_loaded_int(int, u))`. -/
def runRet (file : File Codec.wireModel Unit Unit) (ret u : Sym) : Eff → Bool
  | .mk _ (.run () l [.mk _ () (.call (.sym s)
      [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')])]) =>
      l.key = ret.key && u'.key = u.key && isConvLoadedInt file s
  | _ => false

/-- `kill(int*, x)`. -/
def killPtr (x : Sym) : Eff → Bool
  | .mk _ (.action (.mk .pos (.mk _ _ (.kill (.static t) (.mk _ () (.sym x')))))) =>
      PtrDeref.isIntPtr t && decide (x'.key = x.key)
  | _ => false

/-- The kill of the local `x`: at a pointer type for a pointer local (in `zs`), else
`WrapObj.killAny`. -/
def killOf (file : File Codec.wireModel Unit Unit) (zs : List Sym) (x : Sym) (kl : Eff) : Bool :=
  if isLocal zs x then killPtr x kl else WrapObj.killAny file x kl

/-- `kill(int, x₁); …; kill(int, xₙ); run ret(conv_loaded_int(int, u))` (the pointer locals `zs`
killed at their type). -/
def killsRun (file : File Codec.wireModel Unit Unit) (ret u : Sym) (xs : List Sym) (e : Eff)
    (zs : List Sym := []) : Bool :=
  match xs with
  | [] => runRet file ret u e
  | x :: xs => match e with
    | .mk _ (.sseq (.mk _ (.base (none, _))) kl rest) =>
        killOf file zs x kl && killsRun file ret u xs rest zs
    | _ => false

/-- `return e;` in a block with the locals `xs`. -/
def retStmt (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym) : Eff → Option Term
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e)) kr) =>
      if isFresh xs u = true ∧ killsRun file ret u xs kr = true then term file e else none
  | _ => none

/-- `if (c) return e;` in a block with the locals `xs`: the test and the returned expression. -/
def ifRet (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym) :
    Eff → Option (Term × Term)
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec))
      (.mk _ (.sseq (.mk _ (.base (some b, _))) cb
        (.mk _ (.if_ (.mk _ () (.sym b')) ea (.mk _ (.pure (.mk _ () (.val .unit))))))))) =>
      if b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ isFresh xs c = true ∧ isFresh xs b = true then
        match term file ec, retStmt file ret xs ea with
        | some tc, some ta => some (tc, ta)
        | _, _ => none
      else none
  | _ => none


/-! ## Runs -/

theorem seqFocus_touched (ann : List Annot) (m : Mem.Concrete.State) :
    Touched m (SeqReach.focusMemory ann m) := by
  unfold SeqReach.focusMemory
  split
  · split
    · exact Touched.refl m
    · exact ⟨_, m.lastUsed, rfl⟩
  · exact Touched.refl m

/-- Locals whose keys are those of `xs`. -/
def Keys (ls : List Local) (xs : List Sym) : Prop := ls.map (·.sym.key) = xs.map (·.key)

theorem Keys.fresh {ls : List Local} {xs : List Sym} (h : Keys ls xs) {u : Sym}
    (hu : isFresh xs u = true) : ∀ l ∈ ls, l.sym.key ≠ u.key := by
  intro l hl
  have hm : l.sym.key ∈ xs.map (·.key) := by
    rw [← h]; exact List.mem_map_of_mem hl
  obtain ⟨y, hy, hyk⟩ := List.mem_map.mp hm
  have := List.all_eq_true.mp hu y hy
  simp only [bne_iff_ne, ne_eq] at this
  rw [← hyk]; exact this

theorem killsRun_nil {f : File Codec.wireModel Unit Unit} {ret u : Sym} {e : Eff} {zs : List Sym}
    (h : killsRun f ret u [] e zs = true) :
    ∃ (rann : List Annot) (l : Sym) (cann a3 c3 a4 : List Annot) (s u' : Sym),
      e = .mk rann (.run () l [.mk cann () (.call (.sym s) [Locals.intVal a3 c3, .mk a4 () (.sym u')])]) ∧
      l.key = ret.key ∧ u'.key = u.key ∧ isConvLoadedInt f s = true := by
  simp only [killsRun] at h
  unfold runRet at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨_, _, _, _, _, _, _, _, rfl, h.1.1, h.1.2, h.2⟩
  · cases h

theorem killsRun_consZ {f : File Codec.wireModel Unit Unit} {ret u x : Sym} {xs : List Sym} {e : Eff}
    {zs : List Sym} (h : killsRun f ret u (x :: xs) e zs = true) :
    ∃ (ann pann : List Annot) (ty : BaseType) (kl rest : Eff),
      e = .mk ann (.sseq (.mk pann (.base (none, ty))) kl rest) ∧ killOf f zs x kl = true ∧
        killsRun f ret u xs rest zs = true := by
  simp only [killsRun] at h
  split at h
  · simp only [Bool.and_eq_true] at h
    exact ⟨_, _, _, _, _, rfl, h.1, h.2⟩
  · cases h

theorem killsRun_cons {f : File Codec.wireModel Unit Unit} {ret u x : Sym} {xs : List Sym} {e : Eff}
    (h : killsRun f ret u (x :: xs) e = true) :
    ∃ (ann pann : List Annot) (ty : BaseType) (kl rest : Eff),
      e = .mk ann (.sseq (.mk pann (.base (none, ty))) kl rest) ∧ WrapObj.killAny f x kl = true ∧
        killsRun f ret u xs rest = true := by
  obtain ⟨ann, pann, ty, kl, rest, rfl, hk, hr⟩ := killsRun_consZ h
  exact ⟨ann, pann, ty, kl, rest, rfl, by simpa [killOf, isLocal] using hk, hr⟩

theorem killInt_inv {x : Sym} {e : Eff} (h : Locals.killInt x e = true) :
    ∃ (ann : List Annot) (l : Loc) (u : Unit) (c1 a2 : List Annot) (x' : Sym),
      e = .mk ann (.action (.mk .pos (.mk l u (.kill (.static (Mem.Concrete.intType c1))
        (.mk a2 () (.sym x')))))) ∧ x'.key = x.key := by
  unfold Locals.killInt at h
  split at h
  · exact ⟨_, _, _, _, _, _, rfl, of_decide_eq_true h⟩
  · cases h

theorem killPtr_inv {x : Sym} {e : Eff} (h : killPtr x e = true) :
    ∃ (ann : List Annot) (l : Loc) (u : Unit) (tann : List Annot) (q : Qualifiers) (ann' a1 : List Annot)
      (x' : Sym), e = .mk ann (.action (.mk .pos (.mk l u (.kill (.static
        (.mk tann (.pointer q (.mk ann' (.basic (.integer (.signed .int)))))))
        (.mk a1 () (.sym x')))))) ∧ x'.key = x.key := by
  unfold killPtr at h
  split at h
  · rename_i ann l u t a1 x'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨tann, q, ann', rfl⟩ := PtrDeref.isIntPtr_inv h.1
    exact ⟨_, _, _, _, _, _, _, _, rfl, h.2⟩
  · cases h

/-- `kill(int*, x)` of a live pointer object. -/
theorem killPtr_reaches {x : Sym} {e : Eff} (h : killPtr x e = true) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) {id addr : Int}
    (hx : ∀ y : Sym, y.key = x.key → env.lookup y = some (.object (.pointer (.allocated id addr))))
    (slot : StrMem.PtrSlot m id addr) :
    ∃ ann, Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value .unit, k, Locals.killed (focusMemory ann m) id⟩ := by
  obtain ⟨ann, l, u, tann, q, ann', a1, x', rfl, hk⟩ := killPtr_inv h
  have hev : Eval file (tagsOf file m) env (.inr [.mk a1 () (.sym x')])
      (.inr [.object (.pointer (.allocated id addr))]) := .cons (.sym (hx x' hk)) .nil
  refine ⟨ann, (Locals.action_reaches Locals.request_kill hev).trans ?_⟩
  have hs' : StrMem.PtrSlot (focusMemory ann m) id addr := by
    obtain ⟨loc, hf⟩ := Locals.focusMemory_eq ann m
    rw [hf]; exact ⟨slot.alive, slot.alloc, slot.below, slot.above⟩
  have hkill := StrMem.kill_ptr ⟨file.tagDefs, (focusMemory ann m).enumTypes⟩ tann q
    (.mk ann' (.basic (.integer (.signed .int)))) hs'
  exact Actions.memory_reaches (name := "Kill") (by intro o h; cases h) (by
    simp [request, requestAux, awaitsScheduling, memoryRequest, hkill, bind, Except.bind, pure,
      Except.pure]
    rfl)

/-- What a kill needs of the local `l`: a live pointer object for a pointer local (in `zs`), else
a live `int`. -/
def KLive (zs : List Sym) (m : Mem.Concrete.State) (l : Local) : Prop :=
  if isLocal zs l.sym = true then StrMem.PtrSlot m l.id l.addr else LiveInt m l.id l.addr

theorem KLive.focus {zs : List Sym} {m : Mem.Concrete.State} {l : Local} (h : KLive zs m l)
    (ann : List Annot) : KLive zs (focusMemory ann m) l := by
  unfold KLive at h ⊢
  split
  · rename_i hz
    simp only [hz, ↓reduceIte] at h
    obtain ⟨loc, hf⟩ := Locals.focusMemory_eq ann m
    rw [hf]; exact ⟨h.alive, h.alloc, h.below, h.above⟩
  · rename_i hz
    simp only [hz] at h
    exact Locals.liveInt_focus ann h

theorem KLive.killed {zs : List Sym} {m : Mem.Concrete.State} {l : Local} (h : KLive zs m l)
    (other : Int) (ne : l.id ≠ other) : KLive zs (Locals.killed m other) l := by
  unfold KLive at h ⊢
  split
  · rename_i hz
    simp only [hz, ↓reduceIte] at h
    exact ((StateMem.PFrame.killed [l] m other (by simpa using ne)) l (by simp)).1 h
  · rename_i hz
    simp only [hz] at h
    exact StateMem.live_killed h other ne

/-- **The kills, then the jump to the return label**, halt with the returned value; the pointer
locals `zs` are killed at their pointer type. -/
theorem killsRunZ_halts {ret u : Sym} (hret : ReturnLabel labels ret) (zs : List Sym) :
    (xs : List Sym) → (ls : List Local) → Keys ls xs → (xs.map (·.key)).Nodup →
    {e : Eff} → killsRun file ret u xs e zs = true → (env : Env) → {k : List Frame} → NoBoundary k →
    (m : Mem.Concrete.State) →
    (∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)) →
    (∀ l ∈ ls, KLive zs m l) →
    (∀ a ∈ ls, ∀ b ∈ ls, a.sym.key ≠ b.sym.key → a.id ≠ b.id) →
    {v : Int} → IsInt v → env.lookup u = some (spec v) →
    ∃ m', m'.stdout = m.stdout ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.halt (.defined (spec v)), [], m'⟩
  | [], ls, hls, _, e, h, env, k, hk, m, _, _, _, v, hv, hu => by
    obtain ⟨rann, l, cann, a3, c3, a4, s, u', rfl, hl, hu', hs⟩ := killsRun_nil h
    have heval : Eval file (tagsOf file (focusMemory rann m)) env
        (.inl (.mk cann () (.call (.sym s) [Locals.intVal a3 c3, .mk a4 () (.sym u')])))
        (.inl (spec v)) :=
      ConvInt.convLoadedInt_eval (ann := c3) hs hv
        (.cons .val (.cons (.sym (by rw [ReturnLit.lookup_key hu']; exact hu)) .nil))
    obtain ⟨m', out, halts⟩ := ReturnLit.jump_halts hl hret (spec v) env hk (focusMemory rann m)
    refine ⟨m', by simp [out], ?_⟩
    refine (Straight.focus_reaches (m := m) Straight.request_run).trans ?_
    exact ((Eval.sound file _ heval) labels _ _ rfl).trans halts
  | x :: xs, ls, hls, nodup, e, h, env, k, hk, m, henv, hlive, hids, v, hv, hu => by
    cases ls with
    | nil => cases hls
    | cons l ls =>
      simp only [Keys, List.map_cons, List.cons.injEq] at hls
      obtain ⟨hxl, hls⟩ := hls
      obtain ⟨hxs, nodup⟩ := List.nodup_cons.mp nodup
      obtain ⟨ann, pann, ty, kl, rest, rfl, hkl, hrest⟩ := killsRun_consZ h
      have hzx : isLocal zs x = isLocal zs l.sym := by simp [isLocal, hxl]
      have kill : ∃ kann, Reaches file labels ⟨.effectExpr kl env,
          .strongBind (.mk pann (.base (none, ty))) rest env :: k, m⟩
          ⟨.value .unit, .strongBind (.mk pann (.base (none, ty))) rest env :: k,
            Locals.killed (focusMemory kann m) l.id⟩ := by
        have hl := hlive l (by simp)
        unfold killOf at hkl
        unfold KLive at hl
        rw [hzx] at hkl
        split at hkl
        · rename_i hz
          simp only [hz, ↓reduceIte] at hl
          exact killPtr_reaches hkl env _ m (fun y hy => henv l (by simp) y (hy.trans hxl.symm)) hl
        · rename_i hz
          simp only [hz] at hl
          exact WrapObj.killAny_reaches (file := file) (labels := labels) hkl env _ m
            (fun y hy => henv l (by simp) y (hy.trans hxl.symm)) hl
      obtain ⟨kann, kill⟩ := kill
      let m₁ := Locals.killed (focusMemory kann m) l.id
      have ne : ∀ l' ∈ ls, l'.id ≠ l.id := by
        intro l' hl'
        refine (hids l' (by simp [hl']) l (by simp) ?_)
        intro e
        apply hxs
        have hm : l'.sym.key ∈ ls.map (·.sym.key) := List.mem_map_of_mem hl'
        rw [hls, e, hxl] at hm
        exact hm
      obtain ⟨m', out, reach⟩ := killsRunZ_halts hret zs xs ls hls nodup hrest env hk m₁
        (fun l' hl' => henv l' (by simp [hl']))
        (fun l' hl' => ((hlive l' (by simp [hl'])).focus kann).killed l.id (ne l' hl'))
        (fun a ha b hb => hids a (by simp [ha]) b (by simp [hb])) hv hu
      refine ⟨m', by rw [out]; simp [m₁, Locals.killed], ?_⟩
      exact (ReturnConst.sequence_reaches file labels ann _ _ rest env k m).trans (kill.trans
        ((ReturnConst.wildcard_sequence_reaches file labels pann ty .unit rest env k m₁).trans reach))

/-- **The kills, then the jump to the return label**, halt with the returned value. -/
theorem killsRun_halts {ret u : Sym} (hret : ReturnLabel labels ret)
    (xs : List Sym) (ls : List Local) (hls : Keys ls xs) (nodup : (xs.map (·.key)).Nodup)
    {e : Eff} (h : killsRun file ret u xs e = true) (env : Env) {k : List Frame} (hk : NoBoundary k)
    (m : Mem.Concrete.State)
    (henv : ∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l))
    (hlive : ∀ l ∈ ls, LiveInt m l.id l.addr)
    (hids : ∀ a ∈ ls, ∀ b ∈ ls, a.sym.key ≠ b.sym.key → a.id ≠ b.id)
    {v : Int} (hv : IsInt v) (hu : env.lookup u = some (spec v)) :
    ∃ m', m'.stdout = m.stdout ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.halt (.defined (spec v)), [], m'⟩ :=
  killsRunZ_halts hret [] xs ls hls nodup h env hk m henv
    (fun l hl => by simpa [KLive, isLocal] using hlive l hl) hids hv hu

/-- **`return e;`** shows the value of the closed expression, or undefined behaviour. -/
theorem ret_halts {ret : Sym} (hret : ReturnLabel labels ret) {xs : List Sym} {e : Eff} {t : Term}
    (h : retStmt file ret xs e = some t) {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (hls : Keys ls xs)
    (nodup : (xs.map (·.key)).Nodup) (hd : Defined ds t = true) {k : List Frame}
    (hk : NoBoundary k) :
    LocalExpr.Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0
      (close (defsOf ds) t) m.stdout := by
  unfold retStmt at h
  split at h
  · rename_i ann pann u ty bann e' kr
    split at h
    · rename_i cond
      obtain ⟨hfresh, hkr⟩ := cond
      let σ := values (defsOf ds)
      let K := Frame.strongBind (.mk pann (.base (some u, ty))) kr env :: k
      have pre : Reaches file labels
          ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) kr)) env,
            k, m⟩ ⟨.effectExpr e' env, .bound :: K, m⟩ :=
        (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
          (ReturnLit.bound_reaches bann _ env _ m)
      refine LocalExpr.Shows.pre pre ?_
      have locs := inv.locs hd
      by_cases ok : t.Ok σ
      · left
        refine ⟨StateExpr.close_ok _ t (inv.defs_ok hd) ok, ?_⟩
        obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
          t h ok (.bound :: K) m locs
        let v := spec (t.val σ)
        have inv₁ := (inv.touched tch).extend (x := u) (v := v) (hls.fresh hfresh)
        obtain ⟨m', out, reach⟩ := killsRun_halts hret xs ls hls nodup hkr (extendEnv [(u, v)] env) hk m₁
          inv₁.env inv₁.live (fun a ha b hb ne => (inv₁.apart a ha b hb ne).1)
          (StateExpr.Term.int_of_ok t ok) (ConvInt.lookup_one rfl)
        refine ⟨m', by rw [out, tch.stdout], ?_⟩
        rw [StateExpr.close_val]
        exact (Interleave.reaches_of_local file labels run).trans ((bound_pop hfr v K m₁).trans
          ((ReturnLit.bind_reaches pann u ty v kr env k m₁).trans reach))
      · right
        exact fails_overflows (StateExpr.term_fails (file := file) (labels := labels) t h ok
          (.bound :: K) m locs)
    · cases h
  · cases h

/-- The read of a local's symbol: a read-only task returning its pointer. -/
theorem sym_readTask (I : Mem.Concrete.State → Prop) (env : Env) (an pa : List Annot) (x : Sym)
    {v : Val} (hx : env.lookup x = some v) :
    LoadTask.ReadTask (file := file) (labels := labels) I env (.mk an (.pure (.mk pa () (.sym x)))) v := by
  refine ⟨by rw [hasCCall.eq_def], fun m _ => ?_⟩
  obtain ⟨l', run⟩ := LoadTask.pure_sym_local (file := file) (labels := labels) (wc := false) an pa x
    env hx [] m
  exact ⟨[], _, by simp, ⟨l', m.lastUsed, rfl⟩, [], run, rfl⟩

theorem termP_sym_none (file' : File Codec.wireModel Unit Unit) (pts : Key → Option StateExpr.PtsTo)
    (an pa : List Annot) (x : Sym) :
    StateExpr.termP file' pts (.mk an (.pure (.mk pa () (.sym x)))) = none := by
  unfold StateExpr.termP; rfl

theorem term_sym_none (file' : File Codec.wireModel Unit Unit) (an pa : List Annot) (x : Sym) :
    term file' (.mk an (.pure (.mk pa () (.sym x)))) = none :=
  termP_sym_none file' _ an pa x

theorem assignStmt_inv {f : File Codec.wireModel Unit Unit} {e : Eff} {x : Sym} {t : Term}
    {pts : Key → Option PtsTo} (h : assignStmt f e pts = some (x, t)) :
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
      desigP f pts dx = some x ∧ termP f pts dx = none := by
  unfold assignStmt at h
  split at h
  · split at h
    · rename_i x' hdx
      split at h
      · rename_i hc
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨te, ht, rfl, rfl⟩ := h
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
            _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
            hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, ht, hdx, hc.2.2.2.2.2.2.2⟩
      · cases h
    · cases h
  · cases h

/-- **`x = e;`**: undefined behaviour, or `x` holds the closed expression of `e`. -/
theorem assign_runs {e : Eff} {x : Sym} {t : Term} {pts : Key → Option PtsTo}
    (h : assignStmt file e pts = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} (inv : Inv env m ls ds ps pts) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (k : List Frame)
    (penv : StateMem.PEnv env ps := by intro l hl; cases hl) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m', m'.stdout = m.stdout ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ps pts ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  obtain ⟨a0, a1, ty0, a2, a3, a4, a5, p, tp, a6, t₀, tt, a7, PX, e', b0, b1, ty1, sann, lc, u,
    b2, c1, b3, p', b4, s, b5, c2, b6, t', b7, b8, s', b9, c3, d0, t'', d1, d2, rfl, hp', ht', ht'',
    htp, hann, hs, hs', he, hdx, hnx⟩ := assignStmt_inv h
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
  have hpx : env.lookup x = some (ptr l) := inv.lookup hl hx
  obtain ⟨D, hD, hDm, task⟩ : ∃ D : Mem.Concrete.State → Prop,
      (∀ m₁ m₂, D m₁ → Touched m₁ m₂ → D m₂) ∧ D m ∧
      ∀ I : Mem.Concrete.State → Prop, (∀ m₁ m₂, I m₁ → Touched m₁ m₂ → I m₂) →
        (∀ m₁, I m₁ → D m₁) → LoadTask.ReadTask (file := file) (labels := labels) I env PX (ptr l) := by
    rcases desigP_inv hdx with hdx' | ⟨r, hr, hpr⟩
    · exact ⟨fun _ => True, fun _ _ _ _ => trivial, trivial,
        fun I _ _ => IntWrap.desig_readTask I hdx' hpx⟩
    · obtain ⟨pl, hpl, hpk, lq, hlq, hq, obj⟩ := inv.ptrs.pts r.key _ hpr
      have hlq' : ptr lq = ptr l := by
        have a := inv.env lq hlq lq.sym rfl
        have b := inv.env l hl lq.sym (hq.trans hx)
        rw [a] at b; exact Option.some.inj b
      have al := (inv.ptrs.good (List.ne_nil_of_mem hpl) lq hlq).2.2
      refine ⟨fun m' => StrMem.PtrObj m' pl.id pl.addr lq.id lq.addr ∧ LiveInt m' lq.id lq.addr,
        fun _ _ h t => ⟨h.1.touched t, by obtain ⟨l', u', rfl⟩ := t; exact Locals.liveInt_with h.2 rfl rfl⟩,
        ⟨obj, inv.live lq hlq⟩, fun I hI hID => ?_⟩
      rw [← hlq']
      exact (PtrDeref.deref_runs (file := file) (labels := labels) hr I hI
        (penv pl hpl r hpk.symm) (fun m' hm' => hID m' hm') al).task
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
    have inv₁ : Inv env m₁ ls ds ps pts := inv.touched tch
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
    have inv₃ : Inv env m₃ ls (update ds l.sym.key (some (close (defsOf ds) t))) ps pts := by
      have i₂ : Inv env m₂ ls ds ps pts := (inv₁.nextExcluded _).touched tch₂
      have := i₂.store hl (StateExpr.close_ok _ t (inv.defs_ok hd) ok)
      rwa [StateExpr.close_val] at this
    refine ⟨focusMemory d1 m₃, ?_, inv₃.focus d1, ?_⟩
    · simp [m₃, Locals.stored_stdout, tch₂.stdout, tch.stdout]
    · exact pre.trans ((Interleave.reaches_of_local file labels s₂).trans (s₃.trans (s₄.trans
        (s₅.trans ((ReturnConst.wildcard_sequence_reaches file labels a1 ty0 _ PU env k m₃).trans
          (pure_unit_reaches d1 d2 env k m₃))))))
  · left
    refine Overflows.pre pre (fails_overflows (ArenaFail.fail_pair file labels (.inl ?_)))
    have flag : taskFlag false KB [(0, .effectExpr PX env, [])] = false := by
      simp [taskFlag, Interleave.controlHasCCall_effectExpr, desigP_noCall hdx]
    rw [flag]
    exact StateExpr.termP_fails t he ok [] m locs

theorem initStmt_inv {f : File Codec.wireModel Unit Unit} {e : Eff} {x : Sym} {t : Term}
    {pts : Key → Option PtsTo} (h : initStmt f e pts = some (x, t)) :
    ∃ (a0 a1 : List Annot) (t₀ : Sym) (ty : BaseType) (a2 : List Annot) (e' : Eff)
      (a3 : List Annot) (l : Loc) (u : Unit) (b1 c1 b2 b3 b4 c3 b5 : List Annot) (s t' : Sym),
      e = .mk a0 (.sseq (.mk a1 (.base (some t₀, ty))) (.mk a2 (.bound e'))
        (.mk a3 (.action (.mk .pos (.mk l u (.store false (Locals.intVal b1 c1) (.mk b2 () (.sym x))
          (.mk b3 () (.call (.sym s) [Locals.intVal b4 c3, .mk b5 () (.sym t')])) .na)))))) ∧
      t'.key = t₀.key ∧ t₀.key ≠ x.key ∧ isConvLoadedInt f s = true ∧ termP f pts e' = some t := by
  unfold initStmt at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨te, ht, rfl, rfl⟩ := h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2.1, hc.2.2, ht⟩
    · cases h
  · cases h

/-- **`int x = e;`**: undefined behaviour, or `x` holds the closed expression of `e`. -/
theorem init_runs {e : Eff} {x : Sym} {t : Term} {pts : Key → Option PtsTo}
    (h : initStmt file e pts = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} (inv : Inv env m ls ds ps pts) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key)
    (hd : Defined ds t = true) (k : List Frame)
    (penv : StateMem.PEnv env ps := by intro l hl; cases hl) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ m' xs, m'.stdout = m.stdout ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ps pts ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
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
  have locs := inv.locsP penv hd
  by_cases ok : t.Ok σ
  · right
    refine ⟨ok, ?_⟩
    obtain ⟨xs', m₁, fr, hfr, -, tch, run⟩ := StateExpr.termP_runs (file := file) (labels := labels)
      t he ok (.bound :: K) m locs
    let v := t.val σ
    have hv : IsInt v := StateExpr.Term.int_of_ok t ok
    let env₁ := extendEnv [(t₀, spec v)] env
    have inv₁ : Inv env m₁ ls ds ps pts := inv.touched tch
    have hx₁ : env₁.lookup x = some (ptr l) := by
      rw [ConvInt.lookup_one_other (fun e => htx e.symm)]; exact inv.lookup hl hx
    obtain ⟨ys, hst⟩ := Locals.store_reaches (file := file) (labels := labels) a3 b1 b2 b3 b4 b5 c1 c3
      lc u x s t' hs env₁ k m₁ hx₁ (ConvInt.lookup_one ht') hv (inv₁.live l hl)
    have inv₂ := (inv₁.focus a3).store hl (StateExpr.close_ok _ t (inv.defs_ok hd) ok)
    rw [StateExpr.close_val] at inv₂
    refine ⟨_, ys, ?_, inv₂, ?_⟩
    · simp [Locals.stored_stdout, tch.stdout]
    · exact pre.trans ((Interleave.reaches_of_local file labels run).trans ((bound_pop hfr _ K m₁).trans
        ((ReturnLit.bind_reaches a1 t₀ ty _ ST env k m₁).trans hst)))
  · left
    exact Overflows.pre pre (fails_overflows (StateExpr.termP_fails (file := file) (labels := labels)
      t he ok (.bound :: K) m locs))

theorem uninitStmt_inv {e : Eff} {x : Sym} (h : uninitStmt e = some x) :
    ∃ (a0 : List Annot) (l : Loc) (u : Unit) (b1 c1 b2 b3 c3 : List Annot),
      e = .mk a0 (.action (.mk .pos (.mk l u (.store false (Locals.intVal b1 c1) (.mk b2 () (.sym x))
        (.mk b3 () (.val (.loaded (.unspecified (Mem.Concrete.intType c3))))) .na)))) := by
  unfold uninitStmt at h
  split at h
  · cases h; exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  · cases h

/-- `int x;`, or `T x;` for a struct `T` wrapping an `int` (`WrapObj.uninitWrap`). -/
def uninitAny (file : File Codec.wireModel Unit Unit) (e : Eff) : Option Sym :=
  match uninitStmt e with
  | some x => some x
  | none => WrapObj.uninitWrap file e

/-- **`int x;`**: `x` has no definition. -/
theorem uninit_runs {e : Eff} {x : Sym} (h : uninitStmt e = some x)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} {pts : Key → Option PtsTo}
    (inv : Inv env m ls ds ps pts) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key) (k : List Frame) :
    ∃ m' xs, m'.stdout = m.stdout ∧ Inv env m' ls (update ds l.sym.key none) ps pts ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  obtain ⟨a0, lc, u, b1, c1, b2, b3, c3, rfl⟩ := uninitStmt_inv h
  refine ⟨_, _, ?_, (inv.focus a0).uninit hl, Uninitialized.store_reaches (file := file)
    (labels := labels) a0 b1 c1 b2 b3 c3 lc u x env k m (inv.lookup hl hx) (inv.live l hl)⟩
  simp [Uninitialized.stored_stdout]

/-- **`int x;` or `T x;`** (a wrapper `T`): `x` has no definition. -/
theorem uninitAny_runs {e : Eff} {x : Sym} (h : uninitAny file e = some x)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} {pts : Key → Option PtsTo}
    (inv : Inv env m ls ds ps pts) {l : Local} (hl : l ∈ ls) (hx : x.key = l.sym.key) (k : List Frame) :
    ∃ m' xs, m'.stdout = m.stdout ∧ Inv env m' ls (update ds l.sym.key none) ps pts ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  unfold uninitAny at h
  split at h
  · rename_i x' hu
    cases h
    exact uninit_runs hu inv hl hx k
  · obtain ⟨ann, reach⟩ := WrapObj.uninitWrap_reaches (file := file) (labels := labels) h env k m
      (inv.lookup hl hx) (inv.live l hl)
    exact ⟨_, _, by simp [Uninitialized.stored_stdout], (inv.focus ann).uninit hl, reach⟩


/-- `StmtIf.boolSource_reaches`, keeping track of the memory: only locations change. -/
theorem boolSource_touched {c : Sym} {e : Eff} (h : StmtIf.boolSource c e = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (v : Int)
    (hc : env.lookup c = some (spec v)) :
    ∃ m', Touched m m' ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value (boolean (decide (v ≠ 1))), k, m'⟩ := by
  unfold StmtIf.boolSource at h
  split at h
  · rename_i ann pa c' sa spa z ty ea pif pn pe pz z' pv pt pf ua up un
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hc', hz'⟩ := h
    let env' := extendEnv [(z, (.object (.integer v) : Val))] env
    have hsym : env.lookup c' = some (spec v) := by
      rw [ReturnLit.lookup_key hc']; exact hc
    have hs : SeqReach.PureEval file labels (.mk pa () (.sym c')) env (spec v) :=
      SeqReach.pure_symbol pa c' env _ hsym
    let P : PE := .mk pif () (.if_ (.mk pn () (.not (.mk pe () (.op .eq
      (.mk pz () (.sym z')) (.mk pv () (.val (.object (.integer 1))))))))
      (.mk pt () (.val .true)) (.mk pf () (.val .false)))
    have pre := SeqReach.specified_case_reaches (file := file) (labels := labels)
      ann sa ua (.mk spa (.base (some z, ty))) up (yes := .mk ea (.pure P)) (no := un) hs
      (show matchPattern (.mk spa (.base (some z, ty))) (.object (.integer v)) =
        some [(z, .object (.integer v))] from rfl) k m
    have ev (tags : Mem.Concrete.Tags) : Eval file tags env' (.inl P)
        (.inl (boolean (decide (v ≠ 1)))) := by
      have eq : Eval file tags env'
          (.inl (.mk pe () (.op .eq (.mk pz () (.sym z'))
            (.mk pv () (.val (.object (.integer 1)))))))
          (.inl (boolean (v == 1))) :=
        .op (.cons (.sym (ConvInt.lookup_one hz')) (.cons .val .nil))
          (by simp [primitive, integerBin, runtimeValue, runtimeObject]; rfl)
      have ne : Eval file tags env'
          (.inl (.mk pn () (.not (.mk pe () (.op .eq (.mk pz () (.sym z'))
            (.mk pv () (.val (.object (.integer 1)))))))))
          (.inl (boolean (decide (v ≠ 1)))) := by
        apply Eval.not (.cons eq .nil)
        by_cases hv : v = 1 <;> simp [primitive, hv, boolean] <;> rfl
      by_cases hv : v = 1
      · exact .ifFalse (by simpa [hv, boolean] using ne) (by simpa [hv, boolean, runtimeValue] using
          (Eval.val (file := file) (tags := tags) (env := env') (ann := pf) (v := .false)))
      · exact .ifTrue (by simpa [hv, boolean] using ne) (by simpa [hv, boolean, runtimeValue] using
          (Eval.val (file := file) (tags := tags) (env := env') (ann := pt) (v := .true)))
    have hp : SeqReach.PureEval file labels P env' (boolean (decide (v ≠ 1))) := by
      intro k' m'
      exact (Eval.sound file (tagsOf file m') (ev _)) labels k' m' rfl
    refine ⟨SeqReach.focusMemory ea (SeqReach.focusMemory ann m),
      (seqFocus_touched ann m).trans (seqFocus_touched ea _), pre.trans ?_⟩
    exact SeqReach.effect_pure_reaches ea hp k _
  · cases h

theorem ifRet_inv {f : File Codec.wireModel Unit Unit} {ret : Sym} {xs : List Sym} {e : Eff}
    {tc ta : Term} (h : ifRet f ret xs e = some (tc, ta)) :
    ∃ (a0 a1 : List Annot) (c : Sym) (cty : BaseType) (a2 : List Annot) (ec : Eff) (a3 a4 : List Annot)
      (b : Sym) (bty : BaseType) (cb : Eff) (a5 a6 : List Annot) (b' : Sym) (ea : Eff)
      (a7 a8 : List Annot),
      e = .mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec))
        (.mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb
          (.mk a5 (.if_ (.mk a6 () (.sym b')) ea (.mk a7 (.pure (.mk a8 () (.val .unit))))))))) ∧
      b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ isFresh xs c = true ∧ isFresh xs b = true ∧
      term f ec = some tc ∧ retStmt f ret xs ea = some ta := by
  unfold ifRet at h
  split at h
  · split at h
    · rename_i hc
      split at h
      · rename_i tc' ta' h₁ h₂
        cases h
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hc.1, hc.2.1, hc.2.2.1,
          hc.2.2.2, h₁, h₂⟩
      · cases h
    · cases h
  · cases h

/-- **`if (c) return e;`**: undefined behaviour in the test, or the test is not `1` (`c ≠ 0`) and
the statement shows the return of `e`, or the test is `1` and the statement falls through. -/
theorem ifRet_runs {ret : Sym} (hret : ReturnLabel labels ret) {xs : List Sym} {e : Eff}
    {tc ta : Term} (h : ifRet file ret xs e = some (tc, ta)) {env : Env} {m : Mem.Concrete.State}
    {ls : List Local} {ds : Key → Option IntExpr.Term} (inv : Inv env m ls ds) (hls : Keys ls xs)
    (nodup : (xs.map (·.key)).Nodup) (hdc : Defined ds tc = true) (hda : Defined ds ta = true)
    {k : List Frame} (hk : NoBoundary k) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
    (tc.Ok (values (defsOf ds)) ∧ tc.val (values (defsOf ds)) ≠ 1 ∧
      LocalExpr.Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0
        (close (defsOf ds) ta) m.stdout) ∨
    (tc.Ok (values (defsOf ds)) ∧ tc.val (values (defsOf ds)) = 1 ∧ ∃ m', m'.stdout = m.stdout ∧
      Inv env m' ls ds ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩) := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', ea, a7, a8, rfl, hb', hcb, hfc,
    hfb, htc, hta⟩ := ifRet_inv h
  let σ := values (defsOf ds)
  let PU : EE := .mk a7 (.pure (.mk a8 () (.val .unit)))
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) ea PU)
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
        ⟨.effectExpr (if flag then ea else PU) env₂, k, m₃⟩ :=
      (Interleave.reaches_of_local file labels run).trans ((bound_pop hfr _ K m₁).trans
        ((ReturnLit.bind_reaches a1 c cty _ REST env k m₁).trans
          ((ReturnConst.sequence_reaches file labels a3 _ cb IF env₁ k m₁).trans
            (conv.trans ((ReturnLit.bind_reaches a4 b bty _ IF env₁ k m₂).trans
              (SeqReach.effect_if_reaches a5 flag hp k m₂))))))
    have tch₃ : Touched m m₃ := tch.trans (tch₂.trans (seqFocus_touched a5 m₂))
    have inv₃ : Inv env m₃ ls ds := inv.touched tch₃
    by_cases h1 : cv = 1
    · right
      refine ⟨okc, h1, focusMemory a7 m₃, by simp [tch₃.stdout], inv₃.focus a7, ?_⟩
      have enter' : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
          ⟨.effectExpr PU env₂, k, m₃⟩ := by simpa [flag, h1] using enter
      exact pre.trans (enter'.trans (pure_unit_reaches a7 a8 env₂ k m₃))
    · left
      refine ⟨okc, h1, ?_⟩
      have enter' : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
          ⟨.effectExpr ea env₂, k, m₃⟩ := by simpa [flag, h1] using enter
      have inv₂ : Inv env₂ m₃ ls ds := (inv₃.extend (hls.fresh hfc)).extend (hls.fresh hfb)
      have o := ret_halts hret hta inv₂ hls nodup hda hk
      rw [tch₃.stdout] at o
      exact LocalExpr.Shows.pre (pre.trans enter') o
  · left
    exact Overflows.pre pre (fails_overflows (StateExpr.term_fails (file := file) (labels := labels)
      tc htc okc (.bound :: K) m (inv.locs hdc)))

end Silmaril.Compile.Core.Verified.StateStmt
