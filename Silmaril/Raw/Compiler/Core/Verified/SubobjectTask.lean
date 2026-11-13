module

public import Silmaril.Compiler.Core.Verified.IntSubobject.Defs
public import Silmaril.Compiler.Core.Verified.NegativeStore.Defs

/-! # Loads and lifted stores of integer subobjects

The dynamics must see the actual subobject address and allocation id, including
its exact read/write access range. These local task proofs permit member and
array accesses inside unsequenced arenas. The lifted negative store retains the
selected resumption's exclusion id; it can write a member after reading that
same member without a spurious race.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.SubobjectTask

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf argState Reaches next_reaches)
open Silmaril.Cerberus.Core.Interleave
open Mem.Concrete (IntRange)
open IntSubobject (Live Slot)
open Locals (stored)
open StoreTask (writeAccess)
open LoadTask (plain_value plain_apply plain_pureExpr)
open NegativeStore (excluded_noRace excluded_noRace_rev)

variable {file : Program} {labels : Labels}

/-- A subobject store records its four-byte write, with the enclosing exclusion id. -/
theorem requestAux_store_apply (ann : List Annot) (k : List Frame) {m : Mem.Concrete.State}
    {id addr n : Int} (live : Live m id addr) (hn : IntRange n) :
    requestAux file labels m (.apply (.memory .store)
      [.ctype (Mem.Concrete.intType ann), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))]) k false =
      .memory "Store" (stored m id addr n) (.value .unit) (.annotations [writeAccess k addr] :: k) := by
  rw [requestAux.eq_def]
  simp [awaitsScheduling, memoryRequest, toMemory, objectMemory,
    IntSubobject.store _ ann live hn, IntSubobject.access _ ann live,
    bind, Except.bind, pure, Except.pure, stored, writeAccess]
  rfl

/-- A positive store, with pure operands, can be driven inside an unsequenced arena.
It records exactly one write and touches no other local's byte range. -/
theorem store_local (ann : List Annot) (l : Loc) (u : Unit) (ty p v : PE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (cann : List Annot)
    {id addr n : Int} (live : Live m id addr) (hn : IntRange n)
    (eval : Eval file (tagsOf file m) env (.inr [ty, p, v])
      (.inr [.ctype (Mem.Concrete.intType cann), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))])) :
    LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.store false ty p v .na))))) env, k, m⟩
      ⟨.value .unit, .annotations [writeAccess k addr] :: k,
        stored (ReturnConst.focusMemory ann m) id addr n⟩ := by
  have req : requestAux file labels m
      (.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.store false ty p v .na))))) env) k false =
      if (ReturnConst.focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr ty env) (.arguments (.memory .store) [] [p, v] env :: k)
      else .next (.setLocation (ReturnConst.focusMemory ann m).currentLocation (.pureExpr ty env))
        (.arguments (.memory .store) [] [p, v] env :: k) := by
    simp only [requestAux, awaitsScheduling, arguments]
    rfl
  have hf : LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.store false ty p v .na))))) env, k, m⟩
      ⟨.pureExpr ty env, .arguments (.memory .store) [] [p, v] env :: k,
        ReturnConst.focusMemory ann m⟩ := by
    obtain ⟨loc, hfocus⟩ := Locals.focusMemory_eq ann m
    rw [hfocus] at req ⊢
    by_cases same : loc == m.currentLocation
    · have eq : loc = m.currentLocation := by simpa using same
      subst loc
      simpa using Relation.ReflTransGen.single (Interleave.LocalStep.next
        (by simpa using req) (plain_pureExpr ty env))
    · exact .head (.next (by simpa [same] using req) (LoadTask.plain_setLocation _ _))
        (.single (.update (Interleave.requestAux_setLocation file labels m loc _ _ false)))
  have args := PureLocal.args_local file (tagsOf file m) (labels := labels) (wc := false) eval (.memory .store) [] k
    (ReturnConst.focusMemory ann m) (Locals.tagsOf_focus ann m)
  simp only [argState, List.nil_append] at args
  exact hf.trans (args.tail (.memory
    (requestAux_store_apply cann k (live.focus ann) hn)))


/-- A subobject read records the actual four-byte range, not the whole allocation. -/
theorem requestAux_load_apply (ann : List Annot) (k : List Frame) {m : Mem.Concrete.State}
    {id addr : Int} (h : Live m id addr) (plain : Mem.Concrete.PlainAt m addr) {n : Int}
    (hn : IntRange n)
    (bytes : Mem.Concrete.fetchBytes 4 addr m.bytes = Mem.Concrete.encodeInteger 4 n) :
    ∃ a : Access, a.write = false ∧
      requestAux file labels m (.apply (.memory .load) [.ctype (Mem.Concrete.intType ann),
        .object (.pointer (.allocated id addr))]) k false =
      .memory "Load" {m with lastUsed := some id} (.value (.loaded (.specified (.integer n))))
        (.annotations [a] :: k) := by
  refine ⟨⟨k.findSome? fun f => match f with | .excluded n => some n | _ => none, [], false,
    addr, 4⟩, rfl, ?_⟩
  rw [requestAux.eq_def]
  simp [awaitsScheduling, memoryRequest, fromMemory,
    IntSubobject.load _ ann h plain hn bytes, IntSubobject.access _ ann h, bind,
    Except.bind, pure, Except.pure]
  rfl


/-- Positive loads with arbitrary pure designators run locally over any continuation.
The pure evaluation premise is where member/array address computations plug in. -/
theorem load_local (ann : List Annot) (l : Loc) (u : Unit) (ty p : PE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (cann : List Annot)
    {id addr n : Int} (slot : Slot m id addr n) (hn : IntRange n)
    (eval : Eval file (tagsOf file m) env (.inr [ty, p])
      (.inr [.ctype (Mem.Concrete.intType cann), .object (.pointer (.allocated id addr))])) :
    ∃ a, a.write = false ∧ LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.load ty p .na))))) env, k, m⟩
      ⟨.value (.loaded (.specified (.integer n))), .annotations [a] :: k,
        {ReturnConst.focusMemory ann m with lastUsed := some id}⟩ := by
  obtain ⟨loc, focus⟩ := Locals.focusMemory_eq ann m
  have focused : Slot (ReturnConst.focusMemory ann m) id addr n :=
    slot.touched (LoadTask.focusMemory_touched ann m)
  have req := LoadTask.requestAux_load (file := file) (labels := labels) m ann l u ty p env k false
  have hf : LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.load ty p .na))))) env, k, m⟩
      ⟨.pureExpr ty env, .arguments (.memory .load) [] [p] env :: k,
        ReturnConst.focusMemory ann m⟩ := by
    rw [focus] at req ⊢
    by_cases same : loc == m.currentLocation
    · have eq : loc = m.currentLocation := by simpa using same
      subst loc
      exact .single (.next (by simpa using req) (plain_pureExpr ty env))
    · exact .head (.next (by simpa [same] using req) (LoadTask.plain_setLocation _ _))
        (.single (.update (requestAux_setLocation file labels m loc _ _ false)))
  have args := PureLocal.args_local file (tagsOf file m) (labels := labels) (wc := false)
    eval (.memory .load) [] k (ReturnConst.focusMemory ann m) (Locals.tagsOf_focus ann m)
  simp only [argState, List.nil_append] at args
  obtain ⟨a, ha, reqLoad⟩ := requestAux_load_apply (file := file) (labels := labels) cann k
    focused.live focused.plain hn focused.bytes
  exact ⟨a, ha, hf.trans (args.tail (.memory reqLoad))⟩

/-- Loading through an effectful designator composes with its local pointer run.
The designator may contain member/array shifts and sequencing; it need not be
`pure(symbol)`, which is the scalar recognizer's restriction. -/
theorem load_designator (ann pa la a1 a2 : List Annot) (pt : BaseType) (p : Sym)
    (designator : EE) (l : Loc) (u : Unit) (env : Env) (k : List Frame)
    (m m₁ : Mem.Concrete.State) (cann : List Annot) {id addr n : Int}
    (slot : Slot m id addr n) (hn : IntRange n)
    (touched : LoadTask.Touched m m₁)
    (run : LocalReaches file labels false
      ⟨.effectExpr designator env,
        .effectBind (.mk pa (.base (some p, pt)))
          (.mk la (.action (.mk .pos (.mk l u (.load (Locals.intVal a1 cann)
            (.mk a2 () (.sym p)) .na))))) env :: k, m⟩
      ⟨.value (.object (.pointer (.allocated id addr))),
        .effectBind (.mk pa (.base (some p, pt)))
          (.mk la (.action (.mk .pos (.mk l u (.load (Locals.intVal a1 cann)
            (.mk a2 () (.sym p)) .na))))) env :: k, m₁⟩) :
    ∃ a m₂, a.write = false ∧ LoadTask.Touched m m₂ ∧
      LocalReaches file labels false
        ⟨.effectExpr (.mk ann (.wseq (.mk pa (.base (some p, pt))) designator
          (.mk la (.action (.mk .pos (.mk l u (.load (Locals.intVal a1 cann)
            (.mk a2 () (.sym p)) .na))))))) env, k, m⟩
        ⟨.value (.loaded (.specified (.integer n))), .annotations [a] :: k, m₂⟩ := by
  let ptr : Val := .object (.pointer (.allocated id addr))
  let body : EE := .mk la (.action (.mk .pos (.mk l u
    (.load (Locals.intVal a1 cann) (.mk a2 () (.sym p)) .na))))
  let env₁ := extendEnv [(p, ptr)] env
  have start : LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.wseq (.mk pa (.base (some p, pt))) designator body)) env, k, m⟩
      ⟨.effectExpr designator env, .effectBind (.mk pa (.base (some p, pt))) body env :: k, m⟩ :=
    .single (.next (LoadTask.requestAux_wseq _ _ _ _ _ _ _ _) (LoadTask.plain_effectExpr _ _))
  have bindStep : LocalReaches file labels false
      ⟨.value ptr, .effectBind (.mk pa (.base (some p, pt))) body env :: k, m₁⟩
      ⟨.effectExpr body env₁, k, m₁⟩ :=
    .single (.next (LoadTask.requestAux_bind _ _ _ _ _ _ _ _ _) (LoadTask.plain_effectExpr _ _))
  obtain ⟨a, ha, finish⟩ := load_local la l u (Locals.intVal a1 cann) (.mk a2 () (.sym p)) env₁ k m₁ cann (slot.touched touched) hn
    (.cons .val (.cons (.sym (ConvInt.lookup_one rfl)) .nil)) (labels := labels)
  refine ⟨a, _, ha, touched.trans ?_, start.trans (run.trans (bindStep.trans finish))⟩
  exact (LoadTask.focusMemory_touched la m₁).trans
    ⟨(ReturnConst.focusMemory la m₁).currentLocation, some id, rfl⟩

/-- A negative subobject store uses the same excluded two-task arena as a scalar store. -/
theorem lifted_store (l : Loc) (u : Unit) (ty p v : PE) (env : Env)
    (inner k : List Frame) (m : Mem.Concrete.State) (cann : List Annot)
    {id addr n : Int} (live : Live m id addr) (hn : IntRange n)
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
      ⟨.effectExpr (.mk [] (.action (.mk .neg (.mk l u (.store false ty p v .na))))) env,
        inner ++ .bound :: k, m⟩
      ⟨.value result, k, stored m₂ id addr n⟩ := by
  let act : EE := .mk [] (.action (.mk .pos (.mk l u (.store false ty p v .na))))
  let m₁ : Mem.Concrete.State := {m with nextExcluded := m.nextExcluded + 1}
  let K := Frame.liftedResult :: .bound :: k
  let a := StoreTask.writeAccess [.excluded m.nextExcluded] addr
  let tasks : List (Nat × (Control × List Frame)) :=
    [(0, .effectExpr act env, [.excluded m.nextExcluded]),
     (1, .value .unit, excludeFrames m.nextExcluded inner)]
  let results : List (Nat × (Val × List Access)) := [(0, .unit, [a]), (1, result, xs)]
  have live₁ : Live m₁ id addr := live.mono rfl rfl
  have live₂ : Live m₂ id addr := by
    obtain ⟨loc, used, eq⟩ := touched
    rw [eq]
    exact live₁.mono rfl rfl
  have store := store_local [] l u ty p v env [.excluded m.nextExcluded] m₂ cann
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
      exact excluded_noRace (by simp [a, StoreTask.writeAccess]) (excluded bb hbb)
    · have eq : bb = a := by simpa using hbb
      subst bb
      exact excluded_noRace_rev (by simp [a, StoreTask.writeAccess]) (excluded aa haa)
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
      ⟨.effectExpr (.mk [] (.action (.mk .neg (.mk l u (.store false ty p v .na))))) env,
        inner ++ .bound :: k, m⟩
      ⟨.interleave [] tasks, K, m₁⟩ := by
    apply ReturnConst.update_reaches
    · intro o h; cases h
    · simp only [act] at lift
      simp [request, requestAux, awaitsScheduling, lift]
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

/-- `bound(store⁻(int, p, v))` runs the lifted positive store, discards its
annotations at the sequence point, and leaves the initialized slot. The action has no
outer location annotation (its internal source location is arbitrary). -/
theorem bound_store (bann : List Annot) (l : Loc) (u : Unit) (ty p v : PE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (cann : List Annot)
    {id addr n : Int} (live : Live m id addr) (hn : IntRange n)
    (eval : ∀ m', Eval file (tagsOf file m') env (.inr [ty, p, v])
      (.inr [.ctype (Mem.Concrete.intType cann), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))])) :
    Reaches file labels
      ⟨.effectExpr (.mk bann (.bound (.mk [] (.action (.mk .neg
        (.mk l u (.store false ty p v .na))))))) env, k, m⟩
      ⟨.value .unit, k, stored {m with nextExcluded := m.nextExcluded + 1} id addr n⟩ := by
  refine (ReturnLit.bound_reaches bann _ env k m).trans ?_
  exact lifted_store l u ty p v env [] k m cann live hn eval
    (by simp [List.span, List.span.loop]) ⟨[], .refl, rfl⟩ (LoadTask.Touched.refl _) (by simp) (by simp [activeCall, excludeFrames])


end Silmaril.Compile.Core.Verified.SubobjectTask
