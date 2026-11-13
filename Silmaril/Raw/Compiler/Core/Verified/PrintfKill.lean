module

public import Silmaril.Compiler.Core.Verified.PrintfArg.Defs
public import Silmaril.Compiler.Core.Verified.StoreTask.Defs

/-! # Unsequenced cleanup of printf's argument objects

A variadic call ends with `unseq(kill(format), kill(argument))`. These are
memory actions inside the arena, rather than ordinary sequential statements.
The local task rules below let the arena drive each kill without inventing
read/write access records or leaving a dead temporary live in the invariant.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintfKill

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf argState)
open Silmaril.Cerberus.Core.Interleave (LocalReaches TaskRuns)
open PrintfStd PrintfStmt StrMem

abbrev EExp := Expr Codec.wireModel Unit Unit Sym

variable {file : Program} {labels : Labels}

/-- A positive kill is a task with no memory access annotation. The typed-memory
premise is required after focusing the source location of the action. -/
theorem kill_task {e : EExp} {ty : Ctype} {p : Sym} (shape : killOf e = some (ty, p))
    {env : Env} {id addr : Int} (hp : env.lookup p = some (.object (.pointer (.allocated id addr))))
    (m : Mem.Concrete.State)
    (canKill : ∀ ann, Mem.Concrete.killTyped ⟨file.tagDefs, m.enumTypes⟩
      (SeqReach.focusMemory ann m) ty (.allocated id addr) =
        .ok ((), killed (SeqReach.focusMemory ann m) id)) :
    ∃ ann, TaskRuns file labels false ⟨.effectExpr e env, [], m⟩ .unit []
      (killed (SeqReach.focusMemory ann m) id) := by
  obtain ⟨ann, l, u, a1, u1, rfl⟩ := killOf_inv shape
  cases u1
  have req : requestAux file labels m
      (.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.kill (.static ty) (.mk a1 () (.sym p))))))) env) [] false =
      if (ReturnConst.focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr (.mk a1 () (.sym p)) env) [.arguments (.memory (.kill ty)) [] [] env]
      else .next (.setLocation (ReturnConst.focusMemory ann m).currentLocation
        (.pureExpr (.mk a1 () (.sym p)) env)) [.arguments (.memory (.kill ty)) [] [] env] := by
    simp only [requestAux, awaitsScheduling, arguments]
    rfl
  have focus : LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.kill (.static ty) (.mk a1 () (.sym p))))))) env, [], m⟩
      ⟨.pureExpr (.mk a1 () (.sym p)) env, [.arguments (.memory (.kill ty)) [] [] env],
        ReturnConst.focusMemory ann m⟩ := by
    obtain ⟨loc, hfocus⟩ := Locals.focusMemory_eq ann m
    rw [hfocus] at req ⊢
    by_cases same : loc == m.currentLocation
    · have eq : loc = m.currentLocation := by simpa using same
      subst loc
      simpa using Relation.ReflTransGen.single (Interleave.LocalStep.next
        (by simpa using req) (LoadTask.plain_pureExpr _ _))
    · exact .head (.next (by simpa [same] using req) (LoadTask.plain_setLocation _ _))
        (.single (.update (Interleave.requestAux_setLocation file labels m loc _ _ false)))
  have ev : Eval file (tagsOf file m) env (.inr [.mk a1 () (.sym p)])
      (.inr [.object (.pointer (.allocated id addr))]) := .cons (.sym hp) .nil
  have args := PureLocal.args_local file (tagsOf file m) (labels := labels) (wc := false) ev
    (.memory (.kill ty)) [] [] (ReturnConst.focusMemory ann m) (Locals.tagsOf_focus ann m)
  simp only [argState, List.nil_append] at args
  refine ⟨ann, [], focus.trans (args.tail (.memory (name := "Kill") ?_)), rfl⟩
  rw [focus_same]
  simp only [requestAux, awaitsScheduling, memoryRequest]
  have hkill := canKill ann
  have enums := (keeps_focus ann m).enums
  rw [enums, hkill]
  simp [bind, Except.bind, pure, Except.pure]

/-- An `int` argument can be killed inside the cleanup arena. -/
theorem int_task {e : EExp} {p : Sym} (cann : List Annot)
    (shape : killOf e = some (Mem.Concrete.intType cann, p)) {env : Env} {id addr : Int}
    (hp : env.lookup p = some (.object (.pointer (.allocated id addr)))) {m : Mem.Concrete.State}
    (live : Mem.Concrete.LiveInt m id addr) :
    ∃ ann, TaskRuns file labels false ⟨.effectExpr e env, [], m⟩ .unit []
      (killed (SeqReach.focusMemory ann m) id) :=
  kill_task shape hp m fun ann => Mem.Concrete.kill_int _ cann (Locals.liveInt_focus ann live)

/-- The format pointer object can be killed inside the cleanup arena. -/
theorem pointer_task {e : EExp} {p : Sym} (tann : List Annot) (q : Qualifiers) (ref : Ctype)
    (shape : killOf e = some (.mk tann (.pointer q ref), p)) {env : Env} {id addr : Int}
    (hp : env.lookup p = some (.object (.pointer (.allocated id addr)))) {m : Mem.Concrete.State}
    (slot : PtrSlot m id addr) :
    ∃ ann, TaskRuns file labels false ⟨.effectExpr e env, [], m⟩ .unit []
      (killed (SeqReach.focusMemory ann m) id) :=
  kill_task shape hp m fun ann => kill_ptr _ tann q ref (slot.keeps (keeps_focus ann m))

/-- Killing the integer temporary leaves the separate format object live. -/
theorem pointer_killed {m : Mem.Concrete.State} {id addr other : Int}
    (slot : PtrSlot m id addr) (ne : id ≠ other) : PtrSlot (killed m other) id addr := by
  refine ⟨?_, ?_, slot.below, slot.above⟩
  · simpa [killed, ne] using slot.alive
  · obtain ⟨a, ha, rest⟩ := slot.alloc
    exact ⟨a, by rw [show (killed m other).allocations = m.allocations.erase other from rfl,
      StrMem.map_lookup_erase_ne _ ne]; exact ha, rest⟩

/-- The two cleanup tasks run in the canonical last-task-first order, without
races. Only the two argument objects die; earlier objects are preserved. -/
theorem cleanup {e0 e1 : EExp} {p0 p1 : Sym} (tann cann : List Annot)
    (q : Qualifiers) (ref : Ctype)
    (s0 : killOf e0 = some (.mk tann (.pointer q ref), p0))
    (s1 : killOf e1 = some (Mem.Concrete.intType cann, p1)) {env : Env}
    {fid faddr iid iaddr : Int}
    (h0 : env.lookup p0 = some (.object (.pointer (.allocated fid faddr))))
    (h1 : env.lookup p1 = some (.object (.pointer (.allocated iid iaddr))))
    {m : Mem.Concrete.State} (pointer : PtrSlot m fid faddr)
    (integer : Mem.Concrete.LiveInt m iid iaddr) (ne : fid ≠ iid)
    (ann : List Annot) (k : List Frame) :
    ∃ m', ReturnConst.Reaches file labels ⟨.effectExpr (.mk ann (.unseq [e0, e1])) env, k, m⟩
      ⟨.value (.tuple [.unit, .unit]), .annotations [] :: k, m'⟩ ∧
      m'.stdout = m.stdout ∧ m'.nextId = m.nextId ∧ m'.lastAddress = m.lastAddress ∧
      m'.dead = fid :: iid :: m.dead ∧
      (∀ m₀, Keeps m₀ m → m₀.nextId ≤ fid → m₀.nextId ≤ iid → Keeps m₀ m') := by
  obtain ⟨ann1, run1⟩ := int_task (file := file) (labels := labels) cann s1 h1 integer
  let m1 := killed (SeqReach.focusMemory ann1 m) iid
  have ptr1 : PtrSlot m1 fid faddr := pointer_killed (pointer.keeps (keeps_focus ann1 m)) ne
  obtain ⟨ann0, run0⟩ := pointer_task (file := file) (labels := labels) tann q ref s0 h0 ptr1
  have flag0 : Interleave.taskFlag false k [] = false := by simp [Interleave.taskFlag]
  have flag1 : Interleave.taskFlag false k [(0, .effectExpr e0 env, [])] = false := by
    obtain ⟨A, l, u, a1, u1, rfl⟩ := killOf_inv s0
    simp [Interleave.taskFlag, Interleave.controlHasCCall_effectExpr, hasCCall]
  have runs : Interleave.TasksRun file labels false k
      [(0, .effectExpr e0 env, []), (1, .effectExpr e1 env, [])] m
      [(0, .unit, []), (1, .unit, [])] (killed (SeqReach.focusMemory ann0 m1) fid) :=
    .snoc (flag1 ▸ run1) (.snoc (flag0 ▸ run0) .nil)
  have all := Interleave.unseq_runs file labels (annots := ann) (es := [e0, e1])
    (env := env) (by simpa [Interleave.unseqTasks] using runs)
    (by intro x hx a ha; simp at hx; rcases hx with rfl | rfl <;> simp at ha)
  refine ⟨_, Interleave.reaches_of_local file labels (by simpa using all),
    by simp [killed, m1], by simp [killed, m1], by simp [killed, m1], by simp [killed, m1], ?_⟩
  intro m₀ keep hf hi
  exact ((((keep.trans (keeps_focus ann1 m)).killed hi).trans (keeps_focus ann0 m1)).killed hf)

end Silmaril.Compile.Core.Verified.PrintfKill
