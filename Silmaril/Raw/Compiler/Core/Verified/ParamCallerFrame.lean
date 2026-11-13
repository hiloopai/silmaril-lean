module

public import Silmaril.Compiler.Core.Verified.ParamRunFrame.Defs
public import Silmaril.Compiler.Core.Verified.CallParamAlloc.Defs
/-! # Disjoint caller slots through conditional callees with locals

Caller slots have identifiers below `first` and addresses at or above `top`.
Callee allocations descend below `top` with identifiers at or above `first`.
This separation survives creation, stores, unspecified stores and local cleanup.
The resulting body theorem retains both the caller's definitions and the callee's
allocation cost in a single local trace.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ParamCallerFrame

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Mem.Concrete (nextIntAddress)
open StateMem (Inv Local)
open StateExpr (Key)
open ReturnConst (focusMemory)

/-- The ids and byte ranges owned by this call, independent of source symbol keys. -/
def Owned (first top : Int) (l : Local) : Prop := first ≤ l.id ∧ l.addr + 4 ≤ top

/-- The caller's integer definitions and the allocator's separation from them. -/
structure Protected (env : Env) (ls : List Local) (ds : Key → Option IntExpr.Term)
    (first top : Int) (m : Mem.Concrete.State) : Prop where
  inv : Inv env m ls ds
  next : first ≤ m.nextId
  last : m.lastAddress ≤ top

theorem next_address_le (m : Mem.Concrete.State) : nextIntAddress m + 4 ≤ m.lastAddress := by
  simp only [nextIntAddress]
  have := Int.emod_nonneg m.lastAddress (by decide : (4 : Int) ≠ 0)
  omega

/-- The region interface is inhabited by an actual caller memory invariant.
No symbolic-name separation or restoration of the allocation frontier is assumed. -/
theorem region (env : Env) (ls : List Local) (ds : Key → Option IntExpr.Term) (first top : Int)
    (ids : ∀ l ∈ ls, l.id < first) (addrs : ∀ l ∈ ls, top ≤ l.addr) :
    ParamRunFrame.Region (Protected env ls ds first top) (Owned first top) where
  touched := by
    intro m m' h t
    obtain ⟨a, b, rfl⟩ := t
    exact ⟨h.inv.touched ⟨a, b, rfl⟩, h.next, h.last⟩
  excluded := fun n h => ⟨h.inv.nextExcluded n, h.next, h.last⟩
  stored := by
    intro m a v own h
    refine ⟨StateParamFrame.inv_stored h.inv a.id a.addr v ?_ (by simp), ?_, ?_⟩
    · intro l hl
      exact .inl (le_trans own.2 (addrs l hl))
    · rw [(Rmw.same_stored m a.id a.addr v).1]; exact h.next
    · rw [(Rmw.same_stored m a.id a.addr v).2.2]; exact h.last
  unstored := by
    intro m a own h
    refine ⟨StateParamFrame.inv_unstored h.inv a.id a.addr ?_ (by simp), ?_, ?_⟩
    · intro l hl
      exact .inl (le_trans own.2 (addrs l hl))
    · rw [(ParamRun.same_uninit m a.id a.addr).1]; exact h.next
    · rw [(ParamRun.same_uninit m a.id a.addr).2.2]; exact h.last
  killed := by
    intro m a own h
    refine ⟨StateParamFrame.inv_killed h.inv a.id ?_ (by simp), h.next, h.last⟩
    intro l hl
    exact Int.ne_of_lt (lt_of_lt_of_le (ids l hl) own.1)
  created := by
    intro m pref ann h
    refine ⟨StateParamFrame.inv_created h.inv pref ann ?_ ?_, ?_, ?_⟩
    · intro l hl
      exact Int.ne_of_lt (lt_of_lt_of_le (ids l hl) h.next)
    · intro l hl
      exact .inl (le_trans (next_address_le m) (le_trans h.last (addrs l hl)))
    · rw [State.created_nextId]; have := h.next; omega
    · rw [Locals.created_lastAddress]
      have := next_address_le m
      have := h.last
      omega
  fresh := by
    intro m x h
    exact ⟨h.next, le_trans (next_address_le m) h.last⟩

variable {file : Program} {labels : Labels}

/-- A conditional parameter body with up to `J` locals preserves all caller slots.
The source return, caller invariant and remaining allocation cost share one witness. -/
theorem body_preserves_caller {x : Sym} {e : EE} {t : IntExpr.Term} {J : Nat}
    (body : ParamRun.body file x e J = some t) (env : Env) (caller : List Frame)
    (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : ConvInt.IsInt n) (slot : Locals.Slot m id addr n)
    (hid : id < m.nextId) (haddr : m.lastAddress ≤ addr) (aligned : m.lastAddress % 4 = 0)
    (room : 4 * ((J : Int) + 1) < m.lastAddress) (dead : ∀ d ∈ m.dead, d < m.nextId)
    {cenv : Env} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv cenv m ls ds) {first top : Int}
    (ids : ∀ l ∈ ls, l.id < first) (addrs : ∀ l ∈ ls, top ≤ l.addr)
    (next : first ≤ m.nextId) (last : m.lastAddress ≤ top) (own : Owned first top ⟨x, id, addr⟩) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧
      (ParamRun.Uses J m m' ∧ Protected cenv ls ds first top m') ∧
      Mem.Concrete.LiveInt m' id addr ∧ LocalReaches file labels false
        ⟨.effectExpr e env, .procedureReturn (CallReach.bodyLabels e) :: caller, m⟩
        ⟨.value (IntExpr.spec (t.val n)), .procedureReturn (CallReach.bodyLabels e) :: caller, m'⟩) ∨
    ArenaFail.Fails file labels false
      ⟨.effectExpr e env, .procedureReturn (CallReach.bodyLabels e) :: caller, m⟩ IntExpr.overflow :=
  ParamRunFrame.body_returns body env caller m hx hn slot hid haddr aligned room dead _ _
    (region cenv ls ds first top ids addrs) ⟨inv, next, last⟩ own

/-- The same callee trace can run as the last operand task, retaining arbitrary
completed operands and outer continuation frames. -/
theorem body_in_arena {x : Sym} {e : EE} {t : IntExpr.Term} {J : Nat}
    (h : ParamRun.body file x e J = some t) (env : Env) (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (hn : ConvInt.IsInt n) (slot : Locals.Slot m id addr n)
    (hid : id < m.nextId) (haddr : m.lastAddress ≤ addr) (aligned : m.lastAddress % 4 = 0)
    (room : 4 * ((J : Int) + 1) < m.lastAddress) (dead : ∀ d ∈ m.dead, d < m.nextId)
    {cenv : Env} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv cenv m ls ds) {first top : Int}
    (ids : ∀ l ∈ ls, l.id < first) (addrs : ∀ l ∈ ls, top ≤ l.addr)
    (next : first ≤ m.nextId) (last : m.lastAddress ≤ top) (own : Owned first top ⟨x, id, addr⟩)
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧
      (ParamRun.Uses J m m' ∧ Protected cenv ls ds first top m') ∧ Mem.Concrete.LiveInt m' id addr ∧
      CoreReaches file labels
        ⟨.interleave done [(i, .effectExpr e env, [.procedureReturn (CallReach.bodyLabels e)])], k, m⟩
        ⟨.interleave ((i, IntExpr.spec (t.val n), []) :: done) [], k, m'⟩) ∨
    ArenaFail.Fails file labels false
      ⟨.interleave done [(i, .effectExpr e env, [.procedureReturn (CallReach.bodyLabels e)])], k, m⟩
      IntExpr.overflow := by
  have pending : Pending [] i := ⟨by simp, by simp⟩
  rcases body_preserves_caller (labels := labels) h env [] m hx hn slot hid haddr aligned room dead
      inv ids addrs next last own with ⟨ok, m', out, kept, live, run⟩ | fail
  · left
    refine ⟨ok, m', out, kept, live, reaches_of_local file labels ?_⟩
    apply drive_task file labels pending
    refine ⟨[], ?_, rfl⟩
    have pop : LocalReaches file labels false
        ⟨.value (IntExpr.spec (t.val n)), [.procedureReturn (CallReach.bodyLabels e)], m'⟩
        ⟨.value (IntExpr.spec (t.val n)), [], m'⟩ :=
      .single (.next (by simp [requestAux, awaitsScheduling]) (LoadTask.plain_value _))
    simpa [taskFlag] using run.trans pop
  · right
    apply ArenaFail.fail_task file labels pending
    simpa [taskFlag] using fail

/-- Scheduled entry of a known procedure, its conditional/local body, and its
return preserve the caller and consume only the reserved local-allocation cost.
The argument is already allocated; its setup and caller-side kill are separate. -/
theorem prepared_in_arena {x g : Sym} {e : EE} {t : IntExpr.Term} {J r : Nat}
    (h : ParamRun.body file x e J = some t) (env : Env) (m : Mem.Concrete.State) {id addr n : Int}
    (hn : ConvInt.IsInt n) (slot : Locals.Slot m id addr n)
    (hid : id < m.nextId) (haddr : m.lastAddress ≤ addr)
    (budget : CallParamAlloc.Reserve (r + J) m)
    (ordinary : libraryCall file g = none)
    (resolved : procedureBody file g [.object (.pointer (.allocated id addr))] =
      .ok (e, [(x, .object (.pointer (.allocated id addr)))]))
    {cenv : Env} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv cenv m ls ds) {first top : Int}
    (ids : ∀ l ∈ ls, l.id < first) (addrs : ∀ l ∈ ls, top ≤ l.addr)
    (next : first ≤ m.nextId) (last : m.lastAddress ≤ top) (own : Owned first top ⟨x, id, addr⟩)
    (done : List (Nat × (Val × List Access))) (i : Nat) (k : List Frame) :
    StateStmt.Overflows (file := file) (labels := labels)
      ⟨.interleave done [(i, .apply (.procedure env)
        [.loaded (.specified (.pointer (.function g))), .object (.pointer (.allocated id addr))], [])], k, m⟩ ∨
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧
      Protected cenv ls ds first top m' ∧ CallParamAlloc.Reserve r m' ∧
      Mem.Concrete.LiveInt m' id addr ∧ CoreReaches file labels
        ⟨.interleave done [(i, .apply (.procedure env)
          [.loaded (.specified (.pointer (.function g))), .object (.pointer (.allocated id addr))], [])], k, m⟩
        ⟨.interleave ((i, IntExpr.spec (t.val n), []) :: done) [], k, m'⟩) := by
  have entry := ArenaCall.procedure_enter file labels m done i g
    [.object (.pointer (.allocated id addr))] env e
    [(x, .object (.pointer (.allocated id addr)))] [] k ordinary resolved
  have room : 4 * ((J : Int) + 1) < m.lastAddress := by
    have := budget.room
    omega
  rcases body_in_arena (labels := labels) h
      (extendEnv [(x, .object (.pointer (.allocated id addr)))] env) m
      (ConvInt.lookup_one rfl) hn slot hid haddr budget.aligned room budget.dead
      inv ids addrs next last own done i k with ⟨ok, m', out, kept, live, run⟩ | fail
  · exact .inr ⟨ok, m', out, kept.2, budget.uses kept.1, live,
      entry.trans (by simpa [CallReach.bodyLabels] using run)⟩
  · obtain ⟨s', run, halt⟩ := ArenaFail.fail_reaches file labels fail
    exact .inl ⟨s', entry.trans (by simpa only [CallReach.bodyLabels] using run), halt⟩

end Silmaril.Compile.Core.Verified.ParamCallerFrame
