module

public import Silmaril.Compiler.Core.Verified.ParamCallerFrame.Defs
public import Silmaril.Compiler.Core.Verified.SlotsChecks.Defs
/-! # A nonempty caller frame and colliding source symbol names

The caller holds 17 at address 4096. A call creates a local immediately below it,
writes and clears that local, allocates another local, then kills both. Both
callee locals deliberately use the caller's source symbol. The caller's slot
retains 17 and the allocator remains depleted after cleanup.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.ParamCallerFrameChecks

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open StateMem (Inv Local)
open ParamCallerFrame (Owned Protected)

def x : Sym := ⟨⟨[]⟩, 504, .objectAddress "same-name"⟩
def caller : Local := ⟨x, 0, 4096⟩
def memory : Mem.Concrete.State := Locals.stored SlotsChecks.memory 0 4096 17
def env : Env := extendEnv [(x, StateMem.ptr caller)] ∅
def defs : StateExpr.Key → Option IntExpr.Term := StateSubst.defs (.lit 17) (StateParam.paramDefs x)
def P : Mem.Concrete.State → Prop := Protected env [caller] defs 2 4096

theorem initial : P memory := by
  refine ⟨?_, by decide, by decide⟩
  exact (StateParam.param_at x env memory (ConvInt.lookup_one rfl) (by unfold ConvInt.IsInt; decide)
    (Locals.stored_slot SlotsChecks.first_live 17)).instantiate (by unfold ConvInt.IsInt; decide)

theorem frame : ParamRunFrame.Region P (Owned 2 4096) :=
  ParamCallerFrame.region env [caller] defs 2 4096
    (by intro l hl; obtain rfl := List.mem_singleton.mp hl; decide)
    (by intro l hl; obtain rfl := List.mem_singleton.mp hl; decide)

def first : Local := ⟨x, 2, 4092⟩
def second : Local := ⟨x, 3, 4088⟩
def afterFirst : Mem.Concrete.State :=
  Locals.stored (Uninitialized.stored
    (Locals.stored (Actions.created (.other "callee1") [] memory) first.id first.addr 99)
    first.id first.addr) first.id first.addr (-23)
def finalMemory : Mem.Concrete.State :=
  Locals.killed (Locals.killed
    (Locals.stored (Actions.created (.other "callee2") [] afterFirst) second.id second.addr 42)
    second.id) first.id

/-- The instantiated predicate keeps a caller value across two callee allocations,
unspecified/ordinary stores and both kills, even when source keys coincide. -/
theorem preserves : P finalMemory := by
  have one : Owned 2 4096 first := by unfold Owned first; decide
  have two : Owned 2 4096 second := by unfold Owned second; decide
  have a : P afterFirst := frame.stored (-23) one
    (frame.unstored one (frame.stored 99 one (frame.created _ _ initial)))
  exact frame.killed one (frame.killed two (frame.stored 42 two (frame.created _ _ a)))

/-- The retained invariant really contains the original caller bytes. -/
theorem caller_value : Locals.Slot finalMemory 0 4096 17 := by
  obtain ⟨_, l, hl, _, slot⟩ := preserves.inv.defs x.key (.lit 17) (by
    simp [defs, StateSubst.defs, StateParam.paramDefs, StateSubst.subst])
  obtain rfl := List.mem_singleton.mp hl
  exact slot

/-- Cleanup leaves two allocations consumed; it supplies no per-call restoration. -/
theorem frontier : finalMemory.lastAddress = 4088 ∧ finalMemory.nextId = 4 := by decide

end Silmaril.Compile.Core.Verified.ParamCallerFrameChecks
