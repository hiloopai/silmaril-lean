module

public import Silmaril.Machine.Region.X86.CFG.Defs
public import Silmaril.Machine.Region.X86.Defs

/-! # Conditional execution of byte-CFG rows

Thread retirement refines the handwritten Ext machine. Environment steps may
change ambient data, but preserve the focused PC and an invariant guaranteeing
executable fetch of the exact bytes. The same invariant is preserved by thread
steps. This is an explicit interference contract, not a multithread adequacy or
hardware-memory-model theorem. Faults/nonretirement remain distinguished halts;
normal-edge coverage proves no progress, termination or absence of faults.
-/

@[expose] public section
namespace Silmaril.Machine.Region.X86.CFG
open Silmaril.Semantics.Region

structure ExecutionContract (r : Row) (Ambient : Type*) where
  focus : Ambient → Silmaril.X86.MState
  returnAddress : Silmaril.X86.Word
  invariant : Ambient → Prop
  thread : Ambient → Ambient → Prop
  environment : Ambient → Ambient → Prop
  loaded : ∀ s, invariant s → r.code.LoadedIn (focus s).memory
  thread_step : ∀ s t, thread s t → (system returnAddress).step (focus s) [] (focus t)
  thread_preserves : ∀ s t, invariant s → thread s t → invariant t
  environment_preserves : ∀ s t, invariant s → environment s t → invariant t
  environment_pc : ∀ s t, invariant s → environment s t →
    (focus t).core.rip = (focus s).core.rip

def ExecutionContract.interleaving {r : Row} {Ambient : Type*} (c : ExecutionContract r Ambient) :
    TransitionSystem Ambient Nat Empty Silmaril.X86.Ext.Outcome where
  pc s := (c.focus s).core.rip.toNat
  step s es t := es = [] ∧ (c.thread s t ∨ c.environment s t)
  halt s k := (system c.returnAddress).halt (c.focus s) k

end Silmaril.Machine.Region.X86.CFG
