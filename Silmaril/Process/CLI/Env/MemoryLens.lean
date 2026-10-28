module

public import Silmaril.Process.CLI.Env

/-! # Environments with lawful memory replacement

`Env.Lawful` alone does not prevent `withMemory` from changing hidden state.
Finite internal-run adapters use the two additional update laws below to give
an exact endpoint, rather than just equality of the final memory and exit flag.
These laws hold for the concrete Linux record update and its restrictions.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Env

/-- A lawful memory lens, including identity and overwrite of updates. -/
structure MemoryLens (E : Env) : Prop extends Lawful E where
  withMemory_self : ∀ s, E.withMemory s (E.memory s) = s
  withMemory_withMemory : ∀ s m m', E.withMemory (E.withMemory s m) m' = E.withMemory s m'

theorem linux_memoryLens : linux.MemoryLens where
  toLawful := linux_lawful
  withMemory_self _ := rfl
  withMemory_withMemory _ _ _ := rfl

theorem MemoryLens.restrict {E : Env} (lens : E.MemoryLens)
    (keep : E.State → Syscall.Request → Syscall.Event → Syscall.Reply → E.State → Prop) :
    (E.restrict keep).MemoryLens where
  toLawful := lens.toLawful.restrict keep
  withMemory_self := lens.withMemory_self
  withMemory_withMemory := lens.withMemory_withMemory

theorem eintrClean_memoryLens : eintrClean.MemoryLens := linux_memoryLens.restrict _
theorem reliable_memoryLens : reliable.MemoryLens := linux_memoryLens.restrict _
theorem ideal_memoryLens : ideal.MemoryLens := linux_memoryLens.restrict _

end Silmaril.Process.CLI.Env
