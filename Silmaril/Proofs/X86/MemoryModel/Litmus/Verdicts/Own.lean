module

public import Silmaril.X86.MemoryModel.Litmus.Verdicts.Defs

/-!
# Litmus verdicts: the 10 hand-written x86-TSO-covered own tests (IRIW+mfences, SB+lock-*, RMW atomicity)

Per-test Boolean checks, each proved by kernel `decide` (`decide +kernel`). See
`Silmaril.X86.MemoryModel.Litmus.Verdicts.Thms` for what they give.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts

open Silmaril.X86.MemoryModel.Litmus
open Silmaril.X86.MemoryModel.Litmus.Corpus

set_option maxRecDepth 100000

theorem «check_IRIW+mfences» : «IRIW+mfences».checkTsoBytes = true := by decide +kernel

theorem «check_SB+lock-adds» : «SB+lock-adds».checkTsoBytes = true := by decide +kernel

theorem «check_SB+lock-xadds» : «SB+lock-xadds».checkTsoBytes = true := by decide +kernel

theorem «check_SB+lock-cmpxchgs» : «SB+lock-cmpxchgs».checkTsoBytes = true := by decide +kernel

theorem «check_RMW+lock-xadds» : «RMW+lock-xadds».checkTsoBytes = true := by decide +kernel

theorem «check_RMW+lock-xadds-final» : «RMW+lock-xadds-final».checkTsoBytes = true := by decide +kernel

theorem «check_RMW+lock-cmpxchgs» : «RMW+lock-cmpxchgs».checkTsoBytes = true := by decide +kernel

theorem «check_RMW+xchgs» : «RMW+xchgs».checkTsoBytes = true := by decide +kernel

theorem «check_RMW+lock-inc+W» : «RMW+lock-inc+W».checkTsoBytes = true := by decide +kernel

theorem «check_RMW+inc+W» : «RMW+inc+W».checkTsoBytes = true := by decide +kernel

end Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts
