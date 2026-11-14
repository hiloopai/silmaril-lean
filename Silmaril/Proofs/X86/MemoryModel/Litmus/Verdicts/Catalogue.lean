module

public import Silmaril.X86.MemoryModel.Litmus.Verdicts.Defs

/-!
# Litmus verdicts: the 23 herdtools7 x86 catalogue tests and the herd7 regression tests A011, A013, A014

Per-test Boolean checks, each proved by kernel `decide` (`decide +kernel`). See
`Silmaril.X86.MemoryModel.Litmus.Verdicts.Thms` for what they give.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts

open Silmaril.X86.MemoryModel.Litmus
open Silmaril.X86.MemoryModel.Litmus.Corpus

set_option maxRecDepth 100000

theorem «check_SB» : «SB».checkTsoBytes = true := by decide +kernel

theorem «check_SB+mfence+po» : «SB+mfence+po».checkTsoBytes = true := by decide +kernel

theorem «check_SB+mfences» : «SB+mfences».checkTsoBytes = true := by decide +kernel

theorem «check_SB+rfi-pos» : «SB+rfi-pos».checkTsoBytes = true := by decide +kernel

theorem «check_MP» : «MP».checkTsoBytes = true := by decide +kernel

theorem «check_MP+mfence+po» : «MP+mfence+po».checkTsoBytes = true := by decide +kernel

theorem «check_MP+po+mfence» : «MP+po+mfence».checkTsoBytes = true := by decide +kernel

theorem «check_MP+mfences» : «MP+mfences».checkTsoBytes = true := by decide +kernel

theorem «check_LB» : «LB».checkTsoBytes = true := by decide +kernel

theorem «check_LB+mfence+po» : «LB+mfence+po».checkTsoBytes = true := by decide +kernel

theorem «check_LB+mfences» : «LB+mfences».checkTsoBytes = true := by decide +kernel

theorem «check_R» : «R».checkTsoBytes = true := by decide +kernel

theorem «check_R+mfence+po» : «R+mfence+po».checkTsoBytes = true := by decide +kernel

theorem «check_R+po+mfence» : «R+po+mfence».checkTsoBytes = true := by decide +kernel

theorem «check_R+mfences» : «R+mfences».checkTsoBytes = true := by decide +kernel

theorem «check_R+mfence+rfi-po» : «R+mfence+rfi-po».checkTsoBytes = true := by decide +kernel

theorem «check_S» : «S».checkTsoBytes = true := by decide +kernel

theorem «check_S+mfence+po» : «S+mfence+po».checkTsoBytes = true := by decide +kernel

theorem «check_S+po+mfence» : «S+po+mfence».checkTsoBytes = true := by decide +kernel

theorem «check_S+mfences» : «S+mfences».checkTsoBytes = true := by decide +kernel

theorem «check_2+2W» : «2+2W».checkTsoBytes = true := by decide +kernel

theorem «check_2+2W+mfence+po» : «2+2W+mfence+po».checkTsoBytes = true := by decide +kernel

theorem «check_2+2W+mfences» : «2+2W+mfences».checkTsoBytes = true := by decide +kernel

theorem «check_A011» : «A011».checkTsoBytes = true := by decide +kernel

theorem «check_A013» : «A013».checkTsoBytes = true := by decide +kernel

theorem «check_A014» : «A014».checkTsoBytes = true := by decide +kernel

end Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts
