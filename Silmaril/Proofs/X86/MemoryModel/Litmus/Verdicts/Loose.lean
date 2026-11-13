module

public import Silmaril.X86.MemoryModel.Litmus.Verdicts.Defs

/-!
# Litmus verdicts: the 8 hand-written loose corners (XL verdict only)

Per-test Boolean checks, each proved by kernel `decide` (`decide +kernel`). See
`Silmaril.X86.MemoryModel.Litmus.Verdicts.Thms` for what they give.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts

open Silmaril.X86.MemoryModel.Litmus
open Silmaril.X86.MemoryModel.Litmus.Corpus

set_option maxRecDepth 100000

theorem «check_MS+halves» : «MS+halves».checkXlLoose = true := by decide +kernel

theorem «plain_MS+halves» : «MS+halves».checkPlainLooseBytes = true := by decide +kernel

theorem «check_MIS+straddle» : «MIS+straddle».checkXlLoose = true := by decide +kernel

theorem «plain_MIS+straddle» : «MIS+straddle».checkPlainLooseBytes = true := by decide +kernel

theorem «check_MP+movnti» : «MP+movnti».checkXlLoose = true := by decide +kernel

theorem «check_MP+movnti+sfence» : «MP+movnti+sfence».checkXlLoose = true := by decide +kernel

theorem «check_MP+movnti+lock» : «MP+movnti+lock».checkXlLoose = true := by decide +kernel

theorem «check_MP+stosb» : «MP+stosb».checkXlLoose = true := by decide +kernel

theorem «check_MP+stosb+sfence» : «MP+stosb+sfence».checkXlLoose = true := by decide +kernel

theorem «check_STOS+internal» : «STOS+internal».checkXlLoose = true := by decide +kernel

end Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts
