module

public import Silmaril.X86.MemoryModel.Litmus.Verdicts.Defs

/-!
# Litmus verdicts: the 24 tests of the x86-TSO paper (Owens, Sarkar, Sewell, Appendix A)

Per-test Boolean checks, each proved by kernel `decide` (`decide +kernel`). See
`Silmaril.X86.MemoryModel.Litmus.Verdicts.Thms` for what they give.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts

open Silmaril.X86.MemoryModel.Litmus
open Silmaril.X86.MemoryModel.Litmus.Corpus

set_option maxRecDepth 100000

theorem «check_iwp2.1/amd1» : «iwp2.1/amd1».checkTsoBytes = true := by decide +kernel

theorem «check_iwp2.2/amd2» : «iwp2.2/amd2».checkTsoBytes = true := by decide +kernel

theorem «check_iwp2.3.a/amd4» : «iwp2.3.a/amd4».checkTsoBytes = true := by decide +kernel

theorem «check_iwp2.3.b» : «iwp2.3.b».checkTsoBytes = true := by decide +kernel

theorem «check_iwp2.4/amd9» : «iwp2.4/amd9».checkTsoBytes = true := by decide +kernel

theorem «check_iwp2.5/amd8» : «iwp2.5/amd8».checkTsoBytes = true := by decide +kernel

theorem «check_amd3» : «amd3».checkTsoBytes = true := by decide +kernel

theorem «check_iwp2.6» : «iwp2.6».checkTsoBytes = true := by decide +kernel

theorem «check_amd6» : «amd6».checkTsoBytes = true := by decide +kernel

theorem «check_iwp2.7/amd7» : «iwp2.7/amd7».checkTsoBytes = true := by decide +kernel

theorem «check_iwp2.8.a» : «iwp2.8.a».checkTsoBytes = true := by decide +kernel

theorem «check_iwp2.8.b» : «iwp2.8.b».checkTsoBytes = true := by decide +kernel

theorem «check_n8» : «n8».checkTsoBytes = true := by decide +kernel

theorem «check_n3» : «n3».checkTsoBytes = true := by decide +kernel

theorem «check_amd10» : «amd10».checkTsoBytes = true := by decide +kernel

theorem «check_amd5» : «amd5».checkTsoBytes = true := by decide +kernel

theorem «check_n6» : «n6».checkTsoBytes = true := by decide +kernel

theorem «check_n5» : «n5».checkTsoBytes = true := by decide +kernel

theorem «check_n4» : «n4».checkTsoBytes = true := by decide +kernel

theorem «check_n7» : «n7».checkTsoBytes = true := by decide +kernel

theorem «check_n1» : «n1».checkTsoBytes = true := by decide +kernel

theorem «check_n2» : «n2».checkTsoBytes = true := by decide +kernel

theorem «check_rwc-unfenced» : «rwc-unfenced».checkTsoBytes = true := by decide +kernel

theorem «check_rwc-fenced» : «rwc-fenced».checkTsoBytes = true := by decide +kernel

end Silmaril.Proofs.X86.MemoryModel.Litmus.Verdicts
