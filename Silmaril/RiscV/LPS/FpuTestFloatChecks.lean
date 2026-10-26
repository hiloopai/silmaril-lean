module

public import Silmaril.RiscV.LPS.FpuTestFloat
public meta import Silmaril.RiscV.LPS.FpuTestFloat

/-!
# TestFloat and special-value checks for both RISC-V FPU kernels

Compiled evaluations (`#guard`) of the tables in `Silmaril.RiscV.LPS.FpuTestFloat`. They
are tests, not proofs: no theorem depends on them.
-/

namespace Silmaril.RiscV.LPS.TestFloat

#guard lines.length == 19456
#guard unparsed.isEmpty
-- The literal LPS kernel reproduces every TestFloat vector, bits and flags.
#guard (mismatches FpuImpl.lps).isEmpty
-- So does Silmaril's IEEE 754 kernel.
#guard (mismatches FpuImpl.ieee).isEmpty
-- The two kernels agree on all 71688 special-value requests.
#guard poolAll.length == 71688
#guard poolDisagreements.isEmpty

end Silmaril.RiscV.LPS.TestFloat
