import Silmaril.Compiler.Core.ElaborationCorrectness.Thms

-- Audit the actual source/output API and its kernel dependencies. The universal
-- theorems carry the fragment/runtime/state premises; no expected Core body is
-- supplied as a substitute for real translation success.
#check Silmaril.Compiler.Core.ElaborationCorrectness.returnLiteral_run
#check Silmaril.Compiler.Core.ElaborationCorrectness.returnLiteral_success_reaches
#print axioms Silmaril.Compiler.Core.ElaborationCorrectness.returnLiteral_run
#print axioms Silmaril.Compiler.Core.ElaborationCorrectness.returnLiteral_success_reaches
