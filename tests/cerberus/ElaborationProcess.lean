import Silmaril.Compiler.Core.ElaborationProcess.Thms

/-! Read-only public API and transitive proof-axiom audit. -/

#check Silmaril.Compiler.Core.ElaborationProcess.LiteralMain.program
#check Silmaril.Compiler.Core.ElaborationProcess.literal_elaborate
#check Silmaril.Compiler.Core.ElaborationProcess.literal_recognize
#check Silmaril.Compiler.Core.ElaborationProcess.literal_process

#print axioms Silmaril.Compiler.Core.ElaborationProcess.literal_elaborate
#print axioms Silmaril.Compiler.Core.ElaborationProcess.literal_recognize
#print axioms Silmaril.Compiler.Core.ElaborationProcess.literal_process
