import Silmaril.Compiler.Core.ElaborationTotal.Thms

/-! Audit the universal actual-Core result and its actual-source entry point.
The source theorem assumes runtime syntax/range/freshness facts, not compiler
success or a completed behavior. Arbitrary finite prefixes remain admitted. -/

#check Silmaril.Cerberus.Core.Forced.Reaches
#check Silmaril.Cerberus.Core.Forced.Reaches.single
#check Silmaril.Cerberus.Core.Forced.Reaches.trans
#check Silmaril.Cerberus.Core.Forced.Reaches.erase
#check Silmaril.Cerberus.Core.Forced.step
#check Silmaril.Cerberus.Core.Forced.next
#check Silmaril.Cerberus.Core.Forced.update
#check Silmaril.Cerberus.Core.Forced.memory
#check Silmaril.Cerberus.Core.Forced.end_
#check Silmaril.Cerberus.Core.Forced.choose
#check Silmaril.Cerberus.Core.Forced.scheduled
#check Silmaril.Compiler.Core.ElaborationTotal.returnsInteger
#check Silmaril.Compiler.Core.ElaborationTotal.ForcedSound
#check Silmaril.Compiler.Core.ElaborationTotal.startup_errno_forced
#check Silmaril.Compiler.Core.ElaborationTotal.enter_main_forced
#check Silmaril.Compiler.Core.ElaborationTotal.initial_forced_body
#check Silmaril.Compiler.Core.ElaborationTotal.retLit_forced
#check Silmaril.Compiler.Core.ElaborationTotal.recognized_forced
#check Silmaril.Compiler.Core.ElaborationTotal.recognized_satisfies
#check Silmaril.Compiler.Core.ElaborationTotal.recognized_coreBeh_iff
#check Silmaril.Compiler.Core.ElaborationTotal.literal_total
#check Silmaril.Compiler.Core.ElaborationTotal.satisfies_category
#check Silmaril.Compiler.Core.ElaborationTotal.satisfies_noUndefinedBehaviour
#check Silmaril.Compiler.Core.ElaborationTotal.satisfies_terminates
#check Silmaril.Compiler.Core.ElaborationTotal.satisfies_terminalOutput

#print axioms Silmaril.Cerberus.Core.Forced.terminal_unique
#print axioms Silmaril.Cerberus.Core.Forced.no_infinite
#print axioms Silmaril.Compiler.Core.ElaborationTotal.pureEvaluation_forced
#print axioms Silmaril.Compiler.Core.ElaborationTotal.recognized_satisfies
#print axioms Silmaril.Compiler.Core.ElaborationTotal.recognized_coreBeh_iff
#print axioms Silmaril.Compiler.Core.ElaborationTotal.literal_total
#print axioms Silmaril.Compiler.Core.ElaborationTotal.startup_errno_forced
#print axioms Silmaril.Compiler.Core.ElaborationTotal.enter_main_forced
#print axioms Silmaril.Compiler.Core.ElaborationTotal.initial_forced_body
#print axioms Silmaril.Compiler.Core.ElaborationTotal.retLit_forced
#print axioms Silmaril.Compiler.Core.ElaborationTotal.recognized_forced
#print axioms Silmaril.Compiler.Core.ElaborationTotal.satisfies_category
#print axioms Silmaril.Compiler.Core.ElaborationTotal.satisfies_noUndefinedBehaviour
#print axioms Silmaril.Compiler.Core.ElaborationTotal.satisfies_terminates
#print axioms Silmaril.Compiler.Core.ElaborationTotal.satisfies_terminalOutput
