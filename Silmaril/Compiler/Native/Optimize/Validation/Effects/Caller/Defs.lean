module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Context.Thms
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.ContextualSoundness.Thms
/-! Actual local-SSA caller admission and different-input contextual execution
for every `Lir.Op`, including memory and faulting arithmetic operations. -/
@[expose] public section
