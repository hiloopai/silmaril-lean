module

public import Silmaril.Compiler.Native.Optimize.Validation.Floating.Context.Thms
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.ContextualSoundness.Thms
/-! The actual LambdaSSA selection and retained isSSA/checker identity fallback
remain unchanged while mixed primitive/floating blocks gain a real caller proof. -/
@[expose] public section
