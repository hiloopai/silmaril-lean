module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Soundness.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Context.Thms
/-! Successful `Lir.Op` block execution transports across related partial
inputs with the same concrete memory. Floating/address instructions and calls
remain outside the actual Effects checker admission. -/
@[expose] public section
