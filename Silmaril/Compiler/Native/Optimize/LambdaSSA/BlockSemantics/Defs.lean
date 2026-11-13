module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.InstructionSemantics.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.ViewTyping.Defs
/-! Actual native/older-RTL block semantic bridges. The proofs use the existing
instruction-list, singleton-function and LambdaSSA evaluation relations; this
topic introduces no replacement executor or state conversion. -/
@[expose] public section
