module

public import Silmaril.Compiler.Core.Verified.ReturnLit.Defs
public import Silmaril.Cerberus.Core.CallReach.Defs

/-! Semantic interfaces for the actual Core forms emitted by the first
Cerberus elaboration slice. The semantic results are in `Thms`; there is no
alternate expression syntax or executable translator here. This topic is in
Compiler because its reused `ReturnLit`/`ConvInt` lemmas depend on Compiler.
-/
