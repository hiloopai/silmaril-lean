module

public import Silmaril.Compiler.Native.Optimize.Validation.Floating.Source.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Candidate.Thms
/-! Real floating candidate execution is derived by the retained partial-leaf
guard and existing rooted total DAG meaning; actual memory/event replay is
shared with Effects, without extending or replacing its semantics. -/
@[expose] public section
