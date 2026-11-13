module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Candidate.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.PureSoundness.Thms
/-! Finite successful all-primitive checker soundness reuses the existing
partial-frame relation, including every register below the fresh boundary. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects.Soundness

abbrev FrameAgrees := PureSoundness.FrameAgrees
abbrev Preserves := PureSoundness.Preserves

end Silmaril.Compiler.Native.Optimize.Validation.Effects.Soundness
