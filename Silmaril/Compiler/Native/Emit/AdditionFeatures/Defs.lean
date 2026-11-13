module

public import Silmaril.Compiler.Native.Emit.AdditionFetched.Defs
public import Silmaril.X86.FetchTrace.Features.Defs
public import Silmaril.Compiler.Native.Correctness.Defs
/-! Independent actual Features entry for the canonical unoptimized addition
image. Extended SIMD/floating state is arbitrary and retained by real dispatch. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Emit.AdditionFeatures

abbrev Entry (initial : Silmaril.X86.Features.MState) (left right exit : Silmaril.X86.Word) : Prop :=
  AdditionFetched.Entry initial.toBase left right exit

end Silmaril.Compiler.Native.Emit.AdditionFeatures
