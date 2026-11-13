module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Meaning.Thms
/-! Actual source load execution extends rooted DAG meaning with the real
memory result at the checker's actual next effect index. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects
open Silmaril.Machine

structure LoadResult (before after : State) (frame : Lir.Frame Nat)
    (oldMeaning newMeaning : Interpretation) : Prop where
  rooted : Roots.Rooted after frame newMeaning
  total : Total.TotalNodes after.nodes newMeaning
  loads : LoadsScoped after.nodes after.effects.size
  extension : PrefixExtends before.nodes.size before.effects.size oldMeaning newMeaning
  grows : before.nodes.size ≤ after.nodes.size

end Silmaril.Compiler.Native.Optimize.Validation.Effects
