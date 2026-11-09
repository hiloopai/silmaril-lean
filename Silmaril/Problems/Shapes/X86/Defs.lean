module

public import Silmaril.Problems.Core.Defs
public import Silmaril.Problems.Models.X86.Defs

/-!
# Problem shapes: x86-64 functions on a class of machines

Function correctness against a **model class** (`Silmaril.Problems.Class`), the quantifier
shape of demonic x86-64 function problems (`FnCorrect`).

| name | statement |
|---|---|
| `Correct 𝓜 S` | for every placement `entry`, `S entry` is demonically totally correct on every member of `𝓜` |
| `CorrectLoose D S` | the same on the down-set of the loose top over the listing table `D` (`Models.X86.looseSv1`) |

These are parametric shapes, not problems: a problem instantiates one with a pinned listing
and specification and registers the closed result with `@[problem "ID"]`.
-/

@[expose] public section

namespace Silmaril.Problems.Shapes

open Silmaril.X86 (MState Word)
open Silmaril.X86.FnContract (Spec)

/-- **Demonic function correctness on the class `𝓜`** (`FnCorrect`). -/
def Correct (𝓜 : Silmaril.Problems.Class MState) (S : Word → Spec MState) : Prop :=
  Silmaril.Problems.FnCorrect 𝓜 S

/-- **Demonic function correctness below the loose top** over the listing table `D`. -/
def CorrectLoose (D : Silmaril.X86.Loose.DTable Silmaril.X86.Loose.Listing.LForm)
    (S : Word → Spec MState) : Prop :=
  Correct (Silmaril.Problems.Class.below (Silmaril.Problems.Models.X86.looseSv1 D)) S

end Silmaril.Problems.Shapes
