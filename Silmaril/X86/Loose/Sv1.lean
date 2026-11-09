module

public import Silmaril.X86.Loose.Forms.Int
public import Silmaril.X86.Loose.Forms.Ctl
public import Silmaril.X86.Loose.Forms.MulDiv
public import Silmaril.X86.Loose.Forms.Str

/-!
# `Σ v1`: the loose specification of the integer and string forms

The form index of the open x86 machines is `Str9.Instr`: an `Ext9` instruction or one of the
three string forms. `Σ v1` specifies, over it,

* `intSpec : Ext9.Instr → Option EffSpec`: the integer forms, in three groups. `Ctl`
  (control flow, stack, `cmov`, `setcc`, `endbr64`) comes first, then `MulDiv` (multiply,
  divide, carry arithmetic, `bt`, `bsf`/`bsr`), then `Int` (moves, ALU, tests, shifts,
  `load`/`store`, `nop`). The groups are disjoint except for `endbr64`, which `Int` and `Ctl`
  both specify (as a `nop`); `Ctl`'s spec is the one used;
* `Forms.Str.strSpec`: the string forms;
* `Sv1 : Sigma Str9.Instr`: both, as `FormSpec`s (`EffSpec.toFormSpec`).

The `Ext9` forms not listed in a group (`rep ret`, and the base forms the groups do not
cover, such as `cmpxchg`-style or system forms the decoder does not have) are unspecified.

Lean reserves `Σ`, so the name is `Sv1`.
-/

@[expose] public section

namespace Silmaril.X86.Loose

/-- **The integer forms of `Σ v1`**: `Ctl`, then `MulDiv`, then `Int`. -/
def intSpec (i : Silmaril.X86.Ext9.Instr) : Option EffSpec :=
  (Ctl.ctlSpec i).or ((Forms.MulDiv.specOf i).or (Forms.spec9 i))

/-- The effect form of each form of `Σ v1`. -/
def sv1Eff : Silmaril.X86.Str9.Instr → Option EffSpec
  | .ext9 i => intSpec i
  | .str i => some (Forms.Str.strSpec i)

/-- **`Σ v1`**: the integer forms and the string forms. -/
def Sv1 : Sigma Silmaril.X86.Str9.Instr := fun i => (sv1Eff i).map EffSpec.toFormSpec

end Silmaril.X86.Loose
