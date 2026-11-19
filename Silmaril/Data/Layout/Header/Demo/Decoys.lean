module

public import Silmaril.Data.Layout.Header.Demo.Defs
public import Silmaril.Data.Layout.Header.Thms

/-! # Decoy layout theorems for the Headers tab's link checker (test fixtures)

True statements that **mention** `layoutOf`, a data model, a tag or `demoEnv` without being the
statement a table of `demo.h` needs. The explorer's link checker (`tools/header-pages`,
`header-pages --self-test`) must refuse every link built on them; they are not results.
`rec_other_env` is the decoy loose matching would accept: the same `struct rec` text and the
same slots and shape, but read from another header text (`Header.recH`), so not a theorem about
`demo.h`. -/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Demo.Decoys

open Silmaril.Data.Layout

/-- `rec` read from `Header.recH`, not from `demo.h`: the same layout, another environment. -/
theorem rec_other_env :
    layoutOf .sysv sysvX86_64 Header.recEnv .struct "rec" =
      some ([⟨"c", 0, 8⟩, ⟨"flags", 8, 3⟩, ⟨"mode", 11, 5⟩, ⟨"n", 64, 64⟩, ⟨"x", 128, 32⟩,
        ⟨"d", 192, 64⟩], ⟨32, 8⟩) := by decide +kernel

/-- `pt` read from `Header.ptH` (another `struct pt`). -/
theorem pt_other_env :
    layoutOf .sysv sysvX86_64 Header.ptEnv .struct "pt" =
      some ([⟨"tag", 0, 8⟩, ⟨"v", 64, 64⟩, ⟨"s", 128, 48⟩, ⟨"u", 192, 64⟩], ⟨32, 8⟩) := by
  decide +kernel

/-- A tautology about the right constants. -/
theorem rec_refl :
    layoutOf .sysv sysvX86_64 demoEnv .struct "rec" =
      layoutOf .sysv sysvX86_64 demoEnv .struct "rec" := rfl

/-- The right equation under a disjunction. -/
theorem rec_or_true :
    True ∨ layoutOf .sysv sysvX86_64 demoEnv .struct "rec" =
      some ([⟨"c", 0, 8⟩, ⟨"flags", 8, 3⟩, ⟨"mode", 11, 5⟩, ⟨"n", 64, 64⟩, ⟨"x", 128, 32⟩,
        ⟨"d", 192, 64⟩], ⟨32, 8⟩) := .inl trivial

/-- The right equation, flipped. -/
theorem rec_flipped :
    some ([⟨"c", 0, 8⟩, ⟨"flags", 8, 3⟩, ⟨"mode", 11, 5⟩, ⟨"n", 64, 64⟩, ⟨"x", 128, 32⟩,
        ⟨"d", 192, 64⟩], ⟨32, 8⟩) = layoutOf .sysv sysvX86_64 demoEnv .struct "rec" := by
  decide +kernel

/-- A right-hand side that is not a literal (another definition with the same value). -/
theorem rec_rhs_not_literal :
    layoutOf .sysv sysvX86_64 demoEnv .struct "rec" = Header.recLayout .sysv sysvX86_64 := by
  decide +kernel

/-- The Microsoft bit-field policy with the System V data model: neither table's pair. -/
theorem rec_mixed_model :
    layoutOf .ms sysvX86_64 demoEnv .struct "rec" =
      some ([⟨"c", 0, 8⟩, ⟨"flags", 32, 3⟩, ⟨"mode", 35, 5⟩, ⟨"n", 64, 64⟩, ⟨"x", 128, 32⟩,
        ⟨"d", 192, 64⟩], ⟨32, 8⟩) := by decide +kernel

/-- `word` is a union: there is no `struct word`. -/
theorem word_as_struct : layoutOf .sysv sysvX86_64 demoEnv .struct "word" = none := by
  decide +kernel

end Silmaril.Data.Layout.Header.Demo.Decoys

end
