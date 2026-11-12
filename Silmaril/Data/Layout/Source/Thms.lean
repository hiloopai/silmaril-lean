module

public import Silmaril.Data.Layout.Source.Defs
import Silmaril.Proofs.Data.Layout.Source

/-!
# The record-source parser is sound

PROVED in `Silmaril.Proofs.Data.Layout.Source`: every grammar function of the parser is sound
for the grammar relation of the same name (`parseSpec` for `Spec`, …, `parseUnit` for
`TransUnit`), so a successful `parse` is a derivation of `Parses`.

Not claimed: completeness (the converse, that every derivation is found, is not proved; the
parser commits to the longest scalar spelling), or any relation to the C standard's grammar
beyond the subset written down in `Defs`.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Source

/-- A successful parse derives the parsing relation. -/
theorem parse_sound {src : String} {env : Layout.Env} (h : parse src = .ok env) :
    Parses src env :=
  Silmaril.Proofs.Data.Layout.Source.parse_sound h

/-- The certificate form used by `c_layout`: the parser's result, as an `Option`, is `env`. -/
theorem parses_of_toOption {src : String} {env : Layout.Env}
    (h : (parse src).toOption = some env) : Parses src env := by
  apply parse_sound
  cases hp : parse src <;> simp_all [Except.toOption]

end Silmaril.Data.Layout.Source
