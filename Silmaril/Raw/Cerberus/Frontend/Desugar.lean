module

public import Silmaril.Cerberus.Frontend.Desugar.Knot.Defs

/-! # The Cerberus C frontend: desugaring Cabs to Ail

`desugar` is what `cerb-lean parse --level ail` runs after `Frontend.parse`: a port of
Cerberus's `Cabs_to_ail.desugar` (`frontend/model/cabs_to_ail.lem:4948-5033`, with
`cabs_to_ail_effect.lem` and `cabs_to_ail_aux.lem`) at `b3e11ea3`, under the oracle's
configuration (implementation `gcc_4.9.0_x86_64-apple-darwin10.8.0`, bit-fields not ignored,
no CN magic comments). It returns untyped Ail, `Ail.Program Unit`, or the `Errors.error`
that Cerberus reports, at the stage `desugar`.

`digest` is the MD5 of the input `.i` file (`Ail.fileDigest`), the digest of every symbol
the desugaring creates. Fresh numbers (symbols, loop ids, markers) may come from any
increasing counter: the driver replaces them by their ranks (`Ail.Canonical`), so only
their relative order must be Cerberus's.

The port follows Lem's modules: `Desugar.Effect` (the state, the monad, scopes and the
registration of identifiers, `extract_program`), `Desugar.Auxiliary`
(`cabs_to_ail_aux.lem`), `Desugar.ScopeTable`, `Desugar.Errors` (causes and their short
messages), and the recursive group of `cabs_to_ail.lem` split over `Desugar.Specifiers`,
`Desugar.Declarators` and `Desugar.External`, tied by `Desugar.knot`. A construct that is
not ported yet rejects with a `Silmaril: not ported` message, which no oracle output
carries.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend

open Silmaril.Cerberus

/-- Desugar a Cabs translation unit into untyped Ail, or reject it at the stage `desugar`.
`Cabs_to_ail.desugar` (`cabs_to_ail.lem:4948-5033`): under the file scope, every external
declaration in order, then `extract_program "main"`. Without magic comments there are no
CN declarations, so registering their names first does nothing. -/
def desugar (digest : Digest) (unit : Cabs.TranslationUnit) : Except Ail.Reject (Ail.Program Unit) :=
  Desugar.eval digest <| Desugar.underScope .file do
    unit.declarations.forM (Desugar.desugarAndRegisterExternalDeclaration (Desugar.knot Desugar.depth))
    Desugar.extractProgram "main"

end Silmaril.Cerberus.Frontend
