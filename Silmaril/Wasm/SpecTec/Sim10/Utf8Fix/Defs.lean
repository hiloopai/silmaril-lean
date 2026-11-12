module

public import Silmaril.Wasm.SpecTec.Sim10.StoreFix.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Utf8.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.Defs

/-!
# The `$utf8` erratum for wasm-1.0, as a fixed script (round 8)

Round 7 proved that the 1.0 `$utf8` runs out of fuel on every non-empty list, so no non-empty
string is a 1.0 `name` and no configuration over a store with a non-empty export name is typed
(`Sim10.Name10.typedV_name10_iff`, `not_typed10_export_ne`). This is the 1.0 form of the defect
that round 6 repaired for 2.0 (`Sim20.StoreBulk.utf8Env20`) and round 7 for 3.0
(`Round7.utf8Env`). Those repairs rebind `$utf8` in the environment. Here the repair is a
**script**: one more corrected definition on top of the `STORE` errata, so that the 1.0 erratum
is a theory morphism of the SpecTec institution like the others.

* `utf8Decl10`: `$utf8` with the signature of the 1.0 script (`Round7.utf8Params`,
  `Round7.utf8Res`) and **no clauses**, as a `hint(builtin)` declaration is.
* `utf8Erratum10`: the erratum record (`issue := 0`: no upstream issue is filed).
* `fixedU10`: `StoreFix.fixedT10` with every declaration of `$utf8` replaced by `utf8Decl10`.
* `utf8Env10T B`: the environment of `fixedU10` with the primitives `Round6.MemSimd.withUtf8 B`,
  which answer `$utf8` by the UTF-8 encoding of the characters and defer to `B` elsewhere.

Like the `STORE` errata, it is a Lean-level erratum, not a `spectec_erratum` command, so the
widely imported `Raw` script modules are untouched.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Fix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7 (utf8Params utf8Res)
open Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd (withUtf8)

/-- **The corrected `$utf8`**: same parameters and result type, no clauses. -/
def utf8Decl10 : Def := .decD "utf8" utf8Params utf8Res []

/-- **The erratum on `$utf8`.** -/
def utf8Erratum10 : Erratum where
  issue := 0
  summary := "$utf8 (wasm-1.0): the one-character clauses bind their byte variables only in \
    premises, and the last clause recurses on a one-character list, so $utf8 never evaluates \
    on a non-empty list; declare it as a builtin"
  target := "utf8"
  corrected := utf8Decl10

/-- The wasm-1.0 script with the `STORE` errata and the `$utf8` erratum. -/
noncomputable def fixedU10 : Script := replaceDefs utf8Decl10 StoreFix.fixedT10

/-- **The 1.0 environment with both errata**: `$utf8` answered by the UTF-8 encoding of its
characters, every other primitive by `B`. -/
noncomputable def utf8Env10T (B : Builtins) : Env := (envOfScript fixedU10).withBuiltins (withUtf8 B)

end Silmaril.Wasm.SpecTec.Sim10.Utf8Fix
