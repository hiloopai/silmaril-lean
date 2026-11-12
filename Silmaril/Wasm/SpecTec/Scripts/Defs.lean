module

public import Silmaril.Raw.Wasm.SpecTec.Scripts
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm20
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Env

/-!
# SpecTec scripts: the pinned originals and their fixed versions, by name

One stable name per script that the rest of the development states theorems about:

* `Scripts.Wasm10.original`, `Scripts.Wasm20.original`, `Scripts.Wasm30.original` — the three
  elaborated `--ast` streams of `WebAssembly/spec@608711107b`;
* `Scripts.Wasm10.fixed`, `Scripts.Wasm20.fixed` — the same with the errata of
  `Errata/Wasm10.lean` and `Errata/Wasm20.lean` applied;
* `Scripts.Wasm30.binary51` (binary §5.1 errata #654–#656), `Scripts.Wasm30.text6x` (text §6.x
  errata), and `Scripts.Wasm30.fixed`, both sets together (`fixedErrata`);
* `env*` — each script's lookup environment `Sem.envOfScript`.

**Where the terms come from.**  Each script is explicit Lean source written by
`tools/spectec-gen` under `Silmaril.Raw.Wasm.SpecTec.Scripts` (one `def` per top-level definition;
a fixed script shares every unchanged definition with its original).  The generator reads the
vendored streams and the textual `spectec_erratum` commands of `Errata/*.lean`; CI re-runs it with
`check`.  `Silmaril.Wasm.SpecTec.Scripts.Thms` proves, in the kernel, that every one of these terms
equals the value the elaboration-time importer (`spectec_import`) and the errata commands
(`spectec_erratum`) produce, and that `applyErrata fixedErrata original = some fixed`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Scripts

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod

namespace Wasm10

/-- The pinned wasm-1.0 script. -/
noncomputable abbrev original : Script := Wasm10.Original.script

/-- The wasm-1.0 script with the errata of `Errata/Wasm10.lean` applied. -/
noncomputable abbrev fixed : Script := Wasm10.Fixed.script

/-- The errata taking `original` to `fixed`. -/
noncomputable abbrev fixedErrata : List Erratum := IL.Wasm10.wasm10errata

/-- Lookup environment of `original`. -/
noncomputable abbrev envOriginal : Sem.Env := Sem.envOfScript original

/-- Lookup environment of `fixed`. -/
noncomputable abbrev envFixed : Sem.Env := Sem.envOfScript fixed

end Wasm10

namespace Wasm20

/-- The pinned wasm-2.0 script. -/
noncomputable abbrev original : Script := Wasm20.Original.script

/-- The wasm-2.0 script with the errata of `Errata/Wasm20.lean` applied. -/
noncomputable abbrev fixed : Script := Wasm20.Fixed.script

/-- The errata taking `original` to `fixed`. -/
noncomputable abbrev fixedErrata : List Erratum := IL.Wasm20.wasm20errata

/-- Lookup environment of `original`. -/
noncomputable abbrev envOriginal : Sem.Env := Sem.envOfScript original

/-- Lookup environment of `fixed`. -/
noncomputable abbrev envFixed : Sem.Env := Sem.envOfScript fixed

end Wasm20

namespace Wasm30

/-- The pinned wasm-3.0 script. -/
noncomputable abbrev original : Script := Wasm30.Original.script

/-- The wasm-3.0 script with the binary §5.1 errata (#654, #655, #656) applied. -/
noncomputable abbrev binary51 : Script := Wasm30.Binary51.script

/-- The wasm-3.0 script with the text §6.x errata applied. -/
noncomputable abbrev text6x : Script := Wasm30.Text6x.script

/-- Both sets of wasm-3.0 errata, binary §5.1 then text §6.x, written out as the thirteen
patch constants (`fixedErrata_eq` says it is `binary51 ++ text6x`). -/
noncomputable def fixedErrata : List Erratum :=
  [IL.Binary51.wasm30.erratum654Bi32, IL.Binary51.wasm30.erratum654Bi64,
    IL.Binary51.wasm30.erratum655, IL.Binary51.wasm30.erratum656,
    IL.Text6x.wasm30.erratum661, IL.Text6x.wasm30.erratum662Tfloat,
    IL.Text6x.wasm30.erratum662Thexfloat, IL.Text6x.wasm30.erratum663,
    IL.Text6x.wasm30.erratum664, IL.Text6x.wasm30.erratum665Tblockcomment,
    IL.Text6x.wasm30.erratum665Tblockchar, IL.Text6x.wasm30.erratum692,
    IL.Text6x.wasm30.erratum694]

/-- The thirteen wasm-3.0 patches, as one function on top-level definitions. -/
noncomputable def fixedPatch (d : Def) : Def :=
  IL.Text6x.text6xPatch (IL.Binary51.binary51Patch d)

/-- The wasm-3.0 script with both sets of errata applied, binary §5.1 then text §6.x. -/
noncomputable abbrev fixed : Script := Wasm30.Fixed.script

/-- Lookup environment of `original`. -/
noncomputable abbrev envOriginal : Sem.Env := Sem.envOfScript original

/-- Lookup environment of `binary51`. -/
noncomputable abbrev envBinary51 : Sem.Env := Sem.envOfScript binary51

/-- Lookup environment of `text6x`. -/
noncomputable abbrev envText6x : Sem.Env := Sem.envOfScript text6x

/-- Lookup environment of `fixed`. -/
noncomputable abbrev envFixed : Sem.Env := Sem.envOfScript fixed

end Wasm30

end Silmaril.Wasm.SpecTec.Scripts
