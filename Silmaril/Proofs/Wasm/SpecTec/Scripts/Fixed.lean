module

public import Silmaril.Raw.Wasm.SpecTec.Scripts
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm20
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm20

/-!
# The generated fixed scripts are the errata commands' results

`tools/spectec-gen` reads the `spectec_erratum` commands of `Errata/*.lean` as text, applies
them to the S-expressions, and emits only the definitions that change; the Lean commands apply
the same edits in the elaborator and splice them with `IL.replaceDefs`.  The kernel checks the
generated scripts equal those splices (it computes each `replaceDefs` chain).
-/

public section

namespace Silmaril.Wasm.SpecTec.Scripts

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod

set_option maxRecDepth 100000

theorem generated_wasm10_fixed_eq : Wasm10.Fixed.script = IL.Wasm10.wasm10corrected := by rfl

theorem generated_wasm20_fixed_eq : Wasm20.Fixed.script = IL.Wasm20.wasm20corrected := by rfl

theorem generated_wasm30_binary51_eq :
    Wasm30.Binary51.script = IL.Binary51.wasm30binary51 := by rfl

theorem generated_wasm30_text6x_eq : Wasm30.Text6x.script = IL.Text6x.wasm30text6x := by rfl

/-- The combined wasm-3.0 script is the text §6.x splices on top of the binary §5.1 ones. -/
theorem generated_wasm30_fixed_eq :
    Wasm30.Fixed.script =
      replaceDefs IL.Text6x.wasm30.erratum694.corrected
        (replaceDefs IL.Text6x.wasm30.erratum692.corrected
          (replaceDefs IL.Text6x.wasm30.erratum665Tblockchar.corrected
            (replaceDefs IL.Text6x.wasm30.erratum665Tblockcomment.corrected
              (replaceDefs IL.Text6x.wasm30.erratum664.corrected
                (replaceDefs IL.Text6x.wasm30.erratum663.corrected
                  (replaceDefs IL.Text6x.wasm30.erratum662Thexfloat.corrected
                    (replaceDefs IL.Text6x.wasm30.erratum662Tfloat.corrected
                      (replaceDefs IL.Text6x.wasm30.erratum661.corrected
                        IL.Binary51.wasm30binary51)))))))) := by
  rfl

end Silmaril.Wasm.SpecTec.Scripts
