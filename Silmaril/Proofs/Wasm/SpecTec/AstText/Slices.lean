module

public import Silmaril.Proofs.Wasm.SpecTec.AstText.Check
public import Silmaril.Proofs.Wasm.SpecTec.AstText.Compose
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# Kernel certificates on literal text of `wasm-3.0.ast`

Two slices of `specs/spectec/wasm-3.0.ast`, copied by hand as string literals (track GEN will
emit them as `Scripts.Wasm30.AstSlices`); `spectec_check_slice` confirms at build time that each
literal is exactly the cited line range of the vendored file.

* `prefix5`, lines 1-26: definitions 0 to 4 (`N`, `K`, `n`, `m`, `$min`);
* `bi32`, lines 47339-47347: definition 756, the grammar `Bi32`.

For these the kernel itself runs the verified lexer on the text (`by rfl`), so the S-expressions
are not trusted (`decide +kernel`, a few seconds). The decoding step is *not* reduced in the kernel (that is unaffordable even for
one definition, see `Import.lean`); it is the general theorem `IL.decodeScript?_scriptS`.

The literals are explicit character lists (`spectec_chars%`): reducing `String.toList` of a
UTF-8 string literal in the kernel is what makes `lex? s.toList` exponential
(`SExp/ParseVerified.lean`), and `String.toList_ofList` removes it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.AstText

open Silmaril.SpecTec
open Silmaril.SpecTec.SExp (parseStream?)

set_option maxRecDepth 100000

/-- `specs/spectec/wasm-3.0.ast` lines 1-26. -/
def prefix5Chars : List Char := spectec_chars% "(typ \"N\" (inst (alias nat)))
(typ \"K\" (inst (alias nat)))
(typ \"n\" (inst (alias nat)))
(typ \"m\" (inst (alias nat)))
(def
  \"min\"
  (exp \"nat\" nat)
  (exp \"nat\" nat)
  nat
  (clause
    (exp \"i\" nat)
    (exp \"j\" nat)
    (exp (var \"i\"))
    (exp (var \"j\"))
    (var \"i\")
    (if (cmp le nat (var \"i\") (var \"j\")))
  )
  (clause
    (exp \"i\" nat)
    (exp \"j\" nat)
    (exp (var \"i\"))
    (exp (var \"j\"))
    (var \"j\")
    else
  )
)
"

spectec_check_slice prefix5Chars against "specs/spectec/wasm-3.0.ast" lines 1 26

/-- The first five definitions of `wasm-3.0.ast`, as text. -/
def prefix5 : String := String.ofList prefix5Chars

/-- `specs/spectec/wasm-3.0.ast` lines 47339-47347. -/
def bi32Chars : List Char := spectec_chars% "(gram
  \"Bi32\"
  (var \"i32\")
  (prod
    (exp \"<implicit-prod-result>\" (var \"uN\" (exp (num (nat 32)))))
    (attr (var \"<implicit-prod-result>\") (var \"BuN\" (exp (num (nat 32)))))
    (var \"<implicit-prod-result>\")
  )
)
"

spectec_check_slice bi32Chars against "specs/spectec/wasm-3.0.ast" lines 47339 47347

/-- The definition of the grammar `Bi32` in `wasm-3.0.ast`, as text. -/
def bi32 : String := String.ofList bi32Chars

/-- The kernel lexes the first 26 lines of `wasm-3.0.ast` to the printed form of the pinned
script's first five definitions. -/
theorem parse_prefix5 : parseStream? prefix5 = some (IL.scriptS (Specs.wasm30.take 5)) := by
  rw [prefix5, parseStream?, String.toList_ofList]
  decide +kernel

theorem import_prefix5 : importAstText? prefix5 = some (Specs.wasm30.take 5) :=
  importAstText?_eq_some_iff.mpr ⟨_, parse_prefix5, IL.decodeScript?_scriptS _⟩

theorem astTextRel_prefix5 : AstTextRel prefix5 (Specs.wasm30.take 5) :=
  importAstText?_sound _ _ import_prefix5

/-- The kernel lexes the `Bi32` text to the printed form of definition 756 of the pinned
script. -/
theorem parse_bi32 :
    parseStream? bi32 = some (IL.scriptS ((Specs.wasm30.drop 756).take 1)) := by
  rw [bi32, parseStream?, String.toList_ofList]
  decide +kernel

theorem import_bi32 : importAstText? bi32 = some ((Specs.wasm30.drop 756).take 1) :=
  importAstText?_eq_some_iff.mpr ⟨_, parse_bi32, IL.decodeScript?_scriptS _⟩

theorem astTextRel_bi32 : AstTextRel bi32 ((Specs.wasm30.drop 756).take 1) :=
  importAstText?_sound _ _ import_bi32

end Silmaril.Wasm.SpecTec.AstText
