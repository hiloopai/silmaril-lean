module

public import Silmaril.Wasm.Binaryen.Toolkit.WatParse
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntaxSound

@[expose] public section

/-! Canonical parser acceptance carries the existing Core text grammar
certificate through exact syntax reification. -/

namespace Silmaril.Wasm.Binaryen.Toolkit.Wat

theorem parseCanonical?_sound {x : Text.SExp} {m : Wasm.Module}
    (h : parseCanonical? x = some m) : Text.Core.ModuleT x m :=
  moduleSyntax?_sound (parseCanonical?_reifies h)

end Silmaril.Wasm.Binaryen.Toolkit.Wat
