module

public import Silmaril.Wasm.Text.Extensions.LegacyExceptions.Render
public import Silmaril.Wasm.Text.Extensions.LegacyExceptions.RenderInstructionsSound
public import Silmaril.Wasm.Text.Extensions.Structured.RenderFunctionsSound
public import Silmaril.Wasm.Text.Extensions.Structured.RenderSound

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.LegacyExceptions

open Silmaril Silmaril.Formats.SExpEncoding

theorem functionSyntax?_sound {I : Core.IdCtx} {f : Wasm.Extensions.LegacyExceptions.Func} {x : SExp}
    (h : functionSyntax? I f = some x) : FuncT I x f :=
  Structured.functionSyntax?_sound leafSyntax? (fun _ _ _ h => leafSyntax?_sound h) h

theorem moduleSyntax?_sound {m : Wasm.Extensions.LegacyExceptions.Module} {x : SExp}
    (h : moduleSyntax? m = some x) : ModuleT x m :=
  Structured.moduleSyntax?_sound functionSyntax? FuncT (fun _ _ _ h => functionSyntax?_sound h) _ h

end Silmaril.Wasm.Text.Extensions.LegacyExceptions
