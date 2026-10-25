module

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

def usage : String :=
  "usage: binaryen-tools-lean link-gc NAMESPACE PROVIDER.wasm CONSUMER.wasm -o OUT.wasm\n" ++
  "  two modules; import-free provider; function imports; no memories, tables, tags, segments or starts\n" ++
  "       binaryen-tools-lean shell FUEL MODULE.wasm EXPORT [I32_ARGUMENT ...]\n" ++
  "  no imports; explicit step budget per initialization/invocation; deterministic numeric/growth profile\n" ++
  "       binaryen-tools-lean as IN.wat -o OUT.wasm\n" ++
  "       binaryen-tools-lean dis IN.wasm -o OUT.wat\n" ++
  "  certified canonical integer/function WAT fragment; unsupported features reject"

end Silmaril.Wasm.Binaryen.Toolkit
