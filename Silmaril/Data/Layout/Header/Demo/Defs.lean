module

public import Silmaril.Data.Layout.Header.Defs
public import Silmaril.Data.Layout.Bitfield.Defs

/-!
# The layout demo header (`examples/headers/layout/demo.h`), as a constant

The explorer's Headers tab shows `demo.h`'s aggregates under System V x86-64 and Microsoft x64
(`tools/header-pages`). This module holds the header's text (`demoH`), what the subset reader
reads from it (`demoEnv`) and the layout queries the tab's theorems state (`layoutOf`,
`paddingOf`); `Header.Demo.Thms` evaluates them in the kernel for every aggregate and both data
models. `header-pages` computes the page from this same constant and links a layout to its
theorem only after checking the theorem's statement exactly.

SHA-256 of the file (which `examples/headers/recipe.sh --check` compares with the file, since
Lake does not track `include_str`):

* `examples/headers/layout/demo.h`:
  `2a6fa9bb1aef9c86d6b965a3f0fa124a621895e2a14f1e343657f786ef42905d`
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Demo

open Silmaril.Data.Layout

/-- `examples/headers/layout/demo.h`. -/
def demoH : String :=
  include_str "../../../../../examples/headers/layout/demo.h"

/-- The files of `demo.h`, as the subset reader takes them. -/
def demoFiles : List (String × String) := [("demo.h", demoH)]

/-- The tag definitions `demo.h` reads to (empty if the reader refused it; `Thms` shows it
does not). -/
def demoEnv : Env := ((read demoFiles "demo.h").toOption.map Header.env).getD []

/-- **The bit-level layout of the tag `kind tag`** in `env`, under a bit-field policy and data
model (`bitLayout`): its slots and shape, or `none` when the tag is not defined or the layout is
refused. -/
def layoutOf (pol : BitPolicy) (dm : DataModel) (env : Env) (kind : Kind) (tag : String) :
    Option (List BitSlot × Shape) :=
  (env.find? kind tag).bind fun d => (bitLayout pol dm env d).toOption

/-- The library's padding counts of that layout: `(paddingBytes, paddingBits)`. -/
def paddingOf (pol : BitPolicy) (dm : DataModel) (env : Env) (kind : Kind) (tag : String) :
    Option (Nat × Nat) :=
  (layoutOf pol dm env kind tag).map fun (ss, sh) => (paddingBytes ss sh, paddingBits ss sh)

end Silmaril.Data.Layout.Header.Demo

end
