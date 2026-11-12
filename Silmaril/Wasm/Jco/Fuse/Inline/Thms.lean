module

public import Silmaril.Wasm.Jco.Fuse.Inline.Defs
public import Silmaril.Wasm.Jco.Fuse.Thms
import Silmaril.Proofs.Wasm.Jco.Fuse.Inline

/-!
# Fusion of glue modules is inlining

With glue modules as base modules (`glueSem`), the semantic fusion of
`fuseSem` is realised by the code transformation `Glue.inline`:

* `fused_glue`: `(fuseSem glueSem).sem (.fused g₁ g₂)` equals
  `(fuseSem glueSem).sem (.glue (Glue.inline g₁ g₂))`, provided `g₂` imports
  at most `g₁`'s exports and `g₁` has at most as many bodies as `g₂` imports
  and as it exports (otherwise the masks of the linked form trap on calls
  that the inlined code would serve);
* `inlined_adaptor`: the component with one instance of the inlined glue
  module denotes as the adaptor-style component (with `wrapper_adaptor`).

The proof (`Silmaril.Proofs.Wasm.Jco.Fuse.Inline`) collapses the environment
strategies of `inner g₁ g₂` to handlers (pairing law `cp`), computes the
right projection at the handler level, and ends with `glueH_inline`.
-/

public section

namespace Silmaril.Wasm.Jco.Fuse

open Silmaril.Games
open Silmaril.Wasm.Component

/-- **A fused glue module is its inlining.** -/
theorem fused_glue (g₁ g₂ : Glue) (hg : g₂.imports.length ≤ g₁.exports.length)
    (hk : g₁.code.length ≤ g₂.imports.length) (hc : g₁.code.length ≤ g₁.exports.length) :
    (fuseSem glueSem).sem (.fused g₁ g₂) = (fuseSem glueSem).sem (.glue (Glue.inline g₁ g₂)) :=
  Silmaril.Proofs.Wasm.Jco.Fuse.fused_glue_handler g₁ g₂ hg hk hc

/-- **Fusion by inlining is correct.** -/
theorem inlined_adaptor (I W : Iface) (g₁ g₂ : Glue) (args : List Impl)
    (hlen : args.length = g₁.imports.length) (hsc : ScopedList I.length args)
    (hg : g₂.imports.length ≤ g₁.exports.length) (hW : W.length ≤ g₂.exports.length)
    (hk : g₁.code.length ≤ g₂.imports.length) (hc : g₁.code.length ≤ g₁.exports.length) :
    (Comp.mk I [.core (.glue (Glue.inline g₁ g₂)) args] (liftExports W I.length)).denU
        (fuseSem glueSem) =
      (adaptorComp I W g₁ g₂ args).denU (baseSem glueSem) :=
  Silmaril.Proofs.Wasm.Jco.Fuse.inlined_adaptor I W g₁ g₂ args hlen hsc hg hW hk hc

end Silmaril.Wasm.Jco.Fuse
