module

public import Silmaril.Compiler.Core.Spec.Defs
public import Silmaril.Compiler.Core.Verified.Fragments.Defs
public import Silmaril.Compiler.Core.Verified.WideConst.Defs
/-! # The verified Core compiler

`compile` translates a decoded Cerberus Core document to an x86-64 `Spec.Artifact`, or
returns `none` for a program outside the proved fragment. `compile_sound` proves
`Spec.SoundSpec compile` (`Silmaril/Compile/Core/Spec.lean`, the frozen statement): every
behaviour of the loaded machine code is allowed by the Core program.

`ccomp-verified FILE.c` runs exactly this function (driver
`Silmaril/Compile/Core/Main.lean`); `none` is reported as "outside the verified fragment"
and nothing is linked.

## Structure

`compile` is `Fragment.first Fragments.fragments` behind the spec-trust restriction
`WideConst.restrict` (documents with wide or Unicode character constants, which the C-to-Core
export decodes as signed 8-bit chars, are rejected: `Verified/WideConst.lean`), and
`compile_sound` is `Fragment.first_sound` through `WideConst.restrict_sound`:
each proved construct is a `Fragment` (`Verified/Fragment.lean`), a partial compiler with the
proof of what it produces, in its own file under `Verified/Fragments/`, listed in
`Verified/Fragments.lean`. A new construct adds a file and a list entry; this file does not
change.

## Scope

The accepted fragment, the trusted base and the restrictions are described in
`docs/projects/cerberus.md`. The back end shared by every fragment is proved once:
`Backend.artifactOf_sound` (`Verified/Backend.lean`) says every observation of
`Backend.artifactOf l` is exhaustion, a stuck Lir run of `__ccomp_start`, or crt0's
observation of a Lir behaviour of that run, so a fragment's proof only needs Core and Lir
facts.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified

open Silmaril.Cerberus
open Spec

/-- The verified compiler: the first proved fragment that accepts the document, for documents
without wide character constants (`WideConst.restrict`). -/
def compile (doc : Codec.Document) : Option Artifact :=
  WideConst.restrict (Fragment.first Fragments.fragments) doc

/-- **Soundness**: the frozen statement `Spec.SoundSpec` for `compile`. -/
theorem compile_sound : SoundSpec compile :=
  WideConst.restrict_sound (Fragment.first_sound Fragments.fragments)

end Silmaril.Compile.Core.Verified
