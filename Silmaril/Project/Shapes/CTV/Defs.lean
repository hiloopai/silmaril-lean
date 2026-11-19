module

public import Silmaril.Project.Defs
public import Silmaril.Cerberus.TV.Validate.Defs
public import Silmaril.Cerberus.TV.Provenance.Defs
public import Silmaril.Cerberus.TV.Applicability.Defs
public import Silmaril.Cerberus.TV.Compose.Defs
public import Silmaril.Compiler.Native.TargetCoherence.Defs

/-!
# Standard problem shapes: whole-program C translation validation

The whole-program edges of C translation validation (docs/projects/c-tv.md), stated over the
Cerberus Core semantics (`Silmaril.Cerberus.TV.Behaviour`), and the coherence of a target
profile with that semantics (`Silmaril.Cerberus.TV.Profile`).

| name | statement |
|---|---|
| `silmaril.shapes.c.tv.refines` | `Refines impl src tgt`: every observation of `tgt` is one of `src`, `tgt` reaches no gap or stuck state, and `tgt` has no infinite run |
| `silmaril.shapes.c.tv.refines_ub_free` | `RefinesUBFree impl src tgt`: `Refines`, and no ending of `src` is undefined behaviour, so no target observation is admitted only through source UB |
| `silmaril.shapes.c.tv.not_refines` | `¬ Refines impl src tgt` |
| `silmaril.shapes.c.tv.equivalent` | `Equivalent impl P Q`: refinement both ways |
| `silmaril.shapes.c.tv.profile_coherent_at` | `p.CoherentAt s`: the Core semantics, the elaborator configuration and the target profile agree on the scalar type `s` (storage, alignment, signedness, value range, endianness, numeric format) |
| `silmaril.shapes.c.tv.profile_applies` | `p.AppliesTo b`: the per-type check passes: every type named by the program part of `b`, the runtime functions and the implementation constants it reaches (by name, a superset of what runs) is in the coherence table and coherent (`TV.Applicability`); a necessary filter |
| `silmaril.shapes.c.tv.context_refines` | `FunctionRefines impl ctxs f before after`: the listed contexts are not empty, each defines `f` in its own functions and not in its runtime (`Substitutes`: `f` is replaced, not necessarily called), and in each the program with `f := after` refines the one with `f := before` (function level, over the listed contexts only: not contextual refinement; `TV.Compose`) |
| `silmaril.shapes.c.tv.refines_on` | `RefinesOn p src tgt`: Core refinement with `p`'s `Spec.Impl` choices, and the per-type check passes on both programs; not a statement about the target |

**Every one of these relates Cores, or a Core and a profile.** They are about closed programs (no
input beyond the command-line arguments) and about the Lean port's semantics. None says that a
compiler's output implements C: that compiler-origin relation is `c.compiles_to*` (a placed
machine function and a C function's Core) and the roadmap, and nothing here implies it. When the
two Cores come from two frontends (the corpus's Clang and Cerberus routes), a `refines` row is a
frontend agreement. A Core row describes x86-64 Linux C only through a `profile_applies` row,
which is per type and is necessary, not sufficient: `refines` alone claims nothing about any real
target. Statements about functions in contexts, external calls and divergence are other shapes
(`c.elaborates_to`, `c.compiles_to*`, and the roadmap).

## Profiles

* `linuxX86_64`: x86-64 Linux, System V psABI data model (`Data.Layout.sysvX86_64`), the formats
  binary32, binary64 and x87 extended (80 value bits in 16 bytes), C11, and the elaborator
  configuration `TargetCoherence.linuxLP64`.
* `legacyPinnedApple`: the same data model with upstream's pinned elaborator configuration
  `Target.pinnedApple`, whose every floating layout is 8/8; it is kept to show that it is not
  coherent at `float` and `long double`, not as a target to validate against.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.CTV

open Silmaril.Cerberus
open Silmaril.Cerberus.TV

/-- x86-64 Linux under the System V psABI, C11 (module docstring). -/
def linuxX86_64 : Profile where
  name := "x86_64-linux-gnu (System V LP64), C11"
  language := ⟨.c11, false⟩
  dataModel := Silmaril.Data.Layout.sysvX86_64
  floatFormat
    | .float => some .binary32
    | .double => some .binary64
    | .longDouble => some .x87
    | .float128 => some .binary128
  elaborator := Silmaril.Compiler.Native.TargetCoherence.linuxLP64
  impl := Spec.Impl.lp64

/-- Upstream's pinned elaborator configuration against the System V data model. -/
def legacyPinnedApple : Profile :=
  { linuxX86_64 with
    name := "legacy: Target.pinnedApple elaborator, System V data model"
    elaborator := Target.pinnedApple }

/-- **Whole-program refinement** of closed Core programs. -/
@[problem "silmaril.shapes.c.tv.refines"
  (title := "A closed C program's Core refines another's (terminating, supported, observational)")]
def CRefines (impl : Spec.Impl) (src tgt : Closed) : Prop :=
  Refines impl src tgt

/-- **Refinement of a UB-free source**: the row cannot rest on source undefined behaviour. -/
@[problem "silmaril.shapes.c.tv.refines_ub_free"
  (title := "A closed C program's Core refines another's, which has no undefined behaviour")]
def CRefinesUBFree (impl : Spec.Impl) (src tgt : Closed) : Prop :=
  RefinesUBFree impl src tgt

/-- **Non-refinement**: negative evidence. -/
@[problem "silmaril.shapes.c.tv.not_refines"
  (title := "A closed C program's Core does not refine another's")]
def CNotRefines (impl : Spec.Impl) (src tgt : Closed) : Prop :=
  ¬ Refines impl src tgt

/-- **Whole-program equivalence** of closed Core programs. -/
@[problem "silmaril.shapes.c.tv.equivalent"
  (title := "Two closed C programs' Cores are equivalent (terminating, supported, observational)")]
def CEquivalent (impl : Spec.Impl) (P Q : Closed) : Prop :=
  TV.Equivalent impl P Q

/-- **Profile coherence at a scalar type.** -/
@[problem "silmaril.shapes.c.tv.profile_coherent_at"
  (title := "The Core semantics and a target profile agree on a scalar type")]
def ProfileCoherentAt (p : Profile) (s : Scalar) : Prop :=
  p.CoherentAt s

/-- **A profile applies to a program** (per type: `TV.Profile.AppliesTo`). -/
@[problem "silmaril.shapes.c.tv.profile_applies"
  (title := "The per-type profile check passes: every type the program's reachable Core names (program part, runtime functions and implementation constants reachable by name) is coherent")]
def ProfileApplies (p : Profile) (b : Codec.FileBindings) : Prop :=
  p.AppliesTo b

/-- **Refinement on a target profile** (`TV.RefinesOn`). -/
@[problem "silmaril.shapes.c.tv.refines_on"
  (title := "Core refinement, and the profile's per-type check passes on both programs (a necessary filter, not a target statement)")]
def CRefinesOn (p : Profile) (src tgt : Codec.FileBindings) : Prop :=
  RefinesOn p src tgt

/-- **Function-level refinement over listed contexts** (`TV.ContextRefines`). -/
@[problem "silmaril.shapes.c.tv.context_refines"
  (title := "Replacing a function's Core definition refines the program, in each of a nonempty list of contexts that define it (listed contexts only, not contextual refinement)")]
def CContextRefines (impl : Spec.Impl) (ctxs : List Codec.FileBindings) (f : Sym)
    (before after : Core.FunDecl Codec.wireModel Unit Unit) : Prop :=
  FunctionRefines impl ctxs f before after

end Silmaril.Project.Shapes.CTV
