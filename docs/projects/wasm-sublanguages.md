# Wasm sublanguages and capabilities

Import `Silmaril.Wasm.Sublanguages.Thms` to move native syntax into Core 3.0
without losing information. Use `Profiles` for the edition-indexed syntax
and typing API or `Models.FeatureSet` for capabilities. These answer different
questions: **what AST do I have?** and **which Core features can it use?**

For the smaller strict module record, including function imports, see
[Strict and Ultrastrict](wasm-open-strict.md).

## Syntax and admission

`Language` chooses instruction, function and module types, with injective maps
into their actual Core counterparts. For example, `wasm1.Module` is the native
`V1.Module`, `wasm1.toModule` emits Core, and `wasm1IntoLime.mod` emits native
Lime. `limeIntoWasm2` lands in the domain of the ordinary V2 AST translation:
arbitrary V2 syntax can fail to translate, but `wasm2OfChecked` accepts any
natively checked V2 module and `wasm2_checked_image` agrees exactly with its
interface-preserving checked Core translation. This is not binary retagging.
The [version injection guide](wasm-version-injections.md) covers the native
typing and semantic transfer results and their exceptions. FX is not an
object here: the modeled conservative Core-to-FX map with no FX bindings
does not give an erasure of arbitrary FX instructions or functions.

An `Inclusion` maps all three syntax sorts and commutes with their Core maps.
Use `arrow.comp next`, `language.intoCore` and `arrow.modules` without category
notation. The same maps are the arrows of a thin Mathlib category over Core:
between fixed images there is at most one exact inclusion. Identity and
composition act pointwise; `moduleFunctor` forgets to module types. For an
example beyond editions, `strictIntoFunctional` relaxes mutable GC and
exception restrictions while preserving the same closed-module shape.

`language.Admits caps mod` checks the image of `mod` against a feature set.
`Inclusion.admits` is an iff for an exact inclusion at fixed capabilities;
`Language.admittedImage_mono` grows the admitted Core image along a syntax
inclusion and a capability inequality. The capability order is the existing
bounded distributive `Models.FeatureSet` lattice, with prerequisite-closed
intersection and union; `language.admission` is its monotone map into sets of
Core modules. Edition tags do not form that lattice. Joining
capabilities can admit a module that combines features from both operands;
it is not a union operation on syntax images. Admission is neither native
validation nor a choice of operational policy.

## Lift the existing partial Core linker

Import `Silmaril.Wasm.Sublanguages.Link.Thms` and call, for example,
`wasm1Readback.link? "p" provider consumer`. It calls `Link.GC.link?` on the
exact Core images, asks the native reader for a candidate, and checks exact
Core equality using the existing certified encoder comparison. A successful
candidate is not accepted merely because it parses. In particular, a version
reader can recognize a retagged form that does not erase back to the input.

- `Readback.link?_square` identifies the actual Core linker output exactly.
  `link?_complete` requires an encodable Core result already known to be in
  the source image; `link?_natural` commutes with any inclusion supplied with
  a target read-back on that image.
- `link?_valid` and `link?_intrinsic` recover Core validation and an intrinsic
  Core witness. `link?_recipe` supplies the existing `Recipe.Assembly`,
  retaining the validated interfaces, resolved imports and relocation. With
  `link?_square`, it supplies the first two premises of
  `Link.GC.PreparedObservation.separate_linked_result`. That theorem still
  needs successful Core preparations, a typed invocation, and a source run.
- The [regression](../../tests/wasm/profiles/Sublanguages.lean) resolves an
  imported call, relocates the consumer's type and export, proves the native
  V1 output valid, and checks that the same link commutes into Lime. It also
  checks rejection of the wrong import namespace.

No unconditional closure, native validation reflection, native behavioral
equivalence, or Binaryen `wasm-merge` closure is inferred from injectivity.
The Core linker itself is partial, comparison can reject unencodable syntax,
and the closed functional image cannot express an unresolved consumer import.
For another linker, supply an interface-alignment theorem and either exact
output closure or a certified reader plus its success conditions before
reusing a Core result.

## Rooms and operational semantics

[`Room` and `Corridor`](../../Silmaril/Logic/Institution/Room.lean) distinguish
sentences, a category of models, and satisfaction. A syntax map can supply a
corridor's forward sentence translation if modules are the chosen sentences.
It supplies neither the backward model functor nor the satisfaction iff.
[`ClassicInstitution.equivRoomFunctor`](../../Silmaril/Logic/Institution/Basic.lean)
describes the missing functorial structure; the existing SpecTec institution
chains prove semantic facts for narrower domains. The syntax category here is
also distinct from `Wasm.Category.Linking`, whose arrows are paths of
instances. An operational client may select `HasOpSem` separately; neither
`Language` nor a capability set selects UB, effects or observers.

Reproduce with `make check CHECK_TARGETS=+Silmaril.Wasm.Sublanguages.Link.Thms`.
